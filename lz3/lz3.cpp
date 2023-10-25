#include <algorithm>
#include <cassert>
#include <cstring>
#include <memory>
#include <vector>

#define LZ3_LIBRARY
#include "lz3.h"

#if defined(LZ3_LOG) && !defined(NDEBUG)
#include <fstream>
#endif

#if defined(__GNUC__) || defined(__clang__)
#define LZ3_LIKELY(expr)   __builtin_expect(!!(expr), 1)
#define LZ3_UNLIKELY(expr) __builtin_expect(!!(expr), 0)
#else
#define LZ3_LIKELY(expr)   (expr)
#define LZ3_UNLIKELY(expr) (expr)
#endif

using namespace std;

/*3 byte variant of LZ4 for textures
* modify LZ4 sequence definition to allow match of 3 byte
* |            msb                           lsb               |
* |     1bit    |     7bit     |     4bit     |      4bit      |
* | offset mode | offset value | match length | literal length |
*/

static constexpr uint32_t hash_length = 3;
static constexpr uint32_t hash_bucket = 1 << 13;

struct LZ3_hash_node
{
    uint32_t position;

    LZ3_hash_node(uint32_t position) :
        position(position)
    {
    }
};

struct LZ3_match_info
{
    uint32_t position;
    uint32_t length;
    uint32_t offset;
    uint32_t header;
    uint32_t save;

    LZ3_match_info(uint32_t position, uint32_t length, uint32_t offset, uint32_t header, uint32_t save) :
        position(position), length(length), offset(offset), header(header), save(save)
    {
    }
};

template<uint32_t length>
uint32_t LZ3_FNV_hash(const uint8_t* bytes)
{
    uint32_t hash = 0x811c9dc5;
    for (uint32_t i = 0; i < length; i++)
    {
        hash ^= bytes[i];
        hash *= 0x01000193;
    }
    return hash;
}

inline void LZ3_write_VL48(uint8_t* dst, uint32_t& dstPos, uint32_t value)
{
    if (value >= 0xF)
    {
        value -= 0xF;
        while (value >= 0xFF)
        {
            dst[dstPos++] = 0xFF;
            value -= 0xFF;
        }
        dst[dstPos++] = value;
    }
}

inline uint32_t LZ3_read_VL48(const uint8_t* src, uint32_t& srcPos, uint32_t token)
{
    uint32_t value = token;
    if (token == 0xF)
    {
        while (true)
        {
            uint8_t e = src[srcPos++];
            value += e;
            if (e < 0xFF)
            {
                break;
            }
        }
    }
    return value;
}

inline uint32_t LZ3_sizeof_VL78(uint32_t value)
{
    if ((value % 8) == 0 && (value / 8) < 0x80)
    {
        return 1;
    }
    else
    {
        return 2;
    }
}

inline void LZ3_write_VL78(uint8_t* dst, uint32_t& dstPos, uint32_t token, uint32_t value)
{
    if ((token & 0x8000) == 0)
    {
        dst[dstPos++] = (token & 0xFF) ^ (value & 0xFF);
    }
}

inline uint32_t LZ3_read_VL78(const uint8_t* src, uint32_t& srcPos, uint32_t token)
{
    uint32_t value;
    if ((token & 0x8000) != 0)
    {
        value = ((token & 0x7F00) >> 8) * 8;
    }
    else
    {
        value = token ^ src[srcPos++];
    }
    return value;
}

static constexpr uint32_t wild_cmp_length = 8;

uint32_t LZ3_compress(const uint8_t* src, uint8_t* dst, uint32_t srcSize)
{
    vector<vector<LZ3_hash_node>> bytes_hash(hash_bucket);
    uint32_t outer_skip = 0;
    uint32_t inner_skip = 0;
    vector<LZ3_match_info> matches;
#if defined(LZ3_LOG) && !defined(NDEBUG)
    ofstream fs("LZ3_compress.log");
#endif
    uint32_t srcPos = 0;
    for (; srcPos + hash_length - 1 < srcSize; srcPos++)
    {
        uint32_t hash = LZ3_FNV_hash<hash_length>(&src[srcPos]);
        uint32_t slot = hash % hash_bucket;
        vector<LZ3_hash_node>& found = bytes_hash[slot];
        if (srcPos > outer_skip && found.size() > 0)
        {
        LZ3_restart_search:
            uint32_t inner_temp = inner_skip;
            for (auto iter = found.rbegin(); iter != found.rend(); ++iter)
            {
                uint32_t curPos = iter->position;
                uint32_t o = srcPos - curPos;
                if (o > 0x7FFF)
                {
                    break;
                }
                uint32_t h = LZ3_sizeof_VL78(o) + 1;
                if (h != 2 && srcPos <= inner_temp)
                {
                    continue;
                }
                uint32_t f = 0; //bytes matched forward
                {
                    //match forward
                    constexpr uint32_t srcShortLength = wild_cmp_length - 1;
                    uint32_t srcShortEnd = srcSize > srcShortLength ? srcSize - srcShortLength : 0;
                    while (srcPos + f < srcShortEnd && memcmp(&src[srcPos + f], &src[curPos + f], wild_cmp_length) == 0)
                    {
                        f += wild_cmp_length;
                    }
                    uint32_t srcExactEnd = srcSize;
                    while (srcPos + f < srcExactEnd && src[srcPos + f] == src[curPos + f])
                    {
                        f++;
                    }
                }
                uint32_t b = 0; //bytes matched backward
                {
                    //match backward
                    b += wild_cmp_length;
                    while (curPos >= b && memcmp(&src[srcPos - b], &src[curPos - b], wild_cmp_length) == 0)
                    {
                        b += wild_cmp_length;
                    }
                    b -= wild_cmp_length;
                    b += 1;
                    while (curPos >= b && src[srcPos - b] == src[curPos - b])
                    {
                        b++;
                    }
                    b -= 1;
                }
                uint32_t p = srcPos - b;
                uint32_t l = b + f;
                if (l <= h)
                {
                    continue;
                }
                uint32_t skip = (p + l) - hash_length;
                if (h == 2)
                {
                    outer_skip = max(outer_skip, skip);
                    if (inner_temp != 0 && outer_skip > inner_temp)
                    {
                        inner_skip = 0;
                        goto LZ3_restart_search;
                    }
                }
                else
                {
                    inner_skip = max(inner_skip, skip);
                }
                uint32_t s = l - h;
                bool assign = false;
                auto insert = matches.begin();
                for (auto i = matches.rbegin(); i != matches.rend(); ++i)
                {
                    if (i->position == p && i->header == h)
                    {
                        if (i->save < s)
                        {
                            *i = { p, l, o, h, s };
                        }
                        assign = true;
                        break;
                    }
                    if (i->position < p || (i->position == p && i->header < h))
                    {
                        insert = i.base();
                        break;
                    }
                }
                if (!assign)
                {
                    matches.insert(insert, { p, l, o, h, s });
                }
            }
        }
        found.emplace_back(srcPos);
    }
#if defined(LZ3_LOG) && !defined(NDEBUG)
    for (const LZ3_match_info& match : matches)
    {
        uint32_t position = match.position;
        uint32_t length = match.length;
        uint32_t offset = match.offset;
        fs << position << ": " << length << " " << offset << endl;
    }
#endif
    vector<uint32_t> filter(srcSize);
    vector<LZ3_match_info> upper;
    vector<LZ3_match_info> lower;
    stable_sort(matches.begin(), matches.end(), [](auto x, auto y) { return x.save > y.save; });
    for (uint32_t i = 0; i < matches.size();)
    {
        const LZ3_match_info* match;
        if (lower.size() > 0 && lower.back().save >= matches[i].save)
        {
            match = &lower.back();
            lower.pop_back();
        }
        else
        {
            match = &matches[i];
            i++;
        }
        uint32_t position = match->position;
        uint32_t length = match->length;
        uint32_t head = 0, tail = 0;
        for (uint32_t j = 0; j < length; j++)
        {
            if (filter[position + j] != 0)
            {
                head++;
            }
            else
            {
                break;
            }
        }
        for (uint32_t j = 0; j < length; j++)
        {
            if (filter[position + length - 1 - j] != 0)
            {
                tail++;
            }
            else
            {
                break;
            }
        }
        uint32_t shrink = head + tail;
        if (shrink == 0)
        {
            for (uint32_t j = 0; j < length; ++j)
            {
                filter[position + j] = i + 1;
            }
            upper.push_back(*match);
            continue;
        }
        if (match->save > shrink)
        {
            LZ3_match_info m{ position + head, length - shrink, match->offset, match->header, match->save - shrink };
            auto iter = upper_bound(lower.begin(), lower.end(), m, [](auto x, auto y) { return x.save < y.save; });
            lower.insert(iter, m);
        }
    }
    matches.swap(upper);
    stable_sort(matches.begin(), matches.end(), [](auto x, auto y) { return x.position < y.position; });
    srcPos = 0;
    uint32_t dstPos = 0;
    for (const LZ3_match_info& match : matches)
    {
        if (match.position < srcPos)
        {
            continue;
        }
        uint32_t literal = match.position - srcPos;
        uint32_t length = match.length;
        uint32_t offset = match.offset;
        length -= hash_length;
        uint16_t token = (literal >= 0xF ? 0xF : literal) | ((length >= 0xF ? 0xF : length) << 4) | ((LZ3_sizeof_VL78(offset) == 2 ? (offset >> 8) : ((offset / 8) | 0x80)) << 8);
        memcpy(&dst[dstPos], &token, 2);
        dstPos += 2;
        LZ3_write_VL48(dst, dstPos, literal);
        memcpy(&dst[dstPos], &src[srcPos], literal);
        dstPos += literal;
        srcPos += literal;
        LZ3_write_VL78(dst, dstPos, token, offset);
        LZ3_write_VL48(dst, dstPos, length);
        srcPos += match.length;
    }
    if (srcSize > srcPos)
    {
        uint32_t literal = srcSize - srcPos;
        uint16_t token = (literal >= 0xF ? 0xF : literal);
        memcpy(&dst[dstPos], &token, 2);
        dstPos += 2;
        LZ3_write_VL48(dst, dstPos, literal);
        memcpy(&dst[dstPos], &src[srcSize - literal], literal);
        dstPos += literal;
    }
    vector<uint8_t> test(srcSize);
    assert(LZ3_decompress_fast(dst, test.data(), srcSize) == dstPos);
    for (uint32_t i = 0; i < srcSize; ++i)
    {
        assert(test[i] == src[i]);
    }
    return dstPos;
}

static constexpr uint32_t wild_cpy_length = 16;

uint32_t LZ3_decompress_fast(const uint8_t* src, uint8_t* dst, uint32_t dstSize)
{
#if defined(LZ3_LOG) && !defined(NDEBUG)
    ofstream fs("LZ3_decompress.log");
#endif
    uint32_t srcPos = 0;
    uint32_t dstPos = 0;
    constexpr uint32_t literalShortLen = min(wild_cpy_length, 14u);
    constexpr uint32_t matchShortLen = min(wild_cpy_length, 14u + hash_length);
    constexpr uint32_t dstShortLen = literalShortLen + matchShortLen;
    uint32_t dstShortEnd = dstSize > dstShortLen ? dstSize - dstShortLen : 0;
    while (true)
    {
        uint16_t token;
        memcpy(&token, &src[srcPos], 2);
        srcPos += 2;
        uint32_t literal = token & 0xF;
        uint32_t length = (token >> 4) & 0xF;
        uint32_t offset;
        if (LZ3_LIKELY(literal <= literalShortLen && dstPos < dstShortEnd))
        {
            memcpy(&dst[dstPos], &src[srcPos], wild_cpy_length);
            dstPos += literal;
            srcPos += literal;
            offset = LZ3_read_VL78(src, srcPos, token);
            if (LZ3_LIKELY(length + hash_length <= matchShortLen && offset >= wild_cpy_length))
            {
                length = length + hash_length;
                assert(dstPos >= offset);
                uint32_t refPos = dstPos - offset;
                memcpy(&dst[dstPos], &dst[refPos], wild_cpy_length);
#if defined(LZ3_LOG) && !defined(NDEBUG)
                fs << dstPos << ": " << length << " " << offset << endl;
#endif
                dstPos += length;
                continue;
            }
        }
        else
        {
            literal = LZ3_read_VL48(src, srcPos, literal);
            uint32_t cpyEnd = dstPos + literal;
            uint32_t cpyPos = dstPos;
            uint32_t refPos = srcPos;
            if (cpyEnd <= dstShortEnd/*dstEnd - (wild_cpy_length - 1)*/)
            {
                while(cpyPos < cpyEnd)
                {
                    memcpy(&dst[cpyPos], &src[refPos], wild_cpy_length);
                    cpyPos += wild_cpy_length;
                    refPos += wild_cpy_length;
                }
            }
            else
            {
                assert(cpyEnd <= dstSize);
                memcpy(&dst[cpyPos], &src[refPos], literal);
            }
            dstPos += literal;
            srcPos += literal;
            if (dstPos == dstSize)
            {
                break;
            }
            offset = LZ3_read_VL78(src, srcPos, token);
        }
        {
            length = LZ3_read_VL48(src, srcPos, length) + hash_length;
            uint32_t cpyEnd = dstPos + length;
            uint32_t cpyPos = dstPos;
            uint32_t refPos = dstPos - offset;
            if (cpyEnd <= dstShortEnd/*dstEnd - (wild_cpy_length - 1)*/ && offset >= wild_cpy_length)
            {
                while(cpyPos < cpyEnd)
                {
                    memcpy(&dst[cpyPos], &dst[refPos], wild_cpy_length);
                    cpyPos += wild_cpy_length;
                    refPos += wild_cpy_length;
                }
            }
            else
            {
                assert(cpyEnd <= dstSize);
                while(cpyPos < cpyEnd)
                {
                    dst[cpyPos++] = dst[refPos++];
                }
            }
#if defined(LZ3_LOG) && !defined(NDEBUG)
            fs << dstPos << ": " << length << " " << offset << endl;
#endif
            dstPos += length;
            if (dstPos == dstSize)
            {
                break;
            }
        }
    }
    return srcPos;
}
