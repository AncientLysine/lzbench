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

using namespace std;

//3 byte variant of LZ4 for textures

static constexpr uint32_t hash_length = 3;
static constexpr uint32_t hash_bucket = 1 << 13;
static constexpr uint32_t wild_length = 8;

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

    LZ3_match_info(uint32_t position, uint32_t length, uint32_t offset) :
        position(position), length(length), offset(offset)
    {
    }

    uint32_t header() const
    {
        return (offset % 8 == 0 && offset / 8 <= 0x7F) ? 2 : 3;
    }

    uint32_t save() const
    {
        return length - header();
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

void LZ3_write_VL16(uint8_t* dst, uint32_t& dstPos, uint32_t var)
{
    if (var % 8 != 0 || var / 8 > 0x7F)
    {
        dst[dstPos++] = (uint8_t)((var & 0x7F) | 0x80);
        var >>= 7;
        dst[dstPos++] = (uint8_t)((var & 0xFF) ^ 0x01);
    }
    else
    {
        dst[dstPos++] = (uint8_t)(var / 8);
    }
}

uint32_t LZ3_read_VL16(const uint8_t* src, uint32_t& srcPos)
{
    uint32_t var = src[srcPos++];
    if (var & 0x80)
    {
        var ^= src[srcPos++] << 7;
    }
    else
    {
        var *= 8;
    }
    return var;
}

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
                uint32_t h = (o % 8 == 0 && o / 8 <= 0x7F) ? 2 : 3;
                if (h != 2 && srcPos <= inner_temp)
                {
                    continue;
                }
                uint32_t f = 0; //bytes matched forward
                {
                    //match forward
                    uint32_t srcShortEnd = srcSize - wild_length + 1;
                    while (srcPos + f < srcShortEnd && memcmp(&src[srcPos + f], &src[curPos + f], wild_length) == 0)
                    {
                        f += wild_length;
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
                    b += wild_length;
                    while (curPos >= b && memcmp(&src[srcPos - b], &src[curPos - b], wild_length) == 0)
                    {
                        b += wild_length;
                    }
                    b -= wild_length;
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
                    if (i->position == p && i->header() == h)
                    {
                        if (i->save() < s)
                        {
                            *i = { p, l, o };
                        }
                        assign = true;
                        break;
                    }
                    if (i->position < p || (i->position == p && i->header() < h))
                    {
                        insert = i.base();
                        break;
                    }
                }
                if (!assign)
                {
                    matches.insert(insert, { p, l, o });
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
    stable_sort(matches.begin(), matches.end(), [](auto x, auto y) { return x.save() > y.save(); });
    for (uint32_t i = 0; i < matches.size();)
    {
        const LZ3_match_info* match;
        if (lower.size() > 0 && lower.back().save() >= matches[i].save())
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
        if (head + tail == 0)
        {
            for (uint32_t j = 0; j < length; ++j)
            {
                filter[position + j] = i + 1;
            }
            upper.push_back(*match);
            continue;
        }
        if (match->save() > head + tail)
        {
            LZ3_match_info m{ position + head, length - head - tail, match->offset };
            auto iter = upper_bound(lower.begin(), lower.end(), m, [](auto x, auto y) { return x.save() < y.save(); });
            lower.insert(iter, m);
        }
    }
    matches.swap(upper);
    stable_sort(matches.begin(), matches.end(), [](auto x, auto y) { return x.position < y.position; });
    srcPos = 0;
    uint32_t dstPos = 0;
    for (const LZ3_match_info& match : matches)
    {
        if (match.position >= srcPos)
        {
            uint32_t literal = match.position - srcPos;
            uint32_t length = match.length;
            uint32_t offset = match.offset;
            length -= hash_length;
            dst[dstPos++] = (uint8_t)(((literal >= 0xF ? 0xF : literal) << 4) | (length >= 0xF ? 0xF : length));
            for (int32_t e = (int32_t)literal - 0xF; e >= 0; e -= 0xFF)
            {
                dst[dstPos++] = (uint8_t)(e >= 0xFF ? 0xFF : e);
            }
            memcpy(&dst[dstPos], &src[srcPos], literal);
            dstPos += literal;
            srcPos += literal;
            LZ3_write_VL16(dst, dstPos, offset);
            for (int32_t e = (int32_t)length - 0xF; e >= 0; e -= 0xFF)
            {
                dst[dstPos++] = (uint8_t)(e >= 0xFF ? 0xFF : e);
            }
            srcPos += match.length;
        }
    }
    if (srcSize > srcPos)
    {
        uint32_t literal = srcSize - srcPos;
        dst[dstPos++] = (uint8_t)((literal >= 0xF ? 0xF : literal) << 4);
        for (int32_t e = (int32_t)literal - 0xF; e >= 0; e -= 0xFF)
        {
            dst[dstPos++] = (uint8_t)(e >= 0xFF ? 0xFF : e);
        }
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

uint32_t LZ3_decompress_fast(const uint8_t* src, uint8_t* dst, uint32_t dstSize)
{
#if defined(LZ3_LOG) && !defined(NDEBUG)
    ofstream fs("LZ3_decompress.log");
#endif
    uint32_t srcPos = 0;
    uint32_t dstPos = 0;
    uint32_t dstShortEnd = dstSize - 14 - 16;
    while (true)
    {
        uint8_t token = src[srcPos++];
        uint32_t literal = token >> 4;
        uint32_t length = (token & 0xF) + hash_length;
        uint32_t offset;
        if (literal <= 14 && dstPos < dstShortEnd)
        {
            assert(dstPos + 16 <= dstSize);
            memcpy(&dst[dstPos], &src[srcPos], 16);
            dstPos += literal;
            srcPos += literal;
            offset = LZ3_read_VL16(src, srcPos);
            if (length <= 16 && offset >= 16)
            {
                uint32_t refPos = dstPos - offset;
                assert(dstPos + 16 <= dstSize);
                memcpy(&dst[dstPos], &dst[refPos], 16);
#if defined(LZ3_LOG) && !defined(NDEBUG)
                fs << dstPos << ": " << length << " " << offset << endl;
#endif
                dstPos += length;
                continue;
            }
        }
        else
        {
            if (literal == 0xF)
            {
                while (true)
                {
                    uint8_t e = src[srcPos++];
                    literal += e;
                    if (e < 0xFF)
                    {
                        break;
                    }
                }
            }
            uint32_t outPos = dstPos;
            uint32_t refPos = srcPos;
            if (dstPos + literal <= dstShortEnd)
            {
                for (uint32_t j = 0; j < literal; j += wild_length)
                {
                    assert(outPos + wild_length <= dstSize);
                    memcpy(&dst[outPos], &src[refPos], wild_length);
                    outPos += wild_length;
                    refPos += wild_length;
                }
            }
            else
            {
                assert(dstPos + literal <= dstSize);
                memcpy(&dst[dstPos], &src[srcPos], literal);
            }
            dstPos += literal;
            srcPos += literal;
            if (dstPos == dstSize)
            {
                break;
            }
            offset = LZ3_read_VL16(src, srcPos);
        }
        {
            if (length == 0xF + hash_length)
            {
                while (true)
                {
                    uint8_t e = src[srcPos++];
                    length += e;
                    if (e < 0xFF)
                    {
                        break;
                    }
                }
            }
            uint32_t outPos = dstPos;
            uint32_t refPos = dstPos - offset;
            if (outPos + length < dstShortEnd && offset >= wild_length)
            {
                for (uint32_t j = 0; j < length; j += wild_length)
                {
                    assert(outPos + wild_length <= dstSize);
                    memcpy(&dst[outPos], &dst[refPos], wild_length);
                    outPos += wild_length;
                    refPos += wild_length;
                }
            }
            else
            {
                for (uint32_t j = 0; j < length; j++)
                {
                    assert(outPos < dstSize);
                    dst[outPos++] = dst[refPos++];
                }
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
    return srcPos;
}
