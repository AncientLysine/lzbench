#include <algorithm>
#include <cassert>
#include <cstring>
#include <memory>
#include <vector>

#define LZ3_LIBRARY
#include "lz3.h"

#ifndef NDEBUG
#include <fstream>
#endif

using namespace std;

//3 byte variant of LZ4 for textures

static constexpr uint32_t hash_length = 3;
static constexpr uint32_t hash_size = 1024;
static constexpr uint32_t next_height = 4;
static constexpr uint32_t wild_length = 8;

struct LZ3_hash_node
{
    uint32_t position;
    uint8_t next[next_height];

    LZ3_hash_node(uint32_t position) :
        position(position), next{ 0 }
    {
    }
};

struct LZ3_match_info
{
    uint32_t position;
    uint32_t length;
    uint32_t offset;
    uint32_t save;

    LZ3_match_info(uint32_t position, uint32_t length, uint32_t offset, uint32_t save):
        position(position), length(length), offset(offset), save(save)
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

template<typename iterator>
uint32_t LZ3_jump_next(iterator& iter, uint32_t matched)
{
    uint32_t limited = min(matched, hash_length + next_height - 1);
    for (int32_t i = (int32_t)limited - hash_length; i >= 0; i--)
    {
        uint8_t next = iter->next[i];
        if (next != 0)
        {
            iter += next;
            return next != 0xFF ? i + hash_length : 0;
        }
    }
    ++iter;
    return 0;
}

uint32_t LZ3_compress(const uint8_t* src, uint8_t* dst, uint32_t srcSize)
{
    vector<vector<LZ3_hash_node>> hash_chain(hash_size); //morphing match chain
    vector<uint32_t> overlap(min(srcSize, 0x1000u)); //overlap by offset / 8
    vector<LZ3_match_info> matches;
#ifndef NDEBUG
    ofstream fs("LZ3_compress.log");
#endif
    uint32_t srcPos = 0;
    for (; srcPos + hash_length - 1 < srcSize; srcPos++)
    {
        uint32_t hash = LZ3_FNV_hash<hash_length>(&src[srcPos]);
        uint32_t slot = hash % hash_size;
        vector<LZ3_hash_node>& found = hash_chain[slot];
        if (found.size() > 0)
        {
            uint32_t length = 0;
            uint32_t offset = 0;
            uint32_t save = 0;
            uint32_t threshold = hash_length; //bytes match threshold to be record
            uint32_t sure = 0; //bytes sure to be matched after skip
            for (auto iter = found.rbegin(), prev = found.rend(); iter != found.rend(); sure = LZ3_jump_next(iter, sure))
            {
                uint32_t curPos = iter->position;
                assert(memcmp(&src[srcPos], &src[curPos], sure) == 0);
                uint32_t o = srcPos - curPos;
                if (o > 0x7FFF)
                {
                    break;
                }
                if (o % 8 != 0)
                {
                    continue;
                }
                uint32_t l = sure;
                if (l < threshold)
                {
                    uint32_t srcLimitEnd = min(srcSize, srcPos + threshold);
                    while (srcPos + l < srcLimitEnd && src[srcPos + l] == src[curPos + l])
                    {
                        l++;
                    }
                    if (l < threshold)
                    {
                        sure = l;
                        continue;
                    }
                    uint32_t height = threshold - hash_length;
                    if (height < next_height && prev != found.rend())
                    {
                        assert(memcmp(&src[prev->position], &src[iter->position], threshold) == 0);
                        uint8_t next = (uint8_t)min<size_t>(iter - prev, 0xFF);
                        if (next > 0)
                        {
                            //assert(prev->next[height] == 0);
                            prev->next[height] = next;
                        }
                    }
                }
                prev = iter;
                if (overlap[o / 8] >= srcPos)
                {
                    sure = l;
                    continue;
                }
                {
                    uint32_t srcShortEnd = srcSize - wild_length + 1;
                    while (srcPos + l < srcShortEnd && memcmp(&src[srcPos + l], &src[curPos + l], wild_length) == 0)
                    {
                        l += wild_length;
                    }
                    uint32_t srcExactEnd = srcSize;
                    while (srcPos + l < srcExactEnd && src[srcPos + l] == src[curPos + l])
                    {
                        l++;
                    }
                    sure = l;
                }
                if (threshold < l)
                {
                    threshold = min(l, hash_length + next_height - 1);
                }
                uint32_t h = o / 8 > 0x7F ? 3 : 2;
                if (l <= h)
                {
                    continue;
                }
                uint32_t s = l - h;
                if (save < s || (save == s && offset > o))
                {
                    offset = o;
                    length = l;
                    save = s;
                }
            }
            if (save > 0)
            {
                matches.emplace_back(srcPos, length, offset, save);
#ifndef NDEBUG
                fs << srcPos << ": " << length << " " << offset << endl;
#endif
                uint32_t e = srcPos + length;
                for (uint32_t o = offset; o <= max(length, offset); o += offset)
                {
                    uint32_t i = o / 8;
                    overlap[i] = max(overlap[i], e);
                }
            }
        }
        found.emplace_back(srcPos);
    }
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
        if (head + tail == 0)
        {
            for (uint32_t j = 0; j < length; ++j)
            {
                filter[position + j] = i + 1;
            }
            upper.push_back(*match);
            continue;
        }
        uint32_t offset = match->offset;
        uint32_t save = match->save;
        if (save > head + tail)
        {
            LZ3_match_info m{ position + head, length - head - tail, offset, save - head - tail };
            auto iter = upper_bound(lower.begin(), lower.end(), m, [](auto x, auto y) { return x.save < y.save; });
            lower.insert(iter, m);
        }
    }
    matches.swap(upper);
    stable_sort(matches.begin(), matches.end(), [](auto x, auto y) { return x.position < y.position; });
    srcPos = 0;
    uint32_t dstPos = 0;
    for (const auto& match : matches)
    {
        if (match.position >= srcPos)
        {
            uint32_t literal = match.position - srcPos;
            uint32_t length = match.length;
            uint32_t offset = match.offset;
            length -= hash_length;
            offset /= 8;
            dst[dstPos++] = (uint8_t)(((literal >= 0xF ? 0xF : literal) << 4) | (length >= 0xF ? 0xF : length));
            for (int32_t e = (int32_t)literal - 0xF; e >= 0; e -= 0xFF)
            {
                dst[dstPos++] = (uint8_t)(e >= 0xFF ? 0xFF : e);
                if (e < 0xFF)
                {
                    break;
                }
            }
            memcpy(&dst[dstPos], &src[srcPos], literal);
            dstPos += literal;
            srcPos += literal;
            if (offset <= 0x7F)
            {
                dst[dstPos++] = (uint8_t)offset;
            }
            else
            {
                dst[dstPos++] = (uint8_t)((offset & 0x7F) | 0x80);
                dst[dstPos++] = (uint8_t)((offset >> 7) & 0xFF);
            }
            for (int32_t e = (int32_t)length - 0xF; e >= 0; e -= 0xFF)
            {
                dst[dstPos++] = (uint8_t)(e >= 0xFF ? 0xFF : e);
                if (e < 0xFF)
                {
                    break;
                }
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
            if (e < 0xFF)
            {
                break;
            }
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

uint32_t LZ3_read_VL16(const uint8_t* src, uint32_t& srcPos)
{
    uint32_t var = src[srcPos++];
    if (var & 0x80)
    {
        var &= 0x7F;
        var |= src[srcPos++] << 7;
    }
    return var;
}

uint32_t LZ3_decompress_fast(const uint8_t* src, uint8_t* dst, uint32_t dstSize)
{
#ifndef NDEBUG
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
            if (dstPos == dstSize)
            {
                break;
            }
            offset = LZ3_read_VL16(src, srcPos);
            offset *= 8;
            if (length <= 16 && offset >= 16)
            {
                uint32_t refPos = dstPos - offset;
                assert(dstPos + 16 <= dstSize);
                memcpy(&dst[dstPos], &dst[refPos], 16);
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
            offset *= 8;
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
            if (outPos + length < dstShortEnd)
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
#ifndef NDEBUG
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
