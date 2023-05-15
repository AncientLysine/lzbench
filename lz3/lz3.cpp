#include <algorithm>
#include <cassert>
#include <memory>
#include <vector>

#define LZ3_LIBRARY
#include "lz3.h"

#ifndef NDEBUG
#include <fstream>
#endif

using namespace std;

//3 byte variant of LZ4 for textures

template<typename T, size_t capacity>
class LZ3_stack_vector
{
    T count;
    T arena[capacity];
    unique_ptr<T[]> extra;

public:
    LZ3_stack_vector() : count(0), arena{ 0 }
    {
    }

    void push_back(T value)
    {
        if (count < capacity)
        {
            arena[count] = value;
            count++;
        }
        else
        {
            T alloc;
            if (extra)
            {
                alloc = extra[0];
            }
            else
            {
                alloc = 32;
                extra = make_unique<T[]>(alloc);
                extra[0] = alloc;
                copy(&arena[0], &arena[count], &extra[1]);
            }
            count++;
            if (count >= alloc)
            {
                alloc *= 2;
                auto extend = make_unique<T[]>(alloc);
                extend[0] = alloc;
                copy(&extra[1], &extra[count], &extend[1]);
                extra.swap(extend);
            }
            extra[count] = value;
        }
    }

    typedef const T* const_iterator;

    const_iterator cbegin() const
    {
        if (count <= capacity)
        {
            return &arena[0];
        }
        else
        {
            return &extra[1];
        }
    }

    const_iterator cend() const
    {
        if (count <= capacity)
        {
            return &arena[count];
        }
        else
        {
            return &extra[count + 1];
        }
    }
};

static constexpr uint32_t hash_length = 3;
static constexpr uint32_t hash_alloca = 7;

template<uint32_t capacity, uint32_t depth = 0>
class LZ3_hash_node
{
    LZ3_hash_node<capacity, depth + 1> children[capacity];

public:
    void insert(const uint8_t* sequence, uint16_t position)
    {
        auto& child = children[(*sequence) % capacity];
        child.insert(sequence + 1, position);
    }

    typedef LZ3_stack_vector<uint16_t, hash_alloca>::const_iterator const_iterator;

    pair<const_iterator, const_iterator> equal_range(const uint8_t* sequence) const
    {
        const auto& child = children[(*sequence) % capacity];
        return child.equal_range(sequence + 1);
    }
};

template<uint32_t capacity>
class LZ3_hash_node<capacity, hash_length>
{
    LZ3_stack_vector<uint16_t, hash_alloca> positions;

public:
    void insert(const uint8_t* seq, uint16_t position)
    {
        positions.push_back(position);
    }

    typedef LZ3_stack_vector<uint16_t, hash_alloca>::const_iterator const_iterator;

    pair<const_iterator, const_iterator> equal_range(const uint8_t* seq) const
    {
        return make_pair(positions.cbegin(), positions.cend());
    }
};


struct LZ3_match_info
{
    uint32_t position;
    uint32_t length;
    uint32_t offset;
    uint32_t save;
};

uint32_t LZ3_compress(const uint8_t* src, uint8_t* dst, uint32_t srcSize)
{
    auto hash_table = make_unique<LZ3_hash_node<29>>();
    vector<uint32_t> overlap(min(srcSize, 0x1000u)); //overlap by offset / 8
    vector<LZ3_match_info> matches;
#ifndef NDEBUG
    ofstream fs("LZ3_compress.log");
#endif
    uint32_t srcPos = 0;
    for (; srcPos + hash_length - 1 < srcSize; srcPos++)
    {
        auto equal = hash_table->equal_range(&src[srcPos]);
        if (equal.first != equal.second)
        {
            uint32_t offset = 0;
            uint32_t length = 0;
            uint32_t save = 0;
            for (auto iter = equal.first; iter != equal.second; ++iter)
            {
                uint32_t i = *iter;
                uint32_t o = srcPos - i;
                if (o % 8 != 0 || o > 0x7FFF || overlap[o / 8] >= srcPos)
                {
                    continue;
                }
                if (memcmp(&src[srcPos], &src[i], 3) != 0)
                {
                    continue;
                }
                uint32_t l = 3;
                while (srcPos + l < srcSize && src[srcPos + l] == src[i + l])
                {
                    l++;
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
                matches.push_back({ srcPos, length, offset, save });
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
        hash_table->insert(&src[srcPos], srcPos);
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
            length -= 3;
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

uint32_t LZ3_decompress_fast(const uint8_t* src, uint8_t* dst, uint32_t dstSize)
{
#ifndef NDEBUG
    ofstream fs("LZ3_decompress.log");
#endif
    uint32_t srcPos = 0;
    uint32_t dstPos = 0;
    while (true)
    {
        uint8_t token = src[srcPos++];
        uint32_t literal = token >> 4;
        uint32_t length = token & 0xF;
        if (literal >= 0xF)
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
        uint8_t* dstPtr;
        const uint8_t* srcPtr;
        dstPtr = &dst[dstPos];
        srcPtr = &src[srcPos];
        for (uint32_t j = 0; j < literal; ++j)
        {
            dstPtr[j] = srcPtr[j];
        }
        srcPos += literal;
        dstPos += literal;
        if (dstPos == dstSize)
        {
            break;
        }
        uint32_t offset = src[srcPos++];
        if (offset & 0x80)
        {
            offset &= 0x7F;
            offset |= src[srcPos++] << 7;
        }
        offset *= 8;
        if (length >= 0xF)
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
        length += 3;
        dstPtr = &dst[dstPos];
        srcPtr = dstPtr - offset;
        for (uint32_t j = 0; j < length; ++j)
        {
            dstPtr[j] = srcPtr[j];
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
