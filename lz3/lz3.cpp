#include <algorithm>
#include <cassert>
#include <cstring>
#include <memory>
#include <map>
#include <unordered_map>
#include <vector>

#define LZ3_LIBRARY
#include "lz3.h"

#if defined(LZ3_LOG) && !defined(NDEBUG)
#include <fstream>
#include <iomanip>
#endif

#if defined(__GNUC__) || defined(__clang__)
#define LZ3_LIKELY(expr)   __builtin_expect(!!(expr), 1)
#define LZ3_UNLIKELY(expr) __builtin_expect(!!(expr), 0)
#define LZ3_ALIGN(pot)     __asm__(".p2align "#pot)
#else
#define LZ3_LIKELY(expr)   (expr)
#define LZ3_UNLIKELY(expr) (expr)
#define LZ3_ALIGN(pot)
#endif

using namespace std;

/*3 byte variant of LZ4 for textures
* modify LZ4 sequence definition to allow match of 3 byte
* |            msb                           lsb               |
* |     1bit    |     7bit     |     4bit     |      4bit      |
* | offset mode | offset value | match length | literal length |
*/

static constexpr uint32_t max_block_size = 0x8000;

class LZ3_suffix_array
{
public:
    uint32_t n;

    uint32_t* sa;
    uint32_t* rk;

    //字符串为s，长度为n
    //sa是我们要求的后缀数组
    //rk数组保存的值相当于是rank值。下面的操作只是用rk数组来比较字符的大小，所以没有必要求出当前真实的rank值。所以这里rk保存位置i的字符就好
    //最后返回的rk才是rank值，rk[i]=后缀i的名次
    void cal_suffix_array(const uint8_t* s, uint32_t l) {
        uint32_t bucket_count = 256;

        n = l;
        sa = &buffer[0];
        rk = &buffer[max_block_size];
        uint32_t* sa_2nd = &buffer[max_block_size * 2];
        uint32_t* rk_2nd = &buffer[max_block_size * 3];
        uint32_t* bucket = &buffer[max_block_size * 4];

        //对第一个字符排序
        fill(bucket, bucket + bucket_count, 0);
        for (uint32_t i = 0; i < n; ++i) ++bucket[rk[i] = s[i]];
        for (uint32_t i = 1; i < bucket_count; ++i) bucket[i] += bucket[i - 1];
        for (int32_t i = n - 1; i >= 0; --i) sa[--bucket[rk[i]]] = i;

        //对长度为2^j的后缀排序
        for (uint32_t j = 1;; j *= 2) {
            //接下来进行若干次基数排序，在实现的时候，这里有一个小优化。
            //基数排序要分两次，第一次是对第二关键字排序，第二次是对第一关键字排序。
            //对第二关键字排序的结果实际上可以利用上一次求得的sa直接算出，没有必要再算一次。

            //数组sa_2nd保存的是对第二关键字排序的结果,sa_2nd[p] = 排名为p的为哪个后缀的第二关键字
            uint32_t p = 0;
            for (uint32_t i = n - j; i < n; ++i) sa_2nd[p++] = i; // 因为从n - j开始后面的第二部分都是空串，所以排在前面
            for (uint32_t i = 0; i < n; ++i) if (sa[i] >= j) sa_2nd[p++] = sa[i] - j;

            //按第二关键字排序后，第一关键字的原排名。用第一关键字分桶就得到了一二关键字的排序

            //rk_2nd[i] = rk[sa_2nd[i]]是第二关键字排名为i的后缀的第一关键字排名
            for (uint32_t i = 0; i < n; ++i) rk_2nd[i] = rk[sa_2nd[i]]; // 按第二关键字排序，将rk[sa_2nd[i]]结果存起来，减少寻址次数。

            //分桶，排序
            fill(bucket, bucket + bucket_count, 0);
            for (uint32_t i = 0; i < n; ++i) ++bucket[rk_2nd[i]];
            for (uint32_t i = 1; i < bucket_count; ++i) bucket[i] += bucket[i - 1];
            for (int32_t i = n - 1; i >= 0; --i) sa[--bucket[rk_2nd[i]]] = sa_2nd[i];

            //求解新的rank数组

            //根据sa求rk。sa[i]是排名为i的后缀，rk[sa[i]] = 后缀sa[i]的排名
            swap(rk, rk_2nd);
            p = 0;
            rk[sa[0]] = p++;
            for (uint32_t i = 1; i < n; ++i) {
                //因为这里的sa数组对于后缀相同时，排名按位置前后排，所以这里rank还需要判重
                //对于两个后缀sa[i - 1]和sa[i]，他们第一关键字和第二关键字是否都一样，这个可以通过判断本来的rank在对应位置是否相同
                rk[sa[i]] = rank_both_equal(rk_2nd, sa[i - 1], sa[i], j, n) ? p - 1 : p++;
            }
            if (p >= n) {
                break;
            }
            bucket_count = p; //排序后，桶的数量可以减少到p
        }
    }

    uint32_t* height;

    void cal_height(const uint8_t* s, uint32_t l) {
        assert(l == n);
        height = &buffer[max_block_size * 4];

        uint32_t k = 0;
        for (uint32_t i = 0; i < l; ++i) {
            uint32_t r = rk[i];
            if (r == 0) {
                height[r] = 0;
                k = 0;
            }
            else {
                if (k > 0) --k;
                uint32_t j = sa[r - 1];
                while (i + k < l && j + k < l && s[i + k] == s[j + k]) ++k;
                height[r] = k;
            }
        }
    }

private:
    uint32_t buffer[max_block_size * 5];

    static bool rank_both_equal(uint32_t* r, uint32_t a, uint32_t b, uint32_t l, uint32_t n) {
        if (r[a] != r[b]) return false;
        // 如果开两倍空间，就可以省去下面的两个判断。
        if (a + l >= n && b + l >= n) return true;
        if (a + l >= n || b + l >= n) return false;
        return r[a + l] == r[b + l];
    }
};

static constexpr uint32_t min_match_length = 3;

class LZ3_match_info
{
public:
    uint32_t position;
    uint32_t length;
    uint32_t offset;

    LZ3_match_info(const LZ3_suffix_array* psa, uint32_t position) :
        position(position), length(max_block_size), offset(0)
    {
        prev = psa->rk[position];
        next = psa->rk[position] + 1;
    }

    bool match_next(const LZ3_suffix_array* psa)
    {
        while (true)
        {
            uint32_t index;
            if (prev > 0 && psa->height[prev] >= psa->height[next])
            {
                length = min(length, psa->height[prev]);
                index = psa->sa[--prev];
            }
            else if (next < psa->n)
            {
                length = min(length, psa->height[next]);
                index = psa->sa[next++];
            }
            else
            {
                return false;
            }
            if (length < min_match_length)
            {
                return false;
            }
            if (position > index)
            {
                offset = position - index;
                return true;
            }
        }
    }

private:
    uint32_t prev;    //向前遍历到的后缀排名
    uint32_t next;    //向后遍历到的后缀排名
};

template<typename T, typename Size = size_t, Size min_cap = 16>
class LZ3_vector
{
public:
    typedef T value_type;
    typedef Size size_type;
    typedef T* iterator;
    typedef const T* const_iterator;

    LZ3_vector():
        _data(_local), _size(0u)
    {
    }

    LZ3_vector(LZ3_vector&& other)
    {
        if (other._size > min_cap)
        {
            _data = other._data;
            _size = other._size;
            other._data = nullptr;
        }
        else
        {
            _size = other._size;
            copy(other.begin(), other.end(), begin());
        }
    }

    ~LZ3_vector()
    {
        if (_size > min_cap)
        {
            delete[] _data;
        }
    }

    iterator begin()
    {
        return _data;
    }

    iterator end()
    {
        return _data + _size;
    }

    const_iterator begin() const
    {
        return _data;
    }

    const_iterator end() const
    {
        return _data + _size;
    }

    size_type size() const
    {
        return _size;
    }

    size_type capacity() const
    {
        if (_size > min_cap)
        {
            return _cap;
        }
        else
        {
            return min_cap;
        }
    }

    iterator insert(iterator pos, const T& value)
    {
        size_t index = pos - begin();
        ensure_cap();
        pos = begin() + index;
        copy(pos, end(), pos + 1);
        *pos = value;
        ++_size;
        return pos;
    }

    void push_back(const T& value)
    {
        ensure_cap();
        *end() = value;
        ++_size;
    }

private:
    value_type* _data;
    size_type _size;
    union
    {
        value_type _local[min_cap];
        size_type _cap;
    };

    void ensure_cap()
    {
        if (_size > min_cap)
        {
            if (_size == _cap)
            {
                Size newCap = _cap * 2;
                T* newData = new T[newCap];
                copy(_data, _data + _size, newData);
                delete[] _data;
                _data = newData;
                _cap = newCap;
            }
        }
        else
        {
            if (_size == min_cap)
            {
                Size newCap = min_cap * 2;
                _data = new T[newCap];
                copy(_local, _local + _size, _data);
                _cap = newCap;
            }
        }
    }
};

inline void LZ3_write_LE16(uint8_t* dst, uint32_t& dstPos, uint16_t value)
{
    memcpy(&dst[dstPos], &value, sizeof(uint16_t));
    dstPos += sizeof(uint16_t);
}

inline uint16_t LZ3_read_LE16(const uint8_t* src, uint32_t& srcPos)
{
    uint16_t value;
    memcpy(&value, &src[srcPos], sizeof(uint16_t));
    srcPos += sizeof(uint16_t);
    return value;
}

inline void LZ3_write_VL16(uint8_t* dst, uint32_t& dstPos, uint16_t value)
{
    if (value < 0x80)
    {
        dst[dstPos++] = (value & 0xFF);
    }
    else
    {
        dst[dstPos++] = (value & 0x7F) | 0x80;
        value >>= 7;
        dst[dstPos++] = (value & 0xFF) ^ 0x01;
    }
}

inline uint16_t LZ3_read_VL16(const uint8_t* src, uint32_t& srcPos)
{
    uint16_t value = src[srcPos++];
    if (value & 0x80)
    {
        value ^= src[srcPos++] << 7;
    }
    return value;
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
        dst[dstPos++] = (uint8_t)value;
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

inline void LZ3_write_VL78(uint8_t* dst, uint32_t& dstPos, uint32_t token, uint32_t value)
{
    if ((token & 0x8000) == 0)
    {
        dst[dstPos++] = (token & 0xFF) ^ (value & 0xFF);
    }
}

inline uint32_t LZ3_read_VL78(const uint8_t* src, uint32_t& srcPos, uint32_t token, const uint16_t* dictPre)
{
    if ((token & 0x8000) == 0)
    {
        return token ^ src[srcPos++];
    }
    else
    {
        return dictPre[token >> 8];
    }
}

uint32_t LZ3_compress(const uint8_t* src, uint8_t* dst, uint32_t srcSize)
{
    LZ3_suffix_array* psa = new LZ3_suffix_array();
    psa->cal_suffix_array(src, srcSize);
    psa->cal_height(src, srcSize);
#if defined(LZ3_LOG) && !defined(NDEBUG)
    ofstream sfs("LZ3_suffix_array.log");
    for (uint32_t i = 0; i < srcSize; ++i)
    {
        sfs << dec << setfill(' ') << left << setw(5) << psa->sa[i] << ": ";
        sfs << dec << setfill(' ') << left << setw(5) << psa->height[i] << "| ";
        uint32_t l = psa->height[i];
        if (i + 1 < srcSize)
        {
            l = max(l, psa->height[i + 1]);
        }
        if (i + l + 1 < srcSize)
        {
            l = l + 1;
        }
        for (uint32_t j = 0; j < l; ++j)
        {
            uint8_t c = src[psa->sa[i] + j];
            if (' ' <= c && c <= '~')
            {
                sfs.put((char)c);
            }
            else
            {
                sfs << "\\0x" << hex << setfill('0') << right << setw(2) << (uint32_t)c;
            }
        }
        sfs << endl;
    }
    ofstream cfs("LZ3_compress.log");
#endif
    vector<LZ3_match_info> candidates;
    for (uint32_t i = 1; i < srcSize; ++i)
    {
        LZ3_match_info match(psa, i);
        if (match.match_next(psa))
        {
            candidates.push_back(match);
        }
    }
    uint32_t maxLength = 0;
    for (const LZ3_match_info& match : candidates)
    {
        maxLength = max(maxLength, match.length);
    }
    vector<uint32_t> countByLength(maxLength + 1, 0);
    for (const LZ3_match_info& match : candidates)
    {
        countByLength[match.length]++;
    }
    for (size_t i = maxLength; i > 0 ; --i)
    {
        countByLength[i - 1] += countByLength[i];
    }
    vector<uint32_t> orderByLength(candidates.size());
    for (auto match = candidates.cend(); match != candidates.cbegin(); )
    {
        --match;
        uint32_t length = match->length;
        uint32_t index = (uint32_t)distance(candidates.cbegin(), match);
        orderByLength[--countByLength[length]] = index;
    }
    vector<uint16_t> stained(srcSize);
    vector<uint32_t> matches;
    for (auto i = orderByLength.begin(); i != orderByLength.end(); ++i)
    {
        uint32_t index = *i;
        LZ3_match_info& match = candidates[index];
        uint32_t length = match.length;
        if (length < min_match_length)
        {
            break;
        }
        uint32_t position = match.position;
        if (stained[position] != 0)
        {
            continue;
        }
        if (stained[position + length - 1] != 0)
        {
            length--;
            while (length >= min_match_length && stained[position + length - 1] != 0)
            {
                length--;
            }
            if (length >= min_match_length)
            {
                auto findBegin = orderByLength.begin() + countByLength[length];
                auto findEnd = orderByLength.begin() + countByLength[length - 1];
                auto moveBegin = i + 1;
                auto moveEnd = upper_bound(findBegin, findEnd, index);
                auto moveNext = copy(moveBegin, moveEnd, i);
                *moveNext = index;
                for (uint32_t l = match.length; l > length; --l)
                {
                    countByLength[l - 1]--;
                }
                match.length = length;
                --i;
            }
            continue;
        }
        matches.push_back(index);
        if (length > min_match_length)
        {
            //match longer than 3 bytes, sure to survive
            uint16_t stain = (uint16_t)matches.size();
            for (uint32_t j = 0; j < length; ++j)
            {
                stained[position + j] = stain;
            }
        }
    }
    unordered_map<uint32_t, LZ3_vector<uint16_t, uint16_t, 3>> offsets;
    for (uint32_t index : matches)
    {
        const LZ3_match_info& match = candidates[index];
        uint32_t offset = match.offset;
        auto& vec = offsets[offset];
        vec.push_back((uint16_t)index);
    }
    map<uint32_t, LZ3_vector<uint16_t, uint16_t, 3>> orderByOccur;
    for (const auto& i : offsets)
    {
        uint16_t offset = (uint16_t)i.first;
        uint32_t occur = i.second.size();
        auto& vec = orderByOccur[occur];
        auto ins = upper_bound(vec.begin(), vec.end(), offset);
        vec.insert(ins, offset);
    }
    for (const auto& i : orderByOccur)
    {
        for (uint16_t offset : i.second)
        {
            auto j = offsets.find(offset);
            uint32_t occur = j->second.size();
            if (occur > i.first)
            {
                auto& vec = orderByOccur[occur];
                auto ins = upper_bound(vec.begin(), vec.end(), offset); //does insert postion matters here?
                vec.insert(ins, offset);
                continue;
            }
            if (offsets.size() <= 128 && occur > sizeof(uint16_t)/*sizeof mode1 offset desc*/)
            {
                break;
            }
            for (uint32_t index : j->second)
            {
                LZ3_match_info& match = candidates[index];
                auto o = offsets.end();
                LZ3_match_info m = match;
                while (m.match_next(psa))
                {
                    if (m.length < match.length)
                    {
                        break;
                    }
                    o = offsets.find(m.offset);
                    if (o != offsets.end())
                    {
                        match = m;
                        offsets[m.offset].push_back((uint16_t)index);
                        break;
                    }
                }
            }
            offsets.erase(j);
            if (offsets.empty())
            {
                break;
            }
        }
    }
    delete psa;
    for (auto i = matches.begin(); i != matches.end();)
    {
        const LZ3_match_info& match = candidates[*i];
        uint32_t length = match.length;
        if (length > min_match_length)
        {
            ++i;
            continue;
        }
        uint32_t position = match.position;
        if (stained[position] != 0 || stained[position + length - 1] != 0)
        {
            i = matches.erase(i);
            continue;
        }
        if (offsets.find(match.offset) != offsets.end())
        {
            //match exactly 3 bytes, needs a frequent offset to survive
            uint16_t stain = (uint16_t)matches.size();
            for (uint32_t j = 0; j < length; ++j)
            {
                stained[position + j] = stain;
            }
            ++i;
        }
        else
        {
            i = matches.erase(i);
        }
    }
    sort(matches.begin(), matches.end());
#if defined(LZ3_LOG) && !defined(NDEBUG)
    for (const LZ3_match_info& match : matches)
    {
        uint32_t position = match.position;
        uint32_t length = match.length;
        uint32_t offset = match.offset;
        cfs << position << ": " << length << " " << offset << endl;
    }
#endif
    uint16_t dict[128];
    uint32_t dictSize = 0;
    for (const auto& i : offsets)
    {
        dict[dictSize++] = (uint16_t)i.first;
    }
    sort(dict, dict + dictSize);
    uint32_t srcPos = 0;
    uint32_t dstPos = 0;
    dst[dstPos++] = (uint8_t)dictSize;
    for (uint32_t i = 0; i < dictSize; ++i)
    {
        LZ3_write_VL16(dst, dstPos, dict[i]);
    }
    for (uint32_t i : matches)
    {
        const LZ3_match_info& match = candidates[i];
        uint32_t position = match.position;
        if (position < srcPos)
        {
            continue;
        }
        uint32_t literal = position - srcPos;
        uint32_t length = match.length;
        length -= min_match_length;
        uint32_t offset = match.offset;
        uint16_t token = (uint16_t)((literal >= 0xF ? 0xF : literal) | ((length >= 0xF ? 0xF : length) << 4));
        size_t dictIdx = find(dict, dict + dictSize, offset) - dict;
        if (dictIdx < dictSize)
        {
            token |= dictIdx << 8;
            token |= 0x8000;
        }
        else
        {
            token |= offset & 0x7F00;
        }
        LZ3_write_LE16(dst, dstPos, token);
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
        uint16_t token = (uint16_t)((literal >= 0xF ? 0xF : literal));
        LZ3_write_LE16(dst, dstPos, token);
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
    ofstream dfs("LZ3_decompress.log");
#endif
    uint32_t srcPos = 0;
    uint32_t dstPos = 0;
    uint32_t dstShortEnd = dstSize - min(wild_cpy_length, 14u) - min(wild_cpy_length, 14u + min_match_length);
    uint16_t dict[128];
    uint32_t dictSize = src[srcPos++];
    for (uint32_t i = 0; i < dictSize; ++i)
    {
        dict[i] = LZ3_read_VL16(src, srcPos);
    }
    const uint16_t* dictPre = dict - 128;
    while (true)
    {
        LZ3_ALIGN(5);
        uint16_t token = LZ3_read_LE16(src, srcPos);
        uint32_t literal = token & 0xF;
        uint32_t length = (token >> 4) & 0xF;
        uint32_t offset;
        if (LZ3_LIKELY(literal <= min(wild_cpy_length, 14u) && dstPos < dstShortEnd))
        {
            memcpy(&dst[dstPos], &src[srcPos], wild_cpy_length);
            dstPos += literal;
            srcPos += literal;
            offset = LZ3_read_VL78(src, srcPos, token, dictPre);
            if (LZ3_LIKELY(length + min_match_length <= min(wild_cpy_length, 14u + min_match_length) && offset >= wild_cpy_length))
            {
                length = length + min_match_length;
                assert(dstPos >= offset);
                uint32_t refPos = dstPos - offset;
                memcpy(&dst[dstPos], &dst[refPos], wild_cpy_length);
#if defined(LZ3_LOG) && !defined(NDEBUG)
                dfs << dstPos << ": " << length << " " << offset << endl;
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
            offset = LZ3_read_VL78(src, srcPos, token, dictPre);
        }
        {
            length = LZ3_read_VL48(src, srcPos, length) + min_match_length;
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
            dfs << dstPos << ": " << length << " " << offset << endl;
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
