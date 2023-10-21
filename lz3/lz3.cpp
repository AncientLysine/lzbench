#include <algorithm>
#include <cassert>
#include <cstring>
#include <memory>
#include <array>
#include <map>
#include <queue>
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
        for (int i = 0; i < n; ++i) ++bucket[rk[i] = s[i]];
        for (int i = 1; i < bucket_count; ++i) bucket[i] += bucket[i - 1];
        for (int i = n - 1; i >= 0; --i) sa[--bucket[rk[i]]] = i;

        //对长度为2^j的后缀排序
        for (int j = 1; ; j *= 2) {
            //接下来进行若干次基数排序，在实现的时候，这里有一个小优化。
            //基数排序要分两次，第一次是对第二关键字排序，第二次是对第一关键字排序。
            //对第二关键字排序的结果实际上可以利用上一次求得的sa直接算出，没有必要再算一次。

            //数组sa_2nd保存的是对第二关键字排序的结果,sa_2nd[p] = 排名为p的为哪个后缀的第二关键字
            int p = 0;
            for (int i = n - j; i < n; ++i) sa_2nd[p++] = i; //因为从n - j开始后面的第二部分都是空串，所以排在前面
            for (int i = 0; i < n; ++i) if (sa[i] >= j) sa_2nd[p++] = sa[i] - j;

            //按第二关键字排序后，第一关键字的原排名。用第一关键字分桶就得到了一二关键字的排序

            //rk_2nd[i] = rk[sa_2nd[i]]是第二关键字排名为i的后缀的第一关键字排名
            for (int i = 0; i < n; ++i) rk_2nd[i] = rk[sa_2nd[i]]; //按第二关键字排序，将rk[sa_2nd[i]]结果存起来，减少寻址次数。

            //分桶，排序
            fill(bucket, bucket + bucket_count, 0);
            for (int i = 0; i < n; ++i) ++bucket[rk_2nd[i]];
            for (int i = 1; i < bucket_count; ++i) bucket[i] += bucket[i - 1];
            for (int i = n - 1; i >= 0; --i) sa[--bucket[rk_2nd[i]]] = sa_2nd[i];

            //求解新的rank数组

            //根据sa求rk。sa[i]是排名为i的后缀，rk[sa[i]] = 后缀sa[i]的排名
            swap(rk, rk_2nd);
            p = 0;
            rk[sa[0]] = p++;
            for (int i = 1; i < n; ++i) {
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
        assert(n == l);
        height = &buffer[max_block_size * 4];

        uint32_t k = 0;
        for (int i = 0; i < n; ++i) {
            uint32_t r = rk[i];
            if (r == 0) {
                height[r] = 0;
                k = 0;
            }
            else {
                if (k > 0) --k;
                uint32_t j = sa[r - 1];
                while (i + k < n && j + k < n && s[i + k] == s[j + k]) ++k;
                height[r] = k;
            }
        }
    }

private:
    uint32_t buffer[max_block_size * 5];

    bool rank_both_equal(uint32_t* r, uint32_t a, uint32_t b, uint32_t l, uint32_t n) {
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

    static bool compare_position(const LZ3_match_info& x, const LZ3_match_info& y)
    {
        return x.position < y.position;
    }

    static bool compare_length(const LZ3_match_info& x, const LZ3_match_info& y)
    {
        return x.length != y.length ? x.length < y.length : x.position < y.position;
    }

private:
    uint32_t prev;    //向前遍历到的后缀排名
    uint32_t next;    //向后遍历到的后缀排名
};

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

inline void LZ3_write_VL78(uint8_t* dst, uint32_t& dstPos, uint32_t token, uint16_t value, uint16_t* dict, uint32_t& dictSize)
{
    if ((token & 0x8000) == 0)
    {
        dst[dstPos++] = (token & 0xFF) ^ (value & 0xFF);
    }
    else
    {
        if (find(dict, dict + dictSize, value) == dict + dictSize)
        {
            memcpy(&dst[dstPos], &value, sizeof(uint16_t));
            dstPos += 2;
            dict[dictSize++] = value;
        }
    }
}

inline uint16_t LZ3_read_VL78(const uint8_t* src, uint32_t& srcPos, uint32_t token, uint16_t* dict, uint32_t& dictSize)
{
    uint16_t value;
    if ((token & 0x8000) == 0)
    {
        value = token ^ src[srcPos++];
    }
    else
    {
        uint32_t index = (token & 0x7F00) >> 8;
        if (index >= dictSize)
        {
            memcpy(&value, &src[srcPos], sizeof(uint16_t));
            srcPos += 2;
            dict[dictSize++] = value;
        }
        else
        {
            value = dict[index];
        }
    }
    return value;
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
    priority_queue<LZ3_match_info, vector<LZ3_match_info>, decltype(&LZ3_match_info::compare_length)> candidates(&LZ3_match_info::compare_length);
    for (uint32_t i = 1; i < srcSize; ++i)
    {
        LZ3_match_info match(psa, i);
        if (match.match_next(psa))
        {
            candidates.push(match);
        }
    }
    uint16_t stained[max_block_size] = { 0 };
    vector<LZ3_match_info> matches;
    vector<LZ3_match_info> recycle;
    map<uint32_t, uint32_t> offsets;
    while (!candidates.empty())
    {
        LZ3_match_info match = candidates.top();
        uint32_t length = match.length;
        if (length < min_match_length)
        {
            break;
        }
        candidates.pop();
        uint32_t position = match.position;
        if (stained[position] != 0)
        {
            continue;
        }
        if (stained[position + length - 1] != 0)
        {
            length--;
            while (stained[position + length - 1] != 0)
            {
                length--;
            }
            if (length >= min_match_length)
            {
                match.length = length;
                candidates.push(match);
            }
            continue;
        }
        if (length > min_match_length)
        {
            //match longer than 3 bytes, sure to survive
            matches.push_back(match);
            offsets[match.offset]++;
            uint16_t stain = (uint16_t)matches.size();
            for (uint32_t j = 0; j < length; ++j)
            {
                stained[position + j] = stain;
            }
        }
        else
        {
            //match exactly 3 bytes, needs a frequent offset to survive
            recycle.push_back(match);
            offsets[match.offset]++;
        }
    }
    while (!offsets.empty())
    {
        auto rare = min_element(offsets.begin(), offsets.end(), [](auto x, auto y) { return x.second < y.second; });
        uint32_t offset = rare->first;
        uint32_t count = rare->second;
        if (offsets.size() <= 128 && count > sizeof(uint16_t)/*sizeof mode1 offset desc*/)
        {
            break;
        }
        for (auto match = matches.begin(); match != matches.end();)
        {
            if (match->offset == offset)
            {
                LZ3_match_info m = *match;
                auto o = offsets.end();
                while (m.match_next(psa))
                {
                    if (m.length < match->length)
                    {
                        break;
                    }
                    o = offsets.find(m.offset);
                    if (o != offsets.end())
                    {
                        *match = m;
                        o->second++;
                        break;
                    }
                }
                if (o == offsets.end() && match->length <= min_match_length)
                {
                    match = matches.erase(match);
                    continue;
                }
            }
            ++match;
        }
        for (auto match = recycle.begin(); match != recycle.end();)
        {
            if (match->offset == offset)
            {
                LZ3_match_info m = *match;
                auto o = offsets.end();
                while (m.match_next(psa))
                {
                    if (m.length < match->length)
                    {
                        break;
                    }
                    o = offsets.find(m.offset);
                    if (o != offsets.end())
                    {
                        *match = m;
                        o->second++;
                        break;
                    }
                }
                if (o == offsets.end() && match->length <= min_match_length)
                {
                    match = recycle.erase(match);
                    continue;
                }
            }
            ++match;
        }
        offsets.erase(rare);
    }
    delete psa;
    for (const LZ3_match_info& match : recycle)
    {
        uint32_t position = match.position;
        uint32_t length = match.length;
        if (stained[position] != 0 || stained[position + length - 1] != 0)
        {
            continue;
        }
        {
            matches.push_back(match);
            uint16_t stain = (uint16_t)matches.size();
            for (uint32_t j = 0; j < length; ++j)
            {
                stained[position + j] = stain;
            }
        }
    }
    stable_sort(matches.begin(), matches.end(), &LZ3_match_info::compare_position);
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
    uint32_t srcPos = 0;
    uint32_t dstPos = 0;
    for (const LZ3_match_info& match : matches)
    {
        uint32_t position = match.position;
        if (position < srcPos)
        {
            continue;
        }
        uint32_t literal = position - srcPos;
        uint32_t length = match.length;
        length -= min_match_length;
        uint32_t offset = match.offset;
        uint16_t token = (literal >= 0xF ? 0xF : literal) | ((length >= 0xF ? 0xF : length) << 4);
        if (offsets.find(offset) != offsets.end())
        {
            uint8_t index = (uint8_t)(find(dict, dict + dictSize, offset) - dict);
            token |= (index << 8) | 0x8000;
        }
        else
        {
            token |= offset & 0x7F00;
        }
        memcpy(&dst[dstPos], &token, 2);
        dstPos += 2;
        LZ3_write_VL48(dst, dstPos, literal);
        memcpy(&dst[dstPos], &src[srcPos], literal);
        dstPos += literal;
        srcPos += literal;
        LZ3_write_VL78(dst, dstPos, token, offset, dict, dictSize);
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
    ofstream dfs("LZ3_decompress.log");
#endif
    uint32_t srcPos = 0;
    uint32_t dstPos = 0;
    uint32_t dstShortEnd = dstSize - min(wild_cpy_length, 14u) - min(wild_cpy_length, 14u + min_match_length);
    uint16_t dict[128];
    uint32_t dictSize = 0;
    while (true)
    {
        uint16_t token;
        memcpy(&token, &src[srcPos], 2);
        srcPos += 2;
        uint32_t literal = token & 0xF;
        uint32_t length = (token >> 4) & 0xF;
        uint32_t offset;
        if (LZ3_LIKELY(literal <= min(wild_cpy_length, 14u) && dstPos < dstShortEnd))
        {
            memcpy(&dst[dstPos], &src[srcPos], wild_cpy_length);
            dstPos += literal;
            srcPos += literal;
            offset = LZ3_read_VL78(src, srcPos, token, dict, dictSize);
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
            offset = LZ3_read_VL78(src, srcPos, token, dict, dictSize);
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
