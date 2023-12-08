#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstring>
#include <memory>
#include <unordered_map>
#include <vector>
#include <iterator>

#define LZ3_LIBRARY
#include "lz3.h"
#include "zstd/lib/common/huf.h"
#include "zstd/lib/common/fse.h"

#if defined(LZ3_LOG) && !defined(NDEBUG)
#include <fstream>
#include <iomanip>
#endif

#if defined(__GNUC__) || defined(__clang__)
#define LZ3_FORCE_INLINE   static inline __attribute__((always_inline))
#define LZ3_LIKELY(expr)   __builtin_expect(!!(expr), 1)
#define LZ3_UNLIKELY(expr) __builtin_expect(!!(expr), 0)
#else
#define LZ3_FORCE_INLINE   static inline
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
    
    LZ3_suffix_array(uint32_t l = 0)
    {
        n = l;
        sa = &buffer[0];
        rk = &buffer[max_block_size * 2];
        height = &buffer[max_block_size * 8];
    }

    uint32_t* sa;
    uint32_t* rk;

    //字符串为s，长度为n
    //sa是我们要求的后缀数组
    //rk数组保存的值相当于是rank值。下面的操作只是用rk数组来比较字符的大小，所以没有必要求出当前真实的rank值。所以这里rk保存位置i的字符就好
    //最后返回的rk才是rank值，rk[i]=后缀i的名次
    void cal_suffix_array(const uint8_t* s, uint32_t l) {
        assert(l == n);

        sa = &buffer[0];
        rk = &buffer[max_block_size * 2];
        uint32_t* sa_2nd = &buffer[max_block_size * 4];
        uint32_t* rk_2nd = &buffer[max_block_size * 6];
        uint32_t* bucket = &buffer[max_block_size * 8];
        uint32_t bucket_count = 256;

        //对第一个字符排序
        fill(bucket, bucket + bucket_count, 0);
        for (uint32_t i = 0; i < n; ++i) ++bucket[rk[i] = s[i]];
        for (uint32_t i = 1; i < bucket_count; ++i) bucket[i] += bucket[i - 1];
        for (uint32_t i = n; i > 0; --i) sa[--bucket[rk[i - 1]]] = i - 1;

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
            for (uint32_t i = n; i > 0; --i) sa[--bucket[rk_2nd[i - 1]]] = sa_2nd[i - 1];

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
        height = &buffer[max_block_size * 8];

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

    void popn_suffix(uint32_t l)
    {
        uint32_t h = 0;
        uint32_t c = 0;
        for (uint32_t i = 0; i < n; ++i)
        {
            h = min(h, height[i]);
            uint32_t s = sa[i];
            if (s >= l)
            {
                sa[c] = s - l;
                rk[sa[c]] = c;
                height[c] = h;
                h = max_block_size * 2;
                ++c;
            }
        }
        n = c;
    }

    void push_suffix(const uint8_t* s, const LZ3_suffix_array* psa)
    {
        uint32_t lh = 0;
        uint32_t rh = 0;
        uint32_t li = n;
        uint32_t ri = psa->n;
        uint32_t m = li + ri;
        for (uint32_t i = m; i > 0; --i)
        {
            uint32_t ls = 0;
            uint32_t rs = 0;
            if (li > 0)
            {
                ls = sa[li - 1];
            }
            if (ri > 0)
            {
                rs = psa->sa[ri - 1] + n;
            }
            if (ri > 0 && (li == 0 || lh < rh || (lh == rh && suffix_less_equal(s, ls + lh, rs + rh, m))))
            {
                sa[i - 1] = rs;
                rk[rs] = i - 1;
                if (i < m)
                {
                    height[i] = rh;
                    rh = psa->height[ri - 1];
                    lh = min(lh, rh);
                    if (li > 0) suffix_update_height(s, ls, rs, lh, m);
                }
                --ri;
            }
            else
            {
                sa[i - 1] = ls;
                rk[ls] = i - 1;
                if (i < m)
                {
                    height[i] = lh;
                    lh = height[li - 1];
                    rh = min(rh, lh);
                    if (ri > 0) suffix_update_height(s, ls, rs, rh, m);
                }
                --li;
            }
        }
        height[0] = 0;
        n = m;
    }

private:
    uint32_t buffer[max_block_size * 10];

    static bool rank_both_equal(uint32_t* r, uint32_t a, uint32_t b, uint32_t l, uint32_t n) {
        if (r[a] != r[b]) return false;
        // 如果开两倍空间，就可以省去下面的两个判断。
        if (a + l >= n && b + l >= n) return true;
        if (a + l >= n || b + l >= n) return false;
        return r[a + l] == r[b + l];
    }

    static bool suffix_less_equal(const uint8_t* s, uint32_t a, uint32_t b, uint32_t n)
    {
        uint32_t h = 0;
        while (b + h < n && s[a + h] == s[b + h]) ++h;
        if (b + h == n) return false;
        return s[a + h] <= s[b + h];
    }

    static void suffix_update_height(const uint8_t* s, uint32_t a, uint32_t b, uint32_t& h, uint32_t n)
    {
        while (b + h < n && s[a + h] == s[b + h]) ++h;
    }
};

static constexpr uint32_t min_match_length = 3;

static constexpr uint32_t min_match_offset = 2;

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
            if (prev == 0 && next >= psa->n)
            {
                return false;
            }
            if (prev > 0 && (next >= psa->n || psa->height[prev] >= psa->height[next]))
            {
                length = min(length, psa->height[prev]);
                index = psa->sa[--prev];
            }
            else
            {
                length = min(length, psa->height[next]);
                index = psa->sa[next++];
            }
            if (length < min_match_length)
            {
                return false;
            }
            if (position > index && position - index < max_block_size)
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

LZ3_FORCE_INLINE void LZ3_write_LE16(uint8_t*& dst, uint16_t value)
{
    memcpy(dst, &value, sizeof(uint16_t));
    dst += sizeof(uint16_t);
}

LZ3_FORCE_INLINE uint16_t LZ3_read_LE16(const uint8_t*& src)
{
    uint16_t value;
    memcpy(&value, src, sizeof(uint16_t));
    src += sizeof(uint16_t);
    return value;
}

LZ3_FORCE_INLINE void LZ3_write_VL16(uint8_t*& dst, uint16_t value)
{
    if (value < 0x80)
    {
        *dst++ = (value & 0xFF);
    }
    else
    {
        *dst++ = (value & 0x7F) | 0x80;
        value >>= 7;
        *dst++ = (value & 0xFF) ^ 0x01;
    }
}

LZ3_FORCE_INLINE uint16_t LZ3_read_VL16(const uint8_t*& src)
{
    uint16_t value = *src++;
    if (value & 0x80)
    {
        value ^= (*src++) << 7;
    }
    return value;
}

LZ3_FORCE_INLINE void LZ3_write_HPV8(uint8_t*& dst, uint32_t value)
{
    while (value >= 0xFF)
    {
        *dst++ = 0xFF;
        value -= 0xFF;
    }
    *dst++ = (uint8_t)value;
}

LZ3_FORCE_INLINE uint32_t LZ3_read_HPV8(const uint8_t*& src, uint32_t value)
{
    while (true)
    {
        uint8_t e = *src++;
        value += e;
        if (e < 0xFF)
        {
            break;
        }
    }
    return value;
}

LZ3_FORCE_INLINE void LZ3_write_VL78(uint8_t*& dst, uint32_t token, uint32_t value)
{
    if ((token & 0x8000) == 0)
    {
        *dst++ = (token & 0xFF) ^ (value & 0xFF);
    }
}

LZ3_FORCE_INLINE uint32_t LZ3_read_VL78(const uint8_t*& src, uint32_t token, const uint16_t* dictPre)
{
    if ((token & 0x8000) == 0)
    {
        return token ^ (*src++);
    }
    else
    {
        return dictPre[token >> 8];
    }
}

enum LZ3_entropy_coder
{
    None,
    Huff0,
    FSE,
};

static constexpr uint32_t block_mode_threshold = 16;
static constexpr uint32_t dim_2_mode_threshold = 64;
static constexpr uint32_t uncompress_threshold = 32;
static constexpr uint32_t uncompress_intercept = 0;

const char* LZ3_last_error_name = nullptr;

static size_t LZ3_write_stream(const uint8_t* src, uint8_t* dst, size_t srcSize, LZ3_entropy_coder coder)
{
    uint8_t* dstPtr = dst;
    size_t dstSize = 0;
    if (coder == LZ3_entropy_coder::Huff0)
    {
        dstSize = HUF_compress(&dst[sizeof(uint16_t) * 2], HUF_compressBound(srcSize), src, srcSize);
        if (HUF_isError(dstSize))
        {
            LZ3_last_error_name = HUF_getErrorName(dstSize);
            return -1;
        }
        if (srcSize / uncompress_threshold + uncompress_intercept > srcSize - dstSize)
        {
            dstSize = 0;
        }
        if (dstSize != 0)
        {
            LZ3_write_LE16(dstPtr, (uint16_t)dstSize);
            LZ3_write_LE16(dstPtr, (uint16_t)srcSize);
        }
    }
    if (coder == LZ3_entropy_coder::FSE)
    {
        dstSize = FSE_compress(&dst[sizeof(uint16_t) * 1], FSE_compressBound(srcSize), src, srcSize);
        if (FSE_isError(dstSize))
        {
            LZ3_last_error_name = FSE_getErrorName(dstSize);
            return -1;
        }
        if (srcSize / uncompress_threshold + uncompress_intercept > srcSize - dstSize)
        {
            dstSize = 0;
        }
        if (dstSize != 0)
        {
            LZ3_write_LE16(dstPtr, (uint16_t)dstSize);
        }
    }
    if (dstSize == 0)
    {
        LZ3_write_LE16(dstPtr, (uint16_t)dstSize);
        LZ3_write_LE16(dstPtr, (uint16_t)srcSize);
        memcpy(dstPtr, src, srcSize);
        dstSize = srcSize;
    }
    dstPtr += dstSize;
    return dstPtr - dst;
}

static size_t LZ3_read_stream(const uint8_t* src, uint8_t* dst, size_t dstCap, LZ3_entropy_coder coder)
{
    const uint8_t* srcPtr = src;
    size_t srcSize = LZ3_read_LE16(srcPtr);
    size_t oriSize;
    if (srcSize == 0)
    {
        oriSize = LZ3_read_LE16(srcPtr);
        memcpy(dst, srcPtr, oriSize);
        srcSize = oriSize;
    }
    else if (coder == LZ3_entropy_coder::Huff0)
    {
        oriSize = LZ3_read_LE16(srcPtr);
        oriSize = HUF_decompress(dst, oriSize, srcPtr, srcSize);
        if (HUF_isError(oriSize))
        {
            LZ3_last_error_name = HUF_getErrorName(oriSize);
            return -1;
        }
    }
    else if (coder == LZ3_entropy_coder::FSE)
    {
        oriSize = FSE_decompress(dst, dstCap, srcPtr, srcSize);
        if (FSE_isError(oriSize))
        {
            LZ3_last_error_name = FSE_getErrorName(oriSize);
            return -1;
        }
    }
    srcPtr += srcSize;
    return srcPtr - src;
}

template<LZ3_entropy_coder coder>
LZ3_FORCE_INLINE size_t LZ3_compress_generic(const LZ3_suffix_array* psa, const uint8_t* src, uint8_t* dst, size_t srcSize)
{
    uint32_t hisSize = psa->n - (uint32_t)srcSize;
#if defined(LZ3_LOG) && !defined(NDEBUG)
    ofstream sfs("LZ3_suffix_array.log");
    for (uint32_t i = 0; i < psa->n; ++i)
    {
        sfs << dec << setfill(' ') << left << setw(5) << psa->sa[i] << ": ";
        sfs << dec << setfill(' ') << left << setw(5) << psa->height[i] << "| ";
        uint32_t l = psa->height[i];
        if (i > 1)
        {
            l = max(l, psa->height[i - 1]);
        }
        if (i + 1 < psa->n)
        {
            l = max(l, psa->height[i + 1]);
        }
        l = min(l + 1, psa->n - psa->sa[i]);
        const uint8_t* rawPtr = src + psa->sa[i] - hisSize;
        for (uint32_t j = 0; j < l; ++j)
        {
            uint8_t c = rawPtr[j];
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
    for (uint32_t i = 0; i < srcSize; ++i)
    {
        LZ3_match_info match(psa, i + hisSize);
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
    for (uint32_t i = maxLength; i > 0 ; --i)
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
    uint32_t survive = 0;
    for (auto i = orderByLength.begin(); i != orderByLength.end(); ++i)
    {
        uint32_t index = *i;
        LZ3_match_info& match = candidates[index];
        uint32_t length = match.length;
        if (length < min_match_length)
        {
            break;
        }
        uint32_t position = match.position - hisSize;
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
            for (uint32_t j = 0; j < length; ++j)
            {
                stained[position + j] = (uint16_t)index + 1;
            }
            survive++;
        }
    }
    unordered_map<uint32_t, uint32_t> offsets;
    for (uint32_t index : matches)
    {
        const LZ3_match_info& match = candidates[index];
        uint32_t offset = match.offset;
        ++offsets[offset];
    }
    for (uint32_t index : matches)
    {
        LZ3_match_info& match = candidates[index];
        uint32_t offset = match.offset;
        auto c = offsets.find(offset);
        auto n = c;
        for (LZ3_match_info m = match; m.match_next(psa); )
        {
            if (m.length < match.length)
            {
                break;
            }
            auto o = offsets.find(m.offset);
            if (o != offsets.end() && o->second > n->second)
            {
                match = m;
                n = o;
            }
        }
        if (n != c)
        {
            c->second--;
            n->second++;
        }
    }
    stable_sort(matches.begin() + survive, matches.end(), [&candidates, &offsets](uint32_t x, uint32_t y)
    {
        return offsets[candidates[x].offset] > offsets[candidates[y].offset];
    });
    for (auto i = survive; i < matches.size(); ++i)
    {
        uint32_t index = matches[i];
        const LZ3_match_info& match = candidates[index];
        uint32_t position = match.position - hisSize;
        uint32_t length = match.length;
        uint32_t offset = match.offset;
        auto o = offsets.find(offset);
        if (stained[position] != 0 || stained[position + length - 1] != 0)
        {
            o->second--;
            continue;
        }
        if (o->second >= min_match_offset)
        {
            //match exactly 3 bytes, needs a frequent offset to survive
            for (uint32_t j = 0; j < length; ++j)
            {
                stained[position + j] = (uint16_t)index + 1;
            }
            matches[survive] = index;
            survive++;
        }
        else
        {
            o->second--;
        }
    }
    matches.erase(matches.begin() + survive, matches.end());
    sort(matches.begin(), matches.end());
#if defined(LZ3_LOG) && !defined(NDEBUG)
    for (uint32_t index : matches)
    {
        const LZ3_match_info& match = candidates[index];
        uint32_t position = match.position - hisSize;
        uint32_t length = match.length;
        uint32_t offset = match.offset;
        cfs << position << ": " << length << " " << offset << endl;
    }
#endif
    if (coder == LZ3_entropy_coder::None)
    {
        vector<uint32_t> dict;
        for (const auto& i : offsets)
        {
            if (i.second > sizeof(uint16_t)/*sizeof mode1 offset desc*/)
            {
                dict.push_back(i.first);
            }
        }
        stable_sort(dict.begin(), dict.end(), [&offsets](uint32_t x, uint32_t y)
        {
            return offsets[x] != offsets[y] ? offsets[x] > offsets[y] : x < y;
        });
        if (dict.size() > 128)
        {
            dict.resize(128);
        }
        size_t srcPos = 0;
        uint8_t* dstPtr = dst;
        *dstPtr++ = (uint8_t)dict.size();
        for (uint32_t i = 0; i < dict.size(); ++i)
        {
            LZ3_write_VL16(dstPtr, dict[i]);
        }
        for (uint32_t i : matches)
        {
            const LZ3_match_info& match = candidates[i];
            uint32_t position = match.position - hisSize;
            if (position < srcPos)
            {
                continue;
            }
            uint32_t literal = (uint32_t)(position - srcPos);
            uint32_t length = match.length;
            length -= min_match_length;
            uint32_t offset = match.offset;
            uint16_t token = (uint16_t)((literal >= 0xF ? 0xF : literal) | ((length >= 0xF ? 0xF : length) << 4));
            auto dictPos = find(dict.begin(), dict.end(), offset);
            if (dictPos != dict.end())
            {
                size_t dictIdx = distance(dict.begin(), dictPos);
                token |= dictIdx << 8;
                token |= 0x8000;
            }
            else
            {
                token |= offset & 0x7F00;
            }
            LZ3_write_LE16(dstPtr, token);
            if (literal >= 0xF)
            {
                LZ3_write_HPV8(dstPtr, literal - 0xF);
            }
            memcpy(dstPtr, &src[srcPos], literal);
            dstPtr += literal;
            srcPos += literal;
            LZ3_write_VL78(dstPtr, token, offset);
            if (length >= 0xF)
            {
                LZ3_write_HPV8(dstPtr, length - 0xF);
            }
            srcPos += match.length;
        }
        if (srcSize > srcPos)
        {
            uint32_t literal = (uint32_t)(srcSize - srcPos);
            uint16_t token = (uint16_t)((literal >= 0xF ? 0xF : literal));
            LZ3_write_LE16(dstPtr, token);
            if (literal >= 0xF)
            {
                LZ3_write_HPV8(dstPtr, literal - 0xF);
            }
            memcpy(dstPtr, &src[srcSize - literal], literal);
            dstPtr += literal;
        }
        return dstPtr - dst;
    }
    else
    {
        size_t srcPos = 0;
        uint8_t* dstPtr = dst;
        vector<uint32_t> hist;
        uint32_t total = 0;
        for (const auto& i : offsets)
        {
            if (i.second >= min_match_offset)
            {
                hist.push_back(i.first);
            }
            total += i.second;
        }
        stable_sort(hist.begin(), hist.end(), [&offsets](uint32_t x, uint32_t y)
        {
            return offsets[x] != offsets[y] ? offsets[x] > offsets[y] : x < y;
        });
        uint32_t blockLog = 4;
        for (; blockLog >= 3; --blockLog)
        {
            uint32_t incap = 0;
            for (uint32_t offset : hist)
            {
                if (offset % (1 << blockLog) != 0)
                {
                    incap += offsets[offset];
                }
            }
            if (incap <= total / block_mode_threshold)
            {
                break;
            }
        }
        //ASTC_6x6/12x12 may have NPOT row size
        uint32_t lineSize = 256;
        if (blockLog >= 3)
        {
            for (uint32_t offset : hist)
            {
                if (offset % (1 << blockLog) == 0 && (offset >> blockLog) > dim_2_mode_threshold)
                {
                    lineSize = offset >> blockLog;
                    break;
                }
            }
        }
        else
        {
            blockLog = 0;
        }
        if (lineSize > 256)
        {
            lineSize = 256;
        }
        *dstPtr++ = blockLog;
        *dstPtr++ = lineSize;
        vector<uint8_t> lit;
        vector<uint8_t> seq;
        for (uint32_t index : matches)
        {
            const LZ3_match_info& match = candidates[index];
            uint32_t position = match.position - hisSize;
            if (position < srcPos)
            {
                continue;
            }
            uint32_t literal = (uint32_t)(position - srcPos);
            uint32_t length = match.length;
            length -= min_match_length;
            uint32_t offset = match.offset;
            copy(&src[srcPos], &src[position], back_inserter(lit));
            if (literal < 0xFF)
            {
                seq.push_back((uint8_t)literal);
            }
            else
            {
                seq.push_back(0xFF);
                copy((uint8_t*)&literal, (uint8_t*)&literal + sizeof(uint16_t), back_inserter(seq));
            }
            srcPos += literal;
            if (blockLog > 0)
            {
                uint8_t x = (offset >> blockLog) % lineSize;
                uint8_t y = (offset >> blockLog) / lineSize;
                uint8_t r = (offset << (8 - blockLog));
                seq.push_back(x);
                seq.push_back(y | r);
            }
            else
            {
                copy((uint8_t*)&offset, (uint8_t*)&offset + sizeof(uint16_t), back_inserter(seq));
            }
            if (length < 0xFF)
            {
                seq.push_back((uint8_t)length);
            }
            else
            {
                seq.push_back(0xFF);
                copy((uint8_t*)&length, (uint8_t*)&length + sizeof(uint16_t), back_inserter(seq));
            }
            srcPos += match.length;
        }
        if (srcSize > srcPos)
        {
            uint32_t literal = (uint32_t)(srcSize - srcPos);
            if (literal < 0xFF)
            {
                seq.push_back((uint8_t)literal);
            }
            else
            {
                seq.push_back(0xFF);
                uint16_t val = (uint16_t)literal;
                copy((uint8_t*)&val, ((uint8_t*)&val) + sizeof(uint16_t), back_inserter(seq));
            }
            copy(&src[srcPos], &src[srcSize], back_inserter(lit));
        }
        dstPtr += LZ3_write_stream(lit.data(), dstPtr, (uint32_t)lit.size(), LZ3_entropy_coder::Huff0);
        dstPtr += LZ3_write_stream(seq.data(), dstPtr, (uint32_t)seq.size(), LZ3_entropy_coder::Huff0);
        return dstPtr - dst;
    }
}

static constexpr uint32_t wild_cpy_length = 16;

template<LZ3_entropy_coder coder>
LZ3_FORCE_INLINE size_t LZ3_decompress_generic(const uint8_t* src, uint8_t* dst, size_t dstSize)
{
#if defined(LZ3_LOG) && !defined(NDEBUG)
    ofstream dfs("LZ3_decompress.log");
#endif
    const uint8_t* srcPtr = src;
    uint8_t* dstPtr = dst;
    uint8_t* dstEnd = dstPtr + dstSize;
    uint8_t* dstShortEnd = dstSize > wild_cpy_length ? dstEnd - wild_cpy_length : dstPtr;

    uint16_t dict[128];
    const uint16_t* dictPre = dict - 128;

    uint32_t blockLog = 0;
    uint32_t lineSize = 0;
    uint8_t* buf = nullptr;
    const uint8_t* litPtr = nullptr;
    const uint8_t* seqPtr = nullptr;
    if (coder == LZ3_entropy_coder::None)
    {
        uint32_t dictSize = *srcPtr++;
        for (uint32_t i = 0; i < dictSize; ++i)
        {
            dict[i] = LZ3_read_VL16(srcPtr);
        }
    }
    else
    {
        blockLog = *srcPtr++;
        lineSize = *srcPtr++;
        if (lineSize == 0)
        {
            lineSize = 256;
        }
        buf = new uint8_t[dstSize * 5];
        uint8_t* bufPtr = buf;
        srcPtr += LZ3_read_stream(srcPtr, bufPtr, dstSize, LZ3_entropy_coder::Huff0);
        litPtr = bufPtr;
        bufPtr += dstSize;
        srcPtr += LZ3_read_stream(srcPtr, bufPtr, dstSize, LZ3_entropy_coder::Huff0);
        seqPtr = bufPtr;
    }
    while (true)
    {
        uint16_t token;
        uint32_t literal;
        uint32_t length;
        if (coder == LZ3_entropy_coder::None)
        {
            token = LZ3_read_LE16(srcPtr);
            literal = token & 15;
            length = ((uint8_t)token) >> 4;
        }
        else
        {
            literal = *seqPtr++;
        }
        if (LZ3_LIKELY(literal <= min(wild_cpy_length, coder == LZ3_entropy_coder::None ? 0xEu : 0xFFu)))
        {
            if (LZ3_UNLIKELY(dstPtr >= dstShortEnd))
            {
                goto safe_copy_literal;
            }
            uint8_t* cpyPtr = dstPtr;
            const uint8_t* refPtr;
            if (coder == LZ3_entropy_coder::None)
            {
                refPtr = srcPtr;
            }
            else
            {
                refPtr = litPtr;
            }
            //TODO by Lysine: copy literal may read beyond stream end
            memcpy(cpyPtr + 0, refPtr + 0, 8);
            memcpy(cpyPtr + 8, refPtr + 8, 8);
            dstPtr += literal;
            if (coder == LZ3_entropy_coder::None)
            {
                srcPtr += literal;
            }
            else
            {
                litPtr += literal;
            }
        }
        else
        {
            if (coder == LZ3_entropy_coder::None)
            {
                if (literal >= 0xF)
                {
                    literal = LZ3_read_HPV8(srcPtr, literal);
                }
            }
            else
            {
                if (literal >= 0xFF)
                {
                    literal = LZ3_read_LE16(seqPtr);
                }
            }
        safe_copy_literal:
            uint8_t* cpyPtr = dstPtr;
            uint8_t* cpyEnd = dstPtr + literal;
            const uint8_t* refPtr;
            if (coder == LZ3_entropy_coder::None)
            {
                refPtr = srcPtr;
            }
            else
            {
                refPtr = litPtr;
            }
            if (cpyEnd <= dstShortEnd)
            {
                while(cpyPtr < cpyEnd)
                {
                    memcpy(cpyPtr + 0, refPtr + 0, 8);
                    memcpy(cpyPtr + 8, refPtr + 8, 8);
                    cpyPtr += wild_cpy_length;
                    refPtr += wild_cpy_length;
                }
            }
            else
            {
                assert(cpyEnd <= dstEnd);
                while(cpyPtr < cpyEnd)
                {
                    *cpyPtr++ = *refPtr++;
                }
            }
            dstPtr += literal;
            if (coder == LZ3_entropy_coder::None)
            {
                srcPtr += literal;
            }
            else
            {
                litPtr += literal;
            }
            if (dstPtr >= dstEnd)
            {
                break;
            }
        }
        uint32_t offset;
        if (coder == LZ3_entropy_coder::None)
        {
            offset = LZ3_read_VL78(srcPtr, token, dictPre);
        }
        else
        {
            if (blockLog != 0)
            {
                uint8_t x = (*seqPtr++);
                uint8_t y = (*seqPtr) & ((1 << (8 - blockLog)) - 1);
                uint8_t r = (*seqPtr++) >> (8 - blockLog);
                offset = ((x + y * lineSize) << blockLog) | r;
            }
            else
            {
                offset = LZ3_read_LE16(seqPtr);
            }
            length = *seqPtr++;
        }
        if (LZ3_LIKELY(length <= wild_cpy_length - min_match_length))
        {
            length += min_match_length;
            if (LZ3_UNLIKELY(dstPtr >= dstShortEnd || offset < 8))
            {
                goto safe_copy_match;
            }
            uint8_t* cpyPtr = dstPtr;
            const uint8_t* refPtr = dstPtr - offset;
            memcpy(cpyPtr + 0, refPtr + 0, 8);
            memcpy(cpyPtr + 8, refPtr + 8, 8);
#if defined(LZ3_LOG) && !defined(NDEBUG)
            dfs << dstPtr - dst << ": " << length << " " << offset << endl;
#endif
            dstPtr += length;
        }
        else
        {
            if (coder == LZ3_entropy_coder::None)
            {
                if (length >= 0xF)
                {
                    length = LZ3_read_HPV8(srcPtr, length);
                }
            }
            else
            {
                if (length >= 0xFF)
                {
                    length = LZ3_read_LE16(seqPtr);
                }
            }
            length += min_match_length;
        safe_copy_match:
            uint8_t* cpyPtr = dstPtr;
            uint8_t* cpyEnd = dstPtr + length;
            const uint8_t* refPtr = cpyPtr - offset;
            if (cpyEnd <= dstShortEnd/*dstEnd - (wild_cpy_length - 1)*/ && offset >= 8)
            {
                do
                {
                    memcpy(cpyPtr + 0, refPtr + 0, 8);
                    memcpy(cpyPtr + 8, refPtr + 8, 8);
                    cpyPtr += wild_cpy_length;
                    refPtr += wild_cpy_length;
                }
                while(cpyPtr < cpyEnd);
            }
            else
            {
                assert(cpyEnd <= dstEnd);
                do
                {
                    *cpyPtr++ = *refPtr++;
                }
                while(cpyPtr < cpyEnd);
            }
#if defined(LZ3_LOG) && !defined(NDEBUG)
            dfs << dstPtr - dst << ": " << length << " " << offset << endl;
#endif
            dstPtr += length;
            if (dstPtr >= dstEnd)
            {
                break;
            }
        }
    }
    if (coder != LZ3_entropy_coder::None)
    {
        delete[] buf;
    }
    return srcPtr - src;
}

uint32_t LZ3_compress(const void* src, void* dst, uint32_t srcSize)
{
    size_t dstPos;
    if (srcSize <= max_block_size)
    {
        LZ3_suffix_array* psa = new LZ3_suffix_array(srcSize);
        psa->cal_suffix_array((const uint8_t*)src, srcSize);
        psa->cal_height((const uint8_t*)src, srcSize);
        dstPos = LZ3_compress_generic<LZ3_entropy_coder::None>(psa, (const uint8_t*)src, (uint8_t*)dst, srcSize);
        delete psa;
    }
    else
    {
        LZ3_CStream* pcs = LZ3_createCStream();
        const uint8_t* srcPtr = (const uint8_t*)src;
        const uint8_t* srcEnd = srcPtr + srcSize;
        uint8_t* dstPtr = (uint8_t*)dst;
        while (srcPtr < srcEnd)
        {
            size_t curSize = min<size_t>(srcEnd - srcPtr, max_block_size);
            dstPtr += LZ3_compress_continue(pcs, srcPtr, dstPtr, (uint32_t)curSize);
            srcPtr += curSize;
        }
        LZ3_freeCStream(pcs);
        dstPos = dstPtr - (uint8_t*)dst;
    }
    vector<uint8_t> test(srcSize);
    assert(LZ3_decompress_fast(dst, test.data(), srcSize) == dstPos);
    for (size_t i = 0; i < srcSize; ++i)
    {
        assert(test[i] == ((const uint8_t*)src)[i]);
    }
    return (uint32_t)dstPos;
}

uint32_t LZ3_decompress_fast(const void* src, void* dst, uint32_t dstSize)
{
    size_t srcPos;
    if (dstSize < max_block_size)
    {
        srcPos = LZ3_decompress_generic<LZ3_entropy_coder::None>((const uint8_t*)src, (uint8_t*)dst, dstSize);
    }
    else
    {
        LZ3_DStream* pds = LZ3_createDStream();
        const uint8_t* srcPtr = (const uint8_t*)src;
        uint8_t* dstPtr = (uint8_t*)dst;
        uint8_t* dstEnd = dstPtr + dstSize;
        while (dstPtr < dstEnd)
        {
            size_t curSize = min<size_t>(dstEnd - dstPtr, max_block_size);
            srcPtr += LZ3_decompress_continue(pds, srcPtr, dstPtr, (uint32_t)curSize);
            dstPtr += curSize;
        }
        LZ3_freeDStream(pds);
        srcPos = srcPtr - (const uint8_t*)src;
    }
    return (uint32_t)srcPos;
}

uint32_t LZ3_compress_HUF(const void* src, void* dst, uint32_t srcSize)
{
    size_t dstPos;
    {
        LZ3_suffix_array* psa = new LZ3_suffix_array(srcSize);
        psa->cal_suffix_array((const uint8_t*)src, srcSize);
        psa->cal_height((const uint8_t*)src, srcSize);
        dstPos = LZ3_compress_generic<LZ3_entropy_coder::Huff0>(psa, (const uint8_t*)src, (uint8_t*)dst, srcSize);
        delete psa;
    }
    vector<uint8_t> test(srcSize);
    assert(LZ3_decompress_HUF_fast(dst, test.data(), srcSize) == dstPos);
    for (size_t i = 0; i < srcSize; ++i)
    {
        assert(test[i] == ((const uint8_t*)src)[i]);
    }
    return (uint32_t)dstPos;
}

uint32_t LZ3_decompress_HUF_fast(const void* src, void* dst, uint32_t dstSize)
{
    return (uint32_t)LZ3_decompress_generic<LZ3_entropy_coder::Huff0>((const uint8_t*)src, (uint8_t*)dst, dstSize);
}

struct LZ3_CStream
{
    LZ3_suffix_array hsa;
    LZ3_suffix_array tsa;
    uint8_t sz[max_block_size * 2];
    uint8_t* psz;

    LZ3_CStream()
    {
        psz = sz;
    };
};

LZ3_CStream* LZ3_createCStream()
{
    return new LZ3_CStream();
}

void LZ3_freeCStream(LZ3_CStream* pcs)
{
    delete pcs;
}

uint32_t LZ3_compress_continue(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize)
{
    pcs->tsa.n = srcSize;
    pcs->tsa.cal_suffix_array((const uint8_t*)src, srcSize);
    pcs->tsa.cal_height((const uint8_t*)src, srcSize);
    if (pcs->psz + srcSize > pcs->sz + sizeof(pcs->sz))
    {
        memcpy(pcs->sz, pcs->psz - max_block_size, max_block_size);
        pcs->psz = pcs->sz + max_block_size;
    }
    memcpy(pcs->psz, src, srcSize);
    if (pcs->hsa.n> max_block_size)
    {
        pcs->hsa.popn_suffix(pcs->hsa.n - max_block_size);
    }
    pcs->hsa.push_suffix(pcs->psz - pcs->hsa.n, &pcs->tsa);
    size_t dstPos = LZ3_compress_generic<LZ3_entropy_coder::None>(&pcs->hsa, pcs->psz, (uint8_t*)dst, srcSize);
    pcs->psz += srcSize;
    return (uint32_t)dstPos;
}

struct LZ3_DStream
{
    uint8_t sz[max_block_size * 2];
    uint8_t* psz;

    LZ3_DStream()
    {
        psz = sz;
    };
};

LZ3_DStream* LZ3_createDStream()
{
    return new LZ3_DStream();
}

void LZ3_freeDStream(LZ3_DStream* pds)
{
    delete pds;
}

uint32_t LZ3_decompress_continue(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    if (pds->psz + dstSize > pds->sz + sizeof(pds->sz))
    {
        memcpy(pds->sz, pds->psz - max_block_size, max_block_size);
        pds->psz = pds->sz + max_block_size;
    }
    size_t srcPos = LZ3_decompress_generic<LZ3_entropy_coder::None>((const uint8_t*)src, pds->psz, dstSize);
    memcpy(dst, pds->psz, dstSize);
    pds->psz += dstSize;
    return (uint32_t)srcPos;
}