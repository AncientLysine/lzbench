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

const char* LZ3_last_error_name = nullptr;

class LZ3_suffix_array
{
public:
    uint32_t n;

    LZ3_suffix_array(uint32_t l) {
        n = l;
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
        rk = &buffer[max_block_size];
        uint32_t* sa_2nd = &buffer[max_block_size * 2];
        uint32_t* rk_2nd = &buffer[max_block_size * 3];
        uint32_t* bucket = &buffer[max_block_size * 4];
        uint32_t bucket_count = 256;

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

LZ3_FORCE_INLINE void LZ3_write_LE16(uint8_t* dst, uint32_t& dstPos, uint16_t value)
{
    memcpy(&dst[dstPos], &value, sizeof(uint16_t));
    dstPos += sizeof(uint16_t);
}

LZ3_FORCE_INLINE uint16_t LZ3_read_LE16(const uint8_t* src, uint32_t& srcPos)
{
    uint16_t value;
    memcpy(&value, &src[srcPos], sizeof(uint16_t));
    srcPos += sizeof(uint16_t);
    return value;
}

LZ3_FORCE_INLINE void LZ3_write_VL16(uint8_t* dst, uint32_t& dstPos, uint16_t value)
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

LZ3_FORCE_INLINE uint16_t LZ3_read_VL16(const uint8_t* src, uint32_t& srcPos)
{
    uint16_t value = src[srcPos++];
    if (value & 0x80)
    {
        value ^= src[srcPos++] << 7;
    }
    return value;
}

LZ3_FORCE_INLINE void LZ3_write_HPV8(uint8_t* dst, uint32_t& dstPos, uint32_t value)
{
    while (value >= 0xFF)
    {
        dst[dstPos++] = 0xFF;
        value -= 0xFF;
    }
    dst[dstPos++] = (uint8_t)value;
}

LZ3_FORCE_INLINE uint32_t LZ3_read_HPV8(const uint8_t* src, uint32_t& srcPos, uint32_t value)
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
    return value;
}

LZ3_FORCE_INLINE void LZ3_write_VL78(uint8_t* dst, uint32_t& dstPos, uint32_t token, uint32_t value)
{
    if ((token & 0x8000) == 0)
    {
        dst[dstPos++] = (token & 0xFF) ^ (value & 0xFF);
    }
}

LZ3_FORCE_INLINE uint32_t LZ3_read_VL78(const uint8_t* src, uint32_t& srcPos, uint32_t token, const uint16_t* dictPre)
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

static uint32_t LZ3_write_stream(const uint8_t* src, uint8_t* dst, uint32_t srcSize, LZ3_entropy_coder coder)
{
    uint32_t dstPos = 0;
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
            LZ3_write_LE16(dst, dstPos, (uint16_t)dstSize);
            LZ3_write_LE16(dst, dstPos, (uint16_t)srcSize);
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
            LZ3_write_LE16(dst, dstPos, (uint16_t)dstSize);
        }
    }
    if (dstSize == 0)
    {
        LZ3_write_LE16(dst, dstPos, (uint16_t)dstSize);
        LZ3_write_LE16(dst, dstPos, (uint16_t)srcSize);
        memcpy(&dst[dstPos], src, srcSize);
        dstSize = srcSize;
    }
    dstPos += (uint32_t)dstSize;
    return dstPos;
}

static uint32_t LZ3_read_stream(const uint8_t* src, uint8_t* dst, uint32_t dstCap, LZ3_entropy_coder coder)
{
    uint32_t srcPos = 0;
    size_t srcSize = LZ3_read_LE16(src, srcPos);
    size_t oriSize;
    if (srcSize == 0)
    {
        oriSize = LZ3_read_LE16(src, srcPos);
        memcpy(dst, &src[srcPos], oriSize);
        srcSize = oriSize;
    }
    else if (coder == LZ3_entropy_coder::Huff0)
    {
        oriSize = LZ3_read_LE16(src, srcPos);
        oriSize = HUF_decompress(dst, oriSize, &src[srcPos], srcSize);
        if (HUF_isError(oriSize))
        {
            LZ3_last_error_name = HUF_getErrorName(oriSize);
            return -1;
        }
    }
    else if (coder == LZ3_entropy_coder::FSE)
    {
        oriSize = FSE_decompress(dst, dstCap, &src[srcPos], srcSize);
        if (FSE_isError(oriSize))
        {
            LZ3_last_error_name = FSE_getErrorName(oriSize);
            return -1;
        }
    }
    srcPos += (uint32_t)srcSize;
    return srcPos;
}

template<LZ3_entropy_coder coder>
LZ3_FORCE_INLINE uint32_t LZ3_compress_generic(const uint8_t* src, uint8_t* dst, uint32_t srcSize)
{
    LZ3_suffix_array* psa = new LZ3_suffix_array(srcSize);
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
    delete psa;
    stable_sort(matches.begin() + survive, matches.end(), [&candidates, &offsets](uint32_t x, uint32_t y)
    {
        return offsets[candidates[x].offset] > offsets[candidates[y].offset];
    });
    for (auto i = survive; i < matches.size(); ++i)
    {
        uint32_t index = matches[i];
        const LZ3_match_info& match = candidates[index];
        uint32_t position = match.position;
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
        uint32_t position = match.position;
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
            return offsets[x] > offsets[y];
        });
        if (dict.size() > 128)
        {
            dict.resize(128);
        }
        uint32_t srcPos = 0;
        uint32_t dstPos = 0;
        dst[dstPos++] = (uint8_t)dict.size();
        for (uint32_t i = 0; i < dict.size(); ++i)
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
            LZ3_write_LE16(dst, dstPos, token);
            if (literal >= 0xF)
            {
                LZ3_write_HPV8(dst, dstPos, literal - 0xF);
            }
            memcpy(&dst[dstPos], &src[srcPos], literal);
            dstPos += literal;
            srcPos += literal;
            LZ3_write_VL78(dst, dstPos, token, offset);
            if (length >= 0xF)
            {
                LZ3_write_HPV8(dst, dstPos, length - 0xF);
            }
            srcPos += match.length;
        }
        if (srcSize > srcPos)
        {
            uint32_t literal = srcSize - srcPos;
            uint16_t token = (uint16_t)((literal >= 0xF ? 0xF : literal));
            LZ3_write_LE16(dst, dstPos, token);
            if (literal >= 0xF)
            {
                LZ3_write_HPV8(dst, dstPos, literal - 0xF);
            }
            memcpy(&dst[dstPos], &src[srcSize - literal], literal);
            dstPos += literal;
        }
        return dstPos;
    }
    else
    {
        uint32_t srcPos = 0;
        uint32_t dstPos = 0;
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
            return offsets[x] > offsets[y];
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
        dst[dstPos++] = blockLog;
        dst[dstPos++] = lineSize;
        vector<uint8_t> lit;
        vector<uint8_t> seq;
        for (uint32_t index : matches)
        {
            const LZ3_match_info& match = candidates[index];
            uint32_t position = match.position;
            if (position < srcPos)
            {
                continue;
            }
            uint32_t literal = position - srcPos;
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
            uint32_t literal = srcSize - srcPos;
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
        dstPos += LZ3_write_stream(lit.data(), &dst[dstPos], (uint32_t)lit.size(), LZ3_entropy_coder::Huff0);
        dstPos += LZ3_write_stream(seq.data(), &dst[dstPos], (uint32_t)seq.size(), LZ3_entropy_coder::Huff0);
        return dstPos;
    }
}

static constexpr uint32_t wild_cpy_length = 16;

template<LZ3_entropy_coder coder>
LZ3_FORCE_INLINE uint32_t LZ3_decompress_generic(const uint8_t* src, uint8_t* dst, uint32_t dstSize)
{
#if defined(LZ3_LOG) && !defined(NDEBUG)
    ofstream dfs("LZ3_decompress.log");
#endif
    uint32_t srcPos = 0;
    uint32_t dstPos = 0;
    uint32_t dstShortEnd = dstSize > wild_cpy_length ? dstSize - wild_cpy_length : 0;

    uint16_t dict[128];
    const uint16_t* dictPre = dict - 128;

    uint32_t blockLog = 0;
    uint32_t lineSize = 0;
    const uint8_t* lit = nullptr;
    const uint8_t* seq = nullptr;
    uint32_t litPos = 0;
    uint32_t seqPos = 0;
    if (coder == LZ3_entropy_coder::None)
    {
        uint32_t dictSize = src[srcPos++];
        for (uint32_t i = 0; i < dictSize; ++i)
        {
            dict[i] = LZ3_read_VL16(src, srcPos);
        }
        lit = src;
        seq = src;
    }
    else
    {
        blockLog = src[srcPos++];
        lineSize = src[srcPos++];
        if (lineSize == 0)
        {
            lineSize = 256;
        }
        uint8_t* buf = new uint8_t[dstSize * 5];
        srcPos += LZ3_read_stream(&src[srcPos], buf, dstSize, LZ3_entropy_coder::Huff0);
        lit = buf;
        buf += dstSize;
        srcPos += LZ3_read_stream(&src[srcPos], buf, dstSize, LZ3_entropy_coder::Huff0);
        seq = buf;
    }
    while (true)
    {
        uint16_t token;
        uint32_t literal;
        uint32_t length;
        if (coder == LZ3_entropy_coder::None)
        {
            token = LZ3_read_LE16(src, srcPos);
            literal = token & 15;
            length = ((uint8_t)token) >> 4;
        }
        else
        {
            literal = seq[seqPos++];
        }
        if (LZ3_LIKELY(literal <= min(wild_cpy_length, coder == LZ3_entropy_coder::None ? 0xEu : 0xFFu)))
        {
            if (LZ3_UNLIKELY(dstPos >= dstShortEnd))
            {
                goto safe_copy_literal;
            }
            uint32_t refPos = coder == LZ3_entropy_coder::None ? srcPos : litPos;
            //TODO by Lysine: copy literal may read beyond stream end
            memcpy(&dst[dstPos], &lit[refPos], wild_cpy_length);
            dstPos += literal;
            if (coder == LZ3_entropy_coder::None)
            {
                srcPos += literal;
            }
            else
            {
                litPos += literal;
            }
        }
        else
        {
            if (coder == LZ3_entropy_coder::None)
            {
                if (literal >= 0xF)
                {
                    literal = LZ3_read_HPV8(src, srcPos, literal);
                }
            }
            else
            {
                if (literal >= 0xFF)
                {
                    literal = LZ3_read_LE16(seq, seqPos);
                }
            }
        safe_copy_literal:
            uint32_t cpyEnd = dstPos + literal;
            uint32_t cpyPos = dstPos;
            uint32_t refPos = coder == LZ3_entropy_coder::None ? srcPos : litPos;
            if (cpyEnd <= dstShortEnd)
            {
                while(cpyPos < cpyEnd)
                {
                    memcpy(&dst[cpyPos], &lit[refPos], wild_cpy_length);
                    cpyPos += wild_cpy_length;
                    refPos += wild_cpy_length;
                }
            }
            else
            {
                assert(cpyEnd <= dstSize);
                while(cpyPos < cpyEnd)
                {
                    dst[cpyPos++] = lit[refPos++];
                }
            }
            dstPos += literal;
            if (coder == LZ3_entropy_coder::None)
            {
                srcPos += literal;
            }
            else
            {
                litPos += literal;
            }
            if (dstPos == dstSize)
            {
                break;
            }
        }
        uint32_t offset;
        if (coder == LZ3_entropy_coder::None)
        {
            offset = LZ3_read_VL78(src, srcPos, token, dictPre);
        }
        else
        {
            if (blockLog != 0)
            {
                uint8_t x = seq[seqPos++];
                uint8_t y = seq[seqPos] & ((1 << (8 - blockLog)) - 1);
                uint8_t r = seq[seqPos++] >> (8 - blockLog);
                offset = ((x + y * lineSize) << blockLog) | r;
            }
            else
            {
                offset = LZ3_read_LE16(seq, seqPos);
            }
            length = seq[seqPos++];
        }
        if (LZ3_LIKELY(length <= wild_cpy_length - min_match_length))
        {
            length += min_match_length;
            if (LZ3_UNLIKELY(dstPos >= dstShortEnd || offset < wild_cpy_length))
            {
                goto safe_copy_match;
            }
            assert(dstPos >= offset);
            uint32_t refPos = dstPos - offset;
            memcpy(&dst[dstPos], &dst[refPos], wild_cpy_length);
#if defined(LZ3_LOG) && !defined(NDEBUG)
            dfs << dstPos << ": " << length << " " << offset << endl;
#endif
            dstPos += length;
        }
        else
        {
            if (coder == LZ3_entropy_coder::None)
            {
                if (length >= 0xF)
                {
                    length = LZ3_read_HPV8(src, srcPos, length);
                }
            }
            else
            {
                if (length >= 0xFF)
                {
                    length = LZ3_read_LE16(seq, seqPos);
                }
            }
            length += min_match_length;
        safe_copy_match:
            assert(dstPos >= offset);
            uint32_t cpyEnd = dstPos + length;
            uint32_t cpyPos = dstPos;
            uint32_t refPos = dstPos - offset;
            if (cpyEnd <= dstShortEnd/*dstEnd - (wild_cpy_length - 1)*/ && offset >= wild_cpy_length)
            {
                do
                {
                    memcpy(&dst[cpyPos], &dst[refPos], wild_cpy_length);
                    cpyPos += wild_cpy_length;
                    refPos += wild_cpy_length;
                }
                while(cpyPos < cpyEnd);
            }
            else
            {
                assert(cpyEnd <= dstSize);
                do
                {
                    dst[cpyPos++] = dst[refPos++];
                }
                while(cpyPos < cpyEnd);
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
    if (lit != src)
    {
        delete[] lit;
    }
    return srcPos;
}

uint32_t LZ3_compress(const void* src, void* dst, uint32_t srcSize)
{
    uint32_t dstPos = LZ3_compress_generic<LZ3_entropy_coder::None>((const uint8_t*)src, (uint8_t*)dst, (uint32_t)srcSize);
    vector<uint8_t> test(srcSize);
    assert(LZ3_decompress_fast(dst, test.data(), srcSize) == dstPos);
    for (uint32_t i = 0; i < srcSize; ++i)
    {
        assert(test[i] == ((const uint8_t*)src)[i]);
    }
    return dstPos;
}

uint32_t LZ3_decompress_fast(const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_generic<LZ3_entropy_coder::None>((const uint8_t*)src, (uint8_t*)dst, (uint32_t)dstSize);
}

uint32_t LZ3_compress_HUF(const void* src, void* dst, uint32_t srcSize)
{
    uint32_t dstPos = LZ3_compress_generic<LZ3_entropy_coder::Huff0>((const uint8_t*)src, (uint8_t*)dst, (uint32_t)srcSize);
    vector<uint8_t> test(srcSize);
    assert(LZ3_decompress_HUF_fast(dst, test.data(), srcSize) == dstPos);
    for (uint32_t i = 0; i < srcSize; ++i)
    {
        assert(test[i] == ((const uint8_t*)src)[i]);
    }
    return dstPos;
}

uint32_t LZ3_decompress_HUF_fast(const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_generic<LZ3_entropy_coder::Huff0>((const uint8_t*)src, (uint8_t*)dst, (uint32_t)dstSize);
}
