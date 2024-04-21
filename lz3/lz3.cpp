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
#include "zstd/lib/common/bitstream.h"
#include "zstd/lib/common/huf.h"
#include "zstd/lib/common/fse.h"

#if !defined(NDEBUG) && (defined(LZ3_LOG_SA) || defined(LZ3_LOG_SEQ))
#include <fstream>
#include <iomanip>
#endif

#if defined(__GNUC__) || defined(__clang__)
#define LZ3_FORCE_INLINE   inline __attribute__((always_inline))
#define LZ3_LIKELY(expr)   __builtin_expect(!!(expr), 1)
#define LZ3_UNLIKELY(expr) __builtin_expect(!!(expr), 0)
#define LZ3_UNREACHABLE    __builtin_unreachable()
#elif defined(_MSC_VER)
#define LZ3_FORCE_INLINE   __forceinline
#define LZ3_LIKELY(expr)   (expr)
#define LZ3_UNLIKELY(expr) (expr)
#define LZ3_UNREACHABLE    __assume(0)
#else
#define LZ3_FORCE_INLINE   inline
#define LZ3_LIKELY(expr)   (expr)
#define LZ3_UNLIKELY(expr) (expr)
#define LZ3_UNREACHABLE    
#endif

using namespace std;

/*3 byte variant of LZ4 for textures
* modify LZ4 sequence definition to allow match of 3 byte
* |            msb                           lsb               |
* |     1bit    |     7bit     |     4bit     |      4bit      |
* | offset mode | offset value | match length | literal length |
*/

#define LZ3_MAX_ARRAY_SIZE (LZ3_MAX_BLOCK_SIZE + LZ3_DISTANCE_MAX)

class LZ3_suffix_array
{
public:
    uint32_t n;
    
    LZ3_suffix_array(uint32_t l = 0)
    {
        n = l;
        sa = &buffer[0];
        rk = &buffer[LZ3_MAX_ARRAY_SIZE];
        height = &buffer[LZ3_MAX_ARRAY_SIZE * 4];
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
        rk = &buffer[LZ3_MAX_ARRAY_SIZE];
        uint32_t* sa_2nd = &buffer[LZ3_MAX_ARRAY_SIZE * 2];
        uint32_t* rk_2nd = &buffer[LZ3_MAX_ARRAY_SIZE * 3];
        uint32_t* bucket = &buffer[LZ3_MAX_ARRAY_SIZE * 4];
        uint32_t bucket_count = 256;

        //对第一个字符排序
        fill_n(bucket, bucket_count, 0);
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
            fill_n(bucket, bucket_count, 0);
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
        height = &buffer[LZ3_MAX_ARRAY_SIZE * 4];

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
                h = LZ3_MAX_ARRAY_SIZE;
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
    uint32_t buffer[LZ3_MAX_ARRAY_SIZE * 5];

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

class LZ3_match_info
{
public:
    uint32_t position;
    uint32_t length;
    uint32_t offset;
};

class LZ3_match_iter : public LZ3_match_info
{
public:
    LZ3_match_iter(const LZ3_suffix_array* psa, uint32_t position) :
        LZ3_match_info{ position, LZ3_DISTANCE_MAX + 1, 0 }
    {
        prev = psa->rk[position];
        next = psa->rk[position] + 1;
    }

    bool match_next(const LZ3_suffix_array* psa, uint32_t min_length)
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
            if (length < min_length)
            {
                return false;
            }
            if (position > index && position - index <= LZ3_DISTANCE_MAX)
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

class LZ3_match_optm : public LZ3_match_info
{
public:
    uint32_t literal;
    float price;

    LZ3_match_optm() :
        LZ3_match_info{ 0 ,0, 0 }, literal(0), price(INFINITY)
    {
    }
};

LZ3_FORCE_INLINE static void LZ3_write_LE16(uint8_t*& dst, uint16_t value)
{
    memcpy(dst, &value, sizeof(uint16_t));
    dst += sizeof(uint16_t);
}

LZ3_FORCE_INLINE static uint16_t LZ3_read_LE16(const uint8_t*& src)
{
    uint16_t value;
    memcpy(&value, src, sizeof(uint16_t));
    src += sizeof(uint16_t);
    return value;
}

LZ3_FORCE_INLINE static void LZ3_write_VL16(uint8_t*& dst, uint16_t value)
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

LZ3_FORCE_INLINE static uint16_t LZ3_read_VL16(const uint8_t*& src)
{
    uint16_t value = *src++;
    if (value & 0x80)
    {
        value ^= (*src++) << 7;
    }
    return value;
}

LZ3_FORCE_INLINE static void LZ3_write_HPV8(uint8_t*& dst, uint32_t value)
{
    while (value >= 0xFF)
    {
        *dst++ = 0xFF;
        value -= 0xFF;
    }
    *dst++ = (uint8_t)value;
}

LZ3_FORCE_INLINE static uint32_t LZ3_read_HPV8(const uint8_t*& src, uint32_t value)
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

LZ3_FORCE_INLINE static void LZ3_write_VL78(uint8_t*& dst, uint16_t token, uint32_t value)
{
    if ((token & 0x8000) == 0)
    {
        *dst++ = (token & 0xFF) ^ (value & 0xFF);
    }
}

LZ3_FORCE_INLINE static uint32_t LZ3_read_VL78(const uint8_t*& src, uint16_t token, const uint16_t* dict)
{
    if ((token & 0x8000) == 0)
    {
        return token ^ (*src++);
    }
    else
    {
        return dict[(token >> 8) & 0x7F];
    }
}

enum class LZ3_entropy_coder
{
    None,
    Huff0,
    FSE,
};

enum class LZ3_compress_flag : uint8_t
{
    None,
    OffsetRepeat = 1,
    OffsetBlock  = 2,
    OffsetTwoDim = 4,
};

enum class LZ3_history_pos
{
    Prefix,
    Extern,
};

LZ3_FORCE_INLINE static constexpr LZ3_compress_flag operator|(LZ3_compress_flag lhs, LZ3_compress_flag rhs) 
{
    return static_cast<LZ3_compress_flag>(static_cast<uint8_t>(lhs) | static_cast<uint8_t>(rhs));
}

LZ3_FORCE_INLINE static constexpr LZ3_compress_flag operator^(LZ3_compress_flag lhs, LZ3_compress_flag rhs) 
{
    return static_cast<LZ3_compress_flag>(static_cast<uint8_t>(lhs) ^ static_cast<uint8_t>(rhs));
}

LZ3_FORCE_INLINE static constexpr bool operator&(LZ3_compress_flag lhs, LZ3_compress_flag rhs) 
{
    return (static_cast<uint8_t>(lhs) & static_cast<uint8_t>(rhs)) > 0;
}

#define LZ3_MAX_LL 35

static uint16_t ll_base[LZ3_MAX_LL] = {
    0,        1,        2,        3,        4,        5,        6,        7,
    8,        9,        10,       11,       12,       13,       14,       15,
    16,       18,       20,       22,       24,       28,       32,       40,
    48,       64,       0x80,     0x100,    0x200,    0x400,    0x800,    0x1000,
    0x2000,   0x4000,   0x8000
};

static uint8_t ll_bits[LZ3_MAX_LL] = {
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    1,        1,        1,        1,        2,        2,        3,        3,
    4,        6,        7,        8,        9,        10,       11,       12,
    13,       14,       15
};

#define LZ3_MAX_ML 52

static uint16_t ml_base[LZ3_MAX_ML] = {
    3,        4,        5,        6,        7,        8,        9,        10,
    11,       12,       13,       14,       15,       16,       17,       18,
    19,       20,       21,       22,       23,       24,       25,       26,
    27,       28,       29,       30,       31,       32,       33,       34,
    35,       37,       39,       41,       43,       47,       51,       59,
    67,       83,       99,       0x83,     0x103,    0x203,    0x403,    0x803,
    0x1003,   0x2003,   0x4003,   0x8003
};

static uint8_t ml_bits[LZ3_MAX_ML] = {
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    1,        1,        1,        1,        2,        2,        3,        3,
    4,        4,        5,        7,        8,        9,       10,        11,
    12,       13,       14,       15
};

/* of_base and of_bits will be generated based on compress flags
 
** results of OffsetRepeat

static uint16_t of_base_repeat[] = {
    0,        1,        1,        2,        3,        4,        5,        7,
    9,        0xD,      0x11,     0x19,     0x21,     0x31,     0x41,     0x61,
    0x81,     0xC1,     0x101,    0x181,    0x201,    0x301,    0x401,    0x601,
    0x801,    0xC01,    0x1001,   0x1801,   0x2001,   0x3001,   0x4001,   0x6001,
};

static uint8_t of_bits_repeat[] = {
    0,  1,  0,  0,  0,  0,  1,  1,
    2,  2,  3,  3,  4,  4,  5,  5,
    6,  6,  7,  7,  8,  8,  9,  9,
    10, 10, 11, 11, 12, 12, 13, 13,
};

** results of OffsetBlock | OffsetTwoDim

static uint16_t of_base_dim_x[] = {

    0,
    127,      1,        126,      2,        125,      3,        124,      4,
    123,      5,        122,      6,        121,      7,        120,      8,
    119,      9,        118,      10,       117,      11,       116,      12,
    115,      13,       114,      14,       113,      15,       112,      16,
    111,      17,       109,      19,       107       21,       103,      25,
    99,       29,       91,       37,       83,       45,       67,       61,
};

static uint8_t of_bits_dim_x[] = {
    0,
    0,  0,  0,  0,  0,  0,  0,  0,
    0,  0,  0,  0,  0,  0,  0,  0,
    0,  0,  0,  0,  0,  0,  0,  0,
    0,  0,  0,  0,  0,  0,  0,  0,
    1,  1,  1,  1,  2,  2,  2,  2,
    3,  3,  3,  3,  4,  4,  4,  4,
};*/

static constexpr float repeat_mode_threshold = 0.5f;
static constexpr float block_step_tolerance = 0.98f;
static constexpr float block_mode_threshold = 0.95f;
static constexpr float dim_2_dist_tolerance = 0.12f;
static constexpr float dim_2_mode_threshold = 0.5f;
static constexpr float dim_2_step_tolerance = 0.5f;
static constexpr float uncompress_threshold = 0.99f;
static constexpr float uncompress_intercept = 0.0f;

const char* LZ3_last_error_name = nullptr;

struct LZ3_CCtx
{
    vector<LZ3_match_info> matches;
    unordered_map<uint32_t, uint32_t> offsets;
    union
    {
        struct
        {
            uint16_t dict[128];
            uint32_t dictSize;
        };
        struct
        {
            LZ3_compress_flag flag;
            uint32_t blockLog;
            uint32_t lineSize;
            uint16_t of_base[64];
            uint8_t of_bits[64];
            uint8_t of_size;
            uint32_t preOff[3];
        };
    };
};

struct LZ3_DCtx
{
    union
    {
        struct
        {
            uint16_t dict[128];
        };
        struct
        {
            uint32_t blockLog;
            uint32_t lineSize;
            uint16_t of_base[64];
            uint8_t of_bits[64];
            uint8_t of_size;
            BIT_DStream_t bitStr;
            uint32_t preOff[3];
        };
    };
};

static uint8_t LZ3_gen_off_book(uint16_t* base, uint8_t* bits, uint32_t repeatSize, uint32_t blockLog, uint32_t lineSize, LZ3_compress_flag flag)
{
    uint8_t i = 0;
    if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        uint32_t b = 0;
        for (uint8_t l = 0; b < repeatSize; ++l)
        {
            base[i] = (uint16_t)b;
            bits[i] = l;
            i++;
            b += 1 << l;
        }
    }
    if (flag & LZ3_compress_flag::OffsetTwoDim)
    {
        uint32_t b = 0;
        uint32_t e = lineSize;
        for (uint8_t l = 0; l < 6; ++l)
        {
            base[i] = (uint16_t)b;
            bits[i] = 0;
            i++;
            b++;
            if (b >= e)
            {
                break;
            }
            base[i] = (uint16_t)(e - 1);
            bits[i] = 0;
            i++;
            e--;
            if (b >= e)
            {
                break;
            }
        }
        for (uint8_t j = 0; ; ++j)
        {
            uint8_t l = j / 2;
            base[i] = (uint16_t)b;
            bits[i] = l;
            i++;
            b += 1 << l;
            if (b >= e)
            {
                break;
            }
            base[i] = (uint16_t)(e - (1 << l));
            bits[i] = l;
            i++;
            e -= 1 << l;
            if (b >= e)
            {
                break;
            }
        }
    }
    else
    {
        uint32_t b = 0;
        for (uint8_t l = 0; l < 2; ++l)
        {
            base[i] = (uint16_t)b;
            bits[i] = 0;
            i++;
            b++;
        }
        for (uint8_t j = 0; ; ++j)
        {
            uint8_t l = j / 2;
            base[i] = (uint16_t)b;
            bits[i] = l;
            i++;
            b += 1 << l;
            if (b > 0xFFFF)
            {
                break;
            }
        }
    }
    return i;
}

static uint8_t LZ3_select_code(uint16_t* base, uint8_t* bits, uint8_t codeSta, uint8_t codeEnd, uint32_t value)
{
    for (uint8_t i = codeSta; i < codeEnd; ++i)
    {
        if (value >= base[i] && value - base[i] < (1u << bits[i]))
        {
            return i;
        }
    }
    assert(false);
    return codeEnd;
}

static void LZ3_encode_len(
    vector<uint8_t>& seq, vector<pair<uint32_t, uint8_t>>& ext,
    uint16_t* base, uint8_t* bits, uint8_t codeSta, uint8_t codeEnd, uint32_t value)
{
    uint8_t c = LZ3_select_code(base, bits, codeSta, codeEnd, value);
    seq.push_back(c);
    if (bits[c] > 0)
    {
        uint32_t d = value - base[c];
        ext.emplace_back(d, bits[c]);
    }
}

static void LZ3_encode_off(
    vector<uint8_t>& seq, vector<pair<uint32_t, uint8_t>>& ext,
    LZ3_CCtx& cctx, uint32_t offset, LZ3_compress_flag flag)
{
    uint8_t i = 0;
    if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        if (offset == cctx.preOff[0])
        {
            seq.push_back(0);
            return;
        }
        if (offset == cctx.preOff[1] || offset == cctx.preOff[2])
        {
            seq.push_back(1);
            ext.emplace_back(offset == cctx.preOff[1] ? 0u : 1u, (uint8_t)1u);
            return;
        }
        i += 2;
    }
    if (flag & LZ3_compress_flag::OffsetBlock)
    {
        uint32_t r = offset & ((1 << cctx.blockLog) - 1);
        if (r != 0)
        {
            r = (1 << cctx.blockLog) - r;
            seq.push_back(cctx.of_size);
            ext.emplace_back(r, (uint8_t)cctx.blockLog);
            offset += r;
        }
        offset >>= cctx.blockLog;
    }
    if (flag & LZ3_compress_flag::OffsetTwoDim)
    {
        offset -= 1;
        uint32_t x = offset % cctx.lineSize;
        uint32_t y = offset / cctx.lineSize;
        uint8_t c = LZ3_select_code(cctx.of_base, cctx.of_bits, i, cctx.of_size, x);
        seq.push_back(c);
        if (cctx.of_bits[c] > 0)
        {
            uint32_t d = x - cctx.of_base[c];
            ext.emplace_back(d, cctx.of_bits[c]);
        }
        seq.push_back((uint8_t)y);
    }
    else
    {
        uint8_t c = LZ3_select_code(cctx.of_base, cctx.of_bits, i, cctx.of_size, offset);
        seq.push_back(c);
        if (cctx.of_bits[c] > 0)
        {
            uint32_t d = offset - cctx.of_base[c];
            ext.emplace_back(d, cctx.of_bits[c]);
        }
    }
}

static void LZ3_encode_off_wrapper(
    vector<uint8_t>& seq, vector<pair<uint32_t, uint8_t>>& ext,
    LZ3_CCtx& cctx, uint32_t offset, LZ3_compress_flag flag)
{
    LZ3_encode_off(seq, ext, cctx, offset, flag);
    if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        cctx.preOff[2] = cctx.preOff[1];
        cctx.preOff[1] = cctx.preOff[0];
        cctx.preOff[0] = offset;
    }
}

#if defined(_WIN64)
//windows x64 calling convention only have one 64bit reg for return value
struct LZ3_decode_off_result
{
    typedef uint32_t reg_t;
    reg_t offset;
    reg_t seqLen;
};
#else
//use two reg to avoid shifting
struct LZ3_decode_off_result
{
    typedef size_t reg_t;
    reg_t offset;
    reg_t seqLen;
};
#endif

template<uint32_t blockLog, uint32_t lineSize, uint32_t codeEnd, LZ3_compress_flag flag>
LZ3_FORCE_INLINE static LZ3_decode_off_result LZ3_decode_off(const uint8_t* seqPtr, LZ3_DCtx& dctx)
{
    uint32_t c = *seqPtr++;
    if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        if (c == 0)
        {
            return { dctx.preOff[0],  1 };
        }
        if (c == 1)
        {
            return { dctx.preOff[1 + BIT_readBitsFast(&dctx.bitStr, 1)], 1 };
        }
    }
    uint32_t u = c;
    if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        u -= 2;
    }
    uint32_t b = blockLog;
    uint32_t l = lineSize;
    uint32_t e = codeEnd;
    if (flag & LZ3_compress_flag::OffsetBlock)
    {
        if (blockLog == 0)
            b = dctx.blockLog;
        if (codeEnd == 0)
            e = dctx.of_size;
        if (c >= e)
        {
            uint32_t r = (uint32_t)BIT_readBitsFast(&dctx.bitStr, b);
            auto result = LZ3_decode_off<0, lineSize, 0, flag ^ LZ3_compress_flag::OffsetBlock>(seqPtr, dctx);
            result.offset = (result.offset << b) - r;
            result.seqLen += 1;
            return result;
        }
    }
    if (flag & LZ3_compress_flag::OffsetTwoDim)
    {
        if (lineSize == 0)
            l = dctx.lineSize;
        if (u < 16)
        {
            uint32_t x = dctx.of_base[c];
            /*if ((u % 2) == 0)
            {
                x = u / 2;
            }
            else
            {
                x = l - 1 - u / 2;
            }*/
            uint32_t y = *seqPtr++;
            return { (x + y * l + 1) << b, 2 };
        }
        else
        {
            uint32_t x = dctx.of_base[c] + (uint32_t)BIT_readBitsFast(&dctx.bitStr, dctx.of_bits[c]);
            uint32_t y = *seqPtr++;
            return { (x + y * l + 1) << b, 2 };
        }
    }
    else
    {
        if (u < 4)
        {
            return { u << b, 1 };
        }
        else
        {
            uint32_t o = dctx.of_base[c] + (uint32_t)BIT_readBitsFast(&dctx.bitStr, dctx.of_bits[c]);
            return { o << b, 1 };
        }
    }
    LZ3_UNREACHABLE;
}

template<uint32_t blockLog, uint32_t lineSize, uint32_t codeEnd, LZ3_compress_flag flag>
static LZ3_decode_off_result LZ3_decode_off_wrapper(const uint8_t* seqPtr, LZ3_DCtx& dctx)
{
    auto result = LZ3_decode_off<blockLog, lineSize, codeEnd, flag>(seqPtr, dctx);
    if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        dctx.preOff[2] = dctx.preOff[1];
        dctx.preOff[1] = dctx.preOff[0];
        dctx.preOff[0] = result.offset;
    }
    return result;
}

typedef LZ3_decode_off_result(*LZ3_off_decoder)(const uint8_t* seqPtr, LZ3_DCtx& dctx);

static LZ3_off_decoder LZ3_gen_off_decoder(uint32_t blockLog, uint32_t lineSize, uint32_t codeEnd, LZ3_compress_flag flag)
{
    switch ((uint8_t)flag & 7)
    {
    case 0:
        if (codeEnd == 32)
            return &LZ3_decode_off_wrapper<0, 0, 32, LZ3_compress_flag::None>;
        LZ3_UNREACHABLE;
    case 1:
        if (codeEnd == 34)
            return &LZ3_decode_off_wrapper<0, 0, 34, LZ3_compress_flag::OffsetRepeat>;
        LZ3_UNREACHABLE;
    case 2:
        if (blockLog == 2 && codeEnd == 32)
            return &LZ3_decode_off_wrapper<2, 0, 32, LZ3_compress_flag::OffsetBlock>;
        if (blockLog == 3 && codeEnd == 32)
            return &LZ3_decode_off_wrapper<3, 0, 32, LZ3_compress_flag::OffsetBlock>;
        if (blockLog == 4 && codeEnd == 32)
            return &LZ3_decode_off_wrapper<4, 0, 32, LZ3_compress_flag::OffsetBlock>;
        LZ3_UNREACHABLE;
    case 3:
        if (blockLog == 2 && codeEnd == 34)
            return &LZ3_decode_off_wrapper<2, 0, 34, LZ3_compress_flag::OffsetRepeat | LZ3_compress_flag::OffsetBlock>;
        if (blockLog == 3 && codeEnd == 34)
            return &LZ3_decode_off_wrapper<3, 0, 34, LZ3_compress_flag::OffsetRepeat | LZ3_compress_flag::OffsetBlock>;
        if (blockLog == 4 && codeEnd == 34)
            return &LZ3_decode_off_wrapper<4, 0, 34, LZ3_compress_flag::OffsetRepeat | LZ3_compress_flag::OffsetBlock>;
        LZ3_UNREACHABLE;
    case 4:
        return &LZ3_decode_off_wrapper<0, 0, 0, LZ3_compress_flag::OffsetTwoDim>;
    case 5:
        return &LZ3_decode_off_wrapper<0, 0, 0, LZ3_compress_flag::OffsetRepeat | LZ3_compress_flag::OffsetTwoDim>;
    case 6:
        if (blockLog == 3 && lineSize == 128 && codeEnd == 32)
            return &LZ3_decode_off_wrapper<3, 128, 32, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 3 && lineSize == 256 && codeEnd == 36)
            return &LZ3_decode_off_wrapper<3, 256, 36, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 97 && codeEnd == 30)
            return &LZ3_decode_off_wrapper<4, 97,  30, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 128 && codeEnd == 32)
            return &LZ3_decode_off_wrapper<4, 128, 32, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 171 && codeEnd == 34)
            return &LZ3_decode_off_wrapper<4, 171, 34, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 256 && codeEnd == 36)
            return &LZ3_decode_off_wrapper<4, 256, 36, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        return &LZ3_decode_off_wrapper<0, 0, 0, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
    default:
        return &LZ3_decode_off_wrapper<0, 0, 0, LZ3_compress_flag::OffsetRepeat |LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
    }
}

static void LZ3_write_stream(uint8_t*& dst, const uint8_t* src, size_t srcSize, LZ3_entropy_coder coder)
{
    size_t dstSize = 0;
    if (coder == LZ3_entropy_coder::Huff0)
    {
        dstSize = HUF_compress(&dst[sizeof(uint16_t) * 2], HUF_compressBound(srcSize), src, srcSize);
        if (HUF_isError(dstSize))
        {
            LZ3_last_error_name = HUF_getErrorName(dstSize);
            return;
        }
    }
    if (coder == LZ3_entropy_coder::FSE)
    {
        dstSize = FSE_compress(&dst[sizeof(uint16_t) * 1], FSE_compressBound(srcSize), src, srcSize);
        if (dstSize == 1)
        {
            dstSize = 0;
        }
        if (FSE_isError(dstSize))
        {
            LZ3_last_error_name = FSE_getErrorName(dstSize);
            return;
        }
    }
    if (dstSize + uncompress_intercept > srcSize * uncompress_threshold)
    {
        dstSize = 0;
    }
    if (dstSize == 0)
    {
        LZ3_write_LE16(dst, (uint16_t)dstSize);
        LZ3_write_LE16(dst, (uint16_t)srcSize);
        memcpy(dst, src, srcSize);
        dst += srcSize;
    }
    else if (coder == LZ3_entropy_coder::Huff0)
    {
        LZ3_write_LE16(dst, (uint16_t)dstSize);
        LZ3_write_LE16(dst, (uint16_t)srcSize);
        dst += dstSize;
    }
    else if (coder == LZ3_entropy_coder::FSE)
    {
        LZ3_write_LE16(dst, (uint16_t)dstSize);
        dst += dstSize;
    }
}

static const uint8_t* LZ3_read_stream(const uint8_t*& src, uint8_t* dst, size_t dstCap, LZ3_entropy_coder coder)
{
    size_t srcSize = LZ3_read_LE16(src);
    size_t oriSize;
    if (srcSize == 0)
    {
        oriSize = LZ3_read_LE16(src);
        const uint8_t* raw = src;
        src += oriSize;
        return raw;
    }
    else if (coder == LZ3_entropy_coder::Huff0)
    {
        oriSize = LZ3_read_LE16(src);
        dst += dstCap - oriSize;
        oriSize = HUF_decompress(dst, oriSize, src, srcSize);
        if (HUF_isError(oriSize))
        {
            LZ3_last_error_name = HUF_getErrorName(oriSize);
            return nullptr;
        }
        src += srcSize;
        return dst;
    }
    else if (coder == LZ3_entropy_coder::FSE)
    {
        oriSize = FSE_decompress(dst, dstCap, src, srcSize);
        if (FSE_isError(oriSize))
        {
            LZ3_last_error_name = FSE_getErrorName(oriSize);
            return nullptr;
        }
        src += srcSize;
        return dst;
    }
    else
    {
        return nullptr;
    }
}

template<typename EncodeFunc>
class LZ3_code_hist
{
    uint32_t codes[256];
    uint32_t total;
    EncodeFunc encoder;

public:
    LZ3_code_hist(EncodeFunc encoder) :
        codes{ 0 }, total(0), encoder(encoder)
    {
    }

    void inc_code(uint8_t code, uint32_t inc = 1)
    {
        codes[code] += inc;
        total += inc;
    }

    void inc_value(uint32_t value, uint32_t inc = 1)
    {
        pair<uint8_t, uint8_t> c = encoder(value);
        inc_code(c.first, inc);
    }

    float eval_code(uint8_t code)
    {
        uint32_t f = max(codes[code], 1u);
        float h = -log2(f / (float)total);
        return h;
    }

    float eval_value(uint32_t value)
    {
        pair<uint8_t, uint8_t> c = encoder(value);
        float h = eval_code(c.first);
        h += c.second;
        return h;
    }

    void clear()
    {
        fill_n(codes, 256, 0);
        total = 0;
    }
};

template<typename EncodeFunc>
static LZ3_code_hist<EncodeFunc> LZ3_make_code_hist(EncodeFunc encoder)
{
    return LZ3_code_hist<EncodeFunc>(encoder);
}

static LZ3_compress_flag LZ3_detect_compress_flags(LZ3_CCtx& cctx)
{
    LZ3_compress_flag flag = LZ3_compress_flag::None;
    uint32_t total = (uint32_t)cctx.matches.size();
    uint32_t repeat = 0;
    for (uint32_t i = 3; i < cctx.matches.size(); ++i)
    {
        uint32_t offset = cctx.matches[i].offset;
        if (offset == cctx.matches[i - 1].offset ||
            offset == cctx.matches[i - 2].offset ||
            offset == cctx.matches[i - 3].offset)
        {
            repeat++;
        }
    }
    if (repeat > total * repeat_mode_threshold)
    {
        flag = flag | LZ3_compress_flag::OffsetRepeat;
    }
    vector<uint32_t> hist;
    for (const auto& i : cctx.offsets)
    {
        if (i.second > 0)
        {
            hist.push_back(i.first);
        }
    }
    stable_sort(hist.begin(), hist.end(), [&cctx](uint32_t x, uint32_t y)
    {
        return cctx.offsets[x] != cctx.offsets[y] ? cctx.offsets[x] > cctx.offsets[y] : x < y;
    });
    cctx.blockLog = 0;
    uint32_t blockBest = 0;
    uint32_t blockPrev = total;
    for (uint32_t i = 2; i <= 4; ++i)
    {
        uint32_t count = 0;
        for (uint32_t offset : hist)
        {
            if (offset % (1 << i) == 0)
            {
                count += cctx.offsets[offset];
            }
        }
        if (count > blockPrev * block_step_tolerance)
        {
            blockBest = count;
            cctx.blockLog = i;
        }
        blockPrev = count;
    }
    if (blockBest > total * block_mode_threshold)
    {
        flag = flag | LZ3_compress_flag::OffsetBlock;
    }
    //ASTC may have NPOT line size
    cctx.lineSize = 0;
    uint32_t lineBest = 0;
    for (uint32_t i = 0; i < hist.size() && i < 16u; ++i)
    {
        if (hist[i] % (1 << cctx.blockLog) != 0)
        {
            continue;
        }
        uint32_t count = 0;
        uint32_t divisor = hist[i] >> cctx.blockLog;
        uint32_t sta = min((uint32_t)(divisor * dim_2_dist_tolerance), 16u);
        uint32_t end = divisor - sta;
        for (uint32_t offset : hist)
        {
            if (offset % (1 << cctx.blockLog) != 0)
            {
                continue;
            }
            uint32_t x = (offset >> cctx.blockLog) % divisor;
            uint32_t y = (offset >> cctx.blockLog) / divisor;
            if (y >= 64)
            {
                count = 0;
                break;
            }
            if (y >= 32)
            {
                continue;
            }
            if (x < sta || x >= end)
            {
                count += cctx.offsets[offset];
            }
        }
        if (count > total * dim_2_mode_threshold && count * dim_2_step_tolerance > lineBest)
        {
            lineBest = count;
            cctx.lineSize = divisor;
        }
    }
    if (lineBest > 0)
    {
        flag = flag | LZ3_compress_flag::OffsetBlock;
        flag = flag | LZ3_compress_flag::OffsetTwoDim;
    }
    return flag;
}

template<typename LRawPrice, typename LLenPrice, typename MLenPrice, typename MOffPrice, typename UpdatePrice>
static vector<LZ3_match_info> LZ3_compress_opt(
    const LZ3_suffix_array* psa, const uint8_t* src, size_t srcSize,
    LRawPrice lRawPrice, LLenPrice lLenPrice, MLenPrice mLenPrice, MOffPrice mOffPrice, UpdatePrice updatePrice)
{
    uint32_t hisSize = psa->n - (uint32_t)srcSize;
    uint32_t srcPos = 0;
    vector<LZ3_match_info> matches;
    vector<LZ3_match_optm> optimal;
    vector<LZ3_match_optm> reverse;
    for (uint32_t i = 0; i < srcSize;)
    {
        LZ3_match_iter match(psa, i + hisSize);
        if (match.match_next(psa, min_match_length))
        {
            uint32_t lastPos = match.length;
            optimal.clear();
            optimal.resize(lastPos + 1);
            {
                /* initialize optimal[0] */
                uint32_t lLen = match.position - srcPos;
                optimal[0].literal = lLen;
                optimal[0].price = lLenPrice(lLen);
                /* Set prices for first matches */
                do
                {
                    for (uint32_t k = match.length; k >= min_match_length; --k)
                    {
                        float price = optimal[0].price;
                        price += mLenPrice(k);
                        price += mOffPrice(match.offset);
                        if (price < optimal[k].price)
                        {
                            optimal[k].position = match.position;
                            optimal[k].length = k;
                            optimal[k].offset = match.offset;
                            optimal[k].literal = lLen;
                            optimal[k].price = price;
                        }
                    }
                }
                while (match.match_next(psa, min_match_length));
            }
            for (uint32_t j = 1; j <= lastPos; ++j)
            {
                {
                    /* Fix current position with one literal if cheaper */
                    uint32_t lLen = optimal[j - 1].length == 0 ? optimal[j - 1].literal + 1 : 1;
                    float price = optimal[j - 1].price;
                    price += lRawPrice(src[i + j - 1]);
                    price += lLenPrice(lLen);
                    price -= lLenPrice(lLen - 1);
                    if (price < optimal[j].price)
                    {
                        optimal[j].position = 0;
                        optimal[j].length = 0;
                        optimal[j].offset = 0;
                        optimal[j].literal = lLen;
                        optimal[j].price = price;
                    }
                }
                if (j < lastPos)
                {
                    /* Set prices using further matches found */
                    uint32_t lLen = optimal[j].length == 0 ? optimal[j].literal : 0;
                    LZ3_match_iter matchFurther(psa, i + hisSize + j);
                    while (matchFurther.match_next(psa, min_match_length))
                    {
                        if (j + matchFurther.length > lastPos)
                        {
                            lastPos = j + matchFurther.length;
                            optimal.resize(lastPos + 1);
                        }
                        for (uint32_t k = matchFurther.length; k >= min_match_length; --k)
                        {
                            float price = optimal[j].price;
                            price += mLenPrice(k);
                            price += mOffPrice(matchFurther.offset);
                            if (price < optimal[j + k].price)
                            {
                                optimal[j + k].position = matchFurther.position;
                                optimal[j + k].length = k;
                                optimal[j + k].offset = matchFurther.offset;
                                optimal[j + k].literal = lLen;
                                optimal[j + k].price = price;
                            }
                        }
                    }
                }
            }
            reverse.clear();
            for (uint32_t j = lastPos;;)
            {
                if (optimal[j].length >= min_match_length)
                {
                    reverse.push_back(optimal[j]);
                }
                uint32_t back = optimal[j].literal + optimal[j].length;
                if (j <= back)
                {
                    break;
                }
                j -= back;
            }
            for (auto m = reverse.rbegin(); m != reverse.rend(); ++m)
            {
                srcPos += m->literal;
                matches.push_back({srcPos , m->length, m->offset });
                updatePrice(m->literal, m->length, m->offset);
                srcPos += m->length;
            }
            i += lastPos;
        }
        else
        {
            ++i;
        }
    }
    return matches;
}

template<LZ3_entropy_coder coder>
static size_t LZ3_compress_generic(const LZ3_suffix_array* psa, const uint8_t* src, uint8_t* dst, size_t srcSize)
{
    LZ3_CCtx cctx;
    uint32_t hisSize = psa->n - (uint32_t)srcSize;
    uint32_t srcPos = 0;
#if !defined(NDEBUG) && defined(LZ3_LOG_SA)
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
#endif
    if (coder == LZ3_entropy_coder::None)
    {
        cctx.matches = LZ3_compress_opt(psa, src, srcSize,
            [](uint32_t v) { return 1.0f; },
            [](uint32_t v) { return v < 15 ? 0.5f : (1.5f + (v - 15) / 0xFF); },
            [](uint32_t v) { return v < 18 ? 0.5f : (1.5f + (v - 18) / 0xFF); },
            [&cctx](uint32_t v)
        {
            auto o = cctx.offsets.find(v);
            if (o != cctx.offsets.end())
            {
                return 2.0f / (o->second + 1) + 0.99f/*making appeared offset little cheaper*/;
            }
            else
            {
                return 2.0f;
            }
        },
            [&cctx](uint32_t ll, uint32_t ml, uint32_t mo) { cctx.offsets[mo]++; });
        vector<uint32_t> dict;
        for (auto i = cctx.offsets.begin(); i != cctx.offsets.end();)
        {
            if (i->second >= sizeof(uint16_t)/*sizeof mode1 offset desc*/)
            {
                dict.push_back(i->first);
                ++i;
            }
            else
            {
                i = cctx.offsets.erase(i);
            }
        }
        stable_sort(dict.begin(), dict.end(), [&cctx](uint32_t x, uint32_t y)
        {
            return cctx.offsets[x] != cctx.offsets[y] ? cctx.offsets[x] > cctx.offsets[y] : x < y;
        });
        cctx.dictSize = 0;
        for (uint32_t offset : dict)
        {
            if (cctx.dictSize < 128)
            {
                cctx.dict[cctx.dictSize++] = (uint16_t)offset;
            }
            else
            {
                cctx.offsets.erase(offset);
            }
        }
        cctx.matches = LZ3_compress_opt(psa, src, srcSize,
            [](uint32_t v) { return 1.0f; },
            [](uint32_t v) { return v < 15 ? 0.5f : (1.5f + (v - 15) / 0xFF); },
            [](uint32_t v) { return v < 18 ? 0.5f : (1.5f + (v - 18) / 0xFF); },
            [&cctx](uint32_t v) { return cctx.offsets.find(v) != cctx.offsets.end() ? 1.0f : 2.0f; },
            [](uint32_t ll, uint32_t ml, uint32_t mo) {});
    }
    else
    {
        //init 1st pass code hist
        auto lRawHist = LZ3_make_code_hist([](uint32_t value)
        {
            return make_pair((uint8_t)value, (uint8_t)0);
        });
        for (uint32_t i = 0; i < srcSize; ++i)
        {
            lRawHist.inc_value(src[i]);
        }
        auto lLenHist = LZ3_make_code_hist([](uint32_t value)
        {
            uint8_t c = LZ3_select_code(ll_base, ll_bits, 0, 35, value);
            return make_pair(c, ll_bits[c]);
        });
        static constexpr uint32_t baseLLFreqs[LZ3_MAX_LL] = {
            4, 2, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1
        };
        for (uint8_t i = 0; i < LZ3_MAX_LL; ++i)
        {
            lLenHist.inc_code(i, baseLLFreqs[i]);
        }
        auto mLenHist = LZ3_make_code_hist([](uint32_t value)
        {
            uint8_t c = LZ3_select_code(ml_base, ml_bits, 0, 52, value);
            return make_pair(c, ml_bits[c]);
        });
        for (uint8_t i = 0; i < LZ3_MAX_ML; ++i)
        {
            mLenHist.inc_code(i);
        }
        cctx.of_size = LZ3_gen_off_book(cctx.of_base, cctx.of_bits, 3, 0, 0, LZ3_compress_flag::None);
        auto mOffHist = LZ3_make_code_hist([&cctx](uint32_t value)
        {
            uint8_t i = cctx.flag & LZ3_compress_flag::OffsetRepeat ? 2 : 0;
            uint8_t c = LZ3_select_code(cctx.of_base, cctx.of_bits, i, cctx.of_size, value);
            return make_pair(c, cctx.of_bits[c]);
        });
        for (uint8_t i = 0; i < cctx.of_size; ++i)
        {
            mOffHist.inc_code(i);
        }
        cctx.matches = LZ3_compress_opt(psa, src, srcSize,
            [&lRawHist](uint32_t v) { return lRawHist.eval_value(v); },
            [&lLenHist](uint32_t v) { return lLenHist.eval_value(v); },
            [&mLenHist](uint32_t v) { return mLenHist.eval_value(v); },
            [&mOffHist](uint32_t v) { return mOffHist.eval_value(v); },
            [&lLenHist, &mLenHist, &mOffHist, &cctx](uint32_t ll, uint32_t ml, uint32_t mo)
        {
            lLenHist.inc_value(ll);
            mLenHist.inc_value(ml);
            mOffHist.inc_value(mo);
            cctx.offsets[mo]++;
        });
        //calc 2nd pass code hist
        cctx.flag = LZ3_detect_compress_flags(cctx);
        lRawHist.clear();
        srcPos = 0;
        for (const LZ3_match_info& match : cctx.matches)
        {
            uint32_t position = match.position - hisSize;
            for (uint32_t i = srcPos; i < position; ++i)
            {
                lRawHist.inc_value(src[i]);
            }
            srcPos = position + match.length;
        }
        {
            for (uint32_t i = srcPos; i < srcSize; ++i)
            {
                lRawHist.inc_value(src[i]);
            }
        }
        cctx.of_size = LZ3_gen_off_book(cctx.of_base, cctx.of_bits, 3, cctx.blockLog, cctx.lineSize, cctx.flag);
        mOffHist.clear();
        for (const auto& i : cctx.offsets)
        {
            uint32_t offset = i.first;
            uint32_t count = i.second;
            if (cctx.flag & LZ3_compress_flag::OffsetBlock)
            {
                uint32_t r = offset & ((1 << cctx.blockLog) - 1);
                if (r != 0)
                {
                    r = (1 << cctx.blockLog) - r;
                    mOffHist.inc_value(cctx.of_size, count);
                    offset += r;
                }
                offset >>= cctx.blockLog;
            }
            if (cctx.flag & LZ3_compress_flag::OffsetTwoDim)
            {
                offset -= 1;
                uint32_t x = offset % cctx.lineSize;
                uint32_t y = offset / cctx.lineSize;
                mOffHist.inc_value(x, count);
                mOffHist.inc_code((uint8_t)y, count);
            }
            else
            {
                mOffHist.inc_value(offset, count);
            }
        }
        cctx.matches = LZ3_compress_opt(psa, src, srcSize,
            [&lRawHist](uint32_t v) { return lRawHist.eval_value(v); },
            [&lLenHist](uint32_t v) { return lLenHist.eval_value(v); },
            [&mLenHist](uint32_t v) { return mLenHist.eval_value(v); },
            [&mOffHist, &cctx](uint32_t offset)
        {
            float bits = 0;
            if (cctx.flag & LZ3_compress_flag::OffsetBlock)
            {
                uint32_t r = offset & ((1 << cctx.blockLog) - 1);
                if (r != 0)
                {
                    r = (1 << cctx.blockLog) - r;
                    bits += mOffHist.eval_code(cctx.of_size) + cctx.blockLog;
                    offset += r;
                }
                offset >>= cctx.blockLog;
            }
            if (cctx.flag & LZ3_compress_flag::OffsetTwoDim)
            {
                offset -= 1;
                uint32_t x = offset % cctx.lineSize;
                uint32_t y = offset / cctx.lineSize;
                bits += mOffHist.eval_value(x);
                bits += mOffHist.eval_code((uint8_t)y) + cctx.of_bits[y];
            }
            else
            {
                bits += mOffHist.eval_value(offset);
            }
            return bits;
        },
            [&cctx](uint32_t ll, uint32_t ml, uint32_t mo)
        {
            //TODO by Lysine: update preOff for LZ3_compress_flag::OffsetRepeat
            //cctx.preOff
        });
    }
#if !defined(NDEBUG) && defined(LZ3_LOG_SEQ) 
    ofstream cfs("LZ3_compress.csv");
    cfs << ",Literal,Match,Offset" << endl;
    srcPos = 0;
    for (const LZ3_match_info& match : cctx.matches)
    {
        uint32_t position = match.position - hisSize;
        uint32_t literal = (uint32_t)(position - srcPos);
        uint32_t length = match.length;
        uint32_t offset = match.offset;
        cfs << position << "," << literal << "," << length << "," << offset << endl;
        srcPos += literal;
        srcPos += length;
    }
#endif
    if (coder == LZ3_entropy_coder::None)
    {
        srcPos = 0;
        uint8_t* dstPtr = dst;
        *dstPtr++ = (uint8_t)cctx.dictSize;
        for (uint32_t i = 0; i < cctx.dictSize; ++i)
        {
            LZ3_write_VL16(dstPtr, cctx.dict[i]);
        }
        for (const LZ3_match_info& match : cctx.matches)
        {
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
            uint32_t dictIdx = (uint32_t)distance(cctx.dict, find(cctx.dict, cctx.dict + cctx.dictSize, offset));
            if (dictIdx < cctx.dictSize)
            {
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
        srcPos = 0;
        uint8_t* dstPtr = dst;
        *(LZ3_compress_flag*)(dstPtr++) = cctx.flag;
        if (cctx.flag & LZ3_compress_flag::OffsetBlock)
        {
            *dstPtr++ = (uint8_t)cctx.blockLog;
        }
        if (cctx.flag & LZ3_compress_flag::OffsetTwoDim)
        {
            LZ3_write_LE16(dstPtr, (uint16_t)cctx.lineSize);
        }
        vector<uint8_t> lit;
        vector<uint8_t> lls;
        vector<uint8_t> ofs;
        vector<uint8_t> mls;
        vector<pair<uint32_t, uint8_t>> ext;
        fill_n(cctx.preOff, 3, 0);
        for (const LZ3_match_info& match : cctx.matches)
        {
            uint32_t position = match.position - hisSize;
            if (position < srcPos)
            {
                continue;
            }
            uint32_t literal = (uint32_t)(position - srcPos);
            uint32_t length = match.length;
            uint32_t offset = match.offset;
            copy(&src[srcPos], &src[position], back_inserter(lit));
            if (literal <= 0xF)
            {
                lls.push_back((uint8_t)literal);
            }
            else
            {
                LZ3_encode_len(lls, ext, ll_base, ll_bits, 16, LZ3_MAX_LL, literal);
            }
            srcPos += literal;
            LZ3_encode_off_wrapper(ofs, ext, cctx, offset, cctx.flag);
            if (length <= 0x22)
            {
                mls.push_back((uint8_t)length - min_match_length);
            }
            else
            {
                LZ3_encode_len(mls, ext, ml_base, ml_bits, 32, LZ3_MAX_ML, length);
            }
            srcPos += length;
        }
        if (srcSize > srcPos)
        {
            uint32_t literal = (uint32_t)(srcSize - srcPos);
            if (literal <= 0xF)
            {
                lls.push_back((uint8_t)literal);
            }
            else
            {
                LZ3_encode_len(lls, ext, ll_base, ll_bits, 16, LZ3_MAX_LL, literal);
            }
            copy(&src[srcPos], &src[srcSize], back_inserter(lit));
        }
        LZ3_write_stream(dstPtr, lit.data(), (uint32_t)lit.size(), LZ3_entropy_coder::Huff0);
        LZ3_write_stream(dstPtr, lls.data(), (uint32_t)lls.size(), coder);
        LZ3_write_stream(dstPtr, ofs.data(), (uint32_t)ofs.size(), coder);
        LZ3_write_stream(dstPtr, mls.data(), (uint32_t)mls.size(), coder);
        BIT_CStream_t bitStr;
        BIT_initCStream(&bitStr, dstPtr + sizeof(uint16_t), ext.size() * 2/*15bit*/ + 1 + sizeof(size_t));
        for (size_t i = ext.size(); i > 0; --i)
        {
            const pair<uint32_t, uint8_t>& bits = ext[i - 1];
            BIT_addBitsFast(&bitStr, bits.first, bits.second);
            BIT_flushBits(&bitStr);
        }
        size_t bitSize = BIT_closeCStream(&bitStr);
        LZ3_write_LE16(dstPtr, (uint16_t)bitSize);
        dstPtr += bitSize;
        return dstPtr - dst;
    }
}

template<size_t length>
LZ3_FORCE_INLINE static void LZ3_wild_copy(uint8_t* dst, uint8_t* dstEnd, const uint8_t* src)
{
    do
    {
        memcpy(dst, src, length);
        dst += length;
        src += length;
    }
    while (dst < dstEnd);
}

template<size_t length>
static void LZ3_safe_copy(uint8_t* dst, uint8_t* dstEnd, uint8_t* dstShortEnd, const uint8_t* src)
{
    if (dstEnd <= dstShortEnd)
    {
        LZ3_wild_copy<length>(dst, dstEnd, src);
        return;
    }
    if (dst < dstShortEnd)
    {
        LZ3_wild_copy<length>(dst, dstShortEnd, src);
        src += dstShortEnd - dst;
        dst += dstShortEnd - dst;
    }
    while (dst < dstEnd)
    {
        *dst++ = *src++;
    }
}

template<size_t length>
static void LZ3_safe_move(uint8_t* dst, uint8_t* dstEnd, uint8_t* dstShortEnd, const uint8_t* src)
{
    if (dst + 8 > dstEnd)
    {
        while (dst < dstEnd)
        {
            *dst++ = *src++;
        }
        return;
    }
    ptrdiff_t offset = dst - src;
    if (offset >= 8)
    {
        memcpy(dst, src, 8);
    }
    else
    {
        static constexpr ptrdiff_t dec32table[] = { 0, 1, 2, 1, 4, 4, 4, 4 };   /* added */
        static constexpr ptrdiff_t dec64table[] = { 8, 8, 8, 7, 8, 9,10,11 };   /* subtracted */
        dst[0] = src[0];
        dst[1] = src[1];
        dst[2] = src[2];
        dst[3] = src[3];
        src += dec32table[offset];
        memcpy(dst + 4, src, 4);
        src -= dec64table[offset];
    }
    dst += 8;
    src += 8;
    if (length > 8u && offset < length)
    {
        LZ3_safe_copy<8u>(dst, dstEnd, dstShortEnd, src);
        return;
    }
    LZ3_safe_copy<length>(dst, dstEnd, dstShortEnd, src);
}

static constexpr uint32_t wild_copy_length = 16;

template<LZ3_entropy_coder coder, LZ3_history_pos hisPos>
static size_t LZ3_decompress_generic(const uint8_t* src, uint8_t* dst, size_t dstSize, size_t preSize, const uint8_t* ext, size_t extSize)
{
#if !defined(NDEBUG) && defined(LZ3_LOG_SEQ) 
    ofstream dfs("LZ3_decompress.csv");
    dfs << ",Literal,Match,Offset" << endl;
#endif
    const uint8_t* srcPtr = src;
    uint8_t* dstPtr = dst;
    uint8_t* dstEnd = dstPtr + dstSize;
    uint8_t* dstShortEnd = dstEnd - wild_copy_length;

    LZ3_DCtx dctx;
    LZ3_compress_flag flag = LZ3_compress_flag::None;
    LZ3_off_decoder decodeOffWrapper = nullptr;
    uint8_t* buf = nullptr;
    const uint8_t* litPtr = nullptr;
    const uint8_t* llsPtr = nullptr;
    const uint8_t* ofsPtr = nullptr;
    const uint8_t* mlsPtr = nullptr;
    if (coder == LZ3_entropy_coder::None)
    {
        uint32_t dictSize = *srcPtr++;
        for (uint32_t i = 0; i < dictSize; ++i)
        {
            dctx.dict[i] = LZ3_read_VL16(srcPtr);
        }
    }
    else
    {
        flag = (LZ3_compress_flag)*srcPtr++;
        dctx.blockLog = 0;
        dctx.lineSize = 0;
        if (flag & LZ3_compress_flag::OffsetBlock)
        {
            dctx.blockLog = *srcPtr++;
        }
        if (flag & LZ3_compress_flag::OffsetTwoDim)
        {
            dctx.lineSize = LZ3_read_LE16(srcPtr);
        }
        dctx.of_size = LZ3_gen_off_book(dctx.of_base, dctx.of_bits, 3, dctx.blockLog, dctx.lineSize, flag);
        decodeOffWrapper = LZ3_gen_off_decoder(dctx.blockLog, dctx.lineSize, dctx.of_size, flag);
        buf = new uint8_t[dstSize * 4];
        uint8_t* bufPtr = buf;
        litPtr = LZ3_read_stream(srcPtr, bufPtr, dstSize, LZ3_entropy_coder::Huff0);
        bufPtr += dstSize;
        llsPtr = LZ3_read_stream(srcPtr, bufPtr, dstSize, coder);
        bufPtr += dstSize;
        ofsPtr = LZ3_read_stream(srcPtr, bufPtr, dstSize, coder);
        bufPtr += dstSize;
        mlsPtr = LZ3_read_stream(srcPtr, bufPtr, dstSize, coder);
        size_t bitSize = LZ3_read_LE16(srcPtr);
        BIT_initDStream(&dctx.bitStr, srcPtr, bitSize);
        srcPtr += bitSize;
        fill_n(dctx.preOff, 3, 0);
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
            literal = *llsPtr++;
        }
        if (LZ3_LIKELY(literal <= min(wild_copy_length, coder == LZ3_entropy_coder::None ? 0xEu : 0xFu)))
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
            //TODO by Lysine: copy literal may read beyond source/stream end
            memcpy(cpyPtr, refPtr, wild_copy_length);
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
                if (literal >= 0x10)
                {
                    uint32_t c = literal;
                    literal = ll_base[c] + (uint32_t)BIT_readBitsFast(&dctx.bitStr, ll_bits[c]);
                }
            }
        safe_copy_literal:
            uint8_t* cpyPtr = dstPtr;
            uint8_t* cpyEnd = dstPtr + literal;
            assert(cpyEnd <= dstEnd);
            const uint8_t* refPtr;
            if (coder == LZ3_entropy_coder::None)
            {
                refPtr = srcPtr;
            }
            else
            {
                refPtr = litPtr;
            }
            LZ3_safe_copy<wild_copy_length>(cpyPtr, cpyEnd, dstShortEnd, refPtr);
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
            offset = LZ3_read_VL78(srcPtr, token, dctx.dict);
        }
        else
        {
            auto result = decodeOffWrapper(ofsPtr, dctx);
            offset = (uint32_t)result.offset;
            ofsPtr += result.seqLen;
            length = *mlsPtr++;
        }
        if (LZ3_LIKELY(length <= min(wild_copy_length - min_match_length, coder == LZ3_entropy_coder::None ? 0xEu : 0x1Fu)))
        {
            length += min_match_length;
            if (LZ3_UNLIKELY(dstPtr >= dstShortEnd || offset < 8))
            {
                goto safe_copy_match;
            }
            const uint8_t* refPtr = dstPtr - offset;
            const uint8_t* prePtr = dst - preSize;
            if (hisPos == LZ3_history_pos::Extern && refPtr < prePtr)
            {
                goto safe_copy_match;
            }
            memcpy(dstPtr + 0, refPtr + 0, 8);
            memcpy(dstPtr + 8, refPtr + 8, wild_copy_length - 8);
#if !defined(NDEBUG) && defined(LZ3_LOG_SEQ) 
            dfs << dstPtr - dst << ","  << literal << "," << length << "," << offset << endl;
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
                if (length >= 0x20)
                {
                    uint32_t c = length;
                    length = ml_base[c] + (uint32_t)BIT_readBitsFast(&dctx.bitStr, ml_bits[c]) - min_match_length;
                }
            }
            length += min_match_length;
        safe_copy_match:
            uint8_t* cpyPtr = dstPtr;
            uint8_t* cpyEnd = dstPtr + length;
            assert(cpyEnd <= dstEnd);
            const uint8_t* refPtr = dstPtr - offset;
            const uint8_t* prePtr = dst - preSize;
            if (hisPos == LZ3_history_pos::Extern && refPtr < prePtr)
            {
                ptrdiff_t extLen = prePtr - refPtr;
                const uint8_t* extEnd = ext + extSize;
                const uint8_t* extPtr = extEnd - extLen;
                if (length <= extLen)
                {
                    //full in ext
                    refPtr = extPtr;
                }
                else
                {
                    //both in ext and pre, copy ext here.
                    refPtr = prePtr;
                    do
                    {
                        *cpyPtr++ = *extPtr++;
                    }
                    while (extPtr < extEnd);
                }
                LZ3_safe_copy<wild_copy_length>(cpyPtr, cpyEnd, dstShortEnd, refPtr);
            }
            else
            {
                LZ3_safe_move<wild_copy_length>(cpyPtr, cpyEnd, dstShortEnd, refPtr);
            }
#if !defined(NDEBUG) && defined(LZ3_LOG_SEQ) 
            dfs << dstPtr - dst << "," << literal << "," << length << "," << offset << endl;
#endif
            dstPtr += length;
            if (dstPtr >= dstEnd)
            {
                break;
            }
        }
        if (coder != LZ3_entropy_coder::None)
        {
            BIT_reloadDStream(&dctx.bitStr);
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
    uint32_t dstPos;
    if (srcSize <= LZ3_MAX_BLOCK_SIZE)
    {
        LZ3_suffix_array* psa = new LZ3_suffix_array(srcSize);
        psa->cal_suffix_array((const uint8_t*)src, srcSize);
        psa->cal_height((const uint8_t*)src, srcSize);
        dstPos = (uint32_t)LZ3_compress_generic<LZ3_entropy_coder::None>(psa, (const uint8_t*)src, (uint8_t*)dst, srcSize);
        delete psa;
    }
    else
    {
        LZ3_CStream* pcs = LZ3_createCStream();
        dstPos = LZ3_compress_continue(pcs, src, dst, srcSize);
        LZ3_freeCStream(pcs);
    }
    vector<uint8_t> test(srcSize);
    assert(LZ3_decompress_fast(dst, test.data(), srcSize) == dstPos);
    for (size_t i = 0; i < srcSize; ++i)
    {
        assert(test[i] == ((const uint8_t*)src)[i]);
    }
    return dstPos;
}

uint32_t LZ3_decompress_fast(const void* src, void* dst, uint32_t dstSize)
{
    uint32_t srcPos;
    if (dstSize < LZ3_MAX_BLOCK_SIZE)
    {
        srcPos = (uint32_t)LZ3_decompress_generic<LZ3_entropy_coder::None, LZ3_history_pos::Prefix>((const uint8_t*)src, (uint8_t*)dst, dstSize, 0, nullptr, 0);
    }
    else
    {
        LZ3_DStream* pds = LZ3_createDStream();
        srcPos = LZ3_decompress_fast_continue(pds, src, dst, dstSize);
        LZ3_freeDStream(pds);
    }
    return srcPos;
}

uint32_t LZ3_compress_HUF(const void* src, void* dst, uint32_t srcSize)
{
    uint32_t dstPos;
    if (srcSize <= LZ3_MAX_BLOCK_SIZE)
    {
        LZ3_suffix_array* psa = new LZ3_suffix_array(srcSize);
        psa->cal_suffix_array((const uint8_t*)src, srcSize);
        psa->cal_height((const uint8_t*)src, srcSize);
        dstPos = (uint32_t)LZ3_compress_generic<LZ3_entropy_coder::Huff0>(psa, (const uint8_t*)src, (uint8_t*)dst, srcSize);
        delete psa;
    }
    else
    {
        LZ3_CStream* pcs = LZ3_createCStream();
        dstPos = LZ3_compress_HUF_continue(pcs, src, dst, srcSize);
        LZ3_freeCStream(pcs);
    }
    vector<uint8_t> test(srcSize);
    assert(LZ3_decompress_HUF_fast(dst, test.data(), srcSize) == dstPos);
    for (size_t i = 0; i < srcSize; ++i)
    {
        assert(test[i] == ((const uint8_t*)src)[i]);
    }
    return dstPos;
}

uint32_t LZ3_decompress_HUF_fast(const void* src, void* dst, uint32_t dstSize)
{
    uint32_t srcPos;
    if (dstSize < LZ3_MAX_BLOCK_SIZE)
    {
        srcPos = (uint32_t)LZ3_decompress_generic<LZ3_entropy_coder::Huff0, LZ3_history_pos::Prefix>((const uint8_t*)src, (uint8_t*)dst, dstSize, 0, nullptr, 0);
    }
    else
    {
        LZ3_DStream* pds = LZ3_createDStream();
        srcPos = LZ3_decompress_HUF_fast_continue(pds, src, dst, dstSize);
        LZ3_freeDStream(pds);
    }
    return srcPos;
}

struct LZ3_CStream
{
    LZ3_suffix_array hsa;
    LZ3_suffix_array tsa;
    uint8_t* psz;
    uint8_t sz[LZ3_MAX_ARRAY_SIZE];

    LZ3_CStream()
    {
        psz = sz;
    };
};

template<LZ3_entropy_coder coder>
uint32_t LZ3_compress_continue_generic(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize)
{
    const uint8_t* srcPtr = (const uint8_t*)src;
    const uint8_t* srcEnd = srcPtr + srcSize;
    uint8_t* dstPtr = (uint8_t*)dst;
    while (srcPtr < srcEnd)
    {
        uint32_t curSize = min((uint32_t)(srcEnd - srcPtr), LZ3_MAX_BLOCK_SIZE);
        pcs->tsa.n = curSize;
        pcs->tsa.cal_suffix_array(srcPtr, curSize);
        pcs->tsa.cal_height(srcPtr, curSize);
        if (pcs->psz + curSize > pcs->sz + sizeof(pcs->sz))
        {
            memcpy(pcs->sz, pcs->psz - LZ3_DISTANCE_MAX, LZ3_DISTANCE_MAX);
            pcs->psz = pcs->sz + LZ3_DISTANCE_MAX;
        }
        memcpy(pcs->psz, srcPtr, curSize);
        srcPtr += curSize;
        if (pcs->hsa.n > LZ3_DISTANCE_MAX)
        {
            pcs->hsa.popn_suffix(pcs->hsa.n - LZ3_DISTANCE_MAX);
        }
        pcs->hsa.push_suffix(pcs->psz - pcs->hsa.n, &pcs->tsa);
        dstPtr += LZ3_compress_generic<coder>(&pcs->hsa, pcs->psz, dstPtr, curSize);
        pcs->psz += curSize;
    }
    return (uint32_t)(dstPtr - (uint8_t*)dst);
}

struct LZ3_DStream
{
    uint8_t* preEnd;
    size_t preSize;
    uint8_t* extPtr;
    size_t extSize;
    uint8_t* psz;
    uint8_t sz[LZ3_MAX_ARRAY_SIZE];

    LZ3_DStream()
    {
        preEnd = nullptr;
        preSize = 0;
        extPtr = nullptr;
        extSize = 0;
        psz = sz;
    };
};

template<LZ3_entropy_coder coder>
uint32_t LZ3_decompress_continue_generic(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    const uint8_t* srcPtr = (const uint8_t*)src;
    uint8_t* dstPtr = (uint8_t*)dst;
    uint8_t* dstEnd = dstPtr + dstSize;
    while (dstPtr < dstEnd)
    {
        uint32_t curSize = min((uint32_t)(dstEnd - dstPtr), LZ3_MAX_BLOCK_SIZE);
        if (pds->psz + curSize > pds->sz + sizeof(pds->sz))
        {
            memcpy(pds->sz, pds->psz - LZ3_DISTANCE_MAX, LZ3_DISTANCE_MAX);
            pds->psz = pds->sz + LZ3_DISTANCE_MAX;
        }
        srcPtr += LZ3_decompress_generic<coder, LZ3_history_pos::Prefix>(srcPtr, pds->psz, curSize, 0, nullptr, 0);
        memcpy(dstPtr, pds->psz, curSize);
        dstPtr += curSize;
        pds->psz += curSize;
    }
    return (uint32_t)(srcPtr - (const uint8_t*)src);
}

template<LZ3_entropy_coder coder>
uint32_t LZ3_decompress_fast_continue_generic(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    const uint8_t* srcPtr = (const uint8_t*)src;
    uint8_t* dstPtr = (uint8_t*)dst;
    uint8_t* dstEnd = dstPtr + dstSize;
    while (dstPtr < dstEnd)
    {
        size_t curSize = min<size_t>(dstEnd - dstPtr, LZ3_MAX_BLOCK_SIZE);
        if (pds->preSize == 0)
        {
            //0. Dst
            srcPtr += LZ3_decompress_generic<coder, LZ3_history_pos::Prefix>(srcPtr, dstPtr, curSize, 0, nullptr, 0);
        }
        else if (dstPtr != pds->preEnd)
        {
            //2. Dst------------Ext
            pds->extPtr = pds->preEnd - pds->preSize;
            pds->extSize = pds->preSize;
            pds->preSize = 0;
            srcPtr += LZ3_decompress_generic<coder, LZ3_history_pos::Extern>(srcPtr, dstPtr, curSize, 0, pds->extPtr, pds->extSize);
        }
        else if (pds->preSize >= LZ3_DISTANCE_MAX || pds->extSize == 0)
        {
            //1. -----------Pre-Dst
            srcPtr += LZ3_decompress_generic<coder, LZ3_history_pos::Prefix>(srcPtr, dstPtr, curSize, pds->preSize, nullptr, 0);
        }
        else
        {
            //3. Pre-Dst--------Ext
            srcPtr += LZ3_decompress_generic<coder, LZ3_history_pos::Extern>(srcPtr, dstPtr, curSize, pds->preSize, pds->extPtr, pds->extSize);
        }
        dstPtr += curSize;
        pds->preEnd = dstPtr;
        pds->preSize += curSize;
    }
    return (uint32_t)(srcPtr - (const uint8_t*)src);
}

LZ3_CStream* LZ3_createCStream()
{
    return new LZ3_CStream();
}

LZ3_DStream* LZ3_createDStream()
{
    return new LZ3_DStream();
}

void LZ3_freeCStream(LZ3_CStream* pcs)
{
    delete pcs;
}

void LZ3_freeDStream(LZ3_DStream* pds)
{
    delete pds;
}

uint32_t LZ3_compress_continue(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize)
{
    return LZ3_compress_continue_generic<LZ3_entropy_coder::None>(pcs, src, dst, srcSize);
}

uint32_t LZ3_decompress_continue(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_continue_generic<LZ3_entropy_coder::None>(pds, src, dst, dstSize);
}

uint32_t LZ3_decompress_fast_continue(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_fast_continue_generic<LZ3_entropy_coder::None>(pds, src, dst, dstSize);
}

uint32_t LZ3_compress_HUF_continue(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize)
{
    return LZ3_compress_continue_generic<LZ3_entropy_coder::Huff0>(pcs, src, dst, srcSize);
}

uint32_t LZ3_decompress_HUF_continue(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_continue_generic<LZ3_entropy_coder::Huff0>(pds, src, dst, dstSize);
}

uint32_t LZ3_decompress_HUF_fast_continue(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_fast_continue_generic<LZ3_entropy_coder::Huff0>(pds, src, dst, dstSize);
}
