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

#if defined(LZ3_LOG) && !defined(NDEBUG)
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

LZ3_FORCE_INLINE static void LZ3_write_VL78(uint8_t*& dst, uint32_t token, uint32_t value)
{
    if ((token & 0x8000) == 0)
    {
        *dst++ = (token & 0xFF) ^ (value & 0xFF);
    }
}

LZ3_FORCE_INLINE static uint32_t LZ3_read_VL78(const uint8_t*& src, uint32_t token, const uint16_t* dictPre)
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

enum class LZ3_entropy_coder
{
    None,
    Huff0,
    FSE,
};

enum class LZ3_compress_flag : uint8_t
{
    None,
    OffsetRepeat  = 1,
    OffsetBlock   = 2,
    OffsetTwoDim = 4,
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

static uint16_t ll_base[] = {
    0,        1,        2,        3,        4,        5,        6,        7,
    8,        9,        10,       11,       12,       13,       14,       15,
    16,       18,       20,       22,       24,       28,       32,       40,
    48,       64,       0x80,     0x100,    0x200,    0x400,    0x800,    0x1000,
    0x2000,   0x4000
};

static uint8_t ll_bits[] = {
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    1,        1,        1,        1,        2,        2,        3,        3,
    4,        6,        7,        8,        9,        10,       11,       12,
    13,       14
};

static uint16_t ml_base[] = {
    3,        4,        5,        6,        7,        8,        9,        10,
    11,       12,       13,       14,       15,       16,       17,       18,
    19,       20,       21,       22,       23,       24,       25,       26,
    27,       28,       29,       30,       31,       32,       33,       34,
    35,       37,       39,       41,       43,       47,       51,       59,
    67,       83,       99,       0x83,     0x103,    0x203,    0x403,    0x803,
    0x1003,   0x2003,   0x4003
};

static uint8_t ml_bits[] = {
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    1,        1,        1,        1,        2,        2,        3,        3,
    4,        4,        5,        7,        8,        9,       10,        11,
    12,       13,       14
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

static constexpr uint32_t repeat_mode_threshold = 2;
static constexpr uint32_t block_mode_threshold = 10;
static constexpr uint32_t dim_2_mode_tolerance = 16;
static constexpr uint32_t dim_2_mode_threshold = 2;
static constexpr uint32_t dim_2_mode_stepping = 8;
static constexpr uint32_t uncompress_threshold = 32;
static constexpr uint32_t uncompress_intercept = 0;

const char* LZ3_last_error_name = nullptr;

struct LZ3_CCtx
{
    union
    {
        struct
        {
            vector<uint32_t>* dict;
        };
        struct
        {
            uint32_t blockLog;
            uint32_t lineSize;
            uint16_t of_base[64];
            uint8_t of_bits[64];
            uint8_t of_size;
            vector<uint32_t>* ext;
            vector<uint8_t>* extBits;
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

static uint8_t LZ3_gen_off_book(uint16_t* base, uint8_t* bits, uint32_t preSize, uint32_t lineSize, LZ3_compress_flag flag)
{
    uint8_t i = 0;
    if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        uint16_t b = 0;
        for (uint8_t l = 0; b < preSize; ++l)
        {
            base[i] = b;
            bits[i] = l;
            i++;
            b += 1 << l;
        }
    }
    if (flag & LZ3_compress_flag::OffsetTwoDim)
    {
        uint16_t b = 0;
        uint16_t e = lineSize - 1;
        base[i] = 0;
        bits[i] = 0;
        i++;
        b++;
        for (uint8_t l = 0; l < 14; ++l)
        {
            base[i] = e;
            bits[i] = 0;
            i++;
            if (b >= e)
            {
                break;
            }
            e--;
            base[i] = b;
            bits[i] = 0;
            i++;
            if (b >= e)
            {
                break;
            }
            b++;
        }
        for (uint8_t j = 0; ; ++j)
        {
            uint8_t l = j / 2;
            base[i] = e;
            bits[i] = l;
            i++;
            if (b >= e)
            {
                break;
            }
            e -= 1 << l;
            base[i] = b;
            bits[i] = l;
            i++;
            if (b >= e)
            {
                break;
            }
            b += 1 << l;
        }
    }
    else
    {
        uint32_t b = 0;
        for (uint8_t l = 0; l < 2; ++l)
        {
            base[i] = b;
            bits[i] = 0;
            i++;
            b++;
        }
        for (uint8_t j = 0; ; ++j)
        {
            uint8_t l = j / 2;
            base[i] = b;
            bits[i] = l;
            i++;
            if (b > 0xFFFF)
            {
                break;
            }
            b += 1 << l;
        }
    }
    return i;
}

static void LZ3_encode_seq(
    vector<uint8_t>& seq, vector<uint32_t>& ext, vector<uint8_t>& extBits,
    uint16_t* base, uint8_t* bits, uint8_t codeSta, uint8_t codeEnd, uint32_t value)
{
    uint32_t c = codeSta;
    uint32_t d = value - base[c];
    for (uint32_t i = c + 1; i < codeEnd; ++i)
    {
        if (value >= base[i] && value - base[i] < d)
        {
            c = i;
            d = value - base[i];
        }
    }
    seq.push_back((uint8_t)c);
    ext.push_back(d);
    extBits.push_back(bits[c]);
}

static void LZ3_encode_off(vector<uint8_t>& seq, LZ3_CCtx& cctx, uint32_t offset, LZ3_compress_flag flag)
{
    uint32_t i = 0;
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
            cctx.ext->push_back(offset == cctx.preOff[1] ? 0 : 1);
            cctx.extBits->push_back(1);
            return;
        }
        i += 2;
    }
    if (flag & LZ3_compress_flag::OffsetBlock)
    {
        uint32_t r = offset & ((1 << cctx.blockLog) - 1);
        if (r != 0)
        {
            seq.push_back(cctx.of_size);
            cctx.ext->push_back(r);
            cctx.extBits->push_back(cctx.blockLog);
        }
        offset >>= cctx.blockLog;
    }
    if (flag & LZ3_compress_flag::OffsetTwoDim)
    {
        uint32_t x = offset % cctx.lineSize;
        uint32_t y = offset / cctx.lineSize;
        LZ3_encode_seq(seq, *cctx.ext, *cctx.extBits, cctx.of_base, cctx.of_bits, i, cctx.of_size, x);
        seq.push_back(y);
    }
    else
    {
        LZ3_encode_seq(seq, *cctx.ext, *cctx.extBits, cctx.of_base, cctx.of_bits, i, cctx.of_size, offset);
    }
}

static void LZ3_encode_off_wrapper(vector<uint8_t>& seq, LZ3_CCtx& cctx, uint32_t offset, LZ3_compress_flag flag)
{
    LZ3_encode_off(seq, cctx, offset, flag);
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
    bool d = true;
    if (flag & LZ3_compress_flag::OffsetBlock)
    {
        if (blockLog == 0)
            b = dctx.blockLog;
        if (codeEnd == 0)
            e = dctx.of_size;
        d = c < e;
    }
    if (flag & LZ3_compress_flag::OffsetTwoDim)
    {
        if (lineSize == 0)
            l = dctx.lineSize;
        if (u < 33 && d)
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
            return { (x + y * l) << b, 2 };
        }
        if (d)
        {
            uint32_t x = dctx.of_base[c] + (uint32_t)BIT_readBitsFast(&dctx.bitStr, dctx.of_bits[c]);
            uint32_t y = *seqPtr++;
            return { (x + y * l) << b, 2 };
        }
    }
    else
    {
        if (u < 4 && d)
        {
            return { u << b, 1 };
        }
        if (d)
        {
            uint32_t o = dctx.of_base[c] + (uint32_t)BIT_readBitsFast(&dctx.bitStr, dctx.of_bits[c]);
            return { o << b, 1 };
        }
    }
    if (flag & LZ3_compress_flag::OffsetBlock)
    {
        if (!d)
        {
            uint32_t r = (uint32_t)BIT_readBitsFast(&dctx.bitStr, b);
            auto result = LZ3_decode_off<0, lineSize, 0, flag^ LZ3_compress_flag::OffsetBlock>(seqPtr, dctx);
            result.offset = (result.offset << b) | r;
            result.seqLen += 1;
            return result;
        }
    }
    LZ3_UNREACHABLE;
}

template<uint32_t blockLog, uint32_t lineSize, uint32_t codeEnd, LZ3_compress_flag flag>
static LZ3_decode_off_result LZ3_decode_off_wrapper(const uint8_t* seqPtr, LZ3_DCtx& dctx)
{
    auto result = LZ3_decode_off<blockLog, lineSize, codeEnd, flag>(seqPtr, dctx);
    if ((flag & LZ3_compress_flag::OffsetRepeat) != 0)
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
    switch ((uint8_t)flag)
    {
    case 0:
        return &LZ3_decode_off_wrapper<0, 0, 33, (LZ3_compress_flag)0>;
    case 1:
        return &LZ3_decode_off_wrapper<0, 0, 35, (LZ3_compress_flag)1>;
    case 2:
        if (blockLog == 3 && lineSize == 0 && codeEnd == 33)
            return &LZ3_decode_off_wrapper<3, 0, 33, (LZ3_compress_flag)2>;
        if (blockLog == 4 && lineSize == 0 && codeEnd == 33)
            return &LZ3_decode_off_wrapper<4, 0, 33, (LZ3_compress_flag)2>;
        LZ3_UNREACHABLE;
    case 3:
        if (blockLog == 3 && lineSize == 0 && codeEnd == 35)
            return &LZ3_decode_off_wrapper<3, 0, 35, (LZ3_compress_flag)3>;
        if (blockLog == 4 && lineSize == 0 && codeEnd == 35)
            return &LZ3_decode_off_wrapper<4, 0, 35, (LZ3_compress_flag)3>;
        LZ3_UNREACHABLE;
    case 4:
        return &LZ3_decode_off_wrapper<0, 0, 0, (LZ3_compress_flag)4>;
    case 5:
        return &LZ3_decode_off_wrapper<0, 0, 0, (LZ3_compress_flag)5>;
    case 6:
        if (blockLog == 3 && lineSize == 128 && codeEnd == 49)
            return &LZ3_decode_off_wrapper<3, 128, 49, (LZ3_compress_flag)6>;
        if (blockLog == 3 && lineSize == 256 && codeEnd == 54)
            return &LZ3_decode_off_wrapper<3, 256, 54, (LZ3_compress_flag)6>;
        if (blockLog == 4 && lineSize == 128 && codeEnd == 49)
            return &LZ3_decode_off_wrapper<4, 128, 49, (LZ3_compress_flag)6>;
        if (blockLog == 4 && lineSize == 171 && codeEnd == 51)
            return &LZ3_decode_off_wrapper<4, 171, 51, (LZ3_compress_flag)6>;
        if (blockLog == 4 && lineSize == 256 && codeEnd == 54)
            return &LZ3_decode_off_wrapper<4, 256, 54, (LZ3_compress_flag)6>;
        return &LZ3_decode_off_wrapper<0, 0, 0, (LZ3_compress_flag)6>;
    default:
        return &LZ3_decode_off_wrapper<0, 0, 0, (LZ3_compress_flag)7>;
    }
}

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
static size_t LZ3_compress_generic(const LZ3_suffix_array* psa, const uint8_t* src, uint8_t* dst, size_t srcSize)
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
    LZ3_CCtx cctx;
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
        LZ3_compress_flag& flag = *(LZ3_compress_flag*)(dstPtr++);
        flag = LZ3_compress_flag::None;
        uint32_t total = (uint32_t)matches.size();
        uint32_t repeat = 0;
        for (uint32_t i = 3; i < matches.size(); ++i)
        {
            uint32_t offset = candidates[matches[i]].offset;
            if (offset == candidates[matches[i - 1]].offset ||
                offset == candidates[matches[i - 2]].offset ||
                offset == candidates[matches[i - 3]].offset)
            {
                repeat++;
            }
        }
        if (repeat > total / repeat_mode_threshold)
        {
            flag = flag | LZ3_compress_flag::OffsetRepeat;
        }
        vector<uint32_t> hist;
        for (const auto& i : offsets)
        {
            if (i.second >= min_match_offset)
            {
                hist.push_back(i.first);
            }
        }
        stable_sort(hist.begin(), hist.end(), [&offsets](uint32_t x, uint32_t y)
        {
            return offsets[x] != offsets[y] ? offsets[x] > offsets[y] : x < y;
        });
        cctx.blockLog = 0;
        for (uint32_t i = 4; i >= 3; --i)
        {
            uint32_t incap = 0;
            for (uint32_t offset : hist)
            {
                if (offset % (1 << i) != 0)
                {
                    incap += offsets[offset];
                }
            }
            if (incap <= total / block_mode_threshold)
            {
                cctx.blockLog = i;
                break;
            }
        }
        if (cctx.blockLog > 0)
        {
            flag = flag | LZ3_compress_flag::OffsetBlock;
            *dstPtr++ = cctx.blockLog;
        }
        //ASTC may have NPOT line size
        cctx.lineSize = 0;
        uint32_t lineBest = total;
        for (uint32_t o : hist)
        {
            if (o % (1 << cctx.blockLog) != 0)
            {
                continue;
            }
            uint32_t incap = 0;
            uint32_t divisor = o >> cctx.blockLog;
            if (divisor > 256)
            {
                continue;
            }
            uint32_t min = divisor / dim_2_mode_tolerance;
            uint32_t max = divisor - min;
            for (const auto& i : offsets)
            {
                uint32_t offset = i.first;
                if (offset % (1 << cctx.blockLog) != 0)
                {
                    continue;
                }
                uint32_t x = (offset >> cctx.blockLog) % divisor;
                uint32_t y = (offset >> cctx.blockLog) / divisor;
                if (y >= 64)
                {
                    incap = total;
                    break;
                }
                if ((x >= min && x < max) || y >= min)
                {
                    incap += offsets[offset];
                }
            }
            if (incap < total / dim_2_mode_threshold && incap < (lineBest - lineBest / dim_2_mode_stepping))
            {
                lineBest = incap;
                cctx.lineSize = divisor;
            }
        }
        if (cctx.lineSize > 0)
        {
            flag = flag | LZ3_compress_flag::OffsetTwoDim;
            *dstPtr++ = cctx.lineSize;
        }
        cctx.of_size = LZ3_gen_off_book(cctx.of_base, cctx.of_bits, 3, cctx.lineSize, flag);
        vector<uint8_t> lit;
        vector<uint8_t> seq;
        vector<uint32_t> ext;
        vector<uint8_t> extBits;
        cctx.ext = &ext;
        cctx.extBits = &extBits;
        fill(cctx.preOff, cctx.preOff + 3, 0);
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
            uint32_t offset = match.offset;
            copy(&src[srcPos], &src[position], back_inserter(lit));
            if (literal <= 0xF)
            {
                seq.push_back((uint8_t)literal);
            }
            else
            {
                LZ3_encode_seq(seq, ext, extBits, ll_base, ll_bits, 16, 34, literal);
            }
            srcPos += literal;
            LZ3_encode_off_wrapper(seq, cctx, offset, flag);
            if (length <= 0x22)
            {
                seq.push_back((uint8_t)length - min_match_length);
            }
            else
            {
                LZ3_encode_seq(seq, ext, extBits, ml_base, ml_bits, 32, 51, length);
            }
            srcPos += length;
        }
        if (srcSize > srcPos)
        {
            uint32_t literal = (uint32_t)(srcSize - srcPos);
            if (literal <= 0xF)
            {
                seq.push_back((uint8_t)literal);
            }
            else
            {
                LZ3_encode_seq(seq, ext, extBits, ll_base, ll_bits, 16, 34, literal);
            }
            copy(&src[srcPos], &src[srcSize], back_inserter(lit));
        }
        dstPtr += LZ3_write_stream(lit.data(), dstPtr, (uint32_t)lit.size(), LZ3_entropy_coder::Huff0);
        dstPtr += LZ3_write_stream(seq.data(), dstPtr, (uint32_t)seq.size(), coder);
        BIT_CStream_t bitStr;
        BIT_initCStream(&bitStr, dstPtr + sizeof(uint16_t), ext.size() * 2 + sizeof(size_t));
        for (size_t i = ext.size(); i > 0; --i)
        {
            BIT_addBitsFast(&bitStr, ext[i - 1], extBits[i - 1]);
            BIT_flushBits(&bitStr);
        }
        size_t bitSize = BIT_closeCStream(&bitStr);
        LZ3_write_LE16(dstPtr, (uint16_t)bitSize);
        dstPtr += bitSize;
        return dstPtr - dst;
    }
}

static constexpr uint32_t wild_cpy_length = 16;

template<LZ3_entropy_coder coder>
static size_t LZ3_decompress_generic(const uint8_t* src, uint8_t* dst, size_t dstSize)
{
#if defined(LZ3_LOG) && !defined(NDEBUG)
    ofstream dfs("LZ3_decompress.log");
#endif
    const uint8_t* srcPtr = src;
    uint8_t* dstPtr = dst;
    uint8_t* dstEnd = dstPtr + dstSize;
    uint8_t* dstShortEnd = dstSize > wild_cpy_length ? dstEnd - wild_cpy_length : dstPtr;

    LZ3_DCtx dctx;
    const uint16_t* dictPre = nullptr;
    LZ3_compress_flag flag = LZ3_compress_flag::None;
    LZ3_off_decoder decodeOffWrapper = nullptr;
    uint8_t* buf = nullptr;
    const uint8_t* litPtr = nullptr;
    const uint8_t* seqPtr = nullptr;
    if (coder == LZ3_entropy_coder::None)
    {
        uint32_t dictSize = *srcPtr++;
        for (uint32_t i = 0; i < dictSize; ++i)
        {
            dctx.dict[i] = LZ3_read_VL16(srcPtr);
        }
        dictPre = dctx.dict - 128;
    }
    else
    {
        flag = (LZ3_compress_flag)*srcPtr++;
        dctx.blockLog = 0;
        dctx.lineSize = 0;
        if ((flag & LZ3_compress_flag::OffsetBlock) != 0)
        {
            dctx.blockLog = *srcPtr++;
        }
        if ((flag & LZ3_compress_flag::OffsetTwoDim) != 0)
        {
            dctx.lineSize = *srcPtr++;
            if (dctx.lineSize == 0)
            {
                dctx.lineSize = 256;
            }
        }
        dctx.of_size = LZ3_gen_off_book(dctx.of_base, dctx.of_bits, 3, dctx.lineSize, flag);
        decodeOffWrapper = LZ3_gen_off_decoder(dctx.blockLog, dctx.lineSize, dctx.of_size, flag);
        buf = new uint8_t[dstSize * 5];
        uint8_t* bufPtr = buf;
        srcPtr += LZ3_read_stream(srcPtr, bufPtr, dstSize, LZ3_entropy_coder::Huff0);
        litPtr = bufPtr;
        bufPtr += dstSize;
        srcPtr += LZ3_read_stream(srcPtr, bufPtr, dstSize, coder);
        seqPtr = bufPtr;
        size_t bitSize = LZ3_read_LE16(srcPtr);
        BIT_initDStream(&dctx.bitStr, srcPtr, bitSize);
        srcPtr += bitSize;
        fill(dctx.preOff, dctx.preOff + 3, 0);
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
        if (LZ3_LIKELY(literal <= min(wild_cpy_length, coder == LZ3_entropy_coder::None ? 0xEu : 0xFu)))
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
            if (LZ3_UNLIKELY(cpyEnd > dstShortEnd))
            {
                while(cpyPtr < cpyEnd)
                {
                    *cpyPtr++ = *refPtr++;
                }
            }
            else
            {
                while(cpyPtr < cpyEnd)
                {
                    memcpy(cpyPtr + 0, refPtr + 0, 8);
                    memcpy(cpyPtr + 8, refPtr + 8, 8);
                    cpyPtr += wild_cpy_length;
                    refPtr += wild_cpy_length;
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
            auto result = decodeOffWrapper(seqPtr, dctx);
            offset = (uint32_t)result.offset;
            seqPtr += result.seqLen;
            length = *seqPtr++;
        }
        if (LZ3_LIKELY(length <= min(wild_cpy_length - min_match_length, coder == LZ3_entropy_coder::None ? 0xEu : 0x1Fu)))
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
            const uint8_t* refPtr = cpyPtr - offset;
            if (LZ3_UNLIKELY(cpyEnd > dstShortEnd)/*dstEnd - (wild_cpy_length - 1)*/)
            {
                do
                {
                    *cpyPtr++ = *refPtr++;
                }
                while(cpyPtr < cpyEnd);
            }
            else if (offset >= 8)
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
            else if (offset == 1 || offset == 2 || offset == 4)
            {
                uint8_t buffer[8] = { 0 };
                switch (offset)
                {
                case 1:
                    memset(buffer, *refPtr, 8);
                    break;
                case 2:
                    memcpy(buffer, refPtr, 2);
                    memcpy(buffer + 2, refPtr, 2);
                    memcpy(buffer + 4, buffer, 4);
                    break;
                case 4:
                    memcpy(buffer, refPtr, 4);
                    memcpy(buffer + 4, refPtr, 4);
                    break;
                }
                do
                {
                    memcpy(cpyPtr, buffer, 8);
                    cpyPtr += 8;
                }
                while(cpyPtr < cpyEnd);
            }
            else
            {
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
    if (srcSize <= max_block_size)
    {
        LZ3_suffix_array* psa = new LZ3_suffix_array(srcSize);
        psa->cal_suffix_array((const uint8_t*)src, srcSize);
        psa->cal_height((const uint8_t*)src, srcSize);
        dstPos = LZ3_compress_generic<LZ3_entropy_coder::Huff0>(psa, (const uint8_t*)src, (uint8_t*)dst, srcSize);
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
            dstPtr += LZ3_compress_HUF_continue(pcs, srcPtr, dstPtr, (uint32_t)curSize);
            srcPtr += curSize;
        }
        LZ3_freeCStream(pcs);
        dstPos = dstPtr - (uint8_t*)dst;
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
    size_t srcPos;
    if (dstSize < max_block_size)
    {
        srcPos = LZ3_decompress_generic<LZ3_entropy_coder::Huff0>((const uint8_t*)src, (uint8_t*)dst, dstSize);
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
            srcPtr += LZ3_decompress_HUF_continue(pds, srcPtr, dstPtr, (uint32_t)curSize);
            dstPtr += curSize;
        }
        LZ3_freeDStream(pds);
        srcPos = srcPtr - (const uint8_t*)src;
    }
    return (uint32_t)srcPos;
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

template<LZ3_entropy_coder coder>
uint32_t LZ3_compress_continue_generic(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize)
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
    size_t dstPos = LZ3_compress_generic<coder>(&pcs->hsa, pcs->psz, (uint8_t*)dst, srcSize);
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

template<LZ3_entropy_coder coder>
uint32_t LZ3_decompress_continue_generic(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    if (pds->psz + dstSize > pds->sz + sizeof(pds->sz))
    {
        memcpy(pds->sz, pds->psz - max_block_size, max_block_size);
        pds->psz = pds->sz + max_block_size;
    }
    size_t srcPos = LZ3_decompress_generic<coder>((const uint8_t*)src, pds->psz, dstSize);
    memcpy(dst, pds->psz, dstSize);
    pds->psz += dstSize;
    return (uint32_t)srcPos;
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

uint32_t LZ3_compress_HUF_continue(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize)
{
    return LZ3_compress_continue_generic<LZ3_entropy_coder::Huff0>(pcs, src, dst, srcSize);
}

uint32_t LZ3_decompress_HUF_continue(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_continue_generic<LZ3_entropy_coder::Huff0>(pds, src, dst, dstSize);
}
