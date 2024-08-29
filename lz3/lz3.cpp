#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstring>
#include <limits>
#include <memory>
#include <unordered_map>
#include <vector>
#include <iterator>

#define LZ3_LIBRARY
#include "lz3.h"
#include "lz3_internal.h"
#include "zstd/lib/common/bitstream.h"
#include "zstd/lib/common/huf.h"
#include "zstd/lib/common/fse.h"

#if !defined(NDEBUG) && (defined(LZ3_LOG_SA) || defined(LZ3_LOG_SEQ))
#include <sstream>
#include <fstream>
#include <iomanip>
#endif

using namespace std;

/*3 byte variant of LZ4 for textures
* modify LZ4 sequence definition to allow match of 3 byte
* |            msb                           lsb               |
* |     1bit    |     7bit     |     4bit     |      4bit      |
* | offset mode | offset value | match length | literal length |
*/

#define LZ3_MAX_ARRAY_SIZE (LZ3_MAX_BLOCK_SIZE + ((LZ3_HUF_DISTANCE_MAX > LZ3_DISTANCE_MAX) ? LZ3_HUF_DISTANCE_MAX : LZ3_DISTANCE_MAX))

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
        LZ3_match_info{ position, LZ3_MAX_BLOCK_SIZE + 1, 0 }
    {
        prev = psa->rk[position];
        next = psa->rk[position] + 1;
    }

    bool match_next(const LZ3_suffix_array* psa, uint32_t min_length, uint32_t max_distance)
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
            if (position > index && position - index <= max_distance)
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
    uint32_t preOff[3];
    int64_t price;

    LZ3_match_optm() :
        LZ3_match_info{ 0 ,0, 0 }, literal(0), preOff{ 0 }, price(numeric_limits<int64_t>::max())
    {
    }
};

enum LZ3_compress_param
{
    MaxMatchDistance,
    SufficientMatchLength,
    MaxMatchCount,
    MinFurtherOffset,
    RepeatModeThreshold,
    BlockStepTolerance,
    BlockModeThreshold,
    Dim2ModeThreshold,
    UncompressThreshold,
    UncompressIntercept,
    Count
};

static uint32_t default_params[LZ3_CLevel::LZ3_CLevel_Max + 1][LZ3_compress_param::Count] =
{
    { 0x7FFF,  128,  1,   0,  25, 80, 95, 105, 98,  0 },
    { 0x7FFF,  128,  2,   0,  25, 80, 95, 105, 98,  0 }, //CLevel_Min
    { 0x7FFF,  128,  4,   0,  25, 80, 95, 105, 98,  0 },
    { 0x7FFF,  128,  8,   0,  25, 80, 95, 105, 98,  0 }, //CLevel_Fast
    { 0xFFFF,  172,  16,  1,  25, 80, 95, 105, 98,  0 },
    { 0xFFFF,  172,  32,  1,  25, 80, 95, 105, 99,  0 }, //CLevel_Normal
    { 0xFFFF,  172,  64,  2,  25, 80, 95, 105, 99,  0 },
    { 0x17FFF, 256,  128, 4,  25, 80, 95, 105, 99,  0 }, //CLevel_Optimal
    { 0x17FFF, 256,  256, 16, 25, 80, 95, 105, 100, 0 },
    { 0x1FFFE, 384,  512, 64, 25, 80, 95, 105, 100, 0 }, //CLevel_MAX
};

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

#define LZ3_MAX_LL 34u

static constexpr uint16_t ll_base[LZ3_MAX_LL + 1] = {
    0,        1,        2,        3,        4,        5,        6,        7,
    8,        9,        10,       11,       12,       13,       14,       15,
    16,       18,       20,       22,       24,       28,       32,       40,
    48,       64,       0x80,     0x100,    0x200,    0x400,    0x800,    0x1000,
    0x2000,   0x4000,   0x8000
};

static constexpr uint8_t ll_bits[LZ3_MAX_LL + 1] = {
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    1,        1,        1,        1,        2,        2,        3,        3,
    4,        6,        7,        8,        9,        10,       11,       12,
    13,       14,       15
};

static constexpr uint8_t ll_code[] = {
    0,        1,        2,        3,        4,        5,        6,        7,
    8,        9,        10,       11,       12,       13,       14,       15,
    16,       16,       17,       17,       18,       18,       19,       19,
    20,       20,       20,       20,       21,       21,       21,       21,
    22,       22,       22,       22,       22,       22,       22,       22,
    23,       23,       23,       23,       23,       23,       23,       23,
    24,       24,       24,       24,       24,       24,       24,       24,
    24,       24,       24,       24,       24,       24,       24,       24
};

static uint8_t LZ3_ll_code(uint32_t value)
{
    return value > 63 ? (LZ3_HIGH_BIT_32(value) + 19) : ll_code[value];
}

#define LZ3_MAX_ML 51u

static constexpr uint16_t ml_base[LZ3_MAX_ML + 1] = {
    3,        4,        5,        6,        7,        8,        9,        10,
    11,       12,       13,       14,       15,       16,       17,       18,
    19,       20,       21,       22,       23,       24,       25,       26,
    27,       28,       29,       30,       31,       32,       33,       34,
    35,       37,       39,       41,       43,       47,       51,       59,
    67,       83,       99,       0x83,     0x103,    0x203,    0x403,    0x803,
    0x1003,   0x2003,   0x4003,   0x8003
};

static constexpr uint8_t ml_bits[LZ3_MAX_ML + 1] = {
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    1,        1,        1,        1,        2,        2,        3,        3,
    4,        4,        5,        7,        8,        9,       10,        11,
    12,       13,       14,       15
};

static constexpr uint8_t ml_code[] = {
    0,        1,        2,        3,        4,        5,        6,        7,
    8,        9,        10,       11,       12,       13,       14,       15,
    16,       17,       18,       19,       20,       21,       22,       23,
    24,       25,       26,       27,       28,       29,       30,       31,
    32,       32,       33,       33,       34,       34,       35,       35,
    36,       36,       36,       36,       37,       37,       37,       37,
    38,       38,       38,       38,       38,       38,       38,       38,
    39,       39,       39,       39,       39,       39,       39,       39,
    40,       40,       40,       40,       40,       40,       40,       40,
    40,       40,       40,       40,       40,       40,       40,       40,
    41,       41,       41,       41,       41,       41,       41,       41,
    41,       41,       41,       41,       41,       41,       41,       41,
    42,       42,       42,       42,       42,       42,       42,       42,
    42,       42,       42,       42,       42,       42,       42,       42,
    42,       42,       42,       42,       42,       42,       42,       42,
    42,       42,       42,       42,       42,       42,       42,       42
};

static uint8_t LZ3_ml_code(uint32_t value)
{
    value -= min_match_length;
    return value > 127 ? (LZ3_HIGH_BIT_32(value) + 36) : ml_code[value];
}

#define LZ3_MIN_OF 3u

static uint32_t of_base[] = {
    0,        1,        0,
    1,        2,        3,        5,        7,        11,       15,       0x17,
    0x1F,     0x2F,     0x3F,     0x5F,     0x7F,     0xBF,     0xFF,     0x17F,
    0x1FF,    0x2FF,    0x3FF,    0x5FF,    0x7FF,    0xBFF,    0xFFF,    0x17FF,
    0x1FFF,   0x2FFF,   0x3FFF,   0x5FFF,   0x7FFF,   0xBFFF,   0xFFFF,   0x17FFF
};

static uint8_t of_bits[] = {
    0,        1,        3/4,
    0,        0,        1,        1,        2,        2,        3,        3,
    4,        4,        5,        5,        6,        6,        7,        7,
    8,        8,        9,        9,        10,       10,       11,       11,
    12,       12,       13,       13,       14,       14,       15,       15
};

/*dx_base and dx_bits will be generated based on lineSize

static uint32_t dx_base[] = {
    0,        1,        0,
    0,        127,      1,        126,      2,        124,      4,        122,
    6,        118,      10,       114,      14,       106,      22,       98,
    30,       82,       46,       66,       62,       34,
};

static uint8_t dx_bits[] = {
    0,       1,         3/4,
    0,       0,         0,        0,        1,        1,        1,        1,
    2,       2,         2,        2,        3,        3,        3,        3,
    4,       4,         4,        4,        5,        5,
};*/

//dy_base was similar to ll_base
static constexpr uint32_t dy_base[] = {
    0,        1,        0,
    0,        1,        2,        3,        4,        5,        6,        7,
    8,        9,        10,       11,       12,       13,       14,       15,
    16,       18,       20,       22,       24,       28,       32,       40,
    48,       64,       0x80,     0x100,    0x200,    0x400,    0x800,    0x1000,
    0x2000,   0x4000,   0x8000
};

static constexpr uint8_t dy_bits[] = {
    0,        1,        3/4,
    0,        0,        0,        0,        0,        0,        0,        0,
    0,        0,        0,        0,        0,        0,        0,        0,
    1,        1,        1,        1,        2,        2,        3,        3,
    4,        6,        7,        8,        9,        10,       11,       12,
    13,       14,       15
};

static uint8_t LZ3_of_code(uint32_t value)
{
    uint32_t base = value + 1;
    uint8_t hb = LZ3_HIGH_BIT_32(base);
    uint8_t c = (hb - 1) * 2u;
    if (base & (1 << (hb - 1)))
    {
        c += 1;
    }
    return c + LZ3_MIN_OF;
}

static uint8_t LZ3_dx_code(uint32_t value, uint32_t lineSize)
{
    uint32_t base;
    if (value * 2 < lineSize)
    {
        base = value + 2;
    }
    else
    {
        base = lineSize - value + 1;
    }
    uint8_t hb = LZ3_HIGH_BIT_32(base);
    uint8_t c = (hb - 1) * 4u;
    if (base & (1 << (hb - 1)))
    {
        c += (value * 2 < lineSize) ? 2 : 3;
    }
    else
    {
        c += (value * 2 < lineSize) ? 0 : 1;
    }
    return c + LZ3_MIN_OF;
}

static uint8_t LZ3_dy_code(uint32_t value)
{
    return LZ3_ll_code(value) + LZ3_MIN_OF;
}

struct LZ3_encode_of_result
{
    uint8_t code;
    uint8_t bits;
};

const char* LZ3_last_error_name = nullptr;

struct LZ3_CCtx
{
    uint32_t params[LZ3_compress_param::Count];
    vector<LZ3_match_info> matches;
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
            uint32_t of_base[64];
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
            uint32_t of_base[64];
            uint8_t of_bits[64];
            uint8_t of_size;
            BIT_DStream_t bitStr;
            uint32_t preOff[3];
        };
    };
};

static void LZ3_init_params(uint32_t params[LZ3_compress_param::Count], LZ3_CLevel level, LZ3_entropy_coder coder)
{
    copy_n(default_params[level], LZ3_compress_param::Count, params);
    if (coder == LZ3_entropy_coder::None && params[LZ3_compress_param::MaxMatchDistance] > LZ3_DISTANCE_MAX)
    {
        params[LZ3_compress_param::MaxMatchDistance] = LZ3_DISTANCE_MAX;
    }
}

static uint8_t LZ3_gen_of_book(uint32_t* base, uint8_t* bits, LZ3_compress_flag flag, uint32_t blockLog, uint32_t lineSize)
{
    uint8_t i = 0;
    //if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        uint32_t b = 0;
        for (uint8_t l = 0; b < 3; ++l)
        {
            base[i] = b;
            bits[i] = l;
            i++;
            b += 1 << l;
        }
    }
    //if (flag & LZ3_compress_flag::OffsetBlock)
    {
        base[i] = 0;
        bits[i] = (uint8_t)blockLog;
        i++;
    }
    if (flag & LZ3_compress_flag::OffsetTwoDim)
    {
        uint32_t b = 0;
        uint32_t e = lineSize;
        for (uint8_t j = 0; ; ++j)
        {
            uint8_t l = j / 2;
            base[i] = b;
            bits[i] = l;
            i++;
            b += 1 << l;
            /*if (b >= e)
            {
                break;
            }*/
            base[i] = e - (1 << l);
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
        uint32_t b = 1;
        for (uint8_t j = 0; ; ++j)
        {
            uint8_t l = j / 2;
            base[i] = b;
            bits[i] = l;
            i++;
            b += 1 << l;
            if (b > LZ3_HUF_DISTANCE_MAX)
            {
                break;
            }
        }
    }
    return i;
}

static void LZ3_encode_ll(vector<uint8_t>& seq, vector<pair<uint32_t, uint8_t>>& ext, uint32_t value)
{
    uint8_t c = LZ3_ll_code(value);
    seq.push_back(c);
    if (ll_bits[c] > 0)
    {
        uint32_t d = value - ll_base[c];
        ext.emplace_back(d, ll_bits[c]);
    }
}

static void LZ3_encode_ml(vector<uint8_t>& seq, vector<pair<uint32_t, uint8_t>>& ext, uint32_t value)
{
    uint8_t c = LZ3_ml_code(value);
    seq.push_back(c);
    if (ml_bits[c] > 0)
    {
        uint32_t d = value - ml_base[c];
        ext.emplace_back(d, ml_bits[c]);
    }
}

static uint32_t LZ3_encode_of(uint32_t offset, LZ3_encode_of_result results[3], LZ3_compress_flag flag, uint32_t preOff[3], uint32_t blockLog, uint32_t lineSize, uint32_t* dx_base, uint8_t* dx_bits)
{
    uint32_t count = 0;
    if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        if (offset == preOff[0])
        {
            results[count++] = { 0, 0 };
            return count;
        }
        if (offset == preOff[1] || offset == preOff[2])
        {
            results[count++] = { 1, 1 };
            return count;
        }
    }
    if (flag & LZ3_compress_flag::OffsetBlock)
    {
        uint32_t r = offset & ((1 << blockLog) - 1);
        if (r != 0)
        {
            r = (1 << blockLog) - r;
            results[count++] = { 2, (uint8_t)blockLog };
            offset += r;
        }
        offset >>= blockLog;
    }
    if (flag & LZ3_compress_flag::OffsetTwoDim)
    {
        offset -= 1;
        uint32_t x = offset % lineSize;
        uint32_t y = offset / lineSize;
        uint8_t c = LZ3_dx_code(x, lineSize);
        results[count++] = { c, dx_bits[c] };
        assert(y <= numeric_limits<uint16_t>::max());
        uint8_t e = LZ3_dy_code(y);
        results[count++] = { e, dy_bits[e] };
    }
    else
    {
        uint8_t c = LZ3_of_code(offset);
        results[count++] = { c, of_bits[c] };
    }
    return count;
}

static void LZ3_encode_of(vector<uint8_t>& seq, vector<pair<uint32_t, uint8_t>>& ext, uint32_t offset, const LZ3_CCtx& cctx)
{
    if (cctx.flag & LZ3_compress_flag::OffsetRepeat)
    {
        if (offset == cctx.preOff[0])
        {
            seq.push_back(0);
            return;
        }
        if (offset == cctx.preOff[1] || offset == cctx.preOff[2])
        {
            seq.push_back(1);
            ext.emplace_back(offset == cctx.preOff[1] ? 0u : 1u, (uint8_t)1);
            return;
        }
    }
    if (cctx.flag & LZ3_compress_flag::OffsetBlock)
    {
        uint32_t r = offset & ((1 << cctx.blockLog) - 1);
        if (r != 0)
        {
            r = (1 << cctx.blockLog) - r;
            seq.push_back(2);
            ext.emplace_back(r, (uint8_t)cctx.blockLog);
            offset += r;
        }
        offset >>= cctx.blockLog;
    }
    if (cctx.flag & LZ3_compress_flag::OffsetTwoDim)
    {
        offset -= 1;
        uint32_t x = offset % cctx.lineSize;
        uint32_t y = offset / cctx.lineSize;
        uint8_t c = LZ3_dx_code(x, cctx.lineSize);
        seq.push_back(c);
        const uint8_t* dx_bits = cctx.of_bits;
        if (dx_bits[c] > 0)
        {
            const uint32_t* dx_base = cctx.of_base;
            uint32_t d = x - dx_base[c];
            assert((d >> dx_bits[c]) == 0);
            ext.emplace_back(d, dx_bits[c]);
        }
        assert(y <= numeric_limits<uint16_t>::max());
        uint8_t e = LZ3_dy_code(y);
        seq.push_back(e);
        if (dy_bits[e] > 0)
        {
            uint32_t d = y - dy_base[e];
            assert((d >> dy_bits[e]) == 0);
            ext.emplace_back(d, dy_bits[e]);
        }
    }
    else
    {
        uint8_t c = LZ3_of_code(offset);
        seq.push_back(c);
        if (of_bits[c] > 0)
        {
            uint32_t d = offset - of_base[c];
            assert((d >> of_bits[c]) == 0);
            ext.emplace_back(d, of_bits[c]);
        }
    }
}

static void LZ3_encode_of_wrapper(vector<uint8_t>& seq, vector<pair<uint32_t, uint8_t>>& ext, uint32_t offset, LZ3_CCtx& cctx)
{
    LZ3_encode_of(seq, ext, offset, cctx);
    if (cctx.flag & LZ3_compress_flag::OffsetRepeat)
    {
        cctx.preOff[2] = cctx.preOff[1];
        cctx.preOff[1] = cctx.preOff[0];
        cctx.preOff[0] = offset;
    }
}

#if defined(_WIN64)
//windows x64 calling convention only have one 64bit reg for return value
//put offset behind to combine shl 32 & shl blockSize under little endian 
struct LZ3_decode_of_result
{
    size_t seqLen() const
    {
        return rax & 0xFFFFFFFF;
    }

    size_t offset() const
    {
        return rax >> 0x20;
    }

    size_t rax;
};

LZ3_FORCE_INLINE LZ3_decode_of_result LZ3_make_decode_of_result(uint32_t seqLen, uint32_t offset, uint32_t offShl = 0)
{
    return { (((uint64_t)offset) << (32 + offShl)) | seqLen };
}
#else
//use two reg to avoid shifting
struct LZ3_decode_of_result
{
    size_t seqLen() const
    {
        return rax;
    }

    size_t offset() const
    {
        return rdx;
    }

    size_t rax;
    size_t rdx;
};

LZ3_FORCE_INLINE LZ3_decode_of_result LZ3_make_decode_of_result(uint32_t seqLen, uint32_t offset, uint32_t offShl = 0)
{
    return { seqLen, offset << offShl };
}
#endif

template<uint32_t blockLog, uint32_t lineSize, LZ3_compress_flag flag>
LZ3_FORCE_INLINE static LZ3_decode_of_result LZ3_decode_of(const uint8_t* seqPtr, LZ3_DCtx& dctx)
{
    uint32_t c = *seqPtr++;
    if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        if (c == 0)
        {
            return LZ3_make_decode_of_result(1, dctx.preOff[0]);
        }
        if (c == 1)
        {
            return LZ3_make_decode_of_result(1, dctx.preOff[1 + BIT_readBitsFast(&dctx.bitStr, 1)]);
        }
    }
    uint32_t b = blockLog != 0 ? blockLog : dctx.blockLog;
    uint32_t l = lineSize != 0 ? lineSize : dctx.lineSize;
    if (flag & LZ3_compress_flag::OffsetBlock)
    {
        if (blockLog == 0)
            b = dctx.blockLog;
        if (c == 2)
        {
            uint32_t r = (uint32_t)BIT_readBitsFast(&dctx.bitStr, b);
            auto result = LZ3_decode_of<blockLog, lineSize, flag ^ LZ3_compress_flag::OffsetBlock>(seqPtr, dctx);
            return LZ3_make_decode_of_result((uint32_t)result.seqLen() + 1, (uint32_t)result.offset() - r);
        }
    }
    if (flag & LZ3_compress_flag::OffsetTwoDim)
    {
        uint32_t e = *seqPtr++; //extended code record dy
        const uint32_t* dx_base = dctx.of_base;
        uint32_t x = dx_base[c];
        uint32_t y = dy_base[e];
        if (c >= LZ3_MIN_OF + 4)
        {
            const uint8_t* dx_bits = dctx.of_bits;
            x += (uint32_t)BIT_readBitsFast(&dctx.bitStr, dx_bits[c]);
        }
        if (e >= LZ3_MIN_OF + 16)
        {
            y += (uint32_t)BIT_readBitsFast(&dctx.bitStr, dy_bits[e]);
        }
        uint32_t o = x + y * l + 1;
        return LZ3_make_decode_of_result(2, o, b);
    }
    else
    {
        uint32_t o = of_base[c];
        if (c >= LZ3_MIN_OF + 2)
        {
            o += (uint32_t)BIT_readBitsFast(&dctx.bitStr, of_bits[c]);
        }
        return LZ3_make_decode_of_result(1, o, b);
    }
}

template<uint32_t blockLog, uint32_t lineSize, LZ3_compress_flag flag>
static LZ3_decode_of_result LZ3_decode_of_wrapper(const uint8_t* seqPtr, LZ3_DCtx& dctx)
{
    auto result = LZ3_decode_of<blockLog, lineSize, flag>(seqPtr, dctx);
    if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        dctx.preOff[2] = dctx.preOff[1];
        dctx.preOff[1] = dctx.preOff[0];
        dctx.preOff[0] = (uint32_t)result.offset();
    }
    return result;
}

typedef LZ3_decode_of_result(*LZ3_of_decoder)(const uint8_t* seqPtr, LZ3_DCtx& dctx);

static LZ3_of_decoder LZ3_gen_of_decoder(LZ3_compress_flag flag, uint32_t blockLog, uint32_t lineSize)
{
    switch ((uint8_t)flag & 7)
    {
    case 0:
        return &LZ3_decode_of_wrapper<0, 0, LZ3_compress_flag::None>;
    case 1:
        return &LZ3_decode_of_wrapper<0, 0, LZ3_compress_flag::OffsetRepeat>;
    case 2:
        if (blockLog == 2)
            return &LZ3_decode_of_wrapper<2, 0, LZ3_compress_flag::OffsetBlock>;
        if (blockLog == 3)
            return &LZ3_decode_of_wrapper<3, 0, LZ3_compress_flag::OffsetBlock>;
        if (blockLog == 4)
            return &LZ3_decode_of_wrapper<4, 0, LZ3_compress_flag::OffsetBlock>;
        LZ3_UNREACHABLE;
    case 3:
        return &LZ3_decode_of_wrapper<0, 0, LZ3_compress_flag::OffsetRepeat | LZ3_compress_flag::OffsetBlock>;
    case 4:
        return &LZ3_decode_of_wrapper<0, 0, LZ3_compress_flag::OffsetTwoDim>;
    case 5:
        return &LZ3_decode_of_wrapper<0, 0, LZ3_compress_flag::OffsetRepeat | LZ3_compress_flag::OffsetTwoDim>;
    case 6:
        if (blockLog == 3 && lineSize == 64)
            return &LZ3_decode_of_wrapper<3, 64,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 3 && lineSize == 128)
            return &LZ3_decode_of_wrapper<3, 128, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 3 && lineSize == 256)
            return &LZ3_decode_of_wrapper<3, 256, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 3 && lineSize == 512)
            return &LZ3_decode_of_wrapper<3, 512, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 43)
            return &LZ3_decode_of_wrapper<4, 43,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 52)      
            return &LZ3_decode_of_wrapper<4, 52,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 64)      
            return &LZ3_decode_of_wrapper<4, 64,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 86)      
            return &LZ3_decode_of_wrapper<4, 86,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 103)
            return &LZ3_decode_of_wrapper<4, 103, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 128)
            return &LZ3_decode_of_wrapper<4, 128, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 171)
            return &LZ3_decode_of_wrapper<4, 171, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 205)
            return &LZ3_decode_of_wrapper<4, 205, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 256)
            return &LZ3_decode_of_wrapper<4, 256, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 342)
            return &LZ3_decode_of_wrapper<4, 342, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 410)
            return &LZ3_decode_of_wrapper<4, 410, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockLog == 4 && lineSize == 512)
            return &LZ3_decode_of_wrapper<4, 512, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        return &LZ3_decode_of_wrapper<0, 0, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
    default:
        return &LZ3_decode_of_wrapper<0, 0, LZ3_compress_flag::OffsetRepeat | LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
    }
}

static void LZ3_write_stream(uint8_t*& dst, const uint8_t* src, size_t srcSize, LZ3_entropy_coder coder, uint32_t uncompressIntercept, uint32_t uncompressThreshold)
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
    if (dstSize + uncompressIntercept > srcSize * uncompressThreshold / 100)
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

#define LZ3_BIT_COST_ACC 8u
#define LZ3_BIT_COST_MUL (1u << LZ3_BIT_COST_ACC)

LZ3_FORCE_INLINE static uint32_t LZ3_weight(uint32_t freq)
{
    freq += 1;
    uint8_t hb = LZ3_HIGH_BIT_32(freq);
    uint32_t bw = hb * LZ3_BIT_COST_MUL;
    uint32_t fw = (freq << LZ3_BIT_COST_ACC) >> hb;
    return bw + fw;
}

class LZ3_code_hist
{
    uint32_t freq[256];
    uint32_t size;
    uint32_t base;

public:
    LZ3_code_hist() :
        freq{ 0 }, size(0), base(0)
    {
    }

    void inc_stats(uint8_t code, uint32_t inc = 1)
    {
        freq[code] += inc;
        size += inc;
    }

    void eval_base()
    {
        base = LZ3_weight(size);
    }

    uint32_t eval_bits(uint8_t code) const
    {
        return base - LZ3_weight(freq[code]);
    }

    void clear()
    {
        fill_n(freq, 256, 0);
        size = 0;
        base = 0;
    }
};

static LZ3_compress_flag LZ3_detect_compress_flags(LZ3_CCtx& cctx)
{
    LZ3_compress_flag flag = LZ3_compress_flag::None;
    uint32_t total = (uint32_t)cctx.matches.size();
    if (total < 32)
    {
        return flag;
    }
    uint32_t repeat = 0;
    uint32_t preOff[3] = { 0 };
    unordered_map<uint32_t, uint32_t> freq;
    for (uint32_t i = 0; i < total; ++i)
    {
        uint32_t offset = cctx.matches[i].offset;
        if (offset == preOff[0] ||
            offset == preOff[1] ||
            offset == preOff[2])
        {
            repeat++;
        }
        else
        {
            freq[offset]++;
        }
        preOff[2] = preOff[1];
        preOff[1] = preOff[0];
        preOff[0] = offset;
    }
    if (repeat > total * cctx.params[LZ3_compress_param::RepeatModeThreshold] / 100)
    {
        flag = flag | LZ3_compress_flag::OffsetRepeat;
    }
    total -= repeat;
    vector<pair<uint32_t, uint32_t>> hist;
    for (const auto& p : freq)
    {
        if (p.second > 0)
        {
            hist.emplace_back(p.first, p.second);
        }
    }
    stable_sort(hist.begin(), hist.end(), [](const pair<uint32_t, uint32_t>& x, const pair<uint32_t, uint32_t>& y)
    {
        return x.second > y.second;
    });
    //consider only 4(rgb32), 8(etc1), 16(etc2/astc) byte block
    cctx.blockLog = 0;
    uint32_t blockBest = 0;
    uint32_t blockPrev = total;
    for (uint32_t i = 2; i <= 4; ++i)
    {
        uint32_t count = 0;
        for (const pair<uint32_t, uint32_t>& p : hist)
        {
            if (p.first % (1 << i) == 0)
            {
                count += p.second;
            }
        }
        if (count > blockPrev * cctx.params[LZ3_compress_param::BlockStepTolerance] / 100)
        {
            blockBest = count;
            cctx.blockLog = i;
        }
        blockPrev = count;
    }
    if (blockBest > total * cctx.params[LZ3_compress_param::BlockModeThreshold] / 100)
    {
        flag = flag | LZ3_compress_flag::OffsetBlock;
    }
    //ASTC may have NPOT line size
    cctx.lineSize = 0;
    vector<pair<uint8_t, uint32_t>> codeHist;
    LZ3_code_hist noneHist;
    for (const pair<uint32_t, uint32_t>& p : hist)
    {
        uint32_t offset = p.first;
        uint32_t count = p.second;
        uint8_t code = LZ3_of_code(offset);
        codeHist.emplace_back(code, count);
        noneHist.inc_stats(code, count);
    }
    noneHist.eval_base();
    uint64_t nonePrice = 0;
    for (const pair<uint32_t, uint32_t>& p : codeHist)
    {
        nonePrice += (noneHist.eval_bits(p.first) + of_bits[p.first] * LZ3_BIT_COST_MUL) * p.second;
    }
    for (uint32_t i = 0; i < hist.size() && i < 8u; ++i)
    {
        uint32_t divisor = hist[i].first;
        if (divisor % (1 << cctx.blockLog) != 0)
        {
            continue;
        }
        divisor >>= cctx.blockLog;
        if (divisor < 16 || divisor > numeric_limits<uint16_t>::max())
        {
            continue;
        }
        codeHist.clear();
        LZ3_code_hist dim2Hist;
        for (const auto& p : hist)
        {
            uint32_t offset = p.first;
            uint32_t count = p.second;
            uint32_t r = offset & ((1 << cctx.blockLog) - 1);
            if (r != 0)
            {
                dim2Hist.inc_stats(2, count);
                offset += (1 << cctx.blockLog) - r;
            }
            offset >>= cctx.blockLog;
            offset -= 1;
            uint32_t x = offset % divisor;
            uint32_t y = offset / divisor;
            if (y > numeric_limits<uint16_t>::max())
            {
                divisor = 0;
                break;
            }
            uint8_t code;
            code = LZ3_dx_code(x, divisor);
            codeHist.emplace_back(code, count);
            dim2Hist.inc_stats(code, count);
            code = LZ3_dy_code(y);
            codeHist.emplace_back(code, count);
            dim2Hist.inc_stats(code, count);
        }
        if (divisor ==0)
        {
            continue;
        }
        dim2Hist.eval_base();
        uint64_t dim2Price = 0;
        for (uint32_t j = 0; j < codeHist.size(); j += 2)
        {
            uint8_t* dx_bits = cctx.of_bits;
            auto& x = codeHist[j];
            dim2Price += (dim2Hist.eval_bits(x.first) + dx_bits[x.first] * LZ3_BIT_COST_MUL) * x.second;
            auto& y = codeHist[j + 1];
            dim2Price += (dim2Hist.eval_bits(y.first) + dy_bits[y.first] * LZ3_BIT_COST_MUL) * y.second;
        }
        if (dim2Price < nonePrice * cctx.params[LZ3_compress_param::Dim2ModeThreshold] / 100)
        {
            cctx.lineSize = divisor;
            break;
        }
    }
    if (cctx.lineSize != 0 && cctx.blockLog != 0)
    {
        flag = flag | LZ3_compress_flag::OffsetBlock;
    }
    if (cctx.lineSize != 0)
    {
        flag = flag | LZ3_compress_flag::OffsetTwoDim;
    }
    return flag;
}

template<
    typename LLenPrice, typename MLenPrice, typename MOffPrice, typename LRawPrice,
    typename LLenStats, typename MLenStats, typename MOffStats>
static vector<LZ3_match_info> LZ3_compress_opt(
    const LZ3_suffix_array* psa, const uint8_t* src, size_t srcSize,
    uint32_t max_distance, uint32_t sufficient_length, uint32_t match_count, uint32_t further_offset,
    LLenPrice lLenPrice, MLenPrice mLenPrice, MOffPrice mOffPrice, LRawPrice lRawPrice,
    LLenStats lLenStats, MLenStats mLenStats, MOffStats mOffStats)
{
    uint32_t hisSize = psa->n - (uint32_t)srcSize;
    uint32_t srcPos = 0;
    vector<LZ3_match_info> matches;
    vector<LZ3_match_optm> optimal;
    vector<LZ3_match_optm> reverse;
    for (uint32_t i = 0; i < srcSize;)
    {
        LZ3_match_iter match(psa, i + hisSize);
        if (match.match_next(psa, min_match_length, max_distance))
        {
            optimal.clear();
            uint32_t lastPos = match.length;
            LZ3_match_optm lastMatch;
            if (match.length > sufficient_length)
            {
                lastMatch.position = match.position;
                lastMatch.length = match.length;
                lastMatch.offset = match.offset;
                lastMatch.literal = match.position - srcPos;
                goto sufficient_short_path;
            }
            optimal.resize(lastPos + 1);
            {
                /* initialize optimal[0] */
                uint32_t lLen = match.position - srcPos;
                optimal[0].literal = lLen;
                for (uint32_t p = 0; p < 3 && p < matches.size(); ++p)
                {
                    optimal[0].preOff[p] = matches[matches.size() - 1 - p].offset;
                }
                optimal[0].price = lLenPrice(lLen);
                /* Set prices for first matches */
                int64_t llp = optimal[0].price + lLenPrice(0);
                for (uint32_t count = 0; count < match_count; ++count)
                {
                    uint32_t mop = mOffPrice(match.offset, optimal[0].preOff);
                    if (mop == numeric_limits<uint32_t>::max())
                    {
                        continue;
                    }
                    for (uint32_t k = match.length; k >= min_match_length; --k)
                    {
                        uint32_t mlp = mLenPrice(k);
                        int64_t price = llp + mlp + mop;
                        if (price < optimal[k].price)
                        {
                            optimal[k].position = match.position;
                            optimal[k].length = k;
                            optimal[k].offset = match.offset;
                            optimal[k].literal = lLen;
                            optimal[k].preOff[2] = optimal[0].preOff[1];
                            optimal[k].preOff[1] = optimal[0].preOff[0];
                            optimal[k].preOff[0] = match.offset;
                            optimal[k].price = price;
                        }
                    }
                    if (!match.match_next(psa, min_match_length, max_distance))
                    {
                        break;
                    }
                }
            }
            for (uint32_t j = 1; j <= lastPos; ++j)
            {
                {
                    /* Fix current position with one literal if cheaper */
                    uint32_t lLen = optimal[j - 1].length == 0 ? optimal[j - 1].literal + 1 : 1;
                    int64_t price = optimal[j - 1].price;
                    price += lRawPrice(src[i + j - 1]);
                    price += lLenPrice(lLen);
                    price -= lLenPrice(lLen - 1);
                    if (price < optimal[j].price)
                    {
                        optimal[j].position = 0;
                        optimal[j].length = 0;
                        optimal[j].offset = 0;
                        optimal[j].literal = lLen;
                        optimal[j].preOff[2] = optimal[j - 1].preOff[2];
                        optimal[j].preOff[1] = optimal[j - 1].preOff[1];
                        optimal[j].preOff[0] = optimal[j - 1].preOff[0];
                        optimal[j].price = price;
                    }
                }
                if (j < lastPos)
                {
                    /* Set prices using further matches found */
                    uint32_t lLen = optimal[j].length == 0 ? optimal[j].literal : 0;
                    uint32_t mopBest = numeric_limits<uint32_t>::max();
                    uint32_t furtherLength = min_match_length;
                    if (j + furtherLength + further_offset < lastPos + 1)
                    {
                        furtherLength = lastPos + 1 - j - further_offset;
                    }
                    while (j + furtherLength <= lastPos && optimal[j].price >= optimal[j + furtherLength].price)
                    {
                        furtherLength++;
                    }
                    int64_t llp = optimal[j].price + lLenPrice(0);
                    LZ3_match_iter furtherMatch(psa, i + hisSize + j);
                    for (uint32_t furtherCount = 0; furtherCount < match_count; ++furtherCount)
                    {
                        if (!furtherMatch.match_next(psa, furtherLength, max_distance))
                        {
                            break;
                        }
                        if (j + furtherMatch.length > lastPos)
                        {
                            lastPos = j + furtherMatch.length;
                            if (furtherMatch.length > sufficient_length)
                            {
                                lastMatch.position = furtherMatch.position;
                                lastMatch.offset = furtherMatch.offset;
                                lastMatch.length = furtherMatch.length;
                                lastMatch.literal = lLen;
                                goto sufficient_short_path;
                            }
                            optimal.resize(lastPos + 1);
                        }
                        uint32_t mop = mOffPrice(furtherMatch.offset, optimal[j].preOff);
                        if (mop == numeric_limits<uint32_t>::max() || mop >= mopBest)
                        {
                            continue;
                        }
                        mopBest = mop;
                        for (uint32_t k = furtherMatch.length; k >= min_match_length; --k)
                        {
                            uint32_t mlp = mLenPrice(k);
                            int64_t price = llp + mlp + mop;
                            if (price < optimal[j + k].price)
                            {
                                optimal[j + k].position = furtherMatch.position;
                                optimal[j + k].length = k;
                                optimal[j + k].offset = furtherMatch.offset;
                                optimal[j + k].literal = lLen;
                                optimal[j + k].preOff[2] = optimal[j].preOff[1];
                                optimal[j + k].preOff[1] = optimal[j].preOff[0];
                                optimal[j + k].preOff[0] = furtherMatch.offset;
                                optimal[j + k].price = price;
                            }
                        }
                    }
                }
            }
            lastMatch = optimal[lastPos];
        sufficient_short_path:
            reverse.clear();
            for (uint32_t j = lastPos;;)
            {
                if (lastMatch.length >= min_match_length)
                {
                    reverse.push_back(lastMatch);
                }
                uint32_t back = lastMatch.literal + lastMatch.length;
                assert(back > 0);
                if (j <= back)
                {
                    break;
                }
                j -= back;
                lastMatch = optimal[j];
            }
            for (auto m = reverse.rbegin(); m != reverse.rend(); ++m)
            {
                srcPos += m->literal;
                uint32_t preOff[3] = { 0 };
                for (uint32_t p = 0; p < 3 && p < matches.size(); ++p)
                {
                    preOff[p] = matches[matches.size() - 1 - p].offset;
                }
                matches.push_back({srcPos , m->length, m->offset });
                lLenStats(m->literal);
                mLenStats(m->length);
                mOffStats(m->offset, preOff);
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
static size_t LZ3_compress_generic(const uint8_t* src, uint8_t* dst, size_t srcSize, const uint32_t* params, LZ3_suffix_array* hsa, LZ3_suffix_array* tsa)
{
    LZ3_CCtx cctx;
	const LZ3_suffix_array* psa;
    tsa->n = (uint32_t)srcSize;
	tsa->cal_suffix_array(src, (uint32_t)srcSize);
	tsa->cal_height(src, (uint32_t)srcSize);
	uint32_t maxDistance = params[LZ3_compress_param::MaxMatchDistance];
	if (hsa != nullptr)
	{
        if (hsa->n > maxDistance)
        {
            hsa->popn_suffix(hsa->n - maxDistance);
        }
        hsa->push_suffix(src - hsa->n, tsa);
		psa = hsa;
	}
	else
	{
		psa = tsa;
	}
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
    uint32_t hisSize = psa->n - (uint32_t)srcSize;
    uint32_t srcPos = 0;
    if (coder == LZ3_entropy_coder::None)
    {
        auto lRawPrice = [](uint32_t v) { return 8 * LZ3_BIT_COST_MUL; };
        auto lLenPrice = [](uint32_t v)
        {
            if (v < 15)
            {
                return 4u  * LZ3_BIT_COST_MUL;
            }
            else
            {
                return 12u * LZ3_BIT_COST_MUL + (v - 15u) / 0xFFu * 8u * LZ3_BIT_COST_MUL;
            }
        };
        auto mLenPrice = [](uint32_t v)
        {
            v -= 3;
            if (v < 15)
            {
                return 4u  * LZ3_BIT_COST_MUL;
            }
            else
            {
                return 12u * LZ3_BIT_COST_MUL + (v - 15u) / 0xFFu * 8u * LZ3_BIT_COST_MUL;
            }
        };
        unordered_map<uint32_t, uint32_t> freq;
        auto mOffCluster = [&freq](uint32_t v, uint32_t p[3])
        {
            auto o = freq.find(v);
            if (o != freq.end())
            {
                return 16u * LZ3_BIT_COST_MUL / (o->second + 1u) + 8u * LZ3_BIT_COST_MUL - 1u/*making appeared offset little cheaper*/;
            }
            else
            {
                return 16u * LZ3_BIT_COST_MUL;
            }
        };
        auto nLenStats = [](uint32_t) {};
        auto mOffStats = [&freq](uint32_t v, uint32_t p[3]) { freq[v]++; };
        LZ3_init_params(cctx.params, LZ3_CLevel_Min, coder);
        cctx.matches = LZ3_compress_opt(psa, src, srcSize,
            cctx.params[LZ3_compress_param::MaxMatchDistance],
            cctx.params[LZ3_compress_param::SufficientMatchLength],
            cctx.params[LZ3_compress_param::MaxMatchCount],
            cctx.params[LZ3_compress_param::MinFurtherOffset],
            lLenPrice, mLenPrice, mOffCluster, lRawPrice,
            nLenStats, nLenStats, mOffStats);
        copy_n(params, LZ3_compress_param::Count, cctx.params);
        vector<uint32_t> dict;
        for (auto i = freq.begin(); i != freq.end();)
        {
            if (i->second >= sizeof(uint16_t)/*sizeof mode1 offset desc*/)
            {
                dict.push_back(i->first);
                ++i;
            }
            else
            {
                i = freq.erase(i);
            }
        }
        stable_sort(dict.begin(), dict.end(), [&freq](uint32_t x, uint32_t y)
        {
            return freq[x] != freq[y] ? freq[x] > freq[y] : x < y;
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
                freq.erase(offset);
            }
        }
        auto mOffPrice = [&freq](uint32_t v, uint32_t p[3])
        {
            auto o = freq.find(v);
            if (o != freq.end())
            {
                return 8u  * LZ3_BIT_COST_MUL;
            }
            else
            {
                return 16u * LZ3_BIT_COST_MUL;
            }
        };
        auto nOffStats = [](uint32_t, uint32_t[3]) {};
        cctx.matches = LZ3_compress_opt(psa, src, srcSize,
            cctx.params[LZ3_compress_param::MaxMatchDistance],
            cctx.params[LZ3_compress_param::SufficientMatchLength],
            cctx.params[LZ3_compress_param::MaxMatchCount],
            cctx.params[LZ3_compress_param::MinFurtherOffset],
            lLenPrice, mLenPrice, mOffPrice, lRawPrice,
            nLenStats, nLenStats, nOffStats);
    }
    else
    {
        //init 1st pass code hist
        LZ3_code_hist lRawHist;
        for (uint32_t i = 0; i < srcSize;)
        {
            LZ3_match_iter match(psa, i + hisSize);
            if (match.match_next(psa, min_match_length, maxDistance))
            {
                uint32_t lastPos = match.length;
                for (uint32_t j = lastPos - min_match_length + 1; j < lastPos; ++j)
                {
                    LZ3_match_iter furtherMatch(psa, i + j);
                    if (furtherMatch.match_next(psa, min_match_length, maxDistance))
                    {
                        lastPos = j + furtherMatch.length;
                        j = lastPos - min_match_length + 1;
                    }
                }
                i += lastPos;
            }
            else
            {
                lRawHist.inc_stats(src[i]);
                ++i;
            }
        }
        LZ3_code_hist lLenHist;
        static constexpr uint32_t baseLLFreqs[LZ3_MAX_LL + 1] = {
            4, 2, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1
        };
        for (uint8_t i = 0; i <= LZ3_MAX_LL; ++i)
        {
            lLenHist.inc_stats(i, baseLLFreqs[i]);
        }
        LZ3_code_hist mLenHist;
        for (uint8_t i = 0; i <= LZ3_MAX_ML; ++i)
        {
            mLenHist.inc_stats(i);
        }
        cctx.of_size = LZ3_gen_of_book(cctx.of_base, cctx.of_bits, LZ3_compress_flag::OffsetRepeat, 0, 0);
        LZ3_code_hist mOffHist;
        for (uint8_t i = 0; i < cctx.of_size; ++i)
        {
            mOffHist.inc_stats(i);
        }
        lRawHist.eval_base();
        lLenHist.eval_base();
        mLenHist.eval_base();
        mOffHist.eval_base();
        auto lRawPrice = [&lRawHist](uint8_t v)
        { 
            return lRawHist.eval_bits(v);
        };
        auto lLenPrice = [&lLenHist](uint32_t v)
        {
            uint8_t c = LZ3_ll_code(v);
            return lLenHist.eval_bits(c) + ll_bits[c] * LZ3_BIT_COST_MUL;
        };
        auto mLenPrice = [&mLenHist](uint32_t v)
        {
            uint8_t c = LZ3_ml_code(v);
            return mLenHist.eval_bits(c) + ml_bits[c] * LZ3_BIT_COST_MUL;
        };
        auto mOffPrice1st = [&mOffHist, &cctx](uint32_t offset, uint32_t preOff[3])
        {
            LZ3_encode_of_result results[3];
            uint32_t count = LZ3_encode_of(offset, results, LZ3_compress_flag::OffsetRepeat, preOff, 0, 0, cctx.of_base, cctx.of_bits);
            assert(count == 1);
            return mOffHist.eval_bits(results[0].code) + results[0].bits * LZ3_BIT_COST_MUL;
        };
        auto lLenStats = [&lLenHist](uint32_t v)
        { 
            lLenHist.inc_stats(LZ3_ll_code(v));
            lLenHist.eval_base();
        };
        auto mLenStats = [&mLenHist](uint32_t v)
        { 
            mLenHist.inc_stats(LZ3_ml_code(v));
            mLenHist.eval_base();
        };
        auto mOffStats1st = [&mOffHist, &cctx](uint32_t offset, uint32_t preOff[3])
        {
            LZ3_encode_of_result results[3];
            uint32_t count = LZ3_encode_of(offset, results, LZ3_compress_flag::OffsetRepeat, preOff, 0, 0, cctx.of_base, cctx.of_bits);
            assert(count == 1);
            mOffHist.inc_stats(results[0].code);
            mOffHist.eval_base();
        };
        LZ3_init_params(cctx.params, LZ3_CLevel_Min, coder);
        cctx.matches = LZ3_compress_opt(psa, src, srcSize,
            cctx.params[LZ3_compress_param::MaxMatchDistance],
            cctx.params[LZ3_compress_param::SufficientMatchLength],
            cctx.params[LZ3_compress_param::MaxMatchCount],
            cctx.params[LZ3_compress_param::MinFurtherOffset],
            lLenPrice, mLenPrice, mOffPrice1st, lRawPrice,
            lLenStats, mLenStats, mOffStats1st);
        copy_n(params, LZ3_compress_param::Count, cctx.params);
        //calc 2nd pass code hist
        cctx.flag = LZ3_detect_compress_flags(cctx);
        cctx.of_size = LZ3_gen_of_book(cctx.of_base, cctx.of_bits, cctx.flag, cctx.blockLog, cctx.lineSize);
        fill_n(cctx.preOff, 3, 0);
        lRawHist.clear();
        mOffHist.clear();
        srcPos = 0;
        for (const LZ3_match_info& match : cctx.matches)
        {
            uint32_t position = match.position - hisSize;
            for (uint32_t i = srcPos; i < position; ++i)
            {
                lRawHist.inc_stats(src[i]);
            }
            uint32_t offset = match.offset;
            LZ3_encode_of_result results[3];
            uint32_t count = LZ3_encode_of(offset, results, cctx.flag, cctx.preOff, cctx.blockLog, cctx.lineSize, cctx.of_base, cctx.of_bits);
            assert(count != 0);
            for (uint32_t i = 0; i < count; ++i)
            {
                mOffHist.inc_stats(results[i].code);
            }
            cctx.preOff[2] = cctx.preOff[1];
            cctx.preOff[1] = cctx.preOff[0];
            cctx.preOff[0] = offset;
            srcPos = position + match.length;
        }
        {
            for (uint32_t i = srcPos; i < srcSize; ++i)
            {
                lRawHist.inc_stats(src[i]);
            }
        }
        lRawHist.eval_base();
        mOffHist.eval_base();
        auto mOffPrice2nd = [&mOffHist, &cctx](uint32_t offset, uint32_t preOff[3])
        {
            LZ3_encode_of_result results[3];
            uint32_t count = LZ3_encode_of(offset, results, cctx.flag, preOff, cctx.blockLog, cctx.lineSize, cctx.of_base, cctx.of_bits);
            assert(count != 0);
            uint32_t bits = 0;
            for (uint32_t i = 0; i < count; ++i)
            {
                bits += mOffHist.eval_bits(results[i].code) + results[i].bits * LZ3_BIT_COST_MUL;
            }
            return bits;
        };
        auto mOffStats2nd = [&mOffHist, &cctx](uint32_t offset, uint32_t preOff[3])
        {
            LZ3_encode_of_result results[3];
            uint32_t count = LZ3_encode_of(offset, results, cctx.flag, preOff, cctx.blockLog, cctx.lineSize, cctx.of_base, cctx.of_bits);
            assert(count != 0);
            for (uint32_t i = 0; i < count; ++i)
            {
                mOffHist.inc_stats(results[i].code);
            }
            mOffHist.eval_base();
        };
        cctx.matches = LZ3_compress_opt(psa, src, srcSize,
            cctx.params[LZ3_compress_param::MaxMatchDistance],
            cctx.params[LZ3_compress_param::SufficientMatchLength],
            cctx.params[LZ3_compress_param::MaxMatchCount],
            cctx.params[LZ3_compress_param::MinFurtherOffset],
            lLenPrice, mLenPrice, mOffPrice2nd, lRawPrice,
            lLenStats, mLenStats, mOffStats2nd);
    }
#if !defined(NDEBUG) && defined(LZ3_LOG_SEQ)
    static uint32_t ci;
    if (hisSize == 0)
    {
        ci = 0;
    }
    stringstream css;
    css << "LZ3_compress." << ci++ << ".csv";
    ofstream cfs(css.str());
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
            LZ3_encode_ll(lls, ext, literal);
            srcPos += literal;
            LZ3_encode_of_wrapper(ofs, ext, offset, cctx);
            LZ3_encode_ml(mls, ext, length);
            srcPos += length;
        }
        if (srcSize > srcPos)
        {
            uint32_t literal = (uint32_t)(srcSize - srcPos);
            LZ3_encode_ll(lls, ext, literal);
            copy(&src[srcPos], &src[srcSize], back_inserter(lit));
        }
        uint32_t uci = cctx.params[LZ3_compress_param::UncompressIntercept];
        uint32_t uct = cctx.params[LZ3_compress_param::UncompressThreshold];
        LZ3_write_stream(dstPtr, lit.data(), (uint32_t)lit.size(), LZ3_entropy_coder::Huff0, uci, uct);
        LZ3_write_stream(dstPtr, lls.data(), (uint32_t)lls.size(), coder, uci, uct);
        LZ3_write_stream(dstPtr, ofs.data(), (uint32_t)ofs.size(), coder, uci, uct);
        LZ3_write_stream(dstPtr, mls.data(), (uint32_t)mls.size(), coder, uci, uct);
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

static constexpr uint32_t wild_copy_length = 16;

template<LZ3_entropy_coder coder, LZ3_history_pos hisPos>
static size_t LZ3_decompress_generic(const uint8_t* src, uint8_t* dst, size_t dstSize, size_t preSize, const uint8_t* ext, size_t extSize)
{
#if !defined(NDEBUG) && defined(LZ3_LOG_SEQ)
    static uint32_t di;
    if (preSize == 0)
    {
        di = 0;
    }
    stringstream dss;
    dss << "LZ3_decompress." << di++ << ".csv";
    ofstream dfs(dss.str());
    dfs << ",Literal,Match,Offset" << endl;
#endif
    const uint8_t* srcPtr = src;

    LZ3_DCtx dctx;
    LZ3_compress_flag flag = LZ3_compress_flag::None;
    LZ3_of_decoder decodeOfWrapper = nullptr;
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
        dctx.of_size = LZ3_gen_of_book(dctx.of_base, dctx.of_bits, flag, dctx.blockLog, dctx.lineSize);
        decodeOfWrapper = LZ3_gen_of_decoder(flag, dctx.blockLog, dctx.lineSize);
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
    uint8_t* dstPtr = dst;
    uint8_t* dstEnd = dstPtr + dstSize;
    uint8_t* dstShortEnd = dstEnd - wild_copy_length;
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
            auto result = decodeOfWrapper(ofsPtr, dctx);
            offset = (uint32_t)result.offset();
            ofsPtr += result.seqLen();
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

uint32_t LZ3_compress(const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level)
{
    uint32_t dstPos;
    if (srcSize <= LZ3_MAX_BLOCK_SIZE)
    {
        uint32_t params[LZ3_compress_param::Count];
        LZ3_init_params(params, level, LZ3_entropy_coder::None);
        LZ3_suffix_array* psa = new LZ3_suffix_array(srcSize);
        dstPos = (uint32_t)LZ3_compress_generic<LZ3_entropy_coder::None>((const uint8_t*)src, (uint8_t*)dst, srcSize, params, nullptr, psa);
        delete psa;
    }
    else
    {
        LZ3_CStream* pcs = LZ3_createCStream();
        dstPos = LZ3_compress_continue(pcs, src, dst, srcSize, level);
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

uint32_t LZ3_compress_HUF(const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level)
{
    uint32_t dstPos;
    if (srcSize <= LZ3_MAX_BLOCK_SIZE)
    {
        uint32_t params[LZ3_compress_param::Count];
        LZ3_init_params(params, level, LZ3_entropy_coder::Huff0);
        LZ3_suffix_array* psa = new LZ3_suffix_array(srcSize);
        dstPos = (uint32_t)LZ3_compress_generic<LZ3_entropy_coder::Huff0>((const uint8_t*)src, (uint8_t*)dst, srcSize, params, nullptr, psa);
        delete psa;
    }
    else
    {
        LZ3_CStream* pcs = LZ3_createCStream();
        dstPos = LZ3_compress_HUF_continue(pcs, src, dst, srcSize, level);
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
uint32_t LZ3_compress_continue_generic(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level)
{
    const uint8_t* srcPtr = (const uint8_t*)src;
    const uint8_t* srcEnd = srcPtr + srcSize;
    uint8_t* dstPtr = (uint8_t*)dst;
    while (srcPtr < srcEnd)
    {
        uint32_t curSize = min((uint32_t)(srcEnd - srcPtr), LZ3_MAX_BLOCK_SIZE);
        uint32_t params[LZ3_compress_param::Count];
        LZ3_init_params(params, level, coder);
        uint32_t maxDistance = params[LZ3_compress_param::MaxMatchDistance];
        if (pcs->psz + curSize > pcs->sz + sizeof(pcs->sz))
        {
            memcpy(pcs->sz, pcs->psz - maxDistance, maxDistance);
            pcs->psz = pcs->sz + maxDistance;
        }
        memcpy(pcs->psz, srcPtr, curSize);
        srcPtr += curSize;
        dstPtr += LZ3_compress_generic<coder>(pcs->psz, dstPtr, curSize, params, &pcs->hsa, &pcs->tsa);
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
        uint32_t max_distance = coder == LZ3_entropy_coder::None ? LZ3_DISTANCE_MAX : LZ3_HUF_DISTANCE_MAX;
        if (pds->psz + curSize > pds->sz + sizeof(pds->sz))
        {
            memcpy(pds->sz, pds->psz - max_distance, max_distance);
            pds->psz = pds->sz + max_distance;
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
        uint32_t max_distance = coder == LZ3_entropy_coder::None ? LZ3_DISTANCE_MAX : LZ3_HUF_DISTANCE_MAX;
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
        else if (pds->preSize >= max_distance || pds->extSize == 0)
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

uint32_t LZ3_compress_continue(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level)
{
    return LZ3_compress_continue_generic<LZ3_entropy_coder::None>(pcs, src, dst, srcSize, level);
}

uint32_t LZ3_decompress_continue(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_continue_generic<LZ3_entropy_coder::None>(pds, src, dst, dstSize);
}

uint32_t LZ3_decompress_fast_continue(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_fast_continue_generic<LZ3_entropy_coder::None>(pds, src, dst, dstSize);
}

uint32_t LZ3_compress_HUF_continue(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level)
{
    return LZ3_compress_continue_generic<LZ3_entropy_coder::Huff0>(pcs, src, dst, srcSize, level);
}

uint32_t LZ3_decompress_HUF_continue(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_continue_generic<LZ3_entropy_coder::Huff0>(pds, src, dst, dstSize);
}

uint32_t LZ3_decompress_HUF_fast_continue(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_fast_continue_generic<LZ3_entropy_coder::Huff0>(pds, src, dst, dstSize);
}
