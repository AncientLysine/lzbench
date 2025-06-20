#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstring>
#include <limits>
#include <memory>
#include <vector>
#include <list>
#include <unordered_map>
#include <iterator>

#define LZ3_LIBRARY
#include "lz3.h"
#include "lz3_internal.h"
#include "zstd/lib/common/bitstream.h"
#define HUF_STATIC_LINKING_ONLY
#include "zstd/lib/common/huf.h"
#define FSE_STATIC_LINKING_ONLY
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
    
    explicit LZ3_suffix_array(uint32_t l = 0)
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
    OffRepeatModeThreshold,
    OffRepeatModeIntercept,
    OffBlockModeThreshold,
    OffBlockModeIntercept,
    OffDim2ModeThreshold,
    OffDim2ModeIntercept,
    LitBlockModeThreshold,
    LitBlockModeIntercept,
    LitPredictModeThreshold,
    LitPredictModeIntercept,
    LitUncompressThreshold,
    LitUncompressIntercept,
    SeqUncompressThreshold,
    SeqUncompressIntercept,
    Count
};

static uint32_t default_params[LZ3_CLevel::LZ3_CLevel_Max + 1][LZ3_compress_param::Count] =
{
    { 0x7FFF,  128,  1,   0,  100, 0, 100, 0, 105, 0, 100, 0, 100, 0, 98,  0, 98,  0 },
    { 0x7FFF,  128,  2,   0,  100, 0, 100, 0, 105, 0, 100, 0, 100, 0, 98,  0, 98,  0 }, //CLevel_Min
    { 0x7FFF,  128,  4,   0,  100, 0, 100, 0, 105, 0, 100, 0, 100, 0, 98,  0, 98,  0 },
    { 0x7FFF,  128,  8,   0,  100, 0, 100, 0, 105, 0, 100, 0, 100, 0, 98,  0, 98,  0 }, //CLevel_Fast
    { 0xFFFF,  172,  16,  1,  100, 0, 100, 0, 105, 0, 100, 0, 100, 0, 98,  0, 98,  0 },
    { 0xFFFF,  172,  32,  1,  100, 0, 100, 0, 105, 0, 100, 0, 100, 0, 99,  0, 99,  0 }, //CLevel_Normal
    { 0xFFFF,  172,  64,  2,  100, 0, 100, 0, 105, 0, 100, 0, 100, 0, 99,  0, 99,  0 },
    { 0x17FFF, 256,  128, 4,  100, 0, 100, 0, 105, 0, 100, 0, 100, 0, 99,  0, 99,  0 }, //CLevel_Optimal
    { 0x17FFF, 256,  256, 16, 100, 0, 100, 0, 105, 0, 100, 0, 100, 0, 100, 0, 100, 0 },
    { 0x1FFFE, 384,  512, 64, 100, 0, 100, 0, 105, 0, 100, 0, 100, 0, 100, 0, 100, 0 }, //CLevel_MAX
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
    OffsetRepeat   = 1,
    OffsetBlock    = 2,
    OffsetTwoDim   = 4,
    LiteralBlock   = 8,
    LiteralPredict = 16,
};

enum class LZ3_stream_flag : uint8_t
{
    None,
    EndOfStream = 1,
    RawBytes    = 2,
    BoundedBits = 4,
    RunLength   = 8,
    Huff0       = 16,
    FSE         = 32,
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
    return static_cast<LZ3_compress_flag>(static_cast<uint8_t>(lhs) & (~static_cast<uint8_t>(rhs)));
}

LZ3_FORCE_INLINE static constexpr bool operator&(LZ3_compress_flag lhs, LZ3_compress_flag rhs) 
{
    return (static_cast<uint8_t>(lhs) & static_cast<uint8_t>(rhs)) > 0;
}

struct LZ3_block_stream
{
    union
    {
        struct
        {
            uint16_t position;
            uint16_t head;
            uint16_t next;
            uint16_t length;
        };
        uint64_t packed;
    };
};

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
    return value > 63 ? (uint8_t)(LZ3_high_bit_32(value) + 19) : ll_code[value];
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
    return value > 127 ? (uint8_t)(LZ3_high_bit_32(value) + 36) : ml_code[value];
}

#define LZ3_MIN_OF 3u
#define LZ3_MAX_OF 42u

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
    uint8_t hb = (uint8_t)LZ3_high_bit_32(base);
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
    uint8_t hb = (uint8_t)LZ3_high_bit_32(base);
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

const char* LZ3_last_error_name = nullptr;

struct LZ3_CCtx
{
    uint32_t params[LZ3_compress_param::Count];
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
            uint32_t blockSize;
            uint32_t blockLog;
            uint32_t lineSize;
            uint32_t of_base[64];
            uint8_t of_bits[64];
            uint8_t of_size;
            uint32_t preOff[3];
            uint32_t blockLayout;
            uint32_t predictMask;
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
            LZ3_compress_flag flag;
            uint32_t blockSize;
            uint32_t blockLog;
            uint32_t lineSize;
            uint32_t of_base[64];
            uint8_t of_bits[64];
            uint8_t of_size;
            BIT_DStream_t bitStr;
            uint32_t preOff[3];
            LZ3_block_stream blockStr[16];
            uint32_t predictMask;
            uint32_t predictDis;
            uint8_t* predictSta;
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

template<typename Output>
LZ3_FORCE_INLINE static void LZ3_encode_of(Output out, uint32_t offset, LZ3_compress_flag flag, uint32_t preOff[3], uint32_t blockSize, uint32_t blockLog, uint32_t lineSize, uint32_t* dx_base, uint8_t* dx_bits)
{
    if (flag & LZ3_compress_flag::OffsetRepeat)
    {
        if (offset == preOff[0])
        {
            out(0, 0, 0);
            return;
        }
        if (offset == preOff[1] || offset == preOff[2])
        {
            out(1, 1, offset == preOff[1] ? 0 : 1);
            return;
        }
    }
    if (flag & LZ3_compress_flag::OffsetBlock)
    {
        if (blockSize == 0)
        {
            assert(blockSize != 0);
            LZ3_UNREACHABLE;
        }
        uint32_t r = offset % blockSize;
        if (r != 0)
        {
            r = blockSize - r;
            out(2, (uint8_t)blockLog, r);
            offset += r;
        }
        offset /= blockSize;
    }
    if (flag & LZ3_compress_flag::OffsetTwoDim)
    {
        if (lineSize == 0)
        {
            assert(lineSize != 0);
            LZ3_UNREACHABLE;
        }
        offset -= 1;
        uint32_t x = offset % lineSize;
        uint32_t y = offset / lineSize;
        uint8_t c = LZ3_dx_code(x, lineSize);
        out(c, dx_bits[c], x - dx_base[c]);
        uint8_t e = LZ3_dy_code(y);
        out(e, dy_bits[e], y - dy_base[e]);
    }
    else
    {
        uint8_t c = LZ3_of_code(offset);
        out(c, of_bits[c], offset - of_base[c]);
    }
}

static void LZ3_encode_of_wrapper(vector<uint8_t>& seq, vector<pair<uint32_t, uint8_t>>& ext, uint32_t offset, LZ3_CCtx& cctx)
{
    LZ3_encode_of([&seq, &ext](uint8_t c, uint8_t b, uint32_t d) {
        seq.push_back(c);
        assert((d >> b) == 0);
        ext.emplace_back(d, b);
    }, offset, cctx.flag, cctx.preOff, cctx.blockSize, cctx.blockLog, cctx.lineSize, cctx.of_base, cctx.of_bits);
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

LZ3_FORCE_INLINE static LZ3_decode_of_result LZ3_make_decode_of_result(size_t seqLen, size_t offset)
{
    return { (offset << 32) | seqLen };
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

LZ3_FORCE_INLINE static LZ3_decode_of_result LZ3_make_decode_of_result(size_t seqLen, size_t offset)
{
    return { seqLen, offset };
}
#endif

template<uint32_t blockSize, uint32_t lineSize, LZ3_compress_flag flag>
LZ3_FORCE_INLINE static LZ3_decode_of_result LZ3_decode_of(const uint8_t* seqPtr, LZ3_DCtx& dctx)
{
    uint32_t c = *seqPtr++;
    if LZ3_CONSTEXPRIF(flag & LZ3_compress_flag::OffsetRepeat)
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
    uint32_t b = blockSize;
    if LZ3_CONSTEXPRIF(flag & LZ3_compress_flag::OffsetBlock)
    {
        if LZ3_CONSTEXPRIF(blockSize == 0)
            b = dctx.blockSize;
        if (c == 2)
        {
            uint32_t r = (uint32_t)BIT_readBitsFast(&dctx.bitStr, dctx.blockLog);
            constexpr LZ3_compress_flag subFlag = flag ^ (LZ3_compress_flag::OffsetRepeat | LZ3_compress_flag::OffsetBlock);
            auto result = LZ3_decode_of<1, lineSize, subFlag>(seqPtr, dctx);
            return LZ3_make_decode_of_result(result.seqLen() + 1, result.offset() * b - r);
        }
    }
    uint32_t l = lineSize;
    if LZ3_CONSTEXPRIF(flag & LZ3_compress_flag::OffsetTwoDim)
    {
        if (lineSize == 0)
            l = dctx.lineSize;
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
        return LZ3_make_decode_of_result(2, (size_t)o * b);
    }
    else
    {
        uint32_t o = of_base[c];
        if (c >= LZ3_MIN_OF + 2)
        {
            o += (uint32_t)BIT_readBitsFast(&dctx.bitStr, of_bits[c]);
        }
        return LZ3_make_decode_of_result(1, (size_t)o * b);
    }
}

template<uint32_t blockLog, uint32_t lineSize, LZ3_compress_flag flag>
#if defined(__ARM_NEON) && !defined(LZ3_NO_SIMD) && defined(__aarch64__)
__attribute__((aarch64_vector_pcs))
#endif
static LZ3_decode_of_result LZ3_decode_of_wrapper(const uint8_t* seqPtr, LZ3_DCtx& dctx)
{
    auto result = LZ3_decode_of<blockLog, lineSize, flag>(seqPtr, dctx);
    if LZ3_CONSTEXPRIF(flag & LZ3_compress_flag::OffsetRepeat)
    {
        dctx.preOff[2] = dctx.preOff[1];
        dctx.preOff[1] = dctx.preOff[0];
        dctx.preOff[0] = (uint32_t)result.offset();
    }
    return result;
}

#if defined(__ARM_NEON) && !defined(LZ3_NO_SIMD) && defined(__aarch64__)
__attribute__((aarch64_vector_pcs))
#endif
typedef LZ3_decode_of_result(*LZ3_of_decoder)(const uint8_t* seqPtr, LZ3_DCtx& dctx);

LZ3_NO_INLINE static LZ3_of_decoder LZ3_gen_of_decoder(LZ3_compress_flag flag, uint32_t blockSize, uint32_t lineSize)
{
    switch ((uint8_t)flag & 7)
    {
    case 0:
        return &LZ3_decode_of_wrapper<1, 0, LZ3_compress_flag::None>;
    case 1:
        return &LZ3_decode_of_wrapper<1, 0, LZ3_compress_flag::OffsetRepeat>;
    case 2:
        if (blockSize == 3)
            return &LZ3_decode_of_wrapper<3,  0, LZ3_compress_flag::OffsetBlock>;
        if (blockSize == 4)
            return &LZ3_decode_of_wrapper<4,  0, LZ3_compress_flag::OffsetBlock>;
        if (blockSize == 8)
            return &LZ3_decode_of_wrapper<8,  0, LZ3_compress_flag::OffsetBlock>;
        if (blockSize == 16)
            return &LZ3_decode_of_wrapper<16, 0, LZ3_compress_flag::OffsetBlock>;
        return &LZ3_decode_of_wrapper<0, 0, LZ3_compress_flag::OffsetBlock>;
    case 3:
        return &LZ3_decode_of_wrapper<0, 0, LZ3_compress_flag::OffsetRepeat | LZ3_compress_flag::OffsetBlock>;
    case 4:
        return &LZ3_decode_of_wrapper<1, 0, LZ3_compress_flag::OffsetTwoDim>;
    case 5:
        return &LZ3_decode_of_wrapper<1, 0, LZ3_compress_flag::OffsetRepeat | LZ3_compress_flag::OffsetTwoDim>;
    case 6:
        if (blockSize == 3  && lineSize == 64)
            return &LZ3_decode_of_wrapper<3,  64,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 3  && lineSize == 128)
            return &LZ3_decode_of_wrapper<3,  128, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 3  && lineSize == 256)
            return &LZ3_decode_of_wrapper<3,  256, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 3  && lineSize == 512)
            return &LZ3_decode_of_wrapper<3,  512, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 4  && lineSize == 64)
            return &LZ3_decode_of_wrapper<4,  64,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 4  && lineSize == 128)
            return &LZ3_decode_of_wrapper<4,  128, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 4  && lineSize == 256)
            return &LZ3_decode_of_wrapper<4,  256, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 4  && lineSize == 512)
            return &LZ3_decode_of_wrapper<4,  512, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 8  && lineSize == 64)
            return &LZ3_decode_of_wrapper<8,  64,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 8  && lineSize == 128)
            return &LZ3_decode_of_wrapper<8,  128, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 8  && lineSize == 256)
            return &LZ3_decode_of_wrapper<8,  256, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 8  && lineSize == 512)
            return &LZ3_decode_of_wrapper<8,  512, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 43)
            return &LZ3_decode_of_wrapper<16, 43,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 52)      
            return &LZ3_decode_of_wrapper<16, 52,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 64)      
            return &LZ3_decode_of_wrapper<16, 64,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 86)      
            return &LZ3_decode_of_wrapper<16, 86,  LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 103)
            return &LZ3_decode_of_wrapper<16, 103, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 128)
            return &LZ3_decode_of_wrapper<16, 128, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 171)
            return &LZ3_decode_of_wrapper<16, 171, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 205)
            return &LZ3_decode_of_wrapper<16, 205, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 256)
            return &LZ3_decode_of_wrapper<16, 256, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 342)
            return &LZ3_decode_of_wrapper<16, 342, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 410)
            return &LZ3_decode_of_wrapper<16, 410, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        if (blockSize == 16 && lineSize == 512)
            return &LZ3_decode_of_wrapper<16, 512, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
        return &LZ3_decode_of_wrapper<0, 0, LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
    case 7:
        return &LZ3_decode_of_wrapper<0, 0, LZ3_compress_flag::OffsetRepeat | LZ3_compress_flag::OffsetBlock | LZ3_compress_flag::OffsetTwoDim>;
    default:
        LZ3_UNREACHABLE;
    }
}

#if defined(_WIN64)
struct LZ3_decode_ls_result
{
    const uint8_t* getSrcPtr(const uint8_t* srcPtr)
    {
        return (const uint8_t*)(uintptr_t)rax;
    }

    void setSrcPtr(const uint8_t* srcPtr)
    {
        rax = (size_t)(uintptr_t)srcPtr;
    }

    size_t rax;
};
#else
struct LZ3_decode_ls_result
{
    const uint8_t* getSrcPtr(const uint8_t*)
    {
        return (const uint8_t*)(uintptr_t)rax;
    }

    void setSrcPtr(const uint8_t* srcPtr)
    {
        rax = (size_t)(uintptr_t)srcPtr;
    }

    size_t rax;
    //size_t rdx;
};
#endif

template<uint32_t blockSize, typename S>
LZ3_FORCE_INLINE static void LZ3_decode_ls_block(uint8_t* dstPtr, size_t literal, LZ3_DCtx& dctx, S srcReader)
{
    uint32_t b = blockSize;
    if LZ3_CONSTEXPRIF(blockSize == 0)
        b = dctx.blockSize;
    uint8_t* cpyPtr = dstPtr;
    size_t cpyLen = literal;
    uintptr_t blockIdx = (uintptr_t)cpyPtr % b;
    LZ3_block_stream blockStr;
    blockStr.packed = dctx.blockStr[blockIdx].packed;
    size_t blockHead = blockStr.head;
    size_t blockPos = dctx.blockStr[blockHead].position;
    size_t blockLen = min(cpyLen, (size_t)blockStr.length);
    srcReader(cpyPtr, blockPos, blockLen);
    dctx.blockStr[blockHead].position = (uint16_t)(blockPos + blockLen);
    cpyPtr += blockLen;
    cpyLen -= blockLen;
    while (cpyLen > 0)
    {
        blockIdx = blockStr.next;
        blockStr.packed = dctx.blockStr[blockIdx].packed;
        blockPos = blockStr.position;
        blockLen = min(cpyLen, (size_t)blockStr.length);
        srcReader(cpyPtr, blockPos, blockLen);
        dctx.blockStr[blockIdx].position = (uint16_t)(blockPos + blockLen);
        cpyPtr += blockLen;
        cpyLen -= blockLen;
    }
}

template<uint32_t blockSize, typename P, typename S>
LZ3_FORCE_INLINE static void LZ3_decode_ls_predict(uint8_t* dstPtr, size_t literal, LZ3_DCtx& dctx, P prdReader, S srcReader)
{
    uint8_t* prdSta = dctx.predictSta;
    uint8_t* cpyPtr = dstPtr;
    uint8_t* cpyEnd = dstPtr + literal;
    uint32_t b = blockSize;
    if LZ3_CONSTEXPRIF(blockSize == 0)
        b = dctx.blockSize;
    uint32_t m = dctx.predictMask;
    while (cpyPtr < cpyEnd)
    {
        if (cpyPtr >= prdSta && (m & (1 << ((uintptr_t)cpyPtr % b))))
        {
            prdReader(cpyPtr++);
        }
        else
        {
            srcReader(cpyPtr++);
        }
    }
}

//predictable bytes are continuous within a block
template<uint32_t blockSize, uint32_t predictLen, typename P>
LZ3_FORCE_INLINE static void LZ3_decode_ls_predict_conti(uint8_t* dstPtr, size_t literal, LZ3_DCtx& dctx, P prdReader)
{
    uint8_t* prdSta = dctx.predictSta;
    uint8_t* cpyPtr = max(dstPtr, prdSta);
    uint8_t* cpyEnd = dstPtr + literal;
    if (cpyPtr >= cpyEnd)
    {
        return;
    }
    uint32_t b = blockSize;
    if LZ3_CONSTEXPRIF(blockSize == 0)
        b = dctx.blockSize;
    uint32_t m = dctx.predictMask >> (uintptr_t)cpyPtr % b;
    while (true)
    {
        if (m & 1)
        {
            prdReader(cpyPtr++);
            m >>= 1;
        }
        else
        {
            cpyPtr += LZ3_CTZ_32(m);
            break;
        }
    }
    while (cpyPtr < cpyEnd)
    {
        for (size_t i = 0; i < predictLen; ++i)
        {
            prdReader(cpyPtr++);
        }
        cpyPtr += blockSize - predictLen;
    }
}

template<uint32_t blockSize, uint32_t wildLen>
static LZ3_decode_ls_result LZ3_decode_ls_block_wild_wrapper(uint8_t* dstPtr, const uint8_t* srcPtr, size_t literal, LZ3_DCtx& dctx)
{
    LZ3_decode_ls_block<blockSize>(dstPtr, literal, dctx,
        [=](uint8_t* cpyPtr, size_t pos, size_t) { memcpy(cpyPtr, srcPtr + pos, wildLen); });
    LZ3_decode_ls_result result;
    result.setSrcPtr(srcPtr);
    return result;
}

template<uint32_t blockSize, uint32_t predictDis>
static LZ3_decode_ls_result LZ3_decode_ls_predict_wrapper(uint8_t* dstPtr, const uint8_t* srcPtr, size_t literal, LZ3_DCtx& dctx)
{
    uint32_t d = predictDis;
    if LZ3_CONSTEXPRIF(predictDis == 0)
        d = dctx.predictDis;
    LZ3_decode_ls_predict<blockSize>(dstPtr, literal, dctx,
        [=, &srcPtr](uint8_t* cpyPtr) { *cpyPtr = *(srcPtr++) + *(cpyPtr - d); },
        [=, &srcPtr](uint8_t* cpyPtr) { *cpyPtr = *(srcPtr++); });
    LZ3_decode_ls_result result;
    result.setSrcPtr(srcPtr);
    return result;
}

template<uint32_t blockSize, uint32_t wildLen, uint32_t predictDis>
static LZ3_decode_ls_result LZ3_decode_ls_block_wild_predict_wrapper(uint8_t* dstPtr, const uint8_t* srcPtr, size_t literal, LZ3_DCtx& dctx)
{
    LZ3_decode_ls_block<blockSize>(dstPtr, literal, dctx,
        [=](uint8_t* cpyPtr, size_t pos, size_t) { memcpy(cpyPtr, srcPtr + pos, wildLen); });
    uint32_t d = predictDis;
    if LZ3_CONSTEXPRIF(predictDis == 0)
        d = dctx.predictDis;
    LZ3_decode_ls_predict<blockSize>(dstPtr, literal, dctx,
        [=](uint8_t* cpyPtr) { *cpyPtr += *(cpyPtr - d); },
        [=](uint8_t* cpyPtr) {});
    LZ3_decode_ls_result result;
    result.setSrcPtr(srcPtr);
    return result;
}

template<uint32_t blockSize, uint32_t wildLen, uint32_t predictLen, uint32_t predictDis>
static LZ3_decode_ls_result LZ3_decode_ls_block_wild_predict_conti_wrapper(uint8_t* dstPtr, const uint8_t* srcPtr, size_t literal, LZ3_DCtx& dctx)
{
    LZ3_decode_ls_block<blockSize>(dstPtr, literal, dctx,
        [=](uint8_t* cpyPtr, size_t pos, size_t) { memcpy(cpyPtr, srcPtr + pos, wildLen); });
    uint32_t d = predictDis;
    if LZ3_CONSTEXPRIF(predictDis == 0)
        d = dctx.predictDis;
    LZ3_decode_ls_predict_conti<blockSize, predictLen>(dstPtr, literal, dctx,
        [=](uint8_t* cpyPtr) { *cpyPtr += *(cpyPtr - d); });
    LZ3_decode_ls_result result;
    result.setSrcPtr(srcPtr);
    return result;
}

typedef LZ3_decode_ls_result(*LZ3_ls_decoder)(uint8_t* dstPtr, const uint8_t* srcPtr, size_t literal, LZ3_DCtx& dctx);

LZ3_NO_INLINE static LZ3_ls_decoder gen_ls_decoder(LZ3_compress_flag flag, uint32_t blockSize, uint32_t blockLayout, uint32_t predictMask, uint32_t predictDis)
{
    uint32_t predictLen = 0;
    for (uint32_t i = 0; i < blockSize; ++i)
    {
        if (predictMask & (1 << i))
        {
            ++predictLen;
        }
    }
    bool predictConti = false;
    predictMask = (predictMask << blockSize) | predictMask;
    for (uint32_t i = 0; i < blockSize; ++i)
    {
        uint32_t m = (1 << predictLen) - 1;
        if ((predictMask & m) == m)
        {
            predictConti = true;
        }
        predictMask >>= 1;
    }
    switch ((uint8_t)flag & 24)
    {
    case 0:
        break;
    case 8:
        if (blockSize == 3)
            return &LZ3_decode_ls_block_wild_wrapper<3,  4>;
        if (blockSize == 4)
            return &LZ3_decode_ls_block_wild_wrapper<4,  4>;
        if (blockSize == 8)
            return &LZ3_decode_ls_block_wild_wrapper<8,  8>;
        if (blockSize == 16)
            return &LZ3_decode_ls_block_wild_wrapper<16, 16>;
        return &LZ3_decode_ls_block_wild_wrapper<0, 16>;
    case 16:
        return &LZ3_decode_ls_predict_wrapper<0, 0>;
    case 24:
        if (blockSize == 8  && predictConti && predictLen == 3 && predictDis == 8)
            return &LZ3_decode_ls_block_wild_predict_conti_wrapper<8,  8,  3, 8>;
        if (blockSize == 16 && predictConti && predictLen == 1 && predictDis == 16)
            return &LZ3_decode_ls_block_wild_predict_conti_wrapper<16, 16, 1, 16>;
        if (blockSize == 16 && predictConti && predictLen == 2 && predictDis == 16)
            return &LZ3_decode_ls_block_wild_predict_conti_wrapper<16, 16, 2, 16>;
        if (blockSize == 16 && predictConti && predictLen == 3 && predictDis == 16)
            return &LZ3_decode_ls_block_wild_predict_conti_wrapper<16, 16, 3, 16>;
        if (blockSize == 16 && predictConti && predictLen == 4 && predictDis == 16)
            return &LZ3_decode_ls_block_wild_predict_conti_wrapper<16, 16, 4, 16>;
        if (blockSize == 8  && predictDis == 8)
            return &LZ3_decode_ls_block_wild_predict_wrapper<8,  8,  8>;
        if (blockSize == 16 && predictDis == 16)
            return &LZ3_decode_ls_block_wild_predict_wrapper<16, 16, 16>;
        return &LZ3_decode_ls_block_wild_predict_wrapper<0, 16, 0>;
    default:
        LZ3_UNREACHABLE;
    }
    return nullptr;
}

LZ3_NO_INLINE static LZ3_decode_ls_result LZ3_decode_ls_safe(uint8_t* dstPtr, const uint8_t* srcPtr, size_t literal, LZ3_DCtx& dctx)
{
    if (dctx.flag & LZ3_compress_flag::LiteralBlock && dctx.flag & LZ3_compress_flag::LiteralPredict)
    {
        LZ3_decode_ls_block<0>(dstPtr, literal, dctx, [=](uint8_t* cpyPtr, size_t srcPos, size_t cpyLen)
        {
            for (size_t i = 0; i < cpyLen; ++i)
            {
                *cpyPtr++ = srcPtr[srcPos + i];
            }
        });
        uint32_t d = dctx.predictDis;
        LZ3_decode_ls_predict<0>(dstPtr, literal, dctx,
            [=](uint8_t* cpyPtr) { *cpyPtr += *(cpyPtr - d); },
            [=](uint8_t* cpyPtr) {});
    }
    else if (dctx.flag & LZ3_compress_flag::LiteralBlock)
    {
        LZ3_decode_ls_block<0>(dstPtr, literal, dctx, [=](uint8_t* cpyPtr, size_t srcPos, size_t cpyLen)
        {
            for (size_t i = 0; i < cpyLen; ++i)
            {
                *cpyPtr++ = srcPtr[srcPos + i];
            }
        });
    }
    else if (dctx.flag & LZ3_compress_flag::LiteralPredict)
    {
        uint32_t d = dctx.predictDis;
        LZ3_decode_ls_predict<0>(dstPtr, literal, dctx,
            [=, &srcPtr](uint8_t* cpyPtr) { *cpyPtr = *(srcPtr++) + *(cpyPtr - d); },
            [=, &srcPtr](uint8_t* cpyPtr) { *cpyPtr = *(srcPtr++); });
    }
    LZ3_decode_ls_result result;
    result.setSrcPtr(srcPtr);
    return result;
}

#define LZ3_BIT_COST_ACC 8u
#define LZ3_BIT_COST_MUL (1u << LZ3_BIT_COST_ACC)

LZ3_FORCE_INLINE static uint32_t LZ3_weight(uint32_t freq)
{
    freq += 1;
    uint8_t hb = (uint8_t)LZ3_high_bit_32(freq);
    uint32_t bw = hb * LZ3_BIT_COST_MUL;
    uint32_t fw = (freq << LZ3_BIT_COST_ACC) >> hb;
    return bw + fw;
}

class LZ3_code_hist
{
    uint32_t freq[256];
    uint32_t sum;
    uint32_t base;

public:
    LZ3_code_hist() :
        freq{ 0 }, sum(0), base(0)
    {
    }

    void inc_stats(uint8_t code, uint32_t inc = 1)
    {
        freq[code] += inc;
        sum += inc;
    }

    void eval_base()
    {
        base = LZ3_weight(sum);
    }

    uint32_t eval_cost(uint8_t code) const
    {
        return base - LZ3_weight(freq[code]);
    }

    const uint32_t* data() const
    {
        return freq;
    }

    uint32_t size() const
    {
        return sum;
    }

    LZ3_code_hist& merge(const LZ3_code_hist& with)
    {
        for (uint32_t c = 0; c < 256; ++c)
        {
            freq[c] += with.freq[c];
        }
        sum += with.sum;
        return *this;
    }

    LZ3_code_hist merge(const LZ3_code_hist& with) const
    {
        LZ3_code_hist hist = *this;
        return hist.merge(with);
    }

    void clear()
    {
        fill_n(freq, 256, 0);
        sum = 0;
        base = 0;
    }
};

struct LZ3_chunk_huf
{
    LZ3_code_hist codeHist;
    uint8_t codeMax;
    uint8_t codeBits;
    size_t bSize;
    HUF_CElt table[HUF_CTABLE_SIZE(255) / sizeof(HUF_CElt)];
    uint8_t header[256];
    size_t hSize;
    size_t cSize;

    constexpr static LZ3_entropy_coder coder() { return LZ3_entropy_coder::Huff0; }

    LZ3_chunk_huf(const uint8_t* src, size_t srcSize)
    {
        codeMax = 0;
        for (size_t i = 0; i < srcSize; ++i)
        {
            codeHist.inc_stats(src[i]);
            codeMax = max(codeMax, src[i]);
        }
        eval_size();
    }

    LZ3_chunk_huf(const LZ3_code_hist& codeHist, uint8_t codeBound) :
        codeHist(codeHist)
    {
        codeMax = 0;
        for (uint8_t c = codeBound; c > 0; --c)
        {
            if (codeHist.data()[c] > 0)
            {
                codeMax = c;
                break;
            }
        }
        eval_size();
    }

    LZ3_chunk_huf(const LZ3_chunk_huf& a, const LZ3_chunk_huf& b) :
        codeHist(a.codeHist.merge(b.codeHist)), codeMax(max(a.codeMax, b.codeMax))
    {
        eval_size();
    }

    void eval_size()
    {
        codeBits = (uint8_t)LZ3_high_bit_32(max(codeMax, (uint8_t)1)) + 1;
        bSize = (codeHist.size() * codeBits + 3 + 1 + 7) / 8;
        if (codeHist.data()[codeMax] == codeHist.size())
        {
            header[0] = codeMax;
            hSize = 1;
            cSize = 0;
            return;
        }
        uint64_t wksp[HUF_WORKSPACE_SIZE / sizeof(uint64_t)];
        uint32_t hufLog = HUF_optimalTableLog(HUF_TABLELOG_DEFAULT, codeHist.size(), codeMax);
        size_t maxBits = HUF_buildCTable_wksp(table, codeHist.data(), codeMax, hufLog, wksp, sizeof(wksp));
        hufLog = (uint32_t)maxBits;
        size_t tSize = HUF_CTABLE_SIZE(codeMax) / sizeof(HUF_CElt);
        size_t uSize = sizeof(table) - tSize * sizeof(HUF_CElt);
        memset(table + tSize, 0, uSize);
        hSize = HUF_writeCTable_wksp(header, sizeof(header), table, codeMax, hufLog, wksp, sizeof(wksp));
        if (HUF_isError(hSize))
        {
            hSize = 0;
            cSize = codeHist.size();
            return;
        }
        cSize = HUF_estimateCompressedSize(table, codeHist.data(), codeMax) + 6/*HUF_compress4X has a jumptable containing 3 LE16*/;
    }

    size_t estimate_size() const
    {
        return hSize == 1 && cSize == 0 ? 4 : (5 + hSize + cSize);
    }

    size_t fallback_size() const
    {
        return 3 + min((size_t)codeHist.size(), bSize);
    }
};

struct LZ3_chunk_fse
{
    LZ3_code_hist codeHist;
    uint8_t codeMax;
    uint8_t codeBits;
    size_t bSize;
    FSE_CTable table[FSE_CTABLE_SIZE_U32(FSE_MAX_TABLELOG, FSE_MAX_SYMBOL_VALUE)];
    uint8_t header[512];
    size_t hSize;
    size_t cSize;

    constexpr static LZ3_entropy_coder coder() { return LZ3_entropy_coder::FSE; }

    LZ3_chunk_fse(const uint8_t* src, size_t srcSize)
    {
        codeMax = 0;
        for (size_t i = 0; i < srcSize; ++i)
        {
            codeHist.inc_stats(src[i]);
            codeMax = max(codeMax, src[i]);
        }
        eval_size();
    }

    LZ3_chunk_fse(const LZ3_code_hist& codeHist, uint8_t codeBound) :
        codeHist(codeHist)
    {
        codeMax = 0;
        for (uint8_t c = codeBound; c > 0; --c)
        {
            if (codeHist.data()[c] > 0)
            {
                codeMax = c;
                break;
            }
        }
        eval_size();
    }

    LZ3_chunk_fse(const LZ3_chunk_fse& a, const LZ3_chunk_fse& b) :
        codeHist(a.codeHist.merge(b.codeHist)), codeMax(max(a.codeMax, b.codeMax))
    {
        eval_size();
    }

    void eval_size()
    {
        codeBits = (uint8_t)LZ3_high_bit_32(max(codeMax, (uint8_t)1)) + 1;
        bSize = (codeHist.size() * codeBits + 3 + 1 + 7) / 8;
        if (codeHist.data()[codeMax] == codeHist.size())
        {
            header[0] = codeMax;
            hSize = 1;
            cSize = 0;
            return;
        }
        uint32_t tableLog = FSE_optimalTableLog(FSE_DEFAULT_TABLELOG, codeHist.size(), codeMax);
        int16_t norm[FSE_MAX_SYMBOL_VALUE + 1];
        FSE_normalizeCount(norm, tableLog, codeHist.data(), codeHist.size(), codeMax, codeHist.size() > 2048);
        hSize = FSE_writeNCount(header, 512, norm, codeMax, tableLog);
        if (FSE_isError(hSize))
        {
            hSize = 0;
            cSize = codeHist.size();
            return;
        }
        uint32_t wksp[FSE_BUILD_CTABLE_WORKSPACE_SIZE_U32(FSE_MAX_SYMBOL_VALUE, FSE_MAX_TABLELOG)];
        FSE_buildCTable_wksp(table, norm, codeMax, tableLog, wksp, sizeof(wksp));
        uint64_t price = 0;
        codeHist.eval_base();
        for (uint32_t c = 0; c < 256; ++c)
        {
            price += (uint64_t)codeHist.eval_cost((uint8_t)c) * codeHist.data()[c];
        }
        cSize = (size_t)(price / LZ3_BIT_COST_MUL / 8);
    }

    size_t estimate_size() const
    {
        return hSize == 1 && cSize == 0 ? 4 : (3 + hSize + cSize);
    }

    size_t fallback_size() const
    {
        return 3 + min((size_t)codeHist.size(), bSize);
    }
};

template<typename ChunkType>
struct LZ3_chunk_merged : ChunkType
{
    vector<size_t> sources;

    LZ3_chunk_merged(const ChunkType& chunk, size_t index) :
        ChunkType(chunk)
    {
        sources.push_back(index);
    }

    LZ3_chunk_merged(const LZ3_chunk_merged& a, const LZ3_chunk_merged& b) :
        ChunkType(a, b)
    {
        sources.insert(sources.end(), a.sources.begin(), a.sources.end());
        sources.insert(sources.end(), b.sources.begin(), b.sources.end());
    }
};

template<typename ChunkType>
static vector<uint8_t> LZ3_merge_chunks(vector<ChunkType>& chunks)
{
    list<LZ3_chunk_merged<ChunkType>> merged;
    for (size_t i = 0; i < chunks.size(); ++i)
    {
        merged.emplace_back(chunks[i], i);
    }
    while (true)
    {
        size_t oldSize = merged.size();
        for (auto it = merged.begin(); it != merged.end();)
        {
            auto cc = it++;
            auto nc = it;
            if (nc == merged.end())
            {
                nc = cc;
                cc = merged.begin();
            }
            LZ3_chunk_merged<ChunkType> mc(*cc, *nc);
            if (min(mc.estimate_size(), mc.fallback_size()) <= min(cc->estimate_size(), cc->fallback_size()) + min(nc->estimate_size(), nc->fallback_size()))
            {
                *cc = mc;
                it = merged.erase(nc);
            }
        }
        size_t newSize = merged.size();
        if (newSize == oldSize || newSize == 1)
        {
            break;
        }
    }
    vector<uint8_t> splits(chunks.size());
    chunks.erase(chunks.begin() + merged.size(), chunks.end());
    uint8_t index = 0;
    for (const LZ3_chunk_merged<ChunkType>& m : merged)
    {
        chunks[index] = m;
        for (size_t s : m.sources)
        {
            splits[s] = index;
        }
        ++index;
    }
    return splits;
}

static LZ3_compress_flag LZ3_detect_offset_flags(const vector<LZ3_match_info>& matches, LZ3_CCtx& cctx)
{
    LZ3_compress_flag flag = LZ3_compress_flag::None;
    uint32_t total = (uint32_t)matches.size();
    if (total < 32)
    {
        return flag;
    }
    unordered_map<uint32_t, uint32_t> origFreq;
    for (const LZ3_match_info& match : matches)
    {
        uint32_t offset = match.offset;
        origFreq[offset]++;
    }
    vector<pair<uint32_t, uint32_t>> origList(origFreq.begin(), origFreq.end());
    sort(origList.begin(), origList.end(), [](const pair<uint32_t, uint32_t>& x, const pair<uint32_t, uint32_t>& y)
    {
        return x.second != y.second ? x.second > y.second : x.first < y.first;
    });
    vector<pair<uint8_t, uint32_t>> codeList;
    LZ3_code_hist codeHist;
    for (const auto& p : origList)
    {
        uint32_t offset = p.first;
        uint32_t count = p.second;
        LZ3_encode_of([&codeList, &codeHist, count](uint8_t c, uint8_t b, uint32_t d) {
            codeList.emplace_back(c, count);
            codeHist.inc_stats(c, count);
        }, offset, flag, nullptr, 0, 0, 0, nullptr, nullptr);
    }
    codeHist.eval_base();
    int64_t codePrice = 0;
    for (const auto& p : codeList)
    {
        codePrice += (int64_t)(codeHist.eval_cost(p.first) + of_bits[p.first] * LZ3_BIT_COST_MUL) * p.second;
    }
    int64_t bestPrice = codePrice;
    //consider only block of 3(RGB24), 4(RGB32), 8(ETC1), 16(ETC2/ASTC) bytes
    cctx.blockSize = 1;
    cctx.blockLog = 0;
    int64_t blk2Thres = bestPrice * cctx.params[LZ3_compress_param::OffBlockModeThreshold] / 100 - cctx.params[LZ3_compress_param::OffBlockModeIntercept] * 8 * LZ3_BIT_COST_MUL;
    static constexpr uint32_t usualBlockSize[] = { 3, 4, 8, 16 };
    for (uint32_t divisor : usualBlockSize)
    {
        uint8_t nbBits = (uint8_t)LZ3_high_bit_32(divisor - 1) + 1;
        LZ3_compress_flag newFlag = LZ3_compress_flag::OffsetBlock;
        vector<pair<uint8_t, uint32_t>> blk2List;
        LZ3_code_hist blk2Hist;
        int64_t blk2Price = 0;
        for (const auto& p : origList)
        {
            uint32_t offset = p.first;
            uint32_t count = p.second;
            LZ3_encode_of([&blk2List, &blk2Hist, &blk2Price, count](uint8_t c, uint8_t b, uint32_t d)
            {
                blk2List.emplace_back(c, count);
                blk2Hist.inc_stats(c, count);
                blk2Price += b * LZ3_BIT_COST_MUL * count;
            }, offset, flag | newFlag, nullptr, divisor, nbBits, 0, cctx.of_base, cctx.of_bits);
            cctx.preOff[2] = cctx.preOff[1];
            cctx.preOff[1] = cctx.preOff[0];
            cctx.preOff[0] = offset;
        }
        blk2Hist.eval_base();
        for (const auto& p : blk2List)
        {
            blk2Price += (int64_t)blk2Hist.eval_cost(p.first) * p.second;
        }
        if (blk2Price < blk2Thres)
        {
            cctx.blockSize = divisor;
            cctx.blockLog = nbBits;
            flag = flag | newFlag;
            blk2Thres = blk2Price;
            bestPrice = blk2Price;
        }
    }
    //consider ASTC may have NPOT line size
    cctx.lineSize = 0;
    int64_t dim2Thres = bestPrice * cctx.params[LZ3_compress_param::OffDim2ModeThreshold] / 100 - cctx.params[LZ3_compress_param::OffDim2ModeIntercept] * 8 * LZ3_BIT_COST_MUL;
    for (uint32_t i = 0; i < origList.size() && i < 8u; ++i)
    {
        uint32_t divisor = origList[i].first;
        LZ3_compress_flag newFlag = LZ3_compress_flag::OffsetTwoDim;
        if (cctx.blockSize > 1)
        {
            newFlag = newFlag | LZ3_compress_flag::OffsetBlock;
            if (divisor % cctx.blockSize)
            {
                continue;
            }
            divisor /= cctx.blockSize;
        }
        if (divisor < 16 || divisor > 4092)
        {
            continue;
        }
        vector<pair<uint8_t, uint32_t>> dim2List;
        LZ3_code_hist dim2Hist;
        int64_t dim2Price = 0;
        cctx.of_size = LZ3_gen_of_book(cctx.of_base, cctx.of_bits, flag | newFlag, cctx.blockLog, divisor);
        for (const auto& p : origList)
        {
            uint32_t offset = p.first;
            uint32_t count = p.second;
            LZ3_encode_of([&dim2List, &dim2Hist, &dim2Price, count](uint8_t c, uint8_t b, uint32_t d)
            {
                dim2List.emplace_back(c, count);
                dim2Hist.inc_stats(c, count);
                dim2Price += b * LZ3_BIT_COST_MUL* count;
            }, offset, flag | newFlag, nullptr, cctx.blockSize, cctx.blockLog, divisor, cctx.of_base, cctx.of_bits);
        }
        dim2Hist.eval_base();
        for (const auto& p : dim2List)
        {
            dim2Price += (int64_t)dim2Hist.eval_cost(p.first) * p.second;
        }
        if (dim2Price < dim2Thres)
        {
            cctx.lineSize = divisor;
            flag = flag | newFlag;
            dim2Thres = dim2Price;
            bestPrice = dim2Price;
        }
    }
    int64_t rep2Thres = bestPrice * cctx.params[LZ3_compress_param::OffRepeatModeThreshold] / 100 - cctx.params[LZ3_compress_param::OffRepeatModeIntercept] * 8 * LZ3_BIT_COST_MUL;
    {
        fill_n(cctx.preOff, 3, 0);
        LZ3_compress_flag newFlag = LZ3_compress_flag::OffsetRepeat;
        unordered_map<uint8_t, uint32_t> rep2Freq;
        LZ3_code_hist rep2Hist;
        int64_t rep2Price = 0;
        for (const LZ3_match_info& match : matches)
        {
            uint32_t offset = match.offset;
            LZ3_encode_of([&rep2Freq, &rep2Hist, &rep2Price](uint8_t c, uint8_t b, uint32_t d)
            {
                rep2Freq[c]++;
                rep2Hist.inc_stats(c);
                rep2Price += b * LZ3_BIT_COST_MUL;
            }, offset, flag | newFlag, cctx.preOff, cctx.blockSize, cctx.blockLog, cctx.lineSize, cctx.of_base, cctx.of_bits);
            cctx.preOff[2] = cctx.preOff[1];
            cctx.preOff[1] = cctx.preOff[0];
            cctx.preOff[0] = offset;
        }
        rep2Hist.eval_base();
        for (const auto& p : rep2Freq)
        {
            rep2Price += (int64_t)rep2Hist.eval_cost(p.first) * p.second;
        }
        if (rep2Price < rep2Thres)
        {
            flag = flag | newFlag;
            bestPrice = rep2Price;
        }
    }
    return flag;
}

struct LZ3_chunk_pattern
{
    uint32_t bits;
    uint32_t quant;
    uint32_t count;
    uint32_t index;
};

struct LZ3_layout_pattern
{
    vector<LZ3_chunk_pattern> chunks;
};

struct LZ3_literal_pattern
{
    uint32_t blockSize;
    vector<LZ3_layout_pattern> layouts;
    uint32_t(*layoutSelector)(const uint8_t*, uint32_t);
};

struct LZ3_literal_params_BISE
{
    uint32_t trits;
    uint32_t qunits;
    uint32_t bits;
};

struct LZ3_literal_params_ASTC
{
    bool voidExt;
    LZ3_literal_params_BISE weightEncoding;
    uint32_t weightWidth;
    uint32_t weightHeight;
    uint32_t weightSta;
    bool dualPanel;
    uint32_t part;
    uint32_t colorModes[4];
    uint32_t colorSta;
    uint32_t colorExtraSta;
};

static bool LZ3_parse_params_ASTC(const uint8_t* b, LZ3_literal_params_ASTC& p)
{
    memset(&p, 0, sizeof(LZ3_literal_params_ASTC));
    uint32_t blockMode = 0;
    uint32_t weightRange = 0;
    uint32_t b01 = LZ3_extract_bits(b, 0, 2);
    if (b01 != 0)
    {
        blockMode = LZ3_extract_bits(b, 2, 2);
        if (blockMode == 3)
        {
            blockMode += LZ3_extract_bits(b, 8, 1);
        }
        weightRange = (b01 << 1) | LZ3_extract_bits(b, 4, 1);
    }
    else
    {
        uint32_t b78 = LZ3_extract_bits(b, 7, 2);
        if (b78 <= 1)
        {
            blockMode = 5 + b78;
        }
        if (b78 == 3)
        {
            uint32_t b56 = LZ3_extract_bits(b, 5, 2);
            if (b56 <= 1)
            {
                blockMode = 5 + b78 + b56;
            }
            else if (LZ3_extract_bits(b, 2, 5) == 31)
            {
                blockMode = 10;
            }
            else
            {
                return false;
            }
        }
        if (b78 == 2)
        {
            blockMode = 9;
        }
        uint32_t b23 = LZ3_extract_bits(b, 2, 2);
        if (b23 == 0)
        {
            return false;
        }
        weightRange = (b23 << 1) | LZ3_extract_bits(b, 4, 1);
    }
    uint32_t weightPrecision = blockMode < 9 ? LZ3_extract_bits(b, 9, 1) : 0;
    static constexpr LZ3_literal_params_BISE weightEncoding[2][8] = {
        {
            {0, 0, 0},
            {0, 0, 0},
            {0, 0, 1},
            {1, 0, 0},
            {0, 0, 2},
            {0, 1, 0},
            {1, 0, 1},
            {0, 0, 3},
        },
        {
            {0, 0, 0},
            {0, 0, 0},
            {0, 1, 1},
            {1, 0, 2},
            {0, 0, 4},
            {0, 1, 2},
            {1, 0, 3},
            {0, 0, 5},
        }
    };
    p.weightEncoding = weightEncoding[weightPrecision][weightRange];
    switch (blockMode)
    {
    case 0:
        p.weightWidth = LZ3_extract_bits(b, 7, 2) + 4;
        p.weightHeight = LZ3_extract_bits(b, 5, 2) + 2;
        break;
    case 1:
        p.weightWidth = LZ3_extract_bits(b, 7, 2) + 8;
        p.weightHeight = LZ3_extract_bits(b, 5, 2) + 2;
        break;
    case 2:
        p.weightWidth = LZ3_extract_bits(b, 5, 2) + 2;
        p.weightHeight = LZ3_extract_bits(b, 7, 2) + 8;
        break;
    case 3:
        p.weightWidth = LZ3_extract_bits(b, 5, 2) + 2;
        p.weightHeight = LZ3_extract_bits(b, 7, 1) + 6;
        break;
    case 4:
        p.weightWidth = LZ3_extract_bits(b, 7, 1) + 2;
        p.weightHeight = LZ3_extract_bits(b, 5, 2) + 2;
        break;
    case 5:
        p.weightWidth = 12;
        p.weightHeight = LZ3_extract_bits(b, 5, 2) + 2;
        break;
    case 6:
        p.weightWidth = LZ3_extract_bits(b, 5, 2) + 2;
        p.weightHeight = 12;
        break;
    case 7:
        p.weightWidth = 6;
        p.weightHeight = 10;
        break;
    case 8:
        p.weightWidth = 10;
        p.weightHeight = 6;
        break;
    case 9:
        p.weightWidth = LZ3_extract_bits(b, 9, 2) + 6;
        p.weightHeight = LZ3_extract_bits(b, 5, 2) + 6;
        break;
    case 10:
        p.voidExt = true;
        return true;
    }
    uint32_t weightCount = p.weightWidth * p.weightHeight;
    if (weightCount > 64)
    {
        return false;
    }
    uint32_t weightBits;
    if (p.weightEncoding.trits)
    {
        weightBits = (weightCount + 4) / 5 * (5 * p.weightEncoding.bits + 8 * p.weightEncoding.trits);
    }
    else
    {
        weightBits = (weightCount + 2) / 3 * (3 * p.weightEncoding.bits + 7 * p.weightEncoding.qunits);
    }
    if (weightBits > 96 || weightBits < 24)
    {
        return false;
    }
    p.weightSta = 128 - weightBits;
    p.dualPanel = blockMode < 9 ? LZ3_extract_bits(b, 10, 1) : 0;
    p.part = LZ3_extract_bits(b, 11, 2);
    if (p.dualPanel && p.part >= 3)
    {
        return false;
    }
    if (p.part == 0)
    {
        p.colorModes[0] = LZ3_extract_bits(b, 13, 4);
        p.colorExtraSta = p.weightSta;
        p.colorSta = 17;
    }
    else
    {
        uint32_t b2324 = LZ3_extract_bits(b, 23, 2);
        if (b2324 == 0)
        {
            fill_n(p.colorModes, 4, LZ3_extract_bits(b, 25, 4));
        }
        else
        {
            switch (p.part)
            {
            case 1:
                p.colorModes[0] = (b2324 - 1 + LZ3_extract_bits(b, 25, 1)) * 4 + LZ3_extract_bits(b, 27, 2);
                p.colorModes[1] = (b2324 - 1 + LZ3_extract_bits(b, 26, 1)) * 4 + LZ3_extract_bits(b, p.weightSta - 1, 2);
                p.colorExtraSta = p.weightSta - 2;
                break;
            case 2:
                p.colorModes[0] = (b2324 - 1 + LZ3_extract_bits(b, 25, 1)) * 4 + LZ3_extract_bits(b, 28, 1) + LZ3_extract_bits(b, p.weightSta - 4, 1) * 2;
                p.colorModes[1] = (b2324 - 1 + LZ3_extract_bits(b, 26, 1)) * 4 + LZ3_extract_bits(b, p.weightSta - 3, 2);
                p.colorModes[2] = (b2324 - 1 + LZ3_extract_bits(b, 27, 1)) * 4 + LZ3_extract_bits(b, p.weightSta - 1, 2);
                p.colorExtraSta = p.weightSta - 5;
                break;
            case 3:
                p.colorModes[0] = (b2324 - 1 + LZ3_extract_bits(b, 25, 1)) * 4 + LZ3_extract_bits(b, p.weightSta - 7, 2);
                p.colorModes[1] = (b2324 - 1 + LZ3_extract_bits(b, 26, 1)) * 4 + LZ3_extract_bits(b, p.weightSta - 5, 2);
                p.colorModes[2] = (b2324 - 1 + LZ3_extract_bits(b, 27, 1)) * 4 + LZ3_extract_bits(b, p.weightSta - 3, 2);
                p.colorModes[3] = (b2324 - 1 + LZ3_extract_bits(b, 28, 1)) * 4 + LZ3_extract_bits(b, p.weightSta - 1, 2);
                p.colorExtraSta = p.weightSta - 8;
                break;
            }
        }
        p.colorSta = 29;
    }
    return true;
}

struct LZ3_literal_pattern_statistic
{
    struct
    {
        vector<uint32_t> illegal;
        std::unordered_map<uint32_t, uint32_t> weightSta;
        uint32_t dualPanel[2];
        uint32_t part[4];
        uint32_t colorMode[16];
        std::unordered_map<uint32_t, uint32_t> colorSta;
    }ASTC;

    void clear()
    {
        ASTC.illegal.clear();
        ASTC.weightSta.clear();
        fill_n(ASTC.dualPanel, 2, 0);
        fill_n(ASTC.part, 4, 0);
        fill_n(ASTC.colorMode, 16, 0);
        ASTC.colorSta.clear();
    }
};

static LZ3_literal_pattern_statistic LZ3_literal_pattern_sta;

static uint32_t LZ3_select_layout_ASTC(const uint8_t* b, uint32_t o)
{
    LZ3_literal_params_ASTC params;
    if (!LZ3_parse_params_ASTC(b + o, params))
    {
#if defined(LZ3_LIT_STA)
        LZ3_literal_pattern_sta.ASTC.illegal.push_back(o);
#endif
        return 0;
    }
#if defined(LZ3_LIT_STA)
    if (!params.voidExt)
    {
        LZ3_literal_pattern_sta.ASTC.weightSta[params.weightSta]++;
        LZ3_literal_pattern_sta.ASTC.dualPanel[params.dualPanel]++;
        LZ3_literal_pattern_sta.ASTC.part[params.part]++;
        for (uint32_t i = 0; i <= params.part; ++i)
        {
            LZ3_literal_pattern_sta.ASTC.colorMode[params.colorModes[i]]++;
        }
        LZ3_literal_pattern_sta.ASTC.colorSta[params.colorSta]++;
    }
#endif
    if (params.part > 1)
    {
        return 1;
    }
    else
    {
        return 2;
    }
}

static LZ3_literal_pattern lp_list[] = {
    /*{
        8,
        {
            {{{8, 256, 3, 0}, {8, 256, 1, 1}, {8, 256, 4, 2}}}
        }
    },
    {
        8,
        {
            {{{8, 256, 3, 0}, {8, 256, 1, 1}, {8, 256, 2, 2}, {8, 256, 2, 3}}}
        }
    },
    {
        16,
        {
            {{{8, 256, 1, 0}, {8, 256, 1, 1}, {8, 256, 1, 2}, {8, 256, 4, 3}, {8, 256, 9, 4}}}
        }
    },*/
    {
        16,
        {
            {{{8, 256, 16, 0}}},
            {{{8, 256, 1, 1}, {8, 256, 1, 2}, {8, 256, 4, 4}, {8, 256, 10, 6}}},
            {{{8, 256, 1, 1}, {8, 256, 1, 2}, {8, 256, 1, 3}, {8, 256, 4, 5}, {8, 256, 9, 6}}}
        },
        &LZ3_select_layout_ASTC
    },
};

static LZ3_compress_flag LZ3_detect_literal_flags(const uint8_t* src, const vector<pair<uint32_t, uint32_t>>& slices, LZ3_CCtx& cctx, vector<uint8_t>& stream, vector<LZ3_chunk_huf>& chunks)
{
    LZ3_compress_flag flag = LZ3_compress_flag::None;
    stream.clear();
    for (const auto& p : slices)
    {
        for (uint32_t i = p.first; i < p.first + p.second; ++i)
        {
            stream.push_back(src[i]);
        }
    }
    LZ3_chunk_huf rawChunk(stream.data(), stream.size());
    chunks = { rawChunk };
    int64_t origSize = (int64_t)min(rawChunk.estimate_size(), rawChunk.fallback_size());
    int64_t bestSize = origSize;
    //consider block
    cctx.blockLayout = 0;
    int64_t blkThres = origSize * cctx.params[LZ3_compress_param::LitBlockModeThreshold] / 100 - cctx.params[LZ3_compress_param::LitBlockModeIntercept];
    do
    {
        if (!(cctx.flag & LZ3_compress_flag::OffsetBlock))
        {
            break;
        }
        if (cctx.blockSize > 16)
        {
            break;
        }
        vector<LZ3_code_hist> blkHist(cctx.blockSize);
        for (const auto& p : slices)
        {
            for (uint32_t i = p.first; i < p.first + p.second; ++i)
            {
                blkHist[i % cctx.blockSize].inc_stats(src[i]);
            }
        }
        vector<LZ3_chunk_huf> blkChunks;
        for (uint32_t i = 0; i < cctx.blockSize; ++i)
        {
            blkChunks.emplace_back(blkHist[i], (uint8_t)255);
        }
        vector<uint8_t> blkSplits = LZ3_merge_chunks(blkChunks);
        if (blkChunks.size() == 1)
        {
            break;
        }
        int64_t blkSize = 0;
        for (const LZ3_chunk_huf& c : blkChunks)
        {
            blkSize += (int64_t)min(c.estimate_size(), c.fallback_size());
        }
        if (blkSize < blkThres && blkSize < bestSize)
        {
            flag = flag | LZ3_compress_flag::LiteralBlock;
            bestSize = blkSize;
            for (size_t i = 0; i < blkSplits.size(); ++i)
            {
                if (blkSplits[i] != blkSplits[(i == 0 ? blkSplits.size() : i) - 1])
                {
                    cctx.blockLayout |= 1 << i;
                }
            }
            vector<vector<uint8_t>> blkStreams(blkChunks.size());
            for (const auto& p : slices)
            {
                for (uint32_t i = p.first; i < p.first + p.second; ++i)
                {
                    blkStreams[blkSplits[i % cctx.blockSize]].push_back(src[i]);
                }
            }
            stream.clear();
            for (const vector<uint8_t>& s : blkStreams)
            {
                stream.insert(stream.end(), s.begin(), s.end());
            }
            chunks = blkChunks;
        }
    }
    while (false);
    //consider predict
    cctx.predictMask = 0;
    int64_t prdThres = bestSize * cctx.params[LZ3_compress_param::LitPredictModeThreshold] / 100 - cctx.params[LZ3_compress_param::LitPredictModeIntercept];
    do
    {
        uint32_t blkMod = 1;
        uint32_t prdDis = 1;
        if (cctx.flag & LZ3_compress_flag::OffsetBlock)
        {
            blkMod = cctx.blockSize <= 16 ? cctx.blockSize : 1;
            prdDis = cctx.blockSize;
        }
        /*if (cctx.flag & LZ3_compress_flag::OffsetTwoDim)
        {
            prdDis *= cctx.lineSize;
        }*/
        vector<LZ3_code_hist> blkHist(blkMod);
        vector<LZ3_code_hist> prdHist(blkMod);
        for (const auto& p : slices)
        {
            for (uint32_t i = p.first; i < p.first + p.second; ++i)
            {
                uint8_t l = src[i];
                blkHist[i % blkMod].inc_stats(l);
                if (i >= prdDis)
                {
                    l -= src[i - prdDis];
                }
                prdHist[i % blkMod].inc_stats(l);
            }
        }
        for (uint32_t i = 0; i < blkMod; ++i)
        {
            size_t blkPrice = 0;
            size_t prdPrice = 0;
            for (size_t c = 0; c < 256; ++c)
            {
                blkPrice += (size_t)blkHist[i].eval_cost((uint8_t)c) * blkHist[i].data()[c];
                prdPrice += (size_t)prdHist[i].eval_cost((uint8_t)c) * prdHist[i].data()[c];
            }
            if (prdPrice < blkPrice)
            {
                cctx.predictMask |= 1 << i;
            }
        }
        if (cctx.predictMask == 0)
        {
            break;
        }
        vector<LZ3_chunk_huf> prdChunks;
        for (uint32_t i = 0; i < blkMod; ++i)
        {
            if (cctx.predictMask & (1 << i))
            {
                prdChunks.emplace_back(prdHist[i], (uint8_t)255);
            }
            else
            {
                prdChunks.emplace_back(blkHist[i], (uint8_t)255);
            }
        }
        vector<uint8_t> prdSplits;
        if (blkMod > 1)
        {
            prdSplits = LZ3_merge_chunks(prdChunks);
        }
        else
        {
            prdSplits = { 0 };
        }
        int64_t prdSize = 0;
        for (const LZ3_chunk_huf& c : prdChunks)
        {
            prdSize += (int64_t)min(c.estimate_size(), c.fallback_size());
        }
        if (prdSize < prdThres && prdSize < bestSize)
        {
            flag = flag | LZ3_compress_flag::LiteralPredict;
            bestSize = prdSize;
            cctx.blockLayout = 0;
            if (prdChunks.size() > 1)
            {
                flag = flag | LZ3_compress_flag::LiteralBlock;
                for (size_t i = 0; i < prdSplits.size(); ++i)
                {
                    if (prdSplits[i] != prdSplits[(i == 0 ? prdSplits.size() : i) - 1])
                    {
                        cctx.blockLayout |= 1 << i;
                    }
                }
            }
            else
            {
                flag = flag ^ LZ3_compress_flag::LiteralBlock;
            }
            vector<vector<uint8_t>> prdStreams(prdChunks.size());
            for (const auto& p : slices)
            {
                for (uint32_t i = p.first; i < p.first + p.second; ++i)
                {
                    uint8_t l = src[i];
                    if (i >= prdDis && (cctx.predictMask & (1 << (i % blkMod))))
                    {
                        l -= src[i - prdDis];
                    }
                    prdStreams[prdSplits[i % blkMod]].push_back(l);
                }
            }
            stream.clear();
            for (const vector<uint8_t>& s : prdStreams)
            {
                stream.insert(stream.end(), s.begin(), s.end());
            }
            chunks = prdChunks;
        }
    }
    while (false);
    //consider well-defined literal patterns(ETC1, ETC2, ASTC)
    for (const LZ3_literal_pattern& lp : lp_list)
    {
        if (lp.blockSize != cctx.blockSize)
        {
            continue;
        }
        uint32_t maxIndex = 0;
        for (const LZ3_layout_pattern& ap : lp.layouts)
        {
            for (const LZ3_chunk_pattern& cp : ap.chunks)
            {
                maxIndex = max(maxIndex, cp.index);
            }
        }
        for (uint32_t blkOff = 0; blkOff < lp.blockSize; ++blkOff)
        {
            LZ3_literal_pattern_sta.clear();
            vector<vector<uint8_t>> lps(maxIndex + 1);
            for (const auto& p : slices)
            {
                if (p.second == 0)
                {
                    continue;
                }
                uint32_t idxPos = p.first;
                uint32_t idxOff = (idxPos - blkOff) % lp.blockSize;
                uint32_t layoutIdx = 0;
                if (lp.layoutSelector != nullptr && idxPos >= idxOff)
                {
                    layoutIdx = lp.layoutSelector(src, idxPos - idxOff);
                }
                uint32_t bitPos = idxPos * 8;
                uint32_t bitEnd = bitPos + p.second * 8;
                while (true)
                {
                    uint32_t bitOff = idxOff * 8;
                    for (const LZ3_chunk_pattern& cp : lp.layouts[layoutIdx].chunks)
                    {
                        for (uint32_t i = 0; i < cp.count; ++i)
                        {
                            if (bitOff >= cp.bits)
                            {
                                bitOff -= cp.bits;
                                continue;
                            }
                            uint32_t l = LZ3_extract_bits(src, bitPos - bitOff, cp.bits);
                            lps[cp.index].push_back((uint8_t)l);
                            bitPos += cp.bits - bitOff;
                            bitOff = 0;
                            if (bitPos >= bitEnd)
                            {
                                break;
                            }
                        }
                    }
                    if (bitPos >= bitEnd)
                    {
                        break;
                    }
                    assert(bitPos % 8 == 0);
                    idxPos = bitPos / 8;
                    idxOff = (idxPos - blkOff) % lp.blockSize;
                    if (lp.layoutSelector != nullptr && idxPos >= idxOff)
                    {
                        layoutIdx = lp.layoutSelector(src, idxPos - idxOff);
                    }
                }
            }
            vector<LZ3_chunk_huf> hufChunk;
            vector<LZ3_chunk_fse> fseChunk;
            int64_t blkSize = 0;
            for (uint32_t i = 0; i <= maxIndex; ++i)
            {
                LZ3_code_hist codeHist;
                uint8_t codeMax = 0;
                for (uint8_t c : lps[i])
                {
                    codeHist.inc_stats(c);
                    codeMax = max(codeMax, c);
                }
                if (codeMax >= 32)
                {
                    hufChunk.emplace_back(codeHist, codeMax);
                    blkSize += min(hufChunk.back().estimate_size(), hufChunk.back().fallback_size());
                }
                else if (codeMax >= 1)
                {
                    fseChunk.emplace_back(codeHist, codeMax);
                    blkSize += min(fseChunk.back().estimate_size(), fseChunk.back().fallback_size());
                }
            }
            if (blkSize < blkThres && blkSize < bestSize)
            {
                bestSize = blkSize;
            }
        }
    }
    return flag;
}

template<
    typename LRawPrice, typename LLenPrice, typename MLenPrice, typename MOffPrice,
    typename LRawStats, typename LLenStats, typename MLenStats, typename MOffStats>
static vector<LZ3_match_info> LZ3_compress_opt(
    const LZ3_suffix_array* psa, const uint8_t* src, size_t srcSize,
    uint32_t max_distance, uint32_t sufficient_length, uint32_t match_count, uint32_t further_offset,
    LRawPrice lRawPrice, LLenPrice lLenPrice, MLenPrice mLenPrice, MOffPrice mOffPrice,
    LRawStats lRawStats, LLenStats lLenStats, MLenStats mLenStats, MOffStats mOffStats)
{
    uint32_t hisSize = psa->n - (uint32_t)srcSize;
    uint32_t srcPos = hisSize;
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
                    auto mop = mOffPrice(match.offset, optimal[0].preOff);
                    if (mop == numeric_limits<decltype(mop)>::max())
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
                    uint32_t lPos = i + j - 1;
                    uint32_t lLen = optimal[j - 1].length == 0 ? optimal[j - 1].literal + 1 : 1;
                    int64_t price = optimal[j - 1].price;
                    price += lRawPrice(lPos, src[lPos]);
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
                lRawStats(srcPos - hisSize, m->literal, src);
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

template<typename ChunkType>
static void LZ3_write_stream(uint8_t*& dst, const uint8_t* src, const vector<ChunkType>& chunks, uint32_t uncompressIntercept, uint32_t uncompressThreshold)
{
    uint8_t* flag = nullptr;
    for (const ChunkType& chunk : chunks)
    {
        *(flag = dst++) = (uint8_t)LZ3_stream_flag::None;
        size_t rSize = chunk.codeHist.size();
        assert(rSize <= numeric_limits<uint16_t>::max());
        do
        {
            size_t bSize = (rSize * chunk.codeBits + 3 + 1 + 7) / 8;
            if (chunk.hSize == 1 && chunk.cSize == 0)
            {
                *flag |= (uint8_t)LZ3_stream_flag::RunLength;
                LZ3_write_LE16(dst, (uint16_t)rSize);
                *dst = chunk.header[0];
                src += rSize;
                dst += 1;
                break;
            }
            if (chunk.estimate_size() + uncompressIntercept < chunk.fallback_size() * uncompressThreshold / 100)
            {
                if LZ3_CONSTEXPRIF(ChunkType::coder() == LZ3_entropy_coder::FSE)
                {
                    size_t cSize = FSE_compress_usingCTable(
                        dst + sizeof(uint16_t) + chunk.hSize, FSE_compressBound(rSize),
                        src, rSize, (const FSE_CTable*)chunk.table);
                    if (!FSE_isError(cSize) && cSize > 0)
                    {
                        cSize += chunk.hSize;
                        if (3 + cSize < 3 + min(rSize, bSize))
                        {
                            *flag |= (uint8_t)LZ3_stream_flag::FSE;
                            LZ3_write_LE16(dst, (uint16_t)cSize);
                            memcpy(dst, chunk.header, chunk.hSize);
                            src += rSize;
                            dst += cSize;
                            break;
                        }
                    }
                }
                if LZ3_CONSTEXPRIF(ChunkType::coder() == LZ3_entropy_coder::Huff0)
                {
                    size_t cSize = HUF_compress4X_usingCTable(
                        dst + sizeof(uint16_t) * 2 + chunk.hSize, HUF_compressBound(rSize),
                        src, rSize, (const HUF_CElt*)chunk.table);
                    if (!HUF_isError(cSize) && cSize > 0)
                    {
                        cSize += chunk.hSize;
                        if (5 + cSize < 3 + min(rSize, bSize))
                        {
                            *flag |= (uint8_t)LZ3_stream_flag::Huff0;
                            LZ3_write_LE16(dst, (uint16_t)cSize);
                            LZ3_write_LE16(dst, (uint16_t)rSize);
                            memcpy(dst, chunk.header, chunk.hSize);
                            src += rSize;
                            dst += cSize;
                            break;
                        }
                    }
                }
            }
            if (3 + bSize < 3 + rSize)
            {
                *flag |= (uint8_t)LZ3_stream_flag::BoundedBits;
                BIT_CStream_t bitStr;
                BIT_initCStream(&bitStr, dst + sizeof(uint16_t), rSize + 1 + sizeof(size_t));
                for (const uint8_t* b = src + rSize - 1; b >= src; --b)
                {
                    BIT_addBitsFast(&bitStr, *b, chunk.codeBits);
                    BIT_flushBits(&bitStr);
                }
                BIT_addBitsFast(&bitStr, chunk.codeBits, 3);
                size_t cSize = BIT_closeCStream(&bitStr);
                assert(cSize == bSize);
                LZ3_write_LE16(dst, (uint16_t)cSize);
                src += rSize;
                dst += cSize;
            }
            else
            {
                *flag |= (uint8_t)LZ3_stream_flag::RawBytes;
                LZ3_write_LE16(dst, (uint16_t)rSize);
                memcpy(dst, src, rSize);
                src += rSize;
                dst += rSize;
            }
        }
        while (false);
    }
    if (flag != nullptr)
    {
        *flag |= (uint8_t)LZ3_stream_flag::EndOfStream;
    }
    else
    {
        *dst++ = (uint8_t)LZ3_stream_flag::EndOfStream;
    }
}

static void LZ3_write_stream(uint8_t*& dst, const uint8_t* src, size_t srcSize, LZ3_entropy_coder coder, uint32_t uncompressIntercept, uint32_t uncompressThreshold)
{
    if (coder == LZ3_entropy_coder::Huff0)
    {
        vector<LZ3_chunk_huf> chunks;
        chunks.emplace_back(src, srcSize);
        LZ3_write_stream<LZ3_chunk_huf>(dst, src, chunks, uncompressIntercept, uncompressThreshold);
        return;
    }
    if (coder == LZ3_entropy_coder::FSE)
    {
        vector<LZ3_chunk_fse> chunks;
        chunks.emplace_back(src, srcSize);
        LZ3_write_stream<LZ3_chunk_fse>(dst, src, chunks, uncompressIntercept, uncompressThreshold);
        return;
    }
}

const size_t LZ3_read_stream(const uint8_t*& src, uint8_t* dst, size_t dstCap, size_t* chunks)
{
    size_t rSize = 0;
    size_t chunkIdx = 0;
    while (true)
    {
        uint8_t flag = *src++;
        do
        {
            if (flag & (uint8_t)LZ3_stream_flag::RawBytes)
            {
                size_t pSize = LZ3_read_LE16(src);
                rSize += pSize;
                memcpy(dst, src, rSize);
                src += rSize;
                dst += rSize;
                chunks[chunkIdx++] = pSize;
                rSize = 0;
                break;
            }
            if (flag & (uint8_t)LZ3_stream_flag::BoundedBits)
            {
                size_t cSize = LZ3_read_LE16(src);
                BIT_DStream_t bitStr;
                BIT_initDStream(&bitStr, src, cSize);
                uint8_t nbBit = (uint8_t)BIT_readBitsFast(&bitStr, 3);
                uint8_t* b = dst;
                while (!BIT_endOfDStream(&bitStr))
                {
                    *b++ = (uint8_t)BIT_readBitsFast(&bitStr, nbBit);
                    BIT_reloadDStream(&bitStr);
                }
                size_t dSize = b - dst;
                src += cSize;
                dst += dSize;
                chunks[chunkIdx++] = dSize - rSize;
                rSize = 0;
                break;
            }
            if (flag & (uint8_t)LZ3_stream_flag::RunLength)
            {
                size_t pSize = LZ3_read_LE16(src);
                rSize += pSize;
                memset(dst, *src, rSize);
                src += 1;
                dst += rSize;
                chunks[chunkIdx++] = pSize;
                rSize = 0;
                break;
            }
            if (flag & (uint8_t)LZ3_stream_flag::Huff0)
            {
                size_t cSize = LZ3_read_LE16(src);
                size_t pSize = LZ3_read_LE16(src);
                rSize += pSize;
                size_t dSize = HUF_decompress(dst, rSize, src, cSize);
                if (HUF_isError(dSize))
                {
                    LZ3_last_error_name = HUF_getErrorName(dSize);
                    return 0;
                }
                src += cSize;
                dst += dSize;
                chunks[chunkIdx++] = pSize;
                rSize = 0;
                break;
            }
            if (flag & (uint8_t)LZ3_stream_flag::FSE)
            {
                size_t cSize = LZ3_read_LE16(src);
                size_t dSize = FSE_decompress(dst, dstCap, src, cSize);
                if (FSE_isError(dSize))
                {
                    LZ3_last_error_name = FSE_getErrorName(dSize);
                    return 0;
                }
                src += cSize;
                dst += dSize;
                chunks[chunkIdx++] = dSize - rSize;
                rSize = 0;
                break;
            }
        }
        while (false);
        if (flag & (uint8_t)LZ3_stream_flag::EndOfStream)
        {
            break;
        }
    }
    return chunkIdx;
}

static const uint8_t* LZ3_read_stream(const uint8_t*& src, uint8_t*& dst, size_t dstCap)
{
    size_t piece[16] = { 0 };
    size_t count = LZ3_read_stream(src, dst, dstCap, piece);
    uint8_t* ptr = dst;
    for (size_t i = 0; i < count; ++i)
    {
        dst += piece[i];
    }
    return ptr;
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
    uint32_t hisSize = psa->n - (uint32_t)srcSize;
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
    uint32_t srcPos = 0;
    vector<LZ3_match_info> matches;
    if (coder == LZ3_entropy_coder::None)
    {
        auto lRawPrice = [](uint32_t i, uint8_t v) { return 8 * LZ3_BIT_COST_MUL; };
        auto nRawStats = [](uint32_t i, uint32_t l, const uint8_t* r) {};
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
        auto mOffPrice1st = [&freq](uint32_t v, uint32_t p[3])
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
        matches = LZ3_compress_opt(psa, src, srcSize,
            cctx.params[LZ3_compress_param::MaxMatchDistance],
            cctx.params[LZ3_compress_param::SufficientMatchLength],
            cctx.params[LZ3_compress_param::MaxMatchCount],
            cctx.params[LZ3_compress_param::MinFurtherOffset],
            lRawPrice, lLenPrice, mLenPrice, mOffPrice1st,
            nRawStats, nLenStats, nLenStats, mOffStats);
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
        sort(dict.begin(), dict.end(), [&freq](uint32_t x, uint32_t y)
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
        auto mOffPrice2nd = [&freq](uint32_t v, uint32_t p[3])
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
        matches = LZ3_compress_opt(psa, src, srcSize,
            cctx.params[LZ3_compress_param::MaxMatchDistance],
            cctx.params[LZ3_compress_param::SufficientMatchLength],
            cctx.params[LZ3_compress_param::MaxMatchCount],
            cctx.params[LZ3_compress_param::MinFurtherOffset],
            lRawPrice, lLenPrice, mLenPrice, mOffPrice2nd,
            nRawStats, nLenStats, nLenStats, nOffStats);
    }
    else
    {
        //init 1st pass code hist
        LZ3_code_hist lRawHist;
        for (uint32_t c = 0; c < 255; ++c)
        {
            lRawHist.inc_stats((uint8_t)c);
        }
        lRawHist.eval_base();
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
        lLenHist.eval_base();
        mLenHist.eval_base();
        mOffHist.eval_base();
        auto lRawPrice = [&lRawHist](uint32_t i,  uint8_t v)
        { 
            return lRawHist.eval_cost(v);
        };
        auto lRawStats = [&lRawHist](uint32_t i, uint32_t l, const uint8_t* r)
        {
            uint32_t e = i + l;
            for (; i < e; ++i)
            {
                lRawHist.inc_stats(r[i]);
            }
            lRawHist.eval_base();
        };
        auto lLenPrice = [&lLenHist](uint32_t v)
        {
            uint8_t c = LZ3_ll_code(v);
            return lLenHist.eval_cost(c) + ll_bits[c] * LZ3_BIT_COST_MUL;
        };
        auto mLenPrice = [&mLenHist](uint32_t v)
        {
            uint8_t c = LZ3_ml_code(v);
            return mLenHist.eval_cost(c) + ml_bits[c] * LZ3_BIT_COST_MUL;
        };
        auto mOffPrice1st = [&mOffHist, &cctx](uint32_t offset, uint32_t preOff[3])
        {
            uint32_t price = 0;
            LZ3_encode_of([&mOffHist, &price](uint8_t c, uint8_t b, uint32_t d) {
                price += mOffHist.eval_cost(c) + b * LZ3_BIT_COST_MUL;
            }, offset, LZ3_compress_flag::OffsetRepeat, preOff, 0, 0, 0, cctx.of_base, cctx.of_bits);
            return price;
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
            LZ3_encode_of([&mOffHist](uint8_t c, uint8_t b, uint32_t d) {
                mOffHist.inc_stats(c);
            }, offset, LZ3_compress_flag::OffsetRepeat, preOff, 0, 0, 0, cctx.of_base, cctx.of_bits);
            mOffHist.eval_base();
        };
        LZ3_init_params(cctx.params, LZ3_CLevel_Min, coder);
        matches = LZ3_compress_opt(psa, src, srcSize,
            cctx.params[LZ3_compress_param::MaxMatchDistance],
            cctx.params[LZ3_compress_param::SufficientMatchLength],
            cctx.params[LZ3_compress_param::MaxMatchCount],
            cctx.params[LZ3_compress_param::MinFurtherOffset],
            lRawPrice, lLenPrice, mLenPrice, mOffPrice1st,
            lRawStats, lLenStats, mLenStats, mOffStats1st);
        copy_n(params, LZ3_compress_param::Count, cctx.params);
        //calc 2nd pass code hist
        cctx.blockLog = 0;
        cctx.lineSize = 0;
        cctx.flag = LZ3_detect_offset_flags(matches, cctx);
        cctx.of_size = LZ3_gen_of_book(cctx.of_base, cctx.of_bits, cctx.flag, cctx.blockLog, cctx.lineSize);
        fill_n(cctx.preOff, 3, 0);
        mOffHist.clear();
        for (const LZ3_match_info& match : matches)
        {
            uint32_t offset = match.offset;
            LZ3_encode_of([&mOffHist](uint8_t c, uint8_t b, uint32_t d) {
                mOffHist.inc_stats(c);
            }, offset, cctx.flag, cctx.preOff, cctx.blockSize, cctx.blockLog, cctx.lineSize, cctx.of_base, cctx.of_bits);
            cctx.preOff[2] = cctx.preOff[1];
            cctx.preOff[1] = cctx.preOff[0];
            cctx.preOff[0] = offset;
        }
        mOffHist.eval_base();
        auto nRawStats = [](uint32_t i, uint32_t l, const uint8_t* r) {};
        auto mOffPrice2nd = [&mOffHist, &cctx](uint32_t offset, uint32_t preOff[3])
        {
            uint32_t price = 0;
            LZ3_encode_of([&mOffHist, &price](uint8_t c, uint8_t b, uint32_t d) {
                price += mOffHist.eval_cost(c) + b * LZ3_BIT_COST_MUL;
            }, offset, cctx.flag, preOff, cctx.blockSize, cctx.blockLog, cctx.lineSize, cctx.of_base, cctx.of_bits);
            return price;
        };
        auto mOffStats2nd = [&mOffHist, &cctx](uint32_t offset, uint32_t preOff[3])
        {
            LZ3_encode_of([&mOffHist](uint8_t c, uint8_t b, uint32_t d) {
                mOffHist.inc_stats(c);
            }, offset, cctx.flag, preOff, cctx.blockSize, cctx.blockLog, cctx.lineSize, cctx.of_base, cctx.of_bits);
            mOffHist.eval_base();
        };
        matches = LZ3_compress_opt(psa, src, srcSize,
            cctx.params[LZ3_compress_param::MaxMatchDistance],
            cctx.params[LZ3_compress_param::SufficientMatchLength],
            cctx.params[LZ3_compress_param::MaxMatchCount],
            cctx.params[LZ3_compress_param::MinFurtherOffset],
            lRawPrice, lLenPrice, mLenPrice, mOffPrice2nd,
            nRawStats, lLenStats, mLenStats, mOffStats2nd);
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
    for (const LZ3_match_info& match : matches)
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
        for (const LZ3_match_info& match : matches)
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
        vector<uint8_t> lrs; //literal raw stream
        vector<pair<uint32_t, uint32_t>> slices; //literal raw slices
        vector<LZ3_chunk_huf> chunks; //literal raw chunks
        vector<uint8_t> lls; //literal length stream
        vector<uint8_t> ofs; //match offset stream
        vector<uint8_t> mls; //match length stream
        vector<pair<uint32_t, uint8_t>> ext; //sequence extend bits
        fill_n(cctx.preOff, 3, 0);
        srcPos = 0;
        for (const LZ3_match_info& match : matches)
        {
            uint32_t position = match.position - hisSize;
            if (position < srcPos)
            {
                continue;
            }
            uint32_t literal = position - srcPos;
            uint32_t length = match.length;
            uint32_t offset = match.offset;
            slices.emplace_back(srcPos, literal);
            LZ3_encode_ll(lls, ext, literal);
            srcPos += literal;
            LZ3_encode_of_wrapper(ofs, ext, offset, cctx);
            LZ3_encode_ml(mls, ext, length);
            srcPos += length;
        }
        if (srcSize > srcPos)
        {
            uint32_t literal = (uint32_t)(srcSize - srcPos);
            slices.emplace_back(srcPos, literal);
            LZ3_encode_ll(lls, ext, literal);
        }
        cctx.flag = cctx.flag | LZ3_detect_literal_flags(src, slices, cctx, lrs, chunks);
        uint8_t* dstPtr = dst;
        *dstPtr++ = (uint8_t)cctx.flag;
        if (cctx.flag & LZ3_compress_flag::OffsetBlock)
        {
            if (cctx.blockSize == (1u << cctx.blockLog))
            {
                assert(cctx.blockLog < 16);
                *dstPtr++ = (uint8_t)(cctx.blockLog & 0xF);
            }
            else
            {
                assert(cctx.blockSize < 16);
                *dstPtr++ = (uint8_t)(cctx.blockSize << 4);
            }
        }
        if (cctx.flag & LZ3_compress_flag::OffsetTwoDim)
        {
            assert(cctx.lineSize <= numeric_limits<uint16_t>::max());
            LZ3_write_LE16(dstPtr, (uint16_t)cctx.lineSize);
        }
        if (cctx.flag & LZ3_compress_flag::LiteralBlock)
        {
            assert(cctx.lineSize <= numeric_limits<uint16_t>::max());
            LZ3_write_LE16(dstPtr, (uint16_t)cctx.blockLayout);
        }
        if (cctx.flag & LZ3_compress_flag::LiteralPredict)
        {
            assert(cctx.lineSize <= numeric_limits<uint16_t>::max());
            LZ3_write_LE16(dstPtr, (uint16_t)cctx.predictMask);
            //TODO by Lysine select&record prdDis
        }
        uint32_t lui = cctx.params[LZ3_compress_param::LitUncompressIntercept];
        uint32_t lut = cctx.params[LZ3_compress_param::LitUncompressThreshold];
        LZ3_write_stream<LZ3_chunk_huf>(dstPtr, lrs.data(), chunks, lui, lut);
        uint32_t sui = cctx.params[LZ3_compress_param::SeqUncompressIntercept];
        uint32_t sut = cctx.params[LZ3_compress_param::SeqUncompressThreshold];
        LZ3_write_stream(dstPtr, lls.data(), lls.size(), coder, sui, sut);
        LZ3_write_stream(dstPtr, ofs.data(), ofs.size(), coder, sui, sut);
        LZ3_write_stream(dstPtr, mls.data(), mls.size(), coder, sui, sut);
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
#if defined(__ARM_NEON) && !defined(LZ3_NO_SIMD) && defined(__aarch64__)
__attribute__((aarch64_vector_pcs))
#endif
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
#if defined(__ARM_NEON) && !defined(LZ3_NO_SIMD) && defined(__aarch64__)
__attribute__((aarch64_vector_pcs))
#endif
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
    LZ3_of_decoder decodeOfWrapper = nullptr;
    LZ3_ls_decoder decodeLsWrapper = nullptr;
    uint8_t* buf = nullptr;
    const uint8_t* lrsPtr = nullptr; //literal raw stream
    const uint8_t* llsPtr = nullptr; //literal length stream
    const uint8_t* ofsPtr = nullptr; //match offset stream
    const uint8_t* mlsPtr = nullptr; //match length stream
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
        dctx.flag = (LZ3_compress_flag)*srcPtr++;
        dctx.blockSize = 1;
        dctx.blockLog = 0;
        dctx.lineSize = 0;
        if (dctx.flag & LZ3_compress_flag::OffsetBlock)
        {
            dctx.blockLog = *srcPtr++;
            if (dctx.blockLog & 0xF)
            {
                dctx.blockSize = 1u << dctx.blockLog;
            }
            else
            {
                dctx.blockSize = dctx.blockLog >> 4;
                dctx.blockLog = LZ3_high_bit_32(dctx.blockSize - 1) + 1;
            }
        }
        if (dctx.flag & LZ3_compress_flag::OffsetTwoDim)
        {
            dctx.lineSize = LZ3_read_LE16(srcPtr);
        }
        dctx.of_size = LZ3_gen_of_book(dctx.of_base, dctx.of_bits, dctx.flag, dctx.blockLog, dctx.lineSize);
        decodeOfWrapper = LZ3_gen_of_decoder(dctx.flag, dctx.blockSize, dctx.lineSize);
        buf = new uint8_t[dstSize * 4];
        uint8_t* bufPtr = buf;
        uint32_t blockLayout = 0;
        uint32_t predictMask = 0;
        if (dctx.flag & LZ3_compress_flag::LiteralBlock)
        {
            blockLayout = LZ3_read_LE16(srcPtr);
        }
        if (dctx.flag & LZ3_compress_flag::LiteralPredict)
        {
            predictMask = LZ3_read_LE16(srcPtr);
        }
        if (dctx.flag & LZ3_compress_flag::LiteralBlock)
        {
            size_t chunks[16] = { 0 };
            size_t count = LZ3_read_stream(srcPtr, bufPtr, dstSize, chunks);
            lrsPtr = bufPtr;
            for (size_t i = 0; i < count; ++i)
            {
                size_t size = chunks[i];
                chunks[i] = bufPtr - lrsPtr;
                bufPtr += size;
            }
            size_t blockEnd = dctx.blockSize;
            if ((blockLayout & 1) == 0)
            {
                blockEnd += LZ3_high_bit_32(blockLayout);
            }
            uintptr_t dstOff = ((uintptr_t)dst) % dctx.blockSize;
            size_t chunkIdx = count;
            size_t blockLen = 0;
            for (size_t i = 0; i < dctx.blockSize; ++i)
            {
                size_t blockIdx = (blockEnd - i - 1) % dctx.blockSize;
                LZ3_block_stream& blockStr = dctx.blockStr[(blockIdx + dstOff) % dctx.blockSize];
                blockStr.length = (uint16_t)(++blockLen);
                blockStr.next = (uint16_t)((blockIdx + dstOff + blockLen) % dctx.blockSize);
                if (blockLayout & (1 << blockIdx))
                {
                    blockStr.position = (uint16_t)(chunks[--chunkIdx]);
                    blockLen = 0;
                }
                else
                {
                    blockStr.position = 0;
                }
            }
            size_t blockHead = 0;
            for (size_t i = 0; i < dctx.blockSize; ++i)
            {
                size_t blockIdx = (blockEnd + i) % dctx.blockSize;
                if (blockLayout & (1 << blockIdx))
                {
                    blockHead = blockIdx;
                }
                LZ3_block_stream& blockStr = dctx.blockStr[(blockIdx + dstOff) % dctx.blockSize];
                blockStr.head = (uint16_t)((blockHead + dstOff) % dctx.blockSize);
            }
        }
        else
        {
            lrsPtr = LZ3_read_stream(srcPtr, bufPtr, dstSize);
        }
        dctx.predictMask = 0;
        dctx.predictDis = 0;
        if (dctx.flag & LZ3_compress_flag::LiteralPredict)
        {
            uintptr_t dstOff = ((uintptr_t)dst) % dctx.blockSize;
            predictMask = (predictMask << dstOff) & ((1 << dctx.blockSize) - 1) | (predictMask >> (dctx.blockSize - dstOff));
            dctx.predictMask = (predictMask << dctx.blockSize) | predictMask;
            dctx.predictDis = 1;
            if (dctx.flag & LZ3_compress_flag::OffsetBlock)
            {
                dctx.predictDis = dctx.blockSize;
            }
            dctx.predictSta = dst + dctx.predictDis;
        }
        else
        {
            dctx.predictSta = dst + dstSize;
        }
        decodeLsWrapper = gen_ls_decoder(dctx.flag, dctx.blockSize, blockLayout, predictMask, dctx.predictDis);
        llsPtr = LZ3_read_stream(srcPtr, bufPtr, dstSize);
        ofsPtr = LZ3_read_stream(srcPtr, bufPtr, dstSize);
        mlsPtr = LZ3_read_stream(srcPtr, bufPtr, dstSize);
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
        if LZ3_LIKELY(literal <= min(wild_copy_length, coder == LZ3_entropy_coder::None ? 0xEu : 0xFu))
        {
            uint8_t* cpyEnd = dstPtr + literal;
            assert(cpyEnd <= dstEnd);
            //TODO by Lysine: copy literal may read beyond source/stream end
            if (coder == LZ3_entropy_coder::None)
            {
                if LZ3_UNLIKELY(dstPtr >= dstShortEnd)
                {
                    goto safe_copy_literal;
                }
                memcpy(dstPtr, srcPtr, wild_copy_length);
                srcPtr += literal;
            }
            else if (decodeLsWrapper == nullptr)
            {
                if LZ3_UNLIKELY(dstPtr >= dstShortEnd)
                {
                    goto safe_copy_literal;
                }
                memcpy(dstPtr, lrsPtr, wild_copy_length);
                lrsPtr += literal;
            }
            else
            {
                if LZ3_UNLIKELY(cpyEnd >= dstShortEnd)
                {
                    goto safe_copy_literal;
                }
                LZ3_decode_ls_result result = decodeLsWrapper(dstPtr, lrsPtr, literal, dctx);
                lrsPtr = result.getSrcPtr(lrsPtr);
            }
            dstPtr = cpyEnd;
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
            uint8_t* cpyEnd = dstPtr + literal;
            assert(cpyEnd <= dstEnd);
            if (coder == LZ3_entropy_coder::None)
            {
                LZ3_safe_copy<wild_copy_length>(dstPtr, cpyEnd, dstShortEnd, srcPtr);
                srcPtr += literal;
            }
            else if (decodeLsWrapper == nullptr)
            {
                LZ3_safe_copy<wild_copy_length>(dstPtr, cpyEnd, dstShortEnd, lrsPtr);
                lrsPtr += literal;
            }
            else if (cpyEnd <= dstShortEnd)
            {
                LZ3_decode_ls_result result = decodeLsWrapper(dstPtr, lrsPtr, literal, dctx);
                lrsPtr = result.getSrcPtr(srcPtr);
            }
            else
            {
                LZ3_decode_ls_result result;
                if (dstPtr < dstShortEnd)
                {
                    result = decodeLsWrapper(dstPtr, lrsPtr, dstShortEnd - dstPtr, dctx);
                    lrsPtr = result.getSrcPtr(lrsPtr);
                    dstPtr = dstShortEnd;
                }
                result = LZ3_decode_ls_safe(dstPtr, lrsPtr, cpyEnd - dstPtr, dctx);
                lrsPtr = result.getSrcPtr(lrsPtr);
            }
            dstPtr = cpyEnd;
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
        if LZ3_LIKELY(length <= min(wild_copy_length - min_match_length, coder == LZ3_entropy_coder::None ? 0xEu : 0x1Fu))
        {
            length += min_match_length;
            if LZ3_UNLIKELY(dstPtr >= dstShortEnd || offset < 8)
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

template<LZ3_entropy_coder coder>
uint32_t LZ3_compress_continue_generic(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level);

template<LZ3_entropy_coder coder>
uint32_t LZ3_decompress_split_fast_generic(const void* src, void* dst, uint32_t dstSize);

template<LZ3_entropy_coder coder>
uint32_t LZ3_decompress_fast_continue_generic(LZ3_DStream* pds, const void* src, void* dst, uint32_t dstSize);

template<LZ3_entropy_coder coder>
uint32_t LZ3_compress_split_generic(const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level)
{
    uint32_t dstPos;
    if (srcSize <= LZ3_MAX_BLOCK_SIZE)
    {
        uint32_t params[LZ3_compress_param::Count];
        LZ3_init_params(params, level, coder);
        LZ3_suffix_array* psa = new LZ3_suffix_array(srcSize);
        dstPos = (uint32_t)LZ3_compress_generic<coder>((const uint8_t*)src, (uint8_t*)dst, srcSize, params, nullptr, psa);
        delete psa;
    }
    else
    {
        LZ3_CStream* pcs = LZ3_createCStream();
        dstPos = LZ3_compress_continue_generic<coder>(pcs, src, dst, srcSize, level);
        LZ3_freeCStream(pcs);
    }
#if !defined(NDEBUG) && defined(LZ3_CHK_DEC)
    vector<uint8_t> buf(srcSize);
    size_t chkPos = LZ3_decompress_split_fast_generic<coder>(dst, buf.data(), srcSize);
    assert(chkPos == dstPos);
    for (size_t i = 0; i < srcSize; ++i)
    {
        assert(buf[i] == ((const uint8_t*)src)[i]);
    }
#endif
    return dstPos;
}

template<LZ3_entropy_coder coder>
uint32_t LZ3_decompress_split_fast_generic(const void* src, void* dst, uint32_t dstSize)
{
    uint32_t srcPos;
    if (dstSize < LZ3_MAX_BLOCK_SIZE)
    {
        srcPos = (uint32_t)LZ3_decompress_generic<coder, LZ3_history_pos::Prefix>((const uint8_t*)src, (uint8_t*)dst, dstSize, 0, nullptr, 0);
    }
    else
    {
        LZ3_DStream* pds = LZ3_createDStream();
        srcPos = LZ3_decompress_fast_continue_generic<coder>(pds, src, dst, dstSize);
        LZ3_freeDStream(pds);
    }
    return srcPos;
}

uint32_t LZ3_compress(const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level)
{
    return LZ3_compress_split_generic<LZ3_entropy_coder::None>(src, dst, srcSize, level);
}

uint32_t LZ3_decompress_fast(const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_split_fast_generic<LZ3_entropy_coder::None>(src, dst, dstSize);
}

uint32_t LZ3_compress_HUF(const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level)
{
    return LZ3_compress_split_generic<LZ3_entropy_coder::Huff0>(src, dst, srcSize, level);
}

uint32_t LZ3_decompress_HUF_fast(const void* src, void* dst, uint32_t dstSize)
{
    return LZ3_decompress_split_fast_generic<LZ3_entropy_coder::Huff0>(src, dst, dstSize);
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
