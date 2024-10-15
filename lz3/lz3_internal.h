#pragma once

#include <stdint.h>
#include <string.h>

#if defined(__GNUC__) || defined(__clang__)
#define LZ3_FORCE_INLINE      inline __attribute__((always_inline))
#define LZ3_ALIGNED(size)     __attribute__((aligned(size)))
#define LZ3_LIKELY(expr)      (__builtin_expect(!!(expr), 1))
#define LZ3_UNLIKELY(expr)    (__builtin_expect(!!(expr), 0))
#define LZ3_UNREACHABLE       __builtin_unreachable()
#define LZ3_HIGH_BIT_32(expr) ((uint8_t)(31 - __builtin_clz((uint32_t)(expr))))
#elif defined(_MSC_VER)
#define LZ3_FORCE_INLINE      __forceinline
#define LZ3_ALIGNED(size)     __declspec(align(size))
#define LZ3_UNREACHABLE       __assume(0)
#include <intrin.h>
LZ3_FORCE_INLINE uint8_t LZ3_high_bit_32(uint32_t v)
{
    unsigned long r;
    _BitScanReverse(&r, v);
    return (uint8_t)r;
}
#define LZ3_HIGH_BIT_32(expr) LZ3_high_bit_32((uint32_t)(expr))
#endif
#if !defined(LZ3_FORCE_INLINE)
#define LZ3_FORCE_INLINE      inline
#endif
#if !defined(LZ3_ALIGNED)
#define LZ3_ALIGNED(size)
#endif
#if !defined(LZ3_IFCONSTEXPR)
#if __cplusplus >= 201703L
#define LZ3_CONSTEXPRIF(expr) constexpr(expr)
#else
#define LZ3_CONSTEXPRIF(expr) (expr)
#endif
#endif
#if !defined(LZ3_LIKELY) && !defined(LZ3_UNLIKELY)
#if __cplusplus >= 202002L
#define LZ3_LIKELY(expr)      (expr) [[likely]]
#define LZ3_UNLIKELY(expr)    (expr) [[unlikely]]
#else
#define LZ3_LIKELY(expr)      (expr)
#define LZ3_UNLIKELY(expr)    (expr)
#endif
#endif
#if !defined(LZ3_UNREACHABLE)
#define LZ3_UNREACHABLE
#endif
#if !defined(LZ3_HIGH_BIT_32)
LZ3_FORCE_INLINE uint8_t LZ3_high_bit_32(uint32_t v)
{
    static constexpr uint8_t DeBruijnClz[32] = { 0, 9, 1, 10, 13, 21, 2, 29, 11, 14, 16, 18, 22, 25, 3, 30, 8, 12, 20, 28, 15, 17, 24, 7, 19, 27, 23, 6, 26, 5, 4, 31 };
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    return DeBruijnClz[(v * 0x07C4ACDDU) >> 27];
}
#define LZ3_HIGH_BIT_32(expr) LZ3_high_bit_32((uint32_t)(expr))
#endif

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
