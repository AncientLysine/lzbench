#pragma once

#include <cstdint>

#if defined (__cplusplus)
extern "C" {
#endif

#ifdef LZ3_SHARED

#ifdef _WIN32

#ifdef LZ3_LIBRARY
#define LZ3_API __declspec(dllexport)
#else
#define LZ3_API __declspec(dllimport)
#endif

#else

#ifdef LZ3_LIBRARY
#define LZ3_API __attribute__((visibility("default")))
#else
#define LZ3_API
#endif

#endif

#else

#define LZ3_API

#endif

LZ3_API uint32_t LZ3_compress(const void* src, void* dst, uint32_t srcSize);

LZ3_API uint32_t LZ3_decompress_fast(const void* src, void* dst, uint32_t dstSize);

LZ3_API uint32_t LZ3_compress_HUF(const void* src, void* dst, uint32_t srcSize);

LZ3_API uint32_t LZ3_decompress_HUF_fast(const void* src, void* dst, uint32_t dstSize);

#if defined (__cplusplus)
}
#endif