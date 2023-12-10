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

typedef struct LZ3_CStream LZ3_CStream;

typedef struct LZ3_DStream LZ3_DStream;

LZ3_CStream* LZ3_createCStream();

LZ3_DStream* LZ3_createDStream();

void LZ3_freeCStream(LZ3_CStream* pcs);

void LZ3_freeDStream(LZ3_DStream* pds);

uint32_t LZ3_compress_continue(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize);

uint32_t LZ3_decompress_continue(LZ3_DStream* pcs, const void* src, void* dst, uint32_t dstSize);

uint32_t LZ3_compress_HUF_continue(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize);

uint32_t LZ3_decompress_HUF_continue(LZ3_DStream* pcs, const void* src, void* dst, uint32_t dstSize);

#if defined (__cplusplus)
}
#endif