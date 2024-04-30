#pragma once

#include <stdint.h>

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

#ifndef LZ3_MAX_BLOCK_SIZE
#define LZ3_MAX_BLOCK_SIZE 0xFF81u
#endif 

#ifndef LZ3_DISTANCE_MAX
#define LZ3_DISTANCE_MAX 0x7FFFu
#endif 

#ifndef LZ3_HUF_DISTANCE_MAX
#define LZ3_HUF_DISTANCE_MAX 0x1FFFFu
#endif 

 typedef enum LZ3_CLevel
 {
     LZ3_CLevel_Min     = 1,
     LZ3_CLevel_Fast    = 3,
     LZ3_CLevel_Normal  = 5,
     LZ3_CLevel_Optimal = 7,
     LZ3_CLevel_Max     = 9,
 } LZ3_CLevel;

LZ3_API uint32_t LZ3_compress(const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level);

LZ3_API uint32_t LZ3_decompress_fast(const void* src, void* dst, uint32_t dstSize);

LZ3_API uint32_t LZ3_compress_HUF(const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level);

LZ3_API uint32_t LZ3_decompress_HUF_fast(const void* src, void* dst, uint32_t dstSize);

typedef struct LZ3_CStream LZ3_CStream;

typedef struct LZ3_DStream LZ3_DStream;

LZ3_API LZ3_CStream* LZ3_createCStream();

LZ3_API LZ3_DStream* LZ3_createDStream();

LZ3_API void LZ3_freeCStream(LZ3_CStream* pcs);

LZ3_API void LZ3_freeDStream(LZ3_DStream* pds);

LZ3_API uint32_t LZ3_compress_continue(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level);

LZ3_API uint32_t LZ3_decompress_continue(LZ3_DStream* pcs, const void* src, void* dst, uint32_t dstSize);
LZ3_API uint32_t LZ3_decompress_fast_continue(LZ3_DStream* pcs, const void* src, void* dst, uint32_t dstSize);

LZ3_API uint32_t LZ3_compress_HUF_continue(LZ3_CStream* pcs, const void* src, void* dst, uint32_t srcSize, LZ3_CLevel level);

LZ3_API uint32_t LZ3_decompress_HUF_continue(LZ3_DStream* pcs, const void* src, void* dst, uint32_t dstSize);
LZ3_API uint32_t LZ3_decompress_HUF_fast_continue(LZ3_DStream* pcs, const void* src, void* dst, uint32_t dstSize);

#if defined (__cplusplus)
}
#endif