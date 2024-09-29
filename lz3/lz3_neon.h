#pragma once

#include <stdint.h>
#include <arm_neon.h>

inline void LZ3_1x16_copy(uint8_t* dst, const uint8_t** src)
{
    uint8x16_t buf;
    buf = vld1q_lane_u8(src[0x0], buf, 0x0);
    buf = vld1q_lane_u8(src[0x1], buf, 0x1);
    buf = vld1q_lane_u8(src[0x2], buf, 0x2);
    buf = vld1q_lane_u8(src[0x3], buf, 0x3);
    buf = vld1q_lane_u8(src[0x4], buf, 0x4);
    buf = vld1q_lane_u8(src[0x5], buf, 0x5);
    buf = vld1q_lane_u8(src[0x6], buf, 0x6);
    buf = vld1q_lane_u8(src[0x7], buf, 0x7);
    buf = vld1q_lane_u8(src[0x8], buf, 0x8);
    buf = vld1q_lane_u8(src[0x9], buf, 0x9);
    buf = vld1q_lane_u8(src[0xA], buf, 0xA);
    buf = vld1q_lane_u8(src[0xB], buf, 0xB);
    buf = vld1q_lane_u8(src[0xC], buf, 0xC);
    buf = vld1q_lane_u8(src[0xD], buf, 0xD);
    buf = vld1q_lane_u8(src[0xE], buf, 0xE);
    buf = vld1q_lane_u8(src[0xF], buf, 0xF);
    vst1q_u8(dst, buf);
}

inline void LZ3_2x16_copy(uint8_t* dst, const uint8_t** src)
{
    uint8x16x2_t buf;
    buf = vld2q_lane_u8(src[0x0], buf, 0x0);
    buf = vld2q_lane_u8(src[0x1], buf, 0x1);
    buf = vld2q_lane_u8(src[0x2], buf, 0x2);
    buf = vld2q_lane_u8(src[0x3], buf, 0x3);
    buf = vld2q_lane_u8(src[0x4], buf, 0x4);
    buf = vld2q_lane_u8(src[0x5], buf, 0x5);
    buf = vld2q_lane_u8(src[0x6], buf, 0x6);
    buf = vld2q_lane_u8(src[0x7], buf, 0x7);
    buf = vld2q_lane_u8(src[0x8], buf, 0x8);
    buf = vld2q_lane_u8(src[0x9], buf, 0x9);
    buf = vld2q_lane_u8(src[0xA], buf, 0xA);
    buf = vld2q_lane_u8(src[0xB], buf, 0xB);
    buf = vld2q_lane_u8(src[0xC], buf, 0xC);
    buf = vld2q_lane_u8(src[0xD], buf, 0xD);
    buf = vld2q_lane_u8(src[0xE], buf, 0xE);
    buf = vld2q_lane_u8(src[0xF], buf, 0xF);
    vst1q_u8(dst + 0x00, buf.val[0]);
    vst1q_u8(dst + 0x10, buf.val[1]);
}

inline void LZ3_3x16_copy(uint8_t* dst, const uint8_t** src)
{
    uint8x16x3_t buf;
    buf = vld3q_lane_u8(src[0x0], buf, 0x0);
    buf = vld3q_lane_u8(src[0x1], buf, 0x1);
    buf = vld3q_lane_u8(src[0x2], buf, 0x2);
    buf = vld3q_lane_u8(src[0x3], buf, 0x3);
    buf = vld3q_lane_u8(src[0x4], buf, 0x4);
    buf = vld3q_lane_u8(src[0x5], buf, 0x5);
    buf = vld3q_lane_u8(src[0x6], buf, 0x6);
    buf = vld3q_lane_u8(src[0x7], buf, 0x7);
    buf = vld3q_lane_u8(src[0x8], buf, 0x8);
    buf = vld3q_lane_u8(src[0x9], buf, 0x9);
    buf = vld3q_lane_u8(src[0xA], buf, 0xA);
    buf = vld3q_lane_u8(src[0xB], buf, 0xB);
    buf = vld3q_lane_u8(src[0xC], buf, 0xC);
    buf = vld3q_lane_u8(src[0xD], buf, 0xD);
    buf = vld3q_lane_u8(src[0xE], buf, 0xE);
    buf = vld3q_lane_u8(src[0xF], buf, 0xF);
    vst1q_u8(dst + 0x00, buf.val[0]);
    vst1q_u8(dst + 0x10, buf.val[1]);
    vst1q_u8(dst + 0x20, buf.val[2]);
}

inline void LZ3_4x16_copy(uint8_t* dst, const uint8_t** src)
{
    uint8x16x4_t buf;
    buf = vld4q_lane_u8(src[0x0], buf, 0x0);
    buf = vld4q_lane_u8(src[0x1], buf, 0x1);
    buf = vld4q_lane_u8(src[0x2], buf, 0x2);
    buf = vld4q_lane_u8(src[0x3], buf, 0x3);
    buf = vld4q_lane_u8(src[0x4], buf, 0x4);
    buf = vld4q_lane_u8(src[0x5], buf, 0x5);
    buf = vld4q_lane_u8(src[0x6], buf, 0x6);
    buf = vld4q_lane_u8(src[0x7], buf, 0x7);
    buf = vld4q_lane_u8(src[0x8], buf, 0x8);
    buf = vld4q_lane_u8(src[0x9], buf, 0x9);
    buf = vld4q_lane_u8(src[0xA], buf, 0xA);
    buf = vld4q_lane_u8(src[0xB], buf, 0xB);
    buf = vld4q_lane_u8(src[0xC], buf, 0xC);
    buf = vld4q_lane_u8(src[0xD], buf, 0xD);
    buf = vld4q_lane_u8(src[0xE], buf, 0xE);
    buf = vld4q_lane_u8(src[0xF], buf, 0xF);
    vst1q_u8(dst + 0x00, buf.val[0]);
    vst1q_u8(dst + 0x10, buf.val[1]);
    vst1q_u8(dst + 0x20, buf.val[2]);
    vst1q_u8(dst + 0x30, buf.val[3]);
}
