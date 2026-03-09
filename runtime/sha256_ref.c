/*
 * sha256_ref.c — C reference SHA-256 (FIPS 180-4) for cycle-count comparison
 *
 * Provides Lean FFI wrappers that hash hardcoded messages, print the result
 * via UART, and return the cycle count as UInt64.
 *
 * Three input sizes:
 *   lean_c_sha256_bench_3   — "abc"  (3 bytes, 1 block)
 *   lean_c_sha256_bench_64  — 64 bytes (2 blocks after padding)
 *   lean_c_sha256_bench_256 — 256 bytes (5 blocks after padding)
 */

#include <stdint.h>
#include <stddef.h>
#include "lean_rt.h"
#include "uart.h"

/* ---- SHA-256 constants ---- */

static const uint32_t K[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

static const uint32_t H0[8] = {
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};

/* ---- Helpers ---- */

#define ROTR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))
#define CH(x,y,z)  (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x,y,z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define BSIG0(x)   (ROTR(x, 2) ^ ROTR(x,13) ^ ROTR(x,22))
#define BSIG1(x)   (ROTR(x, 6) ^ ROTR(x,11) ^ ROTR(x,25))
#define SSIG0(x)   (ROTR(x, 7) ^ ROTR(x,18) ^ ((x) >> 3))
#define SSIG1(x)   (ROTR(x,17) ^ ROTR(x,19) ^ ((x) >> 10))

static inline uint32_t be32(const uint8_t *p)
{
    return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16)
         | ((uint32_t)p[2] << 8)  |  (uint32_t)p[3];
}

static inline void put_be32(uint8_t *p, uint32_t v)
{
    p[0] = (uint8_t)(v >> 24);
    p[1] = (uint8_t)(v >> 16);
    p[2] = (uint8_t)(v >> 8);
    p[3] = (uint8_t)v;
}

/* ---- Core SHA-256 ---- */

static void sha256_ref(const uint8_t *msg, size_t len, uint8_t digest[32])
{
    uint32_t h[8];
    for (int i = 0; i < 8; i++)
        h[i] = H0[i];

    /* Padding: append 0x80, zeros, 64-bit big-endian bit length */
    size_t bit_len = len * 8;
    /* total padded length = next multiple of 64 after len+1+8 */
    size_t padded_len = ((len + 9 + 63) / 64) * 64;

    /* Process 64-byte blocks */
    for (size_t off = 0; off < padded_len; off += 64) {
        uint8_t block[64];
        for (size_t i = 0; i < 64; i++) {
            size_t pos = off + i;
            if (pos < len)
                block[i] = msg[pos];
            else if (pos == len)
                block[i] = 0x80;
            else if (pos < padded_len - 8)
                block[i] = 0x00;
            else {
                /* big-endian 64-bit bit length in last 8 bytes */
                int shift = (int)(7 - (pos - (padded_len - 8))) * 8;
                block[i] = (uint8_t)(bit_len >> shift);
            }
        }

        /* Message schedule */
        uint32_t w[64];
        for (int i = 0; i < 16; i++)
            w[i] = be32(&block[i * 4]);
        for (int i = 16; i < 64; i++)
            w[i] = SSIG1(w[i-2]) + w[i-7] + SSIG0(w[i-15]) + w[i-16];

        /* Compression */
        uint32_t a = h[0], b = h[1], c = h[2], d = h[3];
        uint32_t e = h[4], f = h[5], g = h[6], hh = h[7];

        for (int i = 0; i < 64; i++) {
            uint32_t t1 = hh + BSIG1(e) + CH(e,f,g) + K[i] + w[i];
            uint32_t t2 = BSIG0(a) + MAJ(a,b,c);
            hh = g; g = f; f = e; e = d + t1;
            d = c; c = b; b = a; a = t1 + t2;
        }

        h[0] += a; h[1] += b; h[2] += c; h[3] += d;
        h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
    }

    for (int i = 0; i < 8; i++)
        put_be32(&digest[i * 4], h[i]);
}

/* ---- UART hex output ---- */

static const char hex_chars[] = "0123456789abcdef";

static void uart_put_hex_digest(const uint8_t digest[32])
{
    for (int i = 0; i < 32; i++) {
        uart_putc(hex_chars[digest[i] >> 4]);
        uart_putc(hex_chars[digest[i] & 0x0f]);
    }
}

/* ---- Generic bench helper ---- */

static uint64_t bench_sha256(const uint8_t *msg, size_t len, const char *label)
{
    uint8_t digest[32];
    uint64_t t0, t1;
    __asm__ volatile("rdcycle %0" : "=r"(t0));
    sha256_ref(msg, len, digest);
    __asm__ volatile("rdcycle %0" : "=r"(t1));

    uart_puts(label);
    uart_put_hex_digest(digest);
    uart_puts("\n  cycles: ");
    uart_put_dec((long)(t1 - t0));
    uart_puts("\n");
    return t1 - t0;
}

/* ---- Test inputs ---- */

/* 64-byte message: 0x00..0x3f */
static const uint8_t msg_64[64] = {
    0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
    0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,
    0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,
    0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
    0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,
    0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
    0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,
    0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f
};

/* 256-byte message: 0x00..0xff */
static const uint8_t msg_256[256] = {
    0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
    0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,
    0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,
    0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
    0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,
    0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
    0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,
    0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,
    0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,
    0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f,
    0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,
    0x58,0x59,0x5a,0x5b,0x5c,0x5d,0x5e,0x5f,
    0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,
    0x68,0x69,0x6a,0x6b,0x6c,0x6d,0x6e,0x6f,
    0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,
    0x78,0x79,0x7a,0x7b,0x7c,0x7d,0x7e,0x7f,
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,
    0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,
    0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f,
    0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7,
    0xa8,0xa9,0xaa,0xab,0xac,0xad,0xae,0xaf,
    0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7,
    0xb8,0xb9,0xba,0xbb,0xbc,0xbd,0xbe,0xbf,
    0xc0,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7,
    0xc8,0xc9,0xca,0xcb,0xcc,0xcd,0xce,0xcf,
    0xd0,0xd1,0xd2,0xd3,0xd4,0xd5,0xd6,0xd7,
    0xd8,0xd9,0xda,0xdb,0xdc,0xdd,0xde,0xdf,
    0xe0,0xe1,0xe2,0xe3,0xe4,0xe5,0xe6,0xe7,
    0xe8,0xe9,0xea,0xeb,0xec,0xed,0xee,0xef,
    0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,
    0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe,0xff
};

/* ---- Lean SHA-256 timing wrapper ---- */

/*
 * Call the Lean-generated l_sha256 with rdcycle timing.
 * Declared weak so non-sha256 examples link without error (resolves to NULL).
 * Returns Prod (Array UInt32) UInt64 = ctor(tag=0, obj[0]=digest, obj[1]=boxed_cycles).
 */
extern lean_object *l_sha256(lean_object *) __attribute__((weak));

lean_object *lean_sha256_timed(lean_object *msg, lean_object *w)
{
    (void)w;
    uint64_t t0, t1;
    __asm__ volatile("rdcycle %0" : "=r"(t0));
    lean_object *digest = l_sha256(msg);
    __asm__ volatile("rdcycle %0" : "=r"(t1));
    uint64_t cycles = t1 - t0;
    lean_object *bcycles = lean_box_uint64(cycles);
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, digest);
    lean_ctor_set(pair, 1, bcycles);
    return lean_io_result_mk_ok(pair);
}

/* ---- Lean FFI wrappers ---- */

lean_object *lean_c_sha256_bench_3(lean_object *w)
{
    (void)w;
    static const uint8_t msg[] = {0x61, 0x62, 0x63}; /* "abc" */
    uint64_t cycles = bench_sha256(msg, 3, "C ref:    ");
    return lean_io_result_mk_ok(lean_box_uint64(cycles));
}

lean_object *lean_c_sha256_bench_64(lean_object *w)
{
    (void)w;
    uint64_t cycles = bench_sha256(msg_64, 64, "C ref:    ");
    return lean_io_result_mk_ok(lean_box_uint64(cycles));
}

lean_object *lean_c_sha256_bench_256(lean_object *w)
{
    (void)w;
    uint64_t cycles = bench_sha256(msg_256, 256, "C ref:    ");
    return lean_io_result_mk_ok(lean_box_uint64(cycles));
}
