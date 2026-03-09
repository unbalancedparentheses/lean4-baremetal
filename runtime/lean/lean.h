/*
 * lean/lean.h — Shim header for freestanding Lean 4 runtime
 *
 * The Lean compiler generates C code with `#include <lean/lean.h>`.
 * This file redirects to our freestanding runtime replacement.
 * The Makefile adds `-Iruntime` so this file is found instead of the real lean.h.
 */

#ifndef LEAN_LEAN_H
#define LEAN_LEAN_H

#include <stdbool.h>
#include "lean_rt.h"

/* ---- Object tag accessor ---- */

static inline uint8_t lean_obj_tag(lean_object *o) {
    if (lean_is_scalar(o)) return (uint8_t)(lean_unbox(o) & 0xFF);
    return o->m_tag;
}

/* ---- Compatibility macros ---- */

/* The generated code may use these attributes */
#ifndef LEAN_EXPORT
#define LEAN_EXPORT __attribute__((visibility("default")))
#endif

#ifndef LEAN_INLINE
#define LEAN_INLINE static inline
#endif

/* Thread-local storage — on bare-metal, just globals */
#define LEAN_THREAD_VALUE(type, name, default_val) static type name = default_val
#define LEAN_THREAD_PTR(type, name) static type *name = (type *)0

/* Multi-threading checks — always single-threaded */
#define lean_is_mt_heap() 0

/* Object size helper used in generated code */
static inline size_t lean_object_byte_size(lean_object *o) {
    /* For small objects, cs_sz stores the size */
    if (o->m_cs_sz != 0)
        return o->m_cs_sz;
    /* Fallback: compute based on tag */
    uint8_t tag = o->m_tag;
    if (tag <= 243) {
        unsigned num_objs = o->m_other;
        return sizeof(lean_ctor_object) + num_objs * sizeof(lean_object *);
    } else if (tag == LeanClosure) {
        lean_closure_object *c = (lean_closure_object *)o;
        return sizeof(lean_closure_object) + c->m_num_fixed * sizeof(lean_object *);
    } else if (tag == LeanArray) {
        lean_array_object *a = (lean_array_object *)o;
        return sizeof(lean_array_object) + a->m_capacity * sizeof(lean_object *);
    } else if (tag == LeanString) {
        lean_string_object *s = (lean_string_object *)o;
        return sizeof(lean_string_object) + s->m_capacity;
    }
    return sizeof(lean_object);
}

/* Task stubs — single-threaded bare-metal */
static inline lean_object *lean_task_spawn(lean_object *c, lean_object *prio) {
    (void)prio;
    /* Execute synchronously */
    lean_object *val = lean_apply_1(c, lean_box(0));
    /* Wrap in a "task" that's just the value */
    return val;
}

static inline lean_object *lean_task_pure(lean_object *a) {
    return a;
}

static inline lean_object *lean_task_get(lean_object *t) {
    lean_inc(t);
    return t;
}

static inline lean_object *lean_task_get_own(lean_object *t) {
    return t;
}

static inline lean_object *lean_task_bind(lean_object *x, lean_object *f, lean_object *prio, uint8_t sync) {
    (void)prio; (void)sync;
    lean_object *val = lean_task_get_own(x);
    return lean_apply_2(f, val, lean_box(0));
}

static inline lean_object *lean_task_map(lean_object *f, lean_object *t, lean_object *prio, uint8_t sync) {
    (void)prio; (void)sync;
    lean_object *val = lean_task_get_own(t);
    return lean_apply_1(f, val);
}

/* Environment (used by generated init code) */
static inline lean_object *lean_mk_empty_environment(uint32_t trust_level) {
    (void)trust_level;
    return lean_box(0);
}

/* Set/Get exit code stubs */
static inline lean_object *lean_io_prim_set_exit_code(lean_object *code, lean_object *w) {
    (void)code; (void)w;
    return lean_io_result_mk_ok(lean_box(0));
}

/* Access current random seed stub */
static inline lean_object *lean_io_prim_rand_nat(lean_object *lo, lean_object *hi, lean_object *w) {
    (void)w;
    /* Return lo as a stub */
    lean_dec(hi);
    return lean_io_result_mk_ok(lo);
}

/* lean_dbg_trace: debug printing */
static inline lean_object *lean_dbg_trace(lean_object *s, lean_object *fn) {
    extern void uart_puts(const char *);
    if (!lean_is_scalar(s) && s->m_tag == LeanString)
        uart_puts(lean_string_cstr(s));
    uart_puts("\n");
    lean_dec(s);
    return lean_apply_1(fn, lean_box(0));
}

/* lean_dbg_trace_if_shared: only prints if object is shared */
static inline lean_object *lean_dbg_trace_if_shared(lean_object *s, lean_object *fn) {
    lean_dec(s);
    return lean_apply_1(fn, lean_box(0));
}

/* String decidable equality */
static inline uint8_t lean_string_dec_eq(lean_object *s1, lean_object *s2) {
    return lean_string_eq(s1, s2);
}

static inline uint8_t lean_string_dec_lt(lean_object *s1, lean_object *s2) {
    return lean_string_lt(s1, s2);
}

/* Nat decidable comparison helpers */
static inline uint8_t lean_nat_dec_eq(lean_object *a, lean_object *b) {
    if (lean_is_scalar(a) && lean_is_scalar(b))
        return a == b;
    return 0; /* big nats: not supported */
}

static inline uint8_t lean_nat_dec_lt(lean_object *a, lean_object *b) {
    if (lean_is_scalar(a) && lean_is_scalar(b))
        return lean_unbox(a) < lean_unbox(b);
    return 0;
}

static inline uint8_t lean_nat_dec_le(lean_object *a, lean_object *b) {
    if (lean_is_scalar(a) && lean_is_scalar(b))
        return lean_unbox(a) <= lean_unbox(b);
    return 0;
}

/* Nat arithmetic helpers */
static inline lean_object *lean_nat_add(lean_object *a, lean_object *b) {
    if (lean_is_scalar(a) && lean_is_scalar(b))
        return lean_box(lean_unbox(a) + lean_unbox(b));
    return lean_nat_big_add(a, b);
}

static inline lean_object *lean_nat_sub(lean_object *a, lean_object *b) {
    if (lean_is_scalar(a) && lean_is_scalar(b)) {
        size_t va = lean_unbox(a), vb = lean_unbox(b);
        return lean_box(va >= vb ? va - vb : 0);
    }
    return lean_nat_big_sub(a, b);
}

static inline lean_object *lean_nat_mul(lean_object *a, lean_object *b) {
    if (lean_is_scalar(a) && lean_is_scalar(b))
        return lean_box(lean_unbox(a) * lean_unbox(b));
    return lean_nat_big_mul(a, b);
}

static inline lean_object *lean_nat_div(lean_object *a, lean_object *b) {
    if (lean_is_scalar(a) && lean_is_scalar(b)) {
        size_t vb = lean_unbox(b);
        if (vb == 0) return lean_box(0);
        return lean_box(lean_unbox(a) / vb);
    }
    return lean_nat_big_div(a, b);
}

static inline lean_object *lean_nat_mod(lean_object *a, lean_object *b) {
    if (lean_is_scalar(a) && lean_is_scalar(b)) {
        size_t vb = lean_unbox(b);
        if (vb == 0) return a;
        return lean_box(lean_unbox(a) % vb);
    }
    return lean_nat_big_mod(a, b);
}

static inline lean_object *lean_nat_succ(lean_object *a) {
    if (lean_is_scalar(a))
        return lean_box(lean_unbox(a) + 1);
    return lean_nat_big_succ(a);
}

/* Lean uses lean_alloc_small for small objects in optimized mode */
static inline lean_object *lean_alloc_small(size_t sz, unsigned cls) {
    (void)cls;
    return lean_alloc_object(sz);
}

static inline void lean_free_small(lean_object *o) {
    lean_free_object(o);
}

/* lean_set_st_header: set object header for single-threaded use */
static inline void lean_set_st_header(lean_object *o, uint8_t tag, unsigned other) {
    o->m_rc = 1;
    o->m_tag = tag;
    o->m_other = (uint8_t)other;
}

/* lean_set_non_heap_header: for objects not on the heap (persistent) */
static inline void lean_set_non_heap_header(size_t sz, uint8_t tag, unsigned other) {
    (void)sz; (void)tag; (void)other;
}

/* Compatibility for generated code that uses lean_ctor_num_objs */
static inline unsigned lean_ctor_num_objs(lean_object *o) {
    return o->m_other;
}

/* lean_io_initializing flag */
static uint8_t g_lean_io_initializing = 0;

static inline uint8_t lean_io_initializing(void) {
    return g_lean_io_initializing;
}

/* Interrupt checking — no-op on bare-metal */
static inline void lean_check_system(void) {}

/* Initialize the Init library — stub for bare-metal.
 * The generated code calls this to init all of Lean's Init module. */
static inline lean_object *initialize_Init(uint8_t builtin) {
    (void)builtin;
    return lean_io_result_mk_ok(lean_box(0));
}

/* ---- Array access functions (used by generated code) ---- */

/* Unchecked access by USize index */
static inline lean_object *lean_array_uget(lean_object *a, size_t i) {
    lean_object *r = lean_array_get_core(a, i);
    lean_inc(r);
    return r;
}

static inline lean_object *lean_array_uset(lean_object *a, size_t i, lean_object *v) {
    if (lean_is_exclusive(a)) {
        lean_dec(lean_array_cptr(a)[i]);
        lean_array_set_core(a, i, v);
        return a;
    }
    lean_array_object *ao = (lean_array_object *)a;
    size_t sz = ao->m_size;
    lean_object *r = lean_mk_empty_array_with_capacity(lean_box(sz));
    for (size_t j = 0; j < sz; j++) {
        lean_object *elem = lean_array_get_core(a, j);
        lean_inc(elem);
        r = lean_array_push(r, elem);
    }
    lean_dec(lean_array_cptr(r)[i]);
    lean_array_set_core(r, i, v);
    lean_dec(a);
    return r;
}

/* Fin-indexed access (index is a Lean Nat object) */
static inline lean_object *lean_array_fget(lean_object *a, lean_object *i) {
    size_t idx = lean_unbox(i);
    lean_object *r = lean_array_get_core(a, idx);
    lean_inc(r);
    return r;
}

/* Fin-indexed borrowed access (no inc on the result, used for read-only access) */
static inline lean_object *lean_array_fget_borrowed(lean_object *a, lean_object *i) {
    size_t idx = lean_unbox(i);
    return lean_array_get_core(a, idx);
}

static inline lean_object *lean_array_fset(lean_object *a, lean_object *i, lean_object *v) {
    size_t idx = lean_unbox(i);
    if (lean_is_exclusive(a)) {
        lean_dec(lean_array_cptr(a)[idx]);
        lean_array_set_core(a, idx, v);
        return a;
    }
    lean_array_object *ao = (lean_array_object *)a;
    size_t sz = ao->m_size;
    lean_object *r = lean_mk_empty_array_with_capacity(lean_box(sz));
    for (size_t j = 0; j < sz; j++) {
        lean_object *elem = lean_array_get_core(a, j);
        lean_inc(elem);
        r = lean_array_push(r, elem);
    }
    lean_dec(lean_array_cptr(r)[idx]);
    lean_array_set_core(r, idx, v);
    lean_dec(a);
    return r;
}

/* Bounds-checked access with default value */
static inline lean_object *lean_array_get(lean_object *def, lean_object *a, lean_object *i) {
    size_t idx = lean_is_scalar(i) ? lean_unbox(i) : (size_t)-1;
    if (idx < lean_array_size(a)) {
        lean_object *r = lean_array_get_core(a, idx);
        lean_inc(r);
        lean_dec(def);
        return r;
    }
    return def;
}

static inline lean_object *lean_array_set(lean_object *a, lean_object *i, lean_object *v) {
    size_t idx = lean_is_scalar(i) ? lean_unbox(i) : (size_t)-1;
    if (idx < lean_array_size(a)) {
        if (lean_is_exclusive(a)) {
            lean_dec(lean_array_cptr(a)[idx]);
            lean_array_set_core(a, idx, v);
            return a;
        }
        lean_array_object *ao = (lean_array_object *)a;
        size_t sz = ao->m_size;
        lean_object *r = lean_mk_empty_array_with_capacity(lean_box(sz));
        for (size_t j = 0; j < sz; j++) {
            lean_object *elem = lean_array_get_core(a, j);
            lean_inc(elem);
            r = lean_array_push(r, elem);
        }
        lean_dec(lean_array_cptr(r)[idx]);
        lean_array_set_core(r, idx, v);
        lean_dec(a);
        return r;
    }
    lean_dec(v);
    return a;
}

/* Array size as a Lean Nat */
static inline lean_object *lean_array_get_size(lean_object *a) {
    return lean_box(lean_array_size(a));
}

/* ---- UInt32 arithmetic (used by SHA-256 generated code) ---- */

static inline uint32_t lean_uint32_add(uint32_t a, uint32_t b) { return a + b; }
static inline uint32_t lean_uint32_sub(uint32_t a, uint32_t b) { return a - b; }
static inline uint32_t lean_uint32_mul(uint32_t a, uint32_t b) { return a * b; }
static inline uint32_t lean_uint32_div(uint32_t a, uint32_t b) { return b == 0 ? 0 : a / b; }
static inline uint32_t lean_uint32_mod(uint32_t a, uint32_t b) { return b == 0 ? a : a % b; }
static inline uint32_t lean_uint32_land(uint32_t a, uint32_t b) { return a & b; }
static inline uint32_t lean_uint32_lor(uint32_t a, uint32_t b) { return a | b; }
static inline uint32_t lean_uint32_xor(uint32_t a, uint32_t b) { return a ^ b; }
static inline uint32_t lean_uint32_complement(uint32_t a) { return ~a; }
static inline uint32_t lean_uint32_shift_left(uint32_t a, uint32_t b) { return a << (b & 31); }
static inline uint32_t lean_uint32_shift_right(uint32_t a, uint32_t b) { return a >> (b & 31); }
static inline uint8_t lean_uint32_dec_eq(uint32_t a, uint32_t b) { return a == b; }
static inline uint8_t lean_uint32_dec_lt(uint32_t a, uint32_t b) { return a < b; }
static inline uint8_t lean_uint32_dec_le(uint32_t a, uint32_t b) { return a <= b; }
static inline uint32_t lean_uint32_of_nat(lean_object *a) {
    if (lean_is_scalar(a)) return (uint32_t)lean_unbox(a);
    return 0;
}
static inline lean_object *lean_uint32_to_nat(uint32_t n) {
    return lean_box((size_t)n);
}

/* ---- UInt8 arithmetic ---- */

static inline uint8_t lean_uint8_add(uint8_t a, uint8_t b) { return a + b; }
static inline uint8_t lean_uint8_sub(uint8_t a, uint8_t b) { return a - b; }
static inline uint8_t lean_uint8_mul(uint8_t a, uint8_t b) { return a * b; }
static inline uint8_t lean_uint8_land(uint8_t a, uint8_t b) { return a & b; }
static inline uint8_t lean_uint8_lor(uint8_t a, uint8_t b) { return a | b; }
static inline uint8_t lean_uint8_xor(uint8_t a, uint8_t b) { return a ^ b; }
static inline uint8_t lean_uint8_shift_left(uint8_t a, uint8_t b) { return a << (b & 7); }
static inline uint8_t lean_uint8_shift_right(uint8_t a, uint8_t b) { return a >> (b & 7); }
static inline uint8_t lean_uint8_complement(uint8_t a) { return ~a; }
static inline uint8_t lean_uint8_dec_eq(uint8_t a, uint8_t b) { return a == b; }
static inline uint8_t lean_uint8_dec_lt(uint8_t a, uint8_t b) { return a < b; }
static inline uint8_t lean_uint8_dec_le(uint8_t a, uint8_t b) { return a <= b; }
static inline uint8_t lean_uint8_of_nat(lean_object *a) {
    if (lean_is_scalar(a)) return (uint8_t)lean_unbox(a);
    return 0;
}
static inline lean_object *lean_uint8_to_nat(uint8_t n) {
    return lean_box((size_t)n);
}
static inline uint32_t lean_uint8_to_uint32(uint8_t a) { return (uint32_t)a; }
static inline uint8_t lean_uint32_to_uint8(uint32_t a) { return (uint8_t)a; }

/* ---- UInt64 arithmetic ---- */

static inline uint64_t lean_uint64_add(uint64_t a, uint64_t b) { return a + b; }
static inline uint64_t lean_uint64_sub(uint64_t a, uint64_t b) { return a - b; }
static inline uint64_t lean_uint64_mul(uint64_t a, uint64_t b) { return a * b; }
static inline uint64_t lean_uint64_div(uint64_t a, uint64_t b) { return b == 0 ? 0 : a / b; }
static inline uint64_t lean_uint64_mod(uint64_t a, uint64_t b) { return b == 0 ? a : a % b; }
static inline uint64_t lean_uint64_land(uint64_t a, uint64_t b) { return a & b; }
static inline uint64_t lean_uint64_lor(uint64_t a, uint64_t b) { return a | b; }
static inline uint64_t lean_uint64_xor(uint64_t a, uint64_t b) { return a ^ b; }
static inline uint64_t lean_uint64_complement(uint64_t a) { return ~a; }
static inline uint64_t lean_uint64_shift_left(uint64_t a, uint64_t b) { return a << (b & 63); }
static inline uint64_t lean_uint64_shift_right(uint64_t a, uint64_t b) { return a >> (b & 63); }
static inline uint8_t lean_uint64_dec_eq(uint64_t a, uint64_t b) { return a == b; }
static inline uint8_t lean_uint64_dec_lt(uint64_t a, uint64_t b) { return a < b; }
static inline uint8_t lean_uint64_dec_le(uint64_t a, uint64_t b) { return a <= b; }
static inline uint64_t lean_uint64_of_nat(lean_object *a) {
    if (lean_is_scalar(a)) return (uint64_t)lean_unbox(a);
    return 0;
}
static inline lean_object *lean_uint64_to_nat(uint64_t n) {
    return lean_box((size_t)n);
}
static inline uint8_t lean_uint64_to_uint8(uint64_t a) { return (uint8_t)a; }

/* ---- USize arithmetic ---- */

static inline size_t lean_usize_add(size_t a, size_t b) { return a + b; }
static inline size_t lean_usize_sub(size_t a, size_t b) { return a - b; }
static inline size_t lean_usize_mul(size_t a, size_t b) { return a * b; }
static inline size_t lean_usize_land(size_t a, size_t b) { return a & b; }
static inline size_t lean_usize_lor(size_t a, size_t b) { return a | b; }
static inline size_t lean_usize_shift_left(size_t a, size_t b) { return a << b; }
static inline size_t lean_usize_shift_right(size_t a, size_t b) { return a >> b; }
static inline uint8_t lean_usize_dec_eq(size_t a, size_t b) { return a == b; }
static inline uint8_t lean_usize_dec_lt(size_t a, size_t b) { return a < b; }
static inline uint8_t lean_usize_dec_le(size_t a, size_t b) { return a <= b; }
static inline size_t lean_usize_of_nat(lean_object *a) {
    if (lean_is_scalar(a)) return lean_unbox(a);
    return 0;
}
static inline lean_object *lean_usize_to_nat(size_t n) {
    return lean_box(n);
}

/* ---- Nat shift right (used by UInt conversions) ---- */

static inline lean_object *lean_nat_shiftr(lean_object *a, lean_object *b) {
    if (lean_is_scalar(a) && lean_is_scalar(b))
        return lean_box(lean_unbox(a) >> lean_unbox(b));
    return lean_box(0);
}

/* ---- Char operations ---- */

static inline uint32_t lean_char_of_nat(lean_object *n) {
    uint32_t v = (uint32_t)(lean_is_scalar(n) ? lean_unbox(n) : 0);
    /* Validate Unicode scalar value */
    if (v > 0x10FFFF || (v >= 0xD800 && v <= 0xDFFF)) return 0;
    return v;
}

static inline uint8_t lean_char_dec_eq(uint32_t a, uint32_t b) { return a == b; }
static inline uint8_t lean_char_dec_lt(uint32_t a, uint32_t b) { return a < b; }

#endif /* LEAN_LEAN_H */
