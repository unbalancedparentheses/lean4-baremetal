/*
 * lean/lean.h — Shim header for freestanding Lean 4 runtime
 *
 * The Lean compiler generates C code with `#include <lean/lean.h>`.
 * This file redirects to our freestanding runtime replacement.
 * The Makefile adds `-I.` so this file is found instead of the real lean.h.
 */

#ifndef LEAN_LEAN_H
#define LEAN_LEAN_H

#include "../lean_rt.h"

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

#endif /* LEAN_LEAN_H */
