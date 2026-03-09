#ifndef LEAN_RT_H
#define LEAN_RT_H

/*
 * lean_rt.h — Freestanding Lean 4 runtime replacement
 *
 * This header provides the types and inline functions that lean.h normally
 * provides, plus declarations for the non-inline functions we implement
 * in lean_rt.c.
 *
 * We define LEAN_FREESTANDING so the generated C code includes this instead
 * of the full lean.h (or we patch the generated code's #include).
 */

#include <stdint.h>
#include <stddef.h>

/* ---- Basic types ---- */

typedef struct lean_object lean_object;
typedef lean_object *lean_obj_arg;    /* borrowed reference */
typedef lean_object *b_lean_obj_arg;  /* borrowed, not consumed */
typedef lean_object *lean_obj_res;    /* returned, caller owns */

struct lean_object {
    int      m_rc;
    uint16_t m_cs_sz;
    uint8_t  m_other;
    uint8_t  m_tag;
};

/* Object tags */
#define LeanClosure     245
#define LeanArray       246
#define LeanScalarArray 248
#define LeanString      249
#define LeanMPZ         250
#define LeanThunk       251
#define LeanTask        252
#define LeanRef         253
#define LeanExternal    254

/* Persistent objects have rc == 0 (never freed) */
#define LEAN_RC_PERSISTENT 0

/* ---- Constructor objects ---- */

/* TODO: The official Lean 4 runtime has no m_num_objs here — the ctor is just
 * the header followed immediately by object pointer slots and scalar data.
 * We keep m_num_objs because removing it currently breaks init-time string
 * operations (the extra 8 bytes shift lean_ctor_obj_cptr, and all internal
 * sizeof(lean_ctor_object) calculations are consistent with it present).
 * Removing it is the right long-term fix but requires auditing every
 * allocation size path. Wastes 8 bytes per constructor object. */
typedef struct {
    lean_object m_header;
    size_t      m_num_objs;
    /* followed by: lean_object* m_objs[m_num_objs], then scalar data */
} lean_ctor_object;

/* ---- Closure objects ---- */

typedef void *lean_cfun;

typedef struct {
    lean_object m_header;
    lean_cfun   m_fun;
    uint16_t    m_arity;
    uint16_t    m_num_fixed;
    /* followed by: lean_object* m_args[m_num_fixed] */
} lean_closure_object;

/* ---- Array objects ---- */

typedef struct {
    lean_object m_header;
    size_t      m_size;
    size_t      m_capacity;
    /* followed by: lean_object* m_data[m_capacity] */
} lean_array_object;

/* ---- Scalar (byte) array objects ---- */

typedef struct {
    lean_object m_header;
    size_t      m_size;
    size_t      m_capacity;
    /* followed by: uint8_t m_data[m_capacity] */
} lean_sarray_object;

/* ---- String objects ---- */

typedef struct {
    lean_object m_header;
    size_t      m_size;     /* byte size including null terminator */
    size_t      m_capacity;
    size_t      m_length;   /* UTF-8 character count */
    /* followed by: char m_data[m_capacity] */
} lean_string_object;

/* ---- Thunk objects ---- */

typedef struct {
    lean_object  m_header;
    lean_object *m_value;
    lean_object *m_closure;
} lean_thunk_object;

/* ---- External objects ---- */

typedef struct lean_external_class {
    void (*m_finalize)(void *);
    void (*m_foreach)(void *, b_lean_obj_arg);
} lean_external_class;

typedef struct {
    lean_object          m_header;
    lean_external_class *m_class;
    void                *m_data;
} lean_external_object;

/* ---- Scalar (boxed integer) tagging ---- */

static inline uint8_t lean_is_scalar(lean_object *o) {
    return ((size_t)o & 1) != 0;
}

static inline lean_object *lean_box(size_t n) {
    return (lean_object *)(((size_t)n << 1) | 1);
}

static inline size_t lean_unbox(lean_object *o) {
    return (size_t)o >> 1;
}

/* ---- Reference counting (inline fast paths) ---- */

static inline uint8_t lean_is_st(lean_object *o) {
    return o->m_rc > 0;
}

static inline uint8_t lean_is_mt(lean_object *o) {
    return o->m_rc < 0;
}

static inline uint8_t lean_is_persistent(lean_object *o) {
    return o->m_rc == LEAN_RC_PERSISTENT;
}

static inline uint8_t lean_is_exclusive(lean_object *o) {
    return o->m_rc == 1;
}

static inline void lean_inc_ref(lean_object *o) {
    if (o->m_rc > 0)
        o->m_rc++;
}

static inline void lean_inc_ref_n(lean_object *o, size_t n) {
    if (o->m_rc > 0)
        o->m_rc += (int)n;
}

static inline void lean_inc(lean_object *o) {
    if (!lean_is_scalar(o))
        lean_inc_ref(o);
}

static inline void lean_inc_n(lean_object *o, size_t n) {
    if (!lean_is_scalar(o))
        lean_inc_ref_n(o, n);
}

/* Forward declaration of cold path */
void lean_dec_ref_cold(lean_object *o);

static inline void lean_dec_ref(lean_object *o) {
    if (o->m_rc > 1) {
        o->m_rc--;
    } else if (o->m_rc == 1) {
        lean_dec_ref_cold(o);
    }
    /* rc == 0 (persistent) or rc < 0 (mt): do nothing */
}

static inline void lean_dec(lean_object *o) {
    if (!lean_is_scalar(o))
        lean_dec_ref(o);
}

/* ---- Constructor field access (inline) ---- */

static inline lean_object **lean_ctor_obj_cptr(lean_object *o) {
    return (lean_object **)((char *)o + sizeof(lean_ctor_object));
}

static inline uint8_t *lean_ctor_scalar_cptr(lean_object *o) {
    return (uint8_t *)((char *)o + sizeof(lean_ctor_object)
           + o->m_other * sizeof(lean_object *));
}

static inline lean_object *lean_ctor_get(lean_object *o, unsigned i) {
    return lean_ctor_obj_cptr(o)[i];
}

static inline void lean_ctor_set(lean_object *o, unsigned i, lean_object *v) {
    lean_ctor_obj_cptr(o)[i] = v;
}

static inline void lean_ctor_release(lean_object *o, unsigned i) {
    lean_object **p = lean_ctor_obj_cptr(o) + i;
    lean_dec(*p);
    *p = lean_box(0);
}

static inline void lean_ctor_set_tag(lean_object *o, uint8_t tag) {
    o->m_tag = tag;
}

static inline size_t lean_ctor_get_usize(lean_object *o, unsigned i) {
    return ((size_t *)lean_ctor_scalar_cptr(o))[i];
}

static inline void lean_ctor_set_usize(lean_object *o, unsigned i, size_t v) {
    ((size_t *)lean_ctor_scalar_cptr(o))[i] = v;
}

/* Scalar field access — offsets are relative to lean_ctor_obj_cptr(o),
 * matching the official Lean 4 runtime and the lean -c code generator.
 * The generated code computes offsets as sizeof(void*)*num_obj_fields + byte_pos. */

static inline uint8_t lean_ctor_get_uint8(lean_object *o, unsigned off) {
    return ((uint8_t *)lean_ctor_obj_cptr(o))[off];
}

static inline void lean_ctor_set_uint8(lean_object *o, unsigned off, uint8_t v) {
    ((uint8_t *)lean_ctor_obj_cptr(o))[off] = v;
}

static inline uint16_t lean_ctor_get_uint16(lean_object *o, unsigned off) {
    uint16_t r;
    __builtin_memcpy(&r, (uint8_t *)lean_ctor_obj_cptr(o) + off, 2);
    return r;
}

static inline void lean_ctor_set_uint16(lean_object *o, unsigned off, uint16_t v) {
    __builtin_memcpy((uint8_t *)lean_ctor_obj_cptr(o) + off, &v, 2);
}

static inline uint32_t lean_ctor_get_uint32(lean_object *o, unsigned off) {
    uint32_t r;
    __builtin_memcpy(&r, (uint8_t *)lean_ctor_obj_cptr(o) + off, 4);
    return r;
}

static inline void lean_ctor_set_uint32(lean_object *o, unsigned off, uint32_t v) {
    __builtin_memcpy((uint8_t *)lean_ctor_obj_cptr(o) + off, &v, 4);
}

static inline uint64_t lean_ctor_get_uint64(lean_object *o, unsigned off) {
    uint64_t r;
    __builtin_memcpy(&r, (uint8_t *)lean_ctor_obj_cptr(o) + off, 8);
    return r;
}

static inline void lean_ctor_set_uint64(lean_object *o, unsigned off, uint64_t v) {
    __builtin_memcpy((uint8_t *)lean_ctor_obj_cptr(o) + off, &v, 8);
}

static inline double lean_ctor_get_float(lean_object *o, unsigned off) {
    double r;
    __builtin_memcpy(&r, (uint8_t *)lean_ctor_obj_cptr(o) + off, 8);
    return r;
}

static inline void lean_ctor_set_float(lean_object *o, unsigned off, double v) {
    __builtin_memcpy((uint8_t *)lean_ctor_obj_cptr(o) + off, &v, 8);
}

/* ---- Closure field access (inline) ---- */

static inline lean_object **lean_closure_arg_cptr(lean_object *o) {
    return (lean_object **)((char *)o + sizeof(lean_closure_object));
}

static inline void lean_closure_set(lean_object *o, unsigned i, lean_object *v) {
    lean_closure_arg_cptr(o)[i] = v;
}

static inline lean_object *lean_closure_get(lean_object *o, unsigned i) {
    return lean_closure_arg_cptr(o)[i];
}

/* ---- Array access (inline) ---- */

static inline lean_object **lean_array_cptr(lean_object *o) {
    return (lean_object **)((char *)o + sizeof(lean_array_object));
}

static inline size_t lean_array_size(lean_object *o) {
    return ((lean_array_object *)o)->m_size;
}

static inline lean_object *lean_array_get_core(lean_object *a, size_t i) {
    return lean_array_cptr(a)[i];
}

static inline void lean_array_set_core(lean_object *a, size_t i, lean_object *v) {
    lean_array_cptr(a)[i] = v;
}

/* ---- String access (inline) ---- */

static inline char *lean_string_cstr(lean_object *o) {
    return (char *)((char *)o + sizeof(lean_string_object));
}

static inline size_t lean_string_size(lean_object *o) {
    return ((lean_string_object *)o)->m_size;
}

static inline size_t lean_string_len(lean_object *o) {
    return ((lean_string_object *)o)->m_length;
}

/* ---- IO result helpers (inline) ---- */

static inline lean_object *lean_io_result_mk_ok(lean_object *v);
static inline lean_object *lean_io_result_mk_error(lean_object *e);
static inline uint8_t lean_io_result_is_ok(lean_object *r) {
    return r->m_tag == 0;
}
static inline uint8_t lean_io_result_is_error(lean_object *r) {
    return r->m_tag == 1;
}
static inline lean_object *lean_io_result_get_value(lean_object *r) {
    return lean_ctor_get(r, 0);
}

/* ---- Non-inline function declarations ---- */

/* Allocation */
lean_object *lean_alloc_object(size_t sz);
lean_object *lean_alloc_small_object(size_t sz);
void lean_free_object(lean_object *o);
void lean_del_object(lean_object *o);

/* Constructors, closures */
lean_object *lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz);
lean_object *lean_alloc_closure(lean_cfun fun, unsigned arity, unsigned num_fixed);

/* Mark persistent */
void lean_mark_persistent(lean_object *o);

/* Strings */
lean_object *lean_mk_string(const char *s);
lean_object *lean_mk_string_unchecked(const char *s, size_t sz, size_t len);
lean_object *lean_mk_string_from_bytes(const char *s, size_t sz);
lean_object *lean_string_push(lean_object *s, uint32_t c);
lean_object *lean_string_append(lean_object *s1, lean_object *s2);
uint8_t lean_string_eq(lean_object *s1, lean_object *s2);
uint8_t lean_string_lt(lean_object *s1, lean_object *s2);
uint64_t lean_string_hash(lean_object *s);
uint32_t lean_string_utf8_get(lean_object *s, lean_object *i);
lean_object *lean_string_utf8_next(lean_object *s, lean_object *i);
lean_object *lean_string_utf8_extract(lean_object *s, lean_object *b, lean_object *e);
lean_object *lean_string_mk(lean_object *cs);
lean_object *lean_string_data(lean_object *s);

/* Array */
lean_object *lean_mk_empty_array(void);
lean_object *lean_mk_empty_array_with_capacity(lean_object *cap);
lean_object *lean_array_push(lean_object *a, lean_object *v);
lean_object *lean_mk_array(lean_object *n, lean_object *v);
lean_object *lean_array_get_panic(lean_object *def);
lean_object *lean_array_set_panic(lean_object *a, lean_object *v);
lean_object *lean_copy_expand_array(lean_object *a, int expand);

/* Boxing */
lean_object *lean_box_uint32(uint32_t v);
lean_object *lean_box_uint64(uint64_t v);
lean_object *lean_box_usize(size_t v);
lean_object *lean_box_float(double v);
uint32_t lean_unbox_uint32(lean_object *o);
uint64_t lean_unbox_uint64(lean_object *o);
size_t lean_unbox_usize(lean_object *o);
double lean_unbox_float(lean_object *o);
lean_object *lean_unsigned_to_nat(size_t n);
lean_object *lean_cstr_to_nat(const char *s);

/* Closure application */
lean_object *lean_apply_1(lean_object *f, lean_object *a1);
lean_object *lean_apply_2(lean_object *f, lean_object *a1, lean_object *a2);
lean_object *lean_apply_3(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3);
lean_object *lean_apply_4(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4);
lean_object *lean_apply_5(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5);
lean_object *lean_apply_6(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6);
lean_object *lean_apply_n(lean_object *f, unsigned n, lean_object **args);
lean_object *lean_apply_m(lean_object *f, unsigned n, lean_object **args);

/* Panic */
lean_object *lean_panic_fn(lean_object *def, lean_object *msg);
void lean_internal_panic(const char *msg) __attribute__((noreturn));
void lean_internal_panic_unreachable(void) __attribute__((noreturn));
void lean_internal_panic_out_of_memory(void) __attribute__((noreturn));
void lean_internal_panic_rc_overflow(void) __attribute__((noreturn));

/* Initialization */
/* Note: the Lean C code generator emits `void lean_initialize_runtime_module()`
 * in generated code, so we must match that signature here. */
void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
char **lean_setup_args(int argc, char **argv);
void lean_set_panic_messages(uint8_t flag);
/* Note: same as lean_initialize_runtime_module — generated code says void. */
void lean_init_task_manager(void);
void lean_finalize_task_manager(void);

/* IO */
lean_object *lean_get_stdout(void);
lean_object *lean_get_stderr(void);
lean_object *lean_get_stdin(void);
lean_object *lean_io_prim_handle_put_str(lean_object *h, lean_object *s, lean_object *w);
lean_object *lean_io_prim_put_str(lean_object *s, lean_object *w);
lean_object *lean_io_result_show_error(lean_object *r);
lean_object *lean_io_prim_handle_get_line(lean_object *h, lean_object *w);

/* Once-cells (single-threaded) */
lean_object *lean_object_once(lean_object **slot, lean_object *(*init)(lean_object *));

/* ST Ref */
lean_object *lean_st_mk_ref(lean_object *v, lean_object *w);
lean_object *lean_st_ref_get(lean_object *r, lean_object *w);
lean_object *lean_st_ref_set(lean_object *r, lean_object *v, lean_object *w);
lean_object *lean_st_ref_take(lean_object *r, lean_object *w);
lean_object *lean_st_ref_swap(lean_object *r, lean_object *v, lean_object *w);

/* Nat big operations (stubs — panic for now) */
lean_object *lean_nat_big_succ(lean_object *a);
lean_object *lean_nat_big_add(lean_object *a, lean_object *b);
lean_object *lean_nat_big_sub(lean_object *a, lean_object *b);
lean_object *lean_nat_big_mul(lean_object *a, lean_object *b);
lean_object *lean_nat_big_div(lean_object *a, lean_object *b);
lean_object *lean_nat_big_mod(lean_object *a, lean_object *b);
uint8_t lean_nat_big_eq(lean_object *a, lean_object *b);
uint8_t lean_nat_big_le(lean_object *a, lean_object *b);
uint8_t lean_nat_big_lt(lean_object *a, lean_object *b);

/* Nat/Int conversions */
lean_object *lean_nat_to_int(lean_object *n);
lean_object *lean_string_length(lean_object *s);

/* Int big operations (stubs) */
lean_object *lean_int_big_neg(lean_object *a);
lean_object *lean_int_big_add(lean_object *a, lean_object *b);
lean_object *lean_int_big_sub(lean_object *a, lean_object *b);
lean_object *lean_int_big_mul(lean_object *a, lean_object *b);

/* Thunk */
lean_object *lean_thunk_get_core(lean_object *t);
lean_object *lean_thunk_get(lean_object *t);
lean_object *lean_thunk_get_own(lean_object *t);
lean_object *lean_thunk_pure(lean_object *v);
lean_object *lean_mk_thunk(lean_object *c);

/* Float to string */
lean_object *lean_float_to_string(double d);

/* Sarray / ByteArray */
lean_object *lean_byte_array_mk(lean_object *l);
lean_object *lean_byte_array_data(lean_object *a);
lean_object *lean_byte_array_push(lean_object *a, uint8_t b);
lean_object *lean_copy_byte_array(lean_object *a);

/* Platform */
uint32_t lean_get_num_heartbeats(void);
void lean_set_max_heartbeat(uint32_t n);
uint8_t lean_io_check_canceled(lean_object *w);
lean_object *lean_io_cancel(lean_object *w);
lean_object *lean_io_get_num_heartbeats(lean_object *w);

/* ---- Deferred inline implementations ---- */

lean_object *lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz);

static inline lean_object *lean_io_result_mk_ok(lean_object *v) {
    lean_object *r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, v);
    lean_ctor_set(r, 1, lean_box(0));
    return r;
}

static inline lean_object *lean_io_result_mk_error(lean_object *e) {
    lean_object *r = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(r, 0, e);
    lean_ctor_set(r, 1, lean_box(0));
    return r;
}

#endif /* LEAN_RT_H */
