/*
 * lean_rt.c — Freestanding Lean 4 runtime replacement
 *
 * Implements the non-inline LEAN_EXPORT functions that the generated C code
 * calls. This is a minimal implementation targeting bare-metal RISC-V 64-bit
 * on QEMU virt.
 *
 * Key design decisions:
 *   - Bump allocator (no free, upgrade to slab later)
 *   - Single-threaded (all TLS → globals, mutexes → no-ops)
 *   - No GMP (bignum operations panic for now)
 *   - No C++ (rewritten in C, exceptions → UART + halt)
 *   - IO output → UART
 */

#include "lean_rt.h"
#include "uart.h"

/* libc stubs we provide in libc_min.c */
extern void *memcpy(void *dst, const void *src, size_t n);
extern void *memset(void *s, int c, size_t n);
extern void *memmove(void *dst, const void *src, size_t n);
extern int memcmp(const void *s1, const void *s2, size_t n);
extern size_t strlen(const char *s);
extern void abort(void) __attribute__((noreturn));

/* ========================================================================
 * Bump Allocator
 * ======================================================================== */

extern char _heap_start[];
extern char _heap_end[];

static char *heap_ptr;

static void heap_init(void)
{
    heap_ptr = _heap_start;
}

static void *bump_alloc(size_t sz)
{
    /* Align to 16 bytes */
    sz = (sz + 15) & ~(size_t)15;
    if (heap_ptr + sz > _heap_end) {
        lean_internal_panic_out_of_memory();
    }
    void *p = heap_ptr;
    heap_ptr += sz;
    return p;
}

/* malloc/free/realloc for libc compatibility */
void *malloc(size_t sz)
{
    if (sz == 0) sz = 1;
    /* Store size before the returned pointer so realloc can work */
    size_t total = sz + 16;
    char *p = (char *)bump_alloc(total);
    *(size_t *)p = sz;
    return p + 16;
}

void free(void *ptr)
{
    /* Bump allocator: no-op */
    (void)ptr;
}

void *realloc(void *ptr, size_t sz)
{
    if (!ptr)
        return malloc(sz);
    if (sz == 0) {
        free(ptr);
        return (void *)0;
    }
    size_t old_sz = *(size_t *)((char *)ptr - 16);
    void *new_ptr = malloc(sz);
    size_t copy_sz = old_sz < sz ? old_sz : sz;
    memcpy(new_ptr, ptr, copy_sz);
    return new_ptr;
}

void *calloc(size_t nmemb, size_t sz)
{
    size_t total = nmemb * sz;
    void *p = malloc(total);
    memset(p, 0, total);
    return p;
}

/* ========================================================================
 * Object Allocation
 * ======================================================================== */

lean_object *lean_alloc_object(size_t sz)
{
    lean_object *o = (lean_object *)malloc(sz);
    o->m_rc = 1;
    o->m_cs_sz = (uint16_t)(sz < 65536 ? sz : 0);
    return o;
}

lean_object *lean_alloc_small_object(size_t sz)
{
    return lean_alloc_object(sz);
}

void lean_free_object(lean_object *o)
{
    free(o);
}

void lean_del_object(lean_object *o)
{
    lean_free_object(o);
}

/* ========================================================================
 * Constructor / Closure Allocation
 * ======================================================================== */

lean_object *lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz)
{
    size_t sz = sizeof(lean_ctor_object)
              + num_objs * sizeof(lean_object *)
              + scalar_sz;
    lean_object *o = lean_alloc_object(sz);
    o->m_tag = (uint8_t)tag;
    o->m_other = (uint8_t)num_objs;
    ((lean_ctor_object *)o)->m_num_objs = num_objs;
    /* Zero the fields */
    memset((char *)o + sizeof(lean_ctor_object), 0,
           num_objs * sizeof(lean_object *) + scalar_sz);
    return o;
}

lean_object *lean_alloc_closure(lean_cfun fun, unsigned arity, unsigned num_fixed)
{
    size_t sz = sizeof(lean_closure_object) + num_fixed * sizeof(lean_object *);
    lean_object *o = lean_alloc_object(sz);
    o->m_tag = LeanClosure;
    o->m_other = 0;
    lean_closure_object *c = (lean_closure_object *)o;
    c->m_fun = fun;
    c->m_arity = (uint16_t)arity;
    c->m_num_fixed = (uint16_t)num_fixed;
    memset(lean_closure_arg_cptr(o), 0, num_fixed * sizeof(lean_object *));
    return o;
}

/* ========================================================================
 * Mark Persistent
 * ======================================================================== */

static void lean_mark_persistent_rec(lean_object *o);

void lean_mark_persistent(lean_object *o)
{
    if (lean_is_scalar(o) || lean_is_persistent(o))
        return;
    lean_mark_persistent_rec(o);
}

static void lean_mark_persistent_rec(lean_object *o)
{
    o->m_rc = LEAN_RC_PERSISTENT;

    uint8_t tag = o->m_tag;
    if (tag <= 243) {
        /* Constructor: mark all object fields */
        unsigned num_objs = o->m_other;
        lean_object **fields = lean_ctor_obj_cptr(o);
        for (unsigned i = 0; i < num_objs; i++) {
            if (!lean_is_scalar(fields[i]))
                lean_mark_persistent_rec(fields[i]);
        }
    } else if (tag == LeanClosure) {
        lean_closure_object *c = (lean_closure_object *)o;
        lean_object **args = lean_closure_arg_cptr(o);
        for (unsigned i = 0; i < c->m_num_fixed; i++) {
            if (!lean_is_scalar(args[i]))
                lean_mark_persistent_rec(args[i]);
        }
    } else if (tag == LeanArray) {
        lean_array_object *a = (lean_array_object *)o;
        lean_object **data = lean_array_cptr(o);
        for (size_t i = 0; i < a->m_size; i++) {
            if (!lean_is_scalar(data[i]))
                lean_mark_persistent_rec(data[i]);
        }
    }
    /* String, ScalarArray, MPZ, External: no object children to mark */
}

/* ========================================================================
 * Reference Count Cold Path (deallocation)
 * ======================================================================== */

void lean_dec_ref_cold(lean_object *o)
{
    uint8_t tag = o->m_tag;

    if (tag <= 243) {
        /* Constructor: dec-ref all object fields, then free */
        unsigned num_objs = o->m_other;
        lean_object **fields = lean_ctor_obj_cptr(o);
        for (unsigned i = 0; i < num_objs; i++)
            lean_dec(fields[i]);
    } else if (tag == LeanClosure) {
        lean_closure_object *c = (lean_closure_object *)o;
        lean_object **args = lean_closure_arg_cptr(o);
        for (unsigned i = 0; i < c->m_num_fixed; i++)
            lean_dec(args[i]);
    } else if (tag == LeanArray) {
        lean_array_object *a = (lean_array_object *)o;
        lean_object **data = lean_array_cptr(o);
        for (size_t i = 0; i < a->m_size; i++)
            lean_dec(data[i]);
    } else if (tag == LeanThunk) {
        lean_thunk_object *t = (lean_thunk_object *)o;
        if (t->m_value) lean_dec(t->m_value);
        if (t->m_closure) lean_dec(t->m_closure);
    } else if (tag == LeanExternal) {
        lean_external_object *e = (lean_external_object *)o;
        if (e->m_class && e->m_class->m_finalize)
            e->m_class->m_finalize(e->m_data);
    }
    /* String, ScalarArray, MPZ: no object children */

    lean_free_object(o);
}

/* ========================================================================
 * Strings
 * ======================================================================== */

lean_object *lean_mk_string_unchecked(const char *s, size_t byte_sz, size_t char_len)
{
    size_t alloc_sz = sizeof(lean_string_object) + byte_sz + 1;
    lean_object *o = lean_alloc_object(alloc_sz);
    o->m_tag = LeanString;
    o->m_other = 0;
    lean_string_object *str = (lean_string_object *)o;
    str->m_size = byte_sz + 1;  /* includes null terminator */
    str->m_capacity = byte_sz + 1;
    str->m_length = char_len;
    char *data = lean_string_cstr(o);
    memcpy(data, s, byte_sz);
    data[byte_sz] = '\0';
    return o;
}

lean_object *lean_mk_string(const char *s)
{
    size_t byte_sz = strlen(s);
    /* Count UTF-8 characters */
    size_t char_len = 0;
    for (size_t i = 0; i < byte_sz; ) {
        uint8_t c = (uint8_t)s[i];
        if (c < 0x80) i += 1;
        else if (c < 0xE0) i += 2;
        else if (c < 0xF0) i += 3;
        else i += 4;
        char_len++;
    }
    return lean_mk_string_unchecked(s, byte_sz, char_len);
}

lean_object *lean_mk_string_from_bytes(const char *s, size_t sz)
{
    /* Count UTF-8 characters */
    size_t char_len = 0;
    for (size_t i = 0; i < sz; ) {
        uint8_t c = (uint8_t)s[i];
        if (c < 0x80) i += 1;
        else if (c < 0xE0) i += 2;
        else if (c < 0xF0) i += 3;
        else i += 4;
        char_len++;
    }
    return lean_mk_string_unchecked(s, sz, char_len);
}

lean_object *lean_string_append(lean_object *s1, lean_object *s2)
{
    size_t sz1 = lean_string_size(s1) - 1;  /* exclude null */
    size_t sz2 = lean_string_size(s2) - 1;
    size_t len1 = lean_string_len(s1);
    size_t len2 = lean_string_len(s2);

    lean_object *r = lean_mk_string_unchecked("", 0, 0);
    lean_free_object(r);

    size_t total_sz = sz1 + sz2;
    size_t alloc_sz = sizeof(lean_string_object) + total_sz + 1;
    lean_object *o = lean_alloc_object(alloc_sz);
    o->m_tag = LeanString;
    o->m_other = 0;
    lean_string_object *str = (lean_string_object *)o;
    str->m_size = total_sz + 1;
    str->m_capacity = total_sz + 1;
    str->m_length = len1 + len2;
    char *data = lean_string_cstr(o);
    memcpy(data, lean_string_cstr(s1), sz1);
    memcpy(data + sz1, lean_string_cstr(s2), sz2);
    data[total_sz] = '\0';

    lean_dec(s1);
    lean_dec(s2);
    return o;
}

lean_object *lean_string_push(lean_object *s, uint32_t c)
{
    /* Encode c as UTF-8 */
    char buf[4];
    size_t enc_len;
    if (c < 0x80) {
        buf[0] = (char)c;
        enc_len = 1;
    } else if (c < 0x800) {
        buf[0] = (char)(0xC0 | (c >> 6));
        buf[1] = (char)(0x80 | (c & 0x3F));
        enc_len = 2;
    } else if (c < 0x10000) {
        buf[0] = (char)(0xE0 | (c >> 12));
        buf[1] = (char)(0x80 | ((c >> 6) & 0x3F));
        buf[2] = (char)(0x80 | (c & 0x3F));
        enc_len = 3;
    } else {
        buf[0] = (char)(0xF0 | (c >> 18));
        buf[1] = (char)(0x80 | ((c >> 12) & 0x3F));
        buf[2] = (char)(0x80 | ((c >> 6) & 0x3F));
        buf[3] = (char)(0x80 | (c & 0x3F));
        enc_len = 4;
    }

    size_t old_sz = lean_string_size(s) - 1;
    size_t new_sz = old_sz + enc_len;
    size_t alloc_sz = sizeof(lean_string_object) + new_sz + 1;
    lean_object *o = lean_alloc_object(alloc_sz);
    o->m_tag = LeanString;
    o->m_other = 0;
    lean_string_object *str = (lean_string_object *)o;
    str->m_size = new_sz + 1;
    str->m_capacity = new_sz + 1;
    str->m_length = lean_string_len(s) + 1;
    char *data = lean_string_cstr(o);
    memcpy(data, lean_string_cstr(s), old_sz);
    memcpy(data + old_sz, buf, enc_len);
    data[new_sz] = '\0';

    lean_dec(s);
    return o;
}

uint8_t lean_string_eq(lean_object *s1, lean_object *s2)
{
    size_t sz1 = lean_string_size(s1);
    size_t sz2 = lean_string_size(s2);
    if (sz1 != sz2) return 0;
    return memcmp(lean_string_cstr(s1), lean_string_cstr(s2), sz1) == 0;
}

uint8_t lean_string_lt(lean_object *s1, lean_object *s2)
{
    size_t sz1 = lean_string_size(s1) - 1;
    size_t sz2 = lean_string_size(s2) - 1;
    size_t min_sz = sz1 < sz2 ? sz1 : sz2;
    int cmp = memcmp(lean_string_cstr(s1), lean_string_cstr(s2), min_sz);
    if (cmp < 0) return 1;
    if (cmp > 0) return 0;
    return sz1 < sz2;
}

uint64_t lean_string_hash(lean_object *s)
{
    /* FNV-1a hash */
    const uint8_t *data = (const uint8_t *)lean_string_cstr(s);
    size_t sz = lean_string_size(s) - 1;
    uint64_t h = 0xcbf29ce484222325ULL;
    for (size_t i = 0; i < sz; i++) {
        h ^= data[i];
        h *= 0x100000001b3ULL;
    }
    return h;
}

uint32_t lean_string_utf8_get(lean_object *s, lean_object *i)
{
    size_t pos = lean_unbox(i);
    const uint8_t *data = (const uint8_t *)lean_string_cstr(s);
    size_t sz = lean_string_size(s) - 1;
    if (pos >= sz) return 0;
    uint8_t c = data[pos];
    if (c < 0x80) return c;
    if (c < 0xE0) {
        if (pos + 1 >= sz) return 0;
        return ((uint32_t)(c & 0x1F) << 6) | (data[pos+1] & 0x3F);
    }
    if (c < 0xF0) {
        if (pos + 2 >= sz) return 0;
        return ((uint32_t)(c & 0x0F) << 12)
             | ((uint32_t)(data[pos+1] & 0x3F) << 6)
             | (data[pos+2] & 0x3F);
    }
    if (pos + 3 >= sz) return 0;
    return ((uint32_t)(c & 0x07) << 18)
         | ((uint32_t)(data[pos+1] & 0x3F) << 12)
         | ((uint32_t)(data[pos+2] & 0x3F) << 6)
         | (data[pos+3] & 0x3F);
}

lean_object *lean_string_utf8_next(lean_object *s, lean_object *i)
{
    size_t pos = lean_unbox(i);
    const uint8_t *data = (const uint8_t *)lean_string_cstr(s);
    size_t sz = lean_string_size(s) - 1;
    if (pos >= sz) return lean_box(pos);
    uint8_t c = data[pos];
    if (c < 0x80) pos += 1;
    else if (c < 0xE0) pos += 2;
    else if (c < 0xF0) pos += 3;
    else pos += 4;
    if (pos > sz) pos = sz;
    return lean_box(pos);
}

lean_object *lean_string_utf8_extract(lean_object *s, lean_object *b, lean_object *e)
{
    size_t start = lean_unbox(b);
    size_t end = lean_unbox(e);
    const char *data = lean_string_cstr(s);
    size_t sz = lean_string_size(s) - 1;
    if (start > sz) start = sz;
    if (end > sz) end = sz;
    if (start >= end)
        return lean_mk_string("");
    return lean_mk_string_from_bytes(data + start, end - start);
}

lean_object *lean_string_mk(lean_object *cs)
{
    /* Convert List Char to String — iterate the list */
    /* First, count characters to know final size */
    size_t byte_count = 0;
    size_t char_count = 0;
    lean_object *cur = cs;
    while (cur->m_tag == 1) {  /* Cons */
        uint32_t ch = (uint32_t)lean_unbox(lean_ctor_get(cur, 0));
        if (ch < 0x80) byte_count += 1;
        else if (ch < 0x800) byte_count += 2;
        else if (ch < 0x10000) byte_count += 3;
        else byte_count += 4;
        char_count++;
        cur = lean_ctor_get(cur, 1);
    }

    size_t alloc_sz = sizeof(lean_string_object) + byte_count + 1;
    lean_object *o = lean_alloc_object(alloc_sz);
    o->m_tag = LeanString;
    o->m_other = 0;
    lean_string_object *str = (lean_string_object *)o;
    str->m_size = byte_count + 1;
    str->m_capacity = byte_count + 1;
    str->m_length = char_count;

    char *data = lean_string_cstr(o);
    size_t pos = 0;
    cur = cs;
    while (cur->m_tag == 1) {
        uint32_t ch = (uint32_t)lean_unbox(lean_ctor_get(cur, 0));
        if (ch < 0x80) {
            data[pos++] = (char)ch;
        } else if (ch < 0x800) {
            data[pos++] = (char)(0xC0 | (ch >> 6));
            data[pos++] = (char)(0x80 | (ch & 0x3F));
        } else if (ch < 0x10000) {
            data[pos++] = (char)(0xE0 | (ch >> 12));
            data[pos++] = (char)(0x80 | ((ch >> 6) & 0x3F));
            data[pos++] = (char)(0x80 | (ch & 0x3F));
        } else {
            data[pos++] = (char)(0xF0 | (ch >> 18));
            data[pos++] = (char)(0x80 | ((ch >> 12) & 0x3F));
            data[pos++] = (char)(0x80 | ((ch >> 6) & 0x3F));
            data[pos++] = (char)(0x80 | (ch & 0x3F));
        }
        cur = lean_ctor_get(cur, 1);
    }
    data[byte_count] = '\0';

    lean_dec(cs);
    return o;
}

lean_object *lean_string_data(lean_object *s)
{
    /* Convert String to List Char */
    const uint8_t *data = (const uint8_t *)lean_string_cstr(s);
    size_t sz = lean_string_size(s) - 1;

    /* Build list in reverse, then reverse */
    lean_object *list = lean_box(0);  /* Nil */
    /* We need to build forward, so collect chars first */
    size_t len = lean_string_len(s);
    if (len == 0) return list;

    /* Traverse forward, build list backwards, then we'd need to reverse.
     * Simpler: traverse and build cons cells. We use a two-pass approach. */
    /* Actually, build backwards from the end is complex for UTF-8.
     * Just build forward using a temporary array. */
    uint32_t *chars = (uint32_t *)malloc(len * sizeof(uint32_t));
    size_t pos = 0;
    for (size_t i = 0; i < len; i++) {
        uint8_t c = data[pos];
        if (c < 0x80) { chars[i] = c; pos += 1; }
        else if (c < 0xE0) {
            chars[i] = ((uint32_t)(c & 0x1F) << 6) | (data[pos+1] & 0x3F);
            pos += 2;
        } else if (c < 0xF0) {
            chars[i] = ((uint32_t)(c & 0x0F) << 12)
                     | ((uint32_t)(data[pos+1] & 0x3F) << 6)
                     | (data[pos+2] & 0x3F);
            pos += 3;
        } else {
            chars[i] = ((uint32_t)(c & 0x07) << 18)
                     | ((uint32_t)(data[pos+1] & 0x3F) << 12)
                     | ((uint32_t)(data[pos+2] & 0x3F) << 6)
                     | (data[pos+3] & 0x3F);
            pos += 4;
        }
    }

    /* Build list from end to start */
    for (size_t i = len; i > 0; i--) {
        lean_object *cons = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cons, 0, lean_box(chars[i-1]));
        lean_ctor_set(cons, 1, list);
        list = cons;
    }

    free(chars);
    return list;
}

/* ========================================================================
 * Arrays
 * ======================================================================== */

lean_object *lean_mk_empty_array(void)
{
    return lean_mk_empty_array_with_capacity(lean_box(0));
}

lean_object *lean_mk_empty_array_with_capacity(lean_object *cap)
{
    size_t capacity = lean_unbox(cap);
    if (capacity == 0) capacity = 4;
    size_t sz = sizeof(lean_array_object) + capacity * sizeof(lean_object *);
    lean_object *o = lean_alloc_object(sz);
    o->m_tag = LeanArray;
    o->m_other = 0;
    lean_array_object *a = (lean_array_object *)o;
    a->m_size = 0;
    a->m_capacity = capacity;
    memset(lean_array_cptr(o), 0, capacity * sizeof(lean_object *));
    return o;
}

lean_object *lean_array_push(lean_object *a, lean_object *v)
{
    lean_array_object *arr = (lean_array_object *)a;
    if (!lean_is_exclusive(a)) {
        /* Shared or persistent array — must copy to preserve value semantics */
        a = lean_copy_expand_array(a, arr->m_size < arr->m_capacity ? 0 : 1);
        arr = (lean_array_object *)a;
    } else if (arr->m_size >= arr->m_capacity) {
        a = lean_copy_expand_array(a, 1);
        arr = (lean_array_object *)a;
    }
    lean_array_cptr(a)[arr->m_size] = v;
    arr->m_size++;
    return a;
}

lean_object *lean_mk_array(lean_object *n, lean_object *v)
{
    size_t count = lean_unbox(n);
    size_t sz = sizeof(lean_array_object) + count * sizeof(lean_object *);
    lean_object *o = lean_alloc_object(sz);
    o->m_tag = LeanArray;
    o->m_other = 0;
    lean_array_object *a = (lean_array_object *)o;
    a->m_size = count;
    a->m_capacity = count;
    lean_object **data = lean_array_cptr(o);
    for (size_t i = 0; i < count; i++) {
        lean_inc(v);
        data[i] = v;
    }
    lean_dec(v);
    return o;
}

lean_object *lean_copy_expand_array(lean_object *a, int expand)
{
    lean_array_object *old = (lean_array_object *)a;
    size_t new_cap = expand ? old->m_capacity * 2 : old->m_capacity;
    if (new_cap < 4) new_cap = 4;
    size_t sz = sizeof(lean_array_object) + new_cap * sizeof(lean_object *);
    lean_object *o = lean_alloc_object(sz);
    o->m_tag = LeanArray;
    o->m_other = 0;
    lean_array_object *na = (lean_array_object *)o;
    na->m_size = old->m_size;
    na->m_capacity = new_cap;
    memcpy(lean_array_cptr(o), lean_array_cptr(a),
           old->m_size * sizeof(lean_object *));
    /* Don't dec-ref elements since we copied them */
    /* But do free the old array container (not elements) */
    free(a);
    return o;
}

lean_object *lean_array_get_panic(lean_object *def)
{
    uart_puts("[lean] array index out of bounds\n");
    return def;
}

lean_object *lean_array_set_panic(lean_object *a, lean_object *v)
{
    uart_puts("[lean] array set index out of bounds\n");
    lean_dec(v);
    return a;
}

/* ========================================================================
 * Boxing / Unboxing
 * ======================================================================== */

lean_object *lean_box_uint32(uint32_t v)
{
    /* On 64-bit, uint32 fits in a scalar */
    return lean_box((size_t)v);
}

lean_object *lean_box_uint64(uint64_t v)
{
    /* Must allocate a ctor with scalar data */
    lean_object *o = lean_alloc_ctor(0, 0, sizeof(uint64_t));
    lean_ctor_set_uint64(o, 0, v);
    return o;
}

lean_object *lean_box_usize(size_t v)
{
    return lean_box(v);
}

lean_object *lean_box_float(double v)
{
    /* Store raw bits to avoid soft-float codegen */
    lean_object *o = lean_alloc_ctor(0, 0, sizeof(uint64_t));
    uint64_t bits;
    __builtin_memcpy(&bits, &v, sizeof(bits));
    lean_ctor_set_uint64(o, 0, bits);
    return o;
}

uint32_t lean_unbox_uint32(lean_object *o)
{
    return (uint32_t)lean_unbox(o);
}

uint64_t lean_unbox_uint64(lean_object *o)
{
    return lean_ctor_get_uint64(o, 0);
}

size_t lean_unbox_usize(lean_object *o)
{
    return lean_unbox(o);
}

double lean_unbox_float(lean_object *o)
{
    uint64_t bits = lean_ctor_get_uint64(o, 0);
    double v;
    __builtin_memcpy(&v, &bits, sizeof(v));
    return v;
}

lean_object *lean_unsigned_to_nat(size_t n)
{
    /* If it fits in a scalar (which on 64-bit is ~2^63 values), box it */
    return lean_box(n);
}

lean_object *lean_cstr_to_nat(const char *s)
{
    size_t n = 0;
    while (*s >= '0' && *s <= '9') {
        n = n * 10 + (size_t)(*s - '0');
        s++;
    }
    return lean_box(n);
}

/* ========================================================================
 * Closure Application
 * ======================================================================== */

/*
 * A closure has:
 *   m_fun:       the C function pointer
 *   m_arity:     total args the function expects
 *   m_num_fixed: args already captured in the closure
 *
 * When we apply N args:
 *   - If num_fixed + N == arity: call m_fun(fixed_args..., new_args...)
 *   - If num_fixed + N < arity:  create new closure with more fixed args
 *   - If num_fixed + N > arity:  call with exactly enough, then apply rest
 */

typedef lean_object *(*lean_cfun1)(lean_object *);
typedef lean_object *(*lean_cfun2)(lean_object *, lean_object *);
typedef lean_object *(*lean_cfun3)(lean_object *, lean_object *, lean_object *);
typedef lean_object *(*lean_cfun4)(lean_object *, lean_object *, lean_object *, lean_object *);
typedef lean_object *(*lean_cfun5)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *);
typedef lean_object *(*lean_cfun6)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *);
typedef lean_object *(*lean_cfun7)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *);
typedef lean_object *(*lean_cfun8)(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *, lean_object *);

static lean_object *lean_closure_call(lean_object *closure, unsigned total_n, lean_object **all_args)
{
    lean_closure_object *c = (lean_closure_object *)closure;
    lean_cfun fun = c->m_fun;
    unsigned arity = c->m_arity;
    unsigned fixed = c->m_num_fixed;
    lean_object **fargs = lean_closure_arg_cptr(closure);

    unsigned total_avail = fixed + total_n;

    if (total_avail < arity) {
        /* Under-application: create new closure with more fixed args */
        lean_object *nc = lean_alloc_closure(fun, arity, total_avail);
        lean_object **nargs = lean_closure_arg_cptr(nc);
        for (unsigned i = 0; i < fixed; i++) {
            lean_inc(fargs[i]);
            nargs[i] = fargs[i];
        }
        for (unsigned i = 0; i < total_n; i++) {
            nargs[fixed + i] = all_args[i];
        }
        lean_dec(closure);
        return nc;
    }

    /* Build full arg array */
    unsigned needed = arity;
    lean_object *args_buf[16];
    lean_object **args = (needed <= 16) ? args_buf : (lean_object **)malloc(needed * sizeof(lean_object *));
    for (unsigned i = 0; i < fixed; i++) {
        lean_inc(fargs[i]);
        args[i] = fargs[i];
    }
    unsigned args_from_new = needed - fixed;
    for (unsigned i = 0; i < args_from_new; i++) {
        args[fixed + i] = all_args[i];
    }

    /* Call the function */
    lean_object *res;
    switch (arity) {
    case 1: res = ((lean_cfun1)fun)(args[0]); break;
    case 2: res = ((lean_cfun2)fun)(args[0], args[1]); break;
    case 3: res = ((lean_cfun3)fun)(args[0], args[1], args[2]); break;
    case 4: res = ((lean_cfun4)fun)(args[0], args[1], args[2], args[3]); break;
    case 5: res = ((lean_cfun5)fun)(args[0], args[1], args[2], args[3], args[4]); break;
    case 6: res = ((lean_cfun6)fun)(args[0], args[1], args[2], args[3], args[4], args[5]); break;
    case 7: res = ((lean_cfun7)fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6]); break;
    case 8: res = ((lean_cfun8)fun)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]); break;
    default:
        lean_internal_panic("lean_closure_call: arity > 8 not supported");
        __builtin_unreachable();
    }

    if (args != args_buf) free(args);
    lean_dec(closure);

    /* Over-application: apply remaining args */
    if (total_avail > arity) {
        unsigned remaining = total_n - args_from_new;
        lean_object **rest = all_args + args_from_new;
        for (unsigned i = 0; i < remaining; i++) {
            res = lean_apply_1(res, rest[i]);
        }
    }

    return res;
}

lean_object *lean_apply_1(lean_object *f, lean_object *a1)
{
    lean_object *args[] = { a1 };
    return lean_closure_call(f, 1, args);
}

lean_object *lean_apply_2(lean_object *f, lean_object *a1, lean_object *a2)
{
    lean_object *args[] = { a1, a2 };
    return lean_closure_call(f, 2, args);
}

lean_object *lean_apply_3(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3)
{
    lean_object *args[] = { a1, a2, a3 };
    return lean_closure_call(f, 3, args);
}

lean_object *lean_apply_4(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4)
{
    lean_object *args[] = { a1, a2, a3, a4 };
    return lean_closure_call(f, 4, args);
}

lean_object *lean_apply_5(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5)
{
    lean_object *args[] = { a1, a2, a3, a4, a5 };
    return lean_closure_call(f, 5, args);
}

lean_object *lean_apply_6(lean_object *f, lean_object *a1, lean_object *a2, lean_object *a3, lean_object *a4, lean_object *a5, lean_object *a6)
{
    lean_object *args[] = { a1, a2, a3, a4, a5, a6 };
    return lean_closure_call(f, 6, args);
}

lean_object *lean_apply_n(lean_object *f, unsigned n, lean_object **args)
{
    return lean_closure_call(f, n, args);
}

lean_object *lean_apply_m(lean_object *f, unsigned n, lean_object **args)
{
    return lean_apply_n(f, n, args);
}

/* ========================================================================
 * Panic
 * ======================================================================== */

lean_object *lean_panic_fn(lean_object *def, lean_object *msg)
{
    uart_puts("[lean] PANIC: ");
    if (!lean_is_scalar(msg) && msg->m_tag == LeanString) {
        uart_puts(lean_string_cstr(msg));
    }
    uart_puts("\n");
    lean_dec(msg);
    return def;
}

void lean_internal_panic(const char *msg)
{
    uart_puts("[lean] INTERNAL PANIC: ");
    uart_puts(msg);
    uart_puts("\n");
    abort();
}

void lean_internal_panic_unreachable(void)
{
    lean_internal_panic("unreachable code reached");
}

void lean_internal_panic_out_of_memory(void)
{
    lean_internal_panic("out of memory");
}

void lean_internal_panic_rc_overflow(void)
{
    lean_internal_panic("reference count overflow");
}

/* ========================================================================
 * IO
 * ======================================================================== */

/*
 * IO.FS.Stream is a Lean structure compiled as a constructor with 5 fields:
 *   field 0: flush  (World → IO Unit)
 *   field 1: read   (USize → World → IO ByteArray)
 *   field 2: write  (ByteArray → World → IO USize)
 *   field 3: getLine (World → IO String)
 *   field 4: putStr (String → World → IO Unit)
 *
 * lean_get_stdout() returns a persistent Stream object.
 */

static lean_object *stream_flush_impl(lean_object *w) {
    (void)w;
    return lean_io_result_mk_ok(lean_box(0));
}

static lean_object *stream_read_impl(lean_object *n, lean_object *w) {
    (void)n; (void)w;
    /* Return empty byte array stub */
    return lean_io_result_mk_ok(lean_box(0));
}

static lean_object *stream_write_impl(lean_object *data, lean_object *w) {
    (void)data; (void)w;
    lean_dec(data);
    return lean_io_result_mk_ok(lean_box(0));
}

static lean_object *stream_getline_impl(lean_object *w) {
    (void)w;
    return lean_io_result_mk_ok(lean_mk_string(""));
}

static lean_object *stream_putstr_impl(lean_object *s, lean_object *w) {
    (void)w;
    if (!lean_is_scalar(s) && s->m_tag == LeanString) {
        uart_puts(lean_string_cstr(s));
    }
    lean_dec(s);
    return lean_io_result_mk_ok(lean_box(0));
}

static lean_object *stdout_stream = (lean_object *)0;
static lean_object *stderr_stream = (lean_object *)0;
static lean_object *stdin_stream = (lean_object *)0;

static lean_object *make_stream(
    lean_object *(*flush_fn)(lean_object *),
    lean_object *(*read_fn)(lean_object *, lean_object *),
    lean_object *(*write_fn)(lean_object *, lean_object *),
    lean_object *(*getline_fn)(lean_object *),
    lean_object *(*putstr_fn)(lean_object *, lean_object *))
{
    lean_object *stream = lean_alloc_ctor(0, 5, 0);
    lean_ctor_set(stream, 0, lean_alloc_closure((lean_cfun)flush_fn, 1, 0));
    lean_ctor_set(stream, 1, lean_alloc_closure((lean_cfun)read_fn, 2, 0));
    lean_ctor_set(stream, 2, lean_alloc_closure((lean_cfun)write_fn, 2, 0));
    lean_ctor_set(stream, 3, lean_alloc_closure((lean_cfun)getline_fn, 1, 0));
    lean_ctor_set(stream, 4, lean_alloc_closure((lean_cfun)putstr_fn, 2, 0));
    lean_mark_persistent(stream);
    return stream;
}

lean_object *lean_get_stdout(void)
{
    if (!stdout_stream)
        stdout_stream = make_stream(stream_flush_impl, stream_read_impl,
                                    stream_write_impl, stream_getline_impl,
                                    stream_putstr_impl);
    lean_inc(stdout_stream);
    return stdout_stream;
}

lean_object *lean_get_stderr(void)
{
    if (!stderr_stream)
        stderr_stream = make_stream(stream_flush_impl, stream_read_impl,
                                    stream_write_impl, stream_getline_impl,
                                    stream_putstr_impl);
    lean_inc(stderr_stream);
    return stderr_stream;
}

lean_object *lean_get_stdin(void)
{
    if (!stdin_stream)
        stdin_stream = make_stream(stream_flush_impl, stream_read_impl,
                                   stream_write_impl, stream_getline_impl,
                                   stream_putstr_impl);
    lean_inc(stdin_stream);
    return stdin_stream;
}

lean_object *lean_io_prim_handle_put_str(lean_object *h, lean_object *s, lean_object *w)
{
    (void)h;
    (void)w;
    if (!lean_is_scalar(s) && s->m_tag == LeanString) {
        uart_puts(lean_string_cstr(s));
    }
    lean_dec(s);
    return lean_io_result_mk_ok(lean_box(0));
}

lean_object *lean_io_prim_put_str(lean_object *s, lean_object *w)
{
    (void)w;
    if (!lean_is_scalar(s) && s->m_tag == LeanString) {
        uart_puts(lean_string_cstr(s));
    }
    lean_dec(s);
    return lean_io_result_mk_ok(lean_box(0));
}

lean_object *lean_io_result_show_error(lean_object *r)
{
    if (lean_io_result_is_error(r)) {
        lean_object *err = lean_ctor_get(r, 0);
        if (!lean_is_scalar(err) && err->m_tag == LeanString) {
            uart_puts("[lean] IO error: ");
            uart_puts(lean_string_cstr(err));
            uart_puts("\n");
        } else {
            uart_puts("[lean] IO error (non-string)\n");
        }
    }
    return lean_box(0);
}

lean_object *lean_io_prim_handle_get_line(lean_object *h, lean_object *w)
{
    (void)h;
    (void)w;
    /* No input on bare-metal, return empty string */
    return lean_io_result_mk_ok(lean_mk_string(""));
}

/* ========================================================================
 * Initialization
 * ======================================================================== */

static uint8_t g_panic_messages = 1;

void lean_initialize_runtime_module(void)
{
    uart_init();
    heap_init();
}

void lean_io_mark_end_initialization(void)
{
    /* Nothing to do in single-threaded mode */
}

char **lean_setup_args(int argc, char **argv)
{
    /* No command-line args on bare-metal */
    (void)argc;
    return argv;
}

void lean_set_panic_messages(uint8_t flag)
{
    g_panic_messages = flag;
}

void lean_init_task_manager(void)
{
    /* No threading on bare-metal */
}

void lean_finalize_task_manager(void)
{
    /* No threading on bare-metal */
}

/* ========================================================================
 * Once-cells (single-threaded: simple null-check)
 * ======================================================================== */

lean_object *lean_object_once(lean_object **slot, lean_object *(*init)(lean_object *))
{
    if (*slot == (lean_object *)0) {
        lean_object *r = init(lean_box(0));
        if (lean_io_result_is_ok(r)) {
            *slot = lean_io_result_get_value(r);
            lean_inc(*slot);
            lean_mark_persistent(*slot);
        }
        lean_dec(r);
    }
    return *slot;
}

/* ========================================================================
 * ST Ref (mutable references — single-threaded)
 * ======================================================================== */

/* We store ST refs as constructor objects with one field */

lean_object *lean_st_mk_ref(lean_object *v, lean_object *w)
{
    (void)w;
    lean_object *r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, v);
    return lean_io_result_mk_ok(r);
}

lean_object *lean_st_ref_get(lean_object *r, lean_object *w)
{
    (void)w;
    lean_object *val = lean_ctor_get(r, 0);
    lean_inc(val);
    return lean_io_result_mk_ok(val);
}

lean_object *lean_st_ref_set(lean_object *r, lean_object *v, lean_object *w)
{
    (void)w;
    lean_object *old = lean_ctor_get(r, 0);
    lean_dec(old);
    lean_ctor_set(r, 0, v);
    return lean_io_result_mk_ok(lean_box(0));
}

lean_object *lean_st_ref_take(lean_object *r, lean_object *w)
{
    (void)w;
    lean_object *val = lean_ctor_get(r, 0);
    lean_ctor_set(r, 0, lean_box(0));
    return lean_io_result_mk_ok(val);
}

lean_object *lean_st_ref_swap(lean_object *r, lean_object *v, lean_object *w)
{
    (void)w;
    lean_object *old = lean_ctor_get(r, 0);
    lean_ctor_set(r, 0, v);
    return lean_io_result_mk_ok(old);
}

/* ========================================================================
 * Nat/Int big operations (stubs — panic on overflow)
 * ======================================================================== */

#define BIG_PANIC(name) \
    lean_object *name(lean_object *a, lean_object *b) { \
        (void)a; (void)b; \
        lean_internal_panic(#name ": big numbers not supported"); \
    }

#define BIG_CMP_PANIC(name) \
    uint8_t name(lean_object *a, lean_object *b) { \
        (void)a; (void)b; \
        lean_internal_panic(#name ": big numbers not supported"); \
    }

lean_object *lean_nat_big_succ(lean_object *a)
{
    (void)a;
    lean_internal_panic("lean_nat_big_succ: big numbers not supported");
}

BIG_PANIC(lean_nat_big_add)
BIG_PANIC(lean_nat_big_sub)
BIG_PANIC(lean_nat_big_mul)
BIG_PANIC(lean_nat_big_div)
BIG_PANIC(lean_nat_big_mod)
BIG_CMP_PANIC(lean_nat_big_eq)
BIG_CMP_PANIC(lean_nat_big_le)
BIG_CMP_PANIC(lean_nat_big_lt)

lean_object *lean_int_big_neg(lean_object *a)
{
    (void)a;
    lean_internal_panic("lean_int_big_neg: big numbers not supported");
}

BIG_PANIC(lean_int_big_add)
BIG_PANIC(lean_int_big_sub)
BIG_PANIC(lean_int_big_mul)

/* ========================================================================
 * Thunk (single-threaded: evaluate immediately)
 * ======================================================================== */

lean_object *lean_mk_thunk(lean_object *c)
{
    size_t sz = sizeof(lean_thunk_object);
    lean_object *o = lean_alloc_object(sz);
    o->m_tag = LeanThunk;
    o->m_other = 0;
    lean_thunk_object *t = (lean_thunk_object *)o;
    t->m_value = (lean_object *)0;
    t->m_closure = c;
    return o;
}

lean_object *lean_thunk_pure(lean_object *v)
{
    size_t sz = sizeof(lean_thunk_object);
    lean_object *o = lean_alloc_object(sz);
    o->m_tag = LeanThunk;
    o->m_other = 0;
    lean_thunk_object *t = (lean_thunk_object *)o;
    t->m_value = v;
    t->m_closure = (lean_object *)0;
    return o;
}

lean_object *lean_thunk_get_core(lean_object *t)
{
    lean_thunk_object *th = (lean_thunk_object *)t;
    if (th->m_value == (lean_object *)0) {
        /* Force the thunk */
        lean_object *c = th->m_closure;
        lean_inc(c);
        lean_object *val = lean_apply_1(c, lean_box(0));
        th->m_value = val;
        lean_inc(val);
        lean_dec(th->m_closure);
        th->m_closure = (lean_object *)0;
    }
    return th->m_value;
}

lean_object *lean_thunk_get(lean_object *t)
{
    lean_object *v = lean_thunk_get_core(t);
    lean_inc(v);
    return v;
}

lean_object *lean_thunk_get_own(lean_object *t)
{
    lean_object *v = lean_thunk_get_core(t);
    lean_inc(v);
    lean_dec(t);
    return v;
}

/* ========================================================================
 * Float to string (minimal)
 * ======================================================================== */

lean_object *lean_float_to_string(double d)
{
    /* Stub — float-to-string requires soft-float libgcc on rv64imac.
     * Will implement properly when targeting rv64gc or linking libgcc. */
    (void)d;
    return lean_mk_string("<float>");
}

/* ========================================================================
 * ByteArray (stubs)
 * ======================================================================== */

lean_object *lean_byte_array_mk(lean_object *l)
{
    /* Convert List UInt8 to ByteArray */
    /* Count elements */
    size_t count = 0;
    lean_object *cur = l;
    while (cur->m_tag == 1) { count++; cur = lean_ctor_get(cur, 1); }

    size_t sz = sizeof(lean_sarray_object) + count;
    lean_object *o = lean_alloc_object(sz);
    o->m_tag = LeanScalarArray;
    o->m_other = 0;
    lean_sarray_object *a = (lean_sarray_object *)o;
    a->m_size = count;
    a->m_capacity = count;

    uint8_t *data = (uint8_t *)((char *)o + sizeof(lean_sarray_object));
    cur = l;
    for (size_t i = 0; i < count; i++) {
        data[i] = (uint8_t)lean_unbox(lean_ctor_get(cur, 0));
        cur = lean_ctor_get(cur, 1);
    }

    lean_dec(l);
    return o;
}

lean_object *lean_byte_array_data(lean_object *a)
{
    lean_sarray_object *sa = (lean_sarray_object *)a;
    uint8_t *data = (uint8_t *)((char *)a + sizeof(lean_sarray_object));
    lean_object *list = lean_box(0);  /* Nil */

    for (size_t i = sa->m_size; i > 0; i--) {
        lean_object *cons = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(cons, 0, lean_box(data[i-1]));
        lean_ctor_set(cons, 1, list);
        list = cons;
    }
    return list;
}

lean_object *lean_byte_array_push(lean_object *a, uint8_t b)
{
    lean_sarray_object *sa = (lean_sarray_object *)a;
    uint8_t *data = (uint8_t *)((char *)a + sizeof(lean_sarray_object));

    if (sa->m_size >= sa->m_capacity) {
        size_t new_cap = sa->m_capacity * 2;
        if (new_cap < 8) new_cap = 8;
        size_t sz = sizeof(lean_sarray_object) + new_cap;
        lean_object *o = lean_alloc_object(sz);
        o->m_tag = LeanScalarArray;
        o->m_other = 0;
        lean_sarray_object *na = (lean_sarray_object *)o;
        na->m_size = sa->m_size;
        na->m_capacity = new_cap;
        memcpy((char *)o + sizeof(lean_sarray_object), data, sa->m_size);
        free(a);
        a = o;
        data = (uint8_t *)((char *)a + sizeof(lean_sarray_object));
        sa = (lean_sarray_object *)a;
    }

    data[sa->m_size] = b;
    sa->m_size++;
    return a;
}

lean_object *lean_copy_byte_array(lean_object *a)
{
    lean_sarray_object *sa = (lean_sarray_object *)a;
    size_t sz = sizeof(lean_sarray_object) + sa->m_capacity;
    lean_object *o = lean_alloc_object(sz);
    o->m_tag = LeanScalarArray;
    o->m_other = 0;
    lean_sarray_object *na = (lean_sarray_object *)o;
    na->m_size = sa->m_size;
    na->m_capacity = sa->m_capacity;
    memcpy((char *)o + sizeof(lean_sarray_object),
           (char *)a + sizeof(lean_sarray_object), sa->m_size);
    return o;
}

/* ========================================================================
 * Heartbeat / Cancel stubs
 * ======================================================================== */

uint32_t lean_get_num_heartbeats(void)
{
    return 0;
}

void lean_set_max_heartbeat(uint32_t n)
{
    (void)n;
}

uint8_t lean_io_check_canceled(lean_object *w)
{
    (void)w;
    return 0;
}

lean_object *lean_io_cancel(lean_object *w)
{
    (void)w;
    return lean_io_result_mk_ok(lean_box(0));
}

lean_object *lean_io_get_num_heartbeats(lean_object *w)
{
    (void)w;
    return lean_io_result_mk_ok(lean_box(0));
}

/* ========================================================================
 * Char.ofNat — used by generated code for Char.ofNat
 * ======================================================================== */

uint32_t l_Char_ofNat(lean_object *n)
{
    uint32_t v = 0;
    if (lean_is_scalar(n))
        v = (uint32_t)lean_unbox(n);
    /* Validate Unicode scalar value */
    if (v > 0x10FFFF || (v >= 0xD800 && v <= 0xDFFF))
        return 0;
    return v;
}

/* ========================================================================
 * Nat.reprFast — convert Nat to decimal string
 * ======================================================================== */

lean_object *l_Nat_reprFast(lean_object *n)
{
    if (lean_is_scalar(n)) {
        size_t v = lean_unbox(n);
        if (v == 0) return lean_mk_string("0");
        char buf[24];
        int pos = 23;
        buf[pos] = '\0';
        while (v > 0 && pos > 0) {
            pos--;
            buf[pos] = '0' + (char)(v % 10);
            v /= 10;
        }
        return lean_mk_string(buf + pos);
    }
    return lean_mk_string("<bignat>");
}

/* ========================================================================
 * RISC-V cycle counter
 * ======================================================================== */

lean_object *lean_cycles_now(lean_object *w)
{
    (void)w;
    uint64_t c;
    __asm__ volatile ("rdcycle %0" : "=r"(c));
    return lean_io_result_mk_ok(lean_box_uint64(c));
}
