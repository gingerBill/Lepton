#if defined(_MSC_VER)
#define _CRT_SECURE_NO_WARNINGS
#include <windows.h>
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>

#ifndef STATIC_ASSERT
	#define STATIC_ASSERT3(cond, msg) typedef char static_assertion_##msg[(!!(cond))*2-1]
	// //NOTE(bill): Token pasting madness!!
	#define STATIC_ASSERT2(cond, line) STATIC_ASSERT3(cond, static_assertion_at_line_##line)
	#define STATIC_ASSERT1(cond, line) STATIC_ASSERT2(cond, line)
	#define STATIC_ASSERT(cond)        STATIC_ASSERT1(cond, __LINE__)
#endif


#if defined(_MSC_VER)
	#if _MSC_VER < 1300
	typedef unsigned char     u8;
	typedef   signed char     i8;
	typedef unsigned short   u16;
	typedef   signed short   i16;
	typedef unsigned int     u32;
	typedef   signed int     i32;
	#else
	typedef unsigned __int8   u8;
	typedef   signed __int8   i8;
	typedef unsigned __int16 u16;
	typedef   signed __int16 i16;
	typedef unsigned __int32 u32;
	typedef   signed __int32 i32;
	#endif
	typedef unsigned __int64 u64;
	typedef   signed __int64 i64;
#else
	#include <stdint.h>
	typedef uint8_t   u8;
	typedef  int8_t   i8;
	typedef uint16_t u16;
	typedef  int16_t i16;
	typedef uint32_t u32;
	typedef  int32_t i32;
	typedef uint64_t u64;
	typedef  int64_t i64;
#endif

STATIC_ASSERT(sizeof(u8)  == sizeof(i8));
STATIC_ASSERT(sizeof(u16) == sizeof(i16));
STATIC_ASSERT(sizeof(u32) == sizeof(i32));
STATIC_ASSERT(sizeof(u64) == sizeof(i64));

STATIC_ASSERT(sizeof(u8)  == 1);
STATIC_ASSERT(sizeof(u16) == 2);
STATIC_ASSERT(sizeof(u32) == 4);
STATIC_ASSERT(sizeof(u64) == 8);

typedef size_t    usize;
typedef ptrdiff_t isize;

STATIC_ASSERT(sizeof(usize) == sizeof(isize));

// NOTE(bill): (u)intptr is only here for semantic reasons really as this library will only support 32/64 bit OSes.
// NOTE(bill): Are there any modern OSes (not 16 bit) where intptr != isize ?
#if defined(_WIN64)
	typedef signed   __int64  intptr;
	typedef unsigned __int64 uintptr;
#elif defined(_WIN32)
	// NOTE(bill); To mark types changing their size, e.g. intptr
	#ifndef _W64
		#if !defined(__midl) && (defined(_X86_) || defined(_M_IX86)) && _MSC_VER >= 1300
			#define _W64 __w64
		#else
			#define _W64
		#endif
	#endif

	typedef _W64   signed int  intptr;
	typedef _W64 unsigned int uintptr;
#else
	typedef uintptr_t uintptr;
	typedef  intptr_t  intptr;
#endif

STATIC_ASSERT(sizeof(uintptr) == sizeof(intptr));

typedef float  f32;
typedef double f64;

STATIC_ASSERT(sizeof(f32) == 4);
STATIC_ASSERT(sizeof(f64) == 8);


// NOTE(bill): Get true and false
#if !defined(__cplusplus)
	#if (defined(_MSC_VER) && _MSC_VER < 1800) || (!defined(_MSC_VER) && !defined(__STDC_VERSION__))
		#ifndef true
		#define true  (0 == 0)
		#endif
		#ifndef false
		#define false (0 != 0)
		#endif
		typedef u8 bool;
	#else
		#include <stdbool.h>
	#endif
#endif

#ifndef offsetof
#define offsetof(st, m) ((isize)&(((st *)0)->m))
#endif
#ifndef alignof
#define alignof(TYPE_) offsetof(struct { char c; TYPE_ member; }, member)
#endif
#ifndef countof
#define countof(x) sizeof(x)/sizeof(*x)
#endif

#ifndef MIN
#define MIN(a, b) ((a) < (b) ? (a) : (b))
#endif
#ifndef MAX
#define MAX(a, b) ((a) > (b) ? (a) : (b))
#endif
#ifndef ABS
#define ABS(x) ((x) < 0 ? -(x) : (x))
#endif

#ifndef cast
#define cast(TYPE_) (TYPE_)
#endif


typedef struct String {
	char *text;
	isize len;
} String;

#define str_lit(text_) {text_, sizeof(text_)-1}
#define LIT(str) (int)str.len, str.text

String make_string(char *text, isize len) {
	String s;
	s.text = text;
	if (len < 0) {
		len = text != NULL ? strlen(cast(char *)text) : 0;
	}
	s.len = len;
	return s;
}

String make_string_c(char *text) {
	return make_string(text, -1);
}

String substring(String s, isize lo, isize hi) {
	isize max = s.len;
	assert(lo <= hi && hi <= max);

	return make_string(s.text+lo, hi-lo);
}


int string_compare(String x, String y) {
	if (x.len != y.len || x.text != y.text) {
		isize n, fast, offset, curr_block;
		isize *la, *lb;
		isize pos;

		n = MIN(x.len, y.len);

		fast = n/sizeof(isize) + 1;
		offset = (fast-1)*sizeof(isize);
		curr_block = 0;
		if (n <= sizeof(isize)) {
			fast = 0;
		}

		la = cast(isize *)x.text;
		lb = cast(isize *)y.text;

		for (; curr_block < fast; curr_block++) {
			if (la[curr_block] ^ lb[curr_block]) {
				for (pos = curr_block*sizeof(isize); pos < n; pos++) {
					if (x.text[pos] ^ y.text[pos]) {
						return cast(int)x.text[pos] - cast(int)y.text[pos];
					}
				}
			}
		}

		for (; offset < n; offset++) {
			if (x.text[offset] ^ y.text[offset]) {
				return cast(int)x.text[offset] - cast(int)y.text[offset];
			}
		}
	}
	return 0;
}


bool str_eq(String a, String b) {
	isize i;
	if (a.len != b.len) {
		return false;
	}
	for (i = 0; i < a.len; i++) {
		if (a.text[i] != b.text[i]) {
			return false;
		}
	}
	return true;
}
bool str_ne(String a, String b) { return !str_eq(a, b);                }
bool str_lt(String a, String b) { return string_compare(a, b) < 0;     }
bool str_gt(String a, String b) { return string_compare(a, b) > 0;     }
bool str_le(String a, String b) { return string_compare(a, b) <= 0;    }
bool str_ge(String a, String b) { return string_compare(a, b) >= 0;    }



void fatal(char const *fmt, ...) {
	va_list args;
	va_start(args, fmt);
	fprintf(stderr, "FATAL: ");
	vfprintf(stderr, fmt, args);
	fprintf(stderr, "\n");
	va_end(args);
	exit(1);
}



#define ALIGN_DOWN(n, a)     ((n) & ~((a) - 1))
#define ALIGN_UP(n, a)       ALIGN_DOWN((n) + (a) - 1, (a))
#define ALIGN_DOWN_PTR(p, a) (cast(void *)ALIGN_DOWN(cast(uintptr)(p), (a)))
#define ALIGN_UP_PTR(p, a)   (cast(void *)ALIGN_UP(cast(uintptr)(p), (a)))

void *mem_zero(void *ptr, isize size) {
	return memset(ptr, 0, size);
}
#define mem_zero_item(ptr) mem_zero((ptr), sizeof(*ptr));

void *mem_alloc(isize size) {
	void *ptr;
	assert(size > 0);
	ptr = malloc(size);
	if (!ptr) {
		fatal("mem_alloc failed");
	}
	mem_zero(ptr, size);
	return ptr;
}

void *mem_realloc(void *ptr, isize size) {
	assert(size >= 0);
	ptr = realloc(ptr, size);
	if (!ptr) {
		fatal("mem_realloc failed");
	}
	return ptr;
}

void *mem_dup(void *src, isize size) {
	void *dest = mem_alloc(size);
	memmove(dest, src, size);
	return dest;
}

void mem_free(void *ptr) {
	if (ptr) free(ptr);
}

#define mem_alloc_array(TYPE_, n) (TYPE_ *)mem_alloc((n)*sizeof(TYPE_))
#define mem_new(TYPE_) (TYPE_ *)mem_alloc(sizeof(TYPE_))



typedef struct BufferHeader {
	isize len, cap;
} BufferHeader;

#define buf(TYPE_) TYPE_ *

#define buf__hdr(b) (cast(BufferHeader *)(b) - 1)
#define buf_len(b) ((b) ? buf__hdr(b)->len : 0)
#define buf_cap(b) ((b) ? buf__hdr(b)->cap : 0)
#define buf_end(b) ((b) + buf_len(b))
#define buf_sizeof(b) ((b) ? buf_len(b)*sizeof(*(b)) : 0)

#define buf_free(b) ((b) ? (mem_free(buf__hdr(b)), (b) = NULL) : 0)
#define buf_fit(b, n) ((n) <= buf_cap(b) ? 0 : ((b) = buf__grow((b), (n), sizeof(*(b)))))
#define buf_push(b, ...) (buf_fit((b), 1 + buf_len(b)), (b)[buf__hdr(b)->len++] = (__VA_ARGS__), (b))
#define buf_pop(b) ((b) : assert(buf_len(b) > 0), buf__hdr(b)->len-- ? 0)
#define buf_clear(b) ((b) : buf__hdr(b)->len = 0, 0)

#define buf_printf(b) ((b) : buf__hdr(b)->len = 0, 0)

#define for_buf(idx_, b) for(idx_ = 0; idx_ < buf_len(b); idx_++)


void *buf__grow(void const *b, isize new_len, isize elem_size) {
	isize new_cap, new_size;
	BufferHeader *new_header;

	new_cap = MAX(MAX(2*buf_cap(b)+8, new_len), 16);
	assert(new_len <= new_cap);

	new_size = sizeof(BufferHeader) + new_cap*elem_size;
	if (b) {
		new_header = mem_realloc(buf__hdr(b), new_size);
	} else {
		new_header = mem_alloc(new_size);
		new_header->len = 0;
	}
	new_header->cap = new_cap;
	return cast(void *)(new_header+1);
}

char *buf__printf(char *buf, char const *fmt, ...) {
	isize n, cap;
    va_list args;
    va_start(args, fmt);
    cap = buf_cap(buf) - buf_len(buf);
    n = 1 + vsnprintf(buf_end(buf), cap, fmt, args);
    va_end(args);
    if (n > cap) {
        buf_fit(buf, n + buf_len(buf));
        va_start(args, fmt);
        cap = buf_cap(buf) - buf_len(buf);
        n = 1 + vsnprintf(buf_end(buf), cap, fmt, args);
        assert(n <= cap);
        va_end(args);
    }
    buf__hdr(buf)->len += n - 1;
    return buf;
}


// Arena from Per Vognsen
typedef struct Arena {
	char *ptr;
	char *end;
	char **blocks;
} Arena;

#define ARENA_ALIGNMENT 8
#define ARENA_BLOCK_SIZE 1024

void arena_grow(Arena *arena, isize min_size) {
	isize size = MAX(ARENA_BLOCK_SIZE, min_size);
	size = ALIGN_UP(size, ARENA_ALIGNMENT);
    arena->ptr = mem_alloc(size);
    assert(arena->ptr == ALIGN_DOWN_PTR(arena->ptr, ARENA_ALIGNMENT));
    arena->end = arena->ptr + size;
    buf_push(arena->blocks, arena->ptr);
}

void *arena_alloc(Arena *arena, isize size) {
    void *ptr;

    if (size > (arena->end - arena->ptr)) {
        arena_grow(arena, size);
        assert(size <= (arena->end - arena->ptr));
    }
    ptr = arena->ptr;
    arena->ptr = ALIGN_UP_PTR(arena->ptr + size, ARENA_ALIGNMENT);
    assert(arena->ptr <= arena->end);
    assert(ptr == ALIGN_DOWN_PTR(ptr, ARENA_ALIGNMENT));
    return ptr;
}

void arena_free(Arena *arena) {
	isize i;
	for (i = 0; i < buf_len(arena->blocks); i++) {
        mem_free(arena->blocks[i]);
    }
    buf_free(arena->blocks);
}



// File stuff


isize file_size(FILE *fp) {
	isize fsize;
	fseek(fp, 0, SEEK_END);
	fsize = cast(isize)ftell(fp);
	fseek(fp, 0, SEEK_SET);
	return fsize;
}

String read_entire_file(char const *path) {
	String res = {0};
	FILE *f = fopen(path, "rb");
	if (f != NULL) {
		long fsize = file_size(f);

		res.text = mem_alloc(fsize+1);
		fread(res.text, fsize, 1, f);
		res.text[fsize] = 0;
		res.len = cast(isize)fsize;

		fclose(f);
	}
	return res;
}


#if defined(_MSC_VER)
static wchar_t *win32_alloc_utf8_to_ucs2(char const *text, isize *w_len_) {
	wchar_t *w_text = NULL;
	isize len = 0, w_len = 0, w_len1 = 0;
	if (text == NULL) {
		if (w_len_) *w_len_ = w_len;
		return NULL;
	}
	len = strlen(text);
	if (len == 0) {
		if (w_len_) *w_len_ = w_len;
		return NULL;
	}
	w_len = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, text, cast(int)len, NULL, 0);
	if (w_len == 0) {
		if (w_len_) *w_len_ = w_len;
		return NULL;
	}
	w_text = mem_alloc_array(wchar_t, w_len+1);
	w_len1 = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, text, cast(int)len, w_text, cast(int)w_len);
	if (w_len1 == 0) {
		mem_free(w_text);
		if (w_len_) *w_len_ = 0;
		return NULL;
	}
	w_text[w_len] = 0;
	if (w_len_) *w_len_ = w_len;
	return w_text;
}
#endif

char *get_fullpath(char const *path) {
#if defined(_MSC_VER)
// TODO(bill): Make UTF-8
	wchar_t *w_path = NULL;
	wchar_t *w_fullpath = NULL;
	isize w_len = 0;
	isize new_len = 0;
	isize new_len1 = 0;
	char *new_path = 0;
	w_path = win32_alloc_utf8_to_ucs2(path, NULL);
	if (w_path == NULL) {
		return NULL;
	}
	w_len = GetFullPathNameW(w_path, 0, NULL, NULL);
	if (w_len == 0) {
		return NULL;
	}
	w_fullpath = mem_alloc_array(wchar_t, w_len+1);
	GetFullPathNameW(w_path, cast(int)w_len, w_fullpath, NULL);
	w_fullpath[w_len] = 0;
	mem_free(w_path);

	new_len = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, w_fullpath, cast(int)w_len, NULL, 0, NULL, NULL);
	if (new_len == 0) {
		mem_free(w_fullpath);
		return NULL;
	}
	new_path = mem_alloc_array(char, new_len+1);
	new_len1 = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, w_fullpath, cast(int)w_len, new_path, cast(int)new_len, NULL, NULL);
	if (new_len1 == 0) {
		mem_free(w_fullpath);
		mem_free(new_path);
		return NULL;
	}
	new_path[new_len] = 0;
	return new_path;
#else
	char *p, *result, *fullpath = NULL;
	isize len;
	p = realpath(path, NULL);
	fullpath = p;
	if (p == NULL) {
		// NOTE(bill): File does not exist
		fullpath = cast(char *)path;
	}

	len = gb_strlen(fullpath);

	result = mem_alloc_array(char, len + 1);
	gb_memmove(result, fullpath, len);
	result[len] = 0;
	free(p);

	return result;
#endif
}


