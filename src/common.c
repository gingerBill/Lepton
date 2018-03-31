#if defined(_MSC_VER)
#define _CRT_SECURE_NO_WARNINGS
#include <windows.h>
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <math.h>

#ifndef STATIC_ASSERT
	#define STATIC_ASSERT3(cond, msg) typedef char static_assertion_##msg[(!!(cond))*2-1]
	// //NOTE(bill): Token pasting madness!!
	#define STATIC_ASSERT2(cond, line) STATIC_ASSERT3(cond, static_assertion_at_line_##line)
	#define STATIC_ASSERT1(cond, line) STATIC_ASSERT2(cond, line)
	#define STATIC_ASSERT(cond)        STATIC_ASSERT1(cond, __LINE__)
#endif

#ifndef DEBUG_TRAP
	#if defined(_MSC_VER)
	 	#if _MSC_VER < 1300
		#define DEBUG_TRAP() __asm int 3 /* Trap to debugger! */
		#else
		#define DEBUG_TRAP() __debugbreak()
		#endif
	#else
		#define DEBUG_TRAP() __builtin_trap()
	#endif
#endif

#ifndef ASSERT_MSG
#define ASSERT_MSG(cond, msg, ...) do { \
	if (!(cond)) { \
		assert_handler(#cond, __FILE__, cast(i64)__LINE__, msg, ##__VA_ARGS__); \
		DEBUG_TRAP(); \
	} \
} while (0)
#endif

#ifndef ASSERT
#define ASSERT(cond) ASSERT_MSG(cond, NULL)
#endif

#ifndef PANIC
#define PANIC(msg, ...) ASSERT_MSG(0, msg, ##__VA_ARGS__);
#endif


static void assert_handler(char const *condition, char const *file, int line, char const *msg, ...) {
	FILE *f = stderr;
	fprintf(f, "%s(%d): Assert Failure: ", file, line);
	if (condition) {
		fprintf(f,  "`%s` ", condition);
	}
	if (msg) {
		va_list va;
		va_start(va, msg);
		vfprintf(f, msg, va);
		va_end(va);
	}
	fprintf(f, "\n");
	fflush(stderr);
}



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



#include "utf8.c"


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
	ASSERT(lo <= hi && hi <= max);

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
	void *ptr = NULL;
	if (size > 0) {
		ptr = malloc(size);
		if (!ptr) {
			fatal("mem_alloc failed");
		}
		mem_zero(ptr, size);
	}
	return ptr;
}

void *mem_realloc(void *ptr, isize size) {
	ASSERT(size >= 0);
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

#define MEM_ALLOC_ARRAY(TYPE_, n) (TYPE_ *)mem_alloc((n)*sizeof(TYPE_))
#define MEM_NEW(TYPE_) (TYPE_ *)mem_alloc(sizeof(TYPE_))
#define MEM_DUP_ARRAY(x, len) mem_dup(x, sizeof(*(x))*(len));

String alloc_string_from_rune(Rune r) {
	char str[4] = {0};
	isize len = utf8_encode_rune(str, r);
	char *text = mem_alloc(len+1);
	memmove(text, str, len);
	return make_string(text, len);
}



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
#define buf_reserve(b, n) ((n) <= buf_cap(b) ? 0 : ((b) = buf__grow((b), (n), sizeof(*(b)))))
#define buf_resize(b, n) (buf_reserve(b, n), (buf__hdr(b)->len = (n)), (b))
#define buf_push(b, ...) (buf_reserve((b), 1 + buf_len(b)), (b)[buf__hdr(b)->len++] = (__VA_ARGS__), (b))
#define buf_pop(b) ((b) ? (buf_len(b) > 0, buf__hdr(b)->len--) : 0)
#define buf_clear(b) ((b) ? buf__hdr(b)->len = 0 : 0)

#define buf_printf(b, ...) ((b) = buf__printf((b), __VA_ARGS__))

#define for_buf(idx_, b) for(idx_ = 0; idx_ < buf_len(b); idx_++)


void *buf__grow(void const *b, isize new_len, isize elem_size) {
	isize new_cap, new_size;
	BufferHeader *new_header;

	new_cap = MAX(MAX(2*buf_cap(b)+8, new_len), 16);
	ASSERT(new_len <= new_cap);

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
        buf_reserve(buf, n + buf_len(buf));
        va_start(args, fmt);
        cap = buf_cap(buf) - buf_len(buf);
        n = 1 + vsnprintf(buf_end(buf), cap, fmt, args);
        ASSERT(n <= cap);
        va_end(args);
    }
    buf__hdr(buf)->len += n - 1;
    return buf;
}


// Doubly Linked Lists
#define DLIST_SET(curr_element, next_element)  do { \
	(curr_element)->next = (next_element);             \
	(curr_element)->next->prev = (curr_element);       \
	(curr_element) = (curr_element)->next;             \
} while (0)

#define DLIST_APPEND(root_element, curr_element, next_element) do { \
	if ((root_element) == NULL) { \
		(root_element) = (curr_element) = (next_element); \
	} else { \
		DLIST_SET(curr_element, next_element); \
	} \
} while (0)





// Arena from Per Vognsen
typedef struct Arena {
	char *ptr;
	char *end;
	char **blocks;
} Arena;

#define ARENA_ALIGNMENT 8
#define ARENA_BLOCK_SIZE (4*1024*1024)

void arena_grow(Arena *arena, isize min_size) {
	isize size = MAX(ARENA_BLOCK_SIZE, min_size);
	size = ALIGN_UP(size, ARENA_ALIGNMENT);
    arena->ptr = mem_alloc(size);
    ASSERT(arena->ptr == ALIGN_DOWN_PTR(arena->ptr, ARENA_ALIGNMENT));
    arena->end = arena->ptr + size;
    buf_push(arena->blocks, arena->ptr);
}

void *arena_alloc(Arena *arena, isize size) {
    void *ptr;

    if (size > (arena->end - arena->ptr)) {
        arena_grow(arena, size);
        ASSERT(size <= (arena->end - arena->ptr));
    }
    ptr = arena->ptr;
    arena->ptr = ALIGN_UP_PTR(arena->ptr + size, ARENA_ALIGNMENT);
    ASSERT(arena->ptr <= arena->end);
    ASSERT(ptr == ALIGN_DOWN_PTR(ptr, ARENA_ALIGNMENT));
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

void debug_println(char const *fmt, ...) {
	FILE *f = stderr;
	va_list va;
	va_start(va, fmt);
	fprintf(f, "Debug: ");
	vfprintf(f, fmt, va);
	fprintf(f, "\n");
	va_end(va);
}



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
	w_text = MEM_ALLOC_ARRAY(wchar_t, w_len+1);
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
	w_fullpath = MEM_ALLOC_ARRAY(wchar_t, w_len+1);
	GetFullPathNameW(w_path, cast(int)w_len, w_fullpath, NULL);
	w_fullpath[w_len] = 0;
	mem_free(w_path);

	new_len = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, w_fullpath, cast(int)w_len, NULL, 0, NULL, NULL);
	if (new_len == 0) {
		mem_free(w_fullpath);
		return NULL;
	}
	new_path = MEM_ALLOC_ARRAY(char, new_len+1);
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

	result = MEM_ALLOC_ARRAY(char, len + 1);
	gb_memmove(result, fullpath, len);
	result[len] = 0;
	free(p);

	return result;
#endif
}


// Math
i32 bit_set_count32(u32 x) {
	x -= ((x >> 1) & 0x55555555);
	x = (((x >> 2) & 0x33333333) + (x & 0x33333333));
	x = (((x >> 4) + x) & 0x0f0f0f0f);
	x += (x >> 8);
	x += (x >> 16);

	return cast(i32)(x & 0x0000003f);
}
i64 bit_set_count64(u64 x) {
	u32 a = *(cast(u32 *)&x);
	u32 b = *(cast(u32 *)&x + 1);
	return bit_set_count32(a) + bit_set_count32(b);
}

u64 ceil_log2(u64 x) {
	i64 y = cast(i64)(x & (x-1));
	y |= -y;
	y >>= 64-1;
	x |= x >> 1;
	x |= x >> 2;
	x |= x >> 4;
	x |= x >> 8;
	x |= x >> 16;
	x |= x >> 32;
	return cast(u64)(bit_set_count64(x) - 1 - y);
}

i64 next_pow2(i64 n) {
	if (n <= 0) {
		return 0;
	}
	n--;
	n |= n >> 1;
	n |= n >> 2;
	n |= n >> 4;
	n |= n >> 8;
	n |= n >> 16;
	n |= n >> 32;
	n++;
	return n;
}


// Conversions

int digit_value(Rune r) {
	if ('0' <= r && r <= '9') {
		return r - '0';
	} else if ('a' <= r && r<= 'f') {
		return r - 'a' + 10;
	} else if ('A' <= r && r<= 'F') {
		return r - 'A' + 10;
	}
	return 16; // NOTE(bill): Larger than highest possible
}

u64 u64_from_string(String string) {
	u64 base = 10;
	bool has_prefix = false;
	char *text;
	isize len, i;
	u64 result;

	if (string.len > 2 && string.text[0] == '0') {
		switch (string.text[1]) {
		case 'b': base = 2;  has_prefix = true; break;
		case 'o': base = 8;  has_prefix = true; break;
		case 'd': base = 10; has_prefix = true; break;
		case 'z': base = 12; has_prefix = true; break;
		case 'x': base = 16; has_prefix = true; break;
		case 'h': base = 16; has_prefix = true; break;
		}
	}

	text = string.text;
	len = string.len;
	if (has_prefix) {
		text += 2;
		len -= 2;
	}

	result = 0ull;
	for (i = 0; i < len; i++) {
		u64 v;
		Rune r = cast(Rune)text[i];
		if (r == '_') {
			continue;
		}
		v = cast(u64)digit_value(r);
		if (v >= base) {
			break;
		}
		result *= base;
		result += v;
	}
	return result;
}

f64 float_from_string(String string) {
	isize i = 0;
	char *str = string.text;
	isize len = string.len;
	bool frac = false;
	f64 scale = 1.0;
	f64 value = 0.0;

	f64 sign = 1.0;
	if (str[i] == '-') {
		sign = -1.0;
		i++;
	} else if (*str == '+') {
		i++;
	}

	value = 0.0;
	for (; i < len; i++) {
		i64 v;
		Rune r = cast(Rune)str[i];
		if (r == '_') {
			continue;
		}
		v = digit_value(r);
		if (v >= 10) {
			break;
		}
		value *= 10.0;
		value += v;
	}

	if (str[i] == '.') {
		f64 pow10 = 10.0;
		i++;
		for (; i < string.len; i++) {
			i64 v;
			Rune r = cast(Rune)str[i];
			if (r == '_') {
				continue;
			}
			v = digit_value(r);
			if (v >= 10) {
				break;
			}
			value += v/pow10;
			pow10 *= 10.0;
		}
	}

	if ((str[i] == 'e') || (str[i] == 'E')) {
		u32 exp = 0;

		i++;

		if (str[i] == '-') {
			frac = true;
			i++;
		} else if (str[i] == '+') {
			i++;
		}

		for (; i < len; i++) {
			u32 d;
			Rune r = cast(Rune)str[i];
			if (r == '_') {
				continue;
			}
			d = cast(u32)digit_value(r);
			if (d >= 10) {
				break;
			}
			exp = exp * 10 + d;
		}
		if (exp > 308) exp = 308;

		while (exp >= 50) { scale *= 1e50; exp -= 50; }
		while (exp >=  8) { scale *= 1e8;  exp -=  8; }
		while (exp >   0) { scale *= 10.0; exp -=  1; }
	}

	return sign * (frac ? (value / scale) : (value * scale));
}
