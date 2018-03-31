typedef struct Type Type;
typedef struct TypeRange TypeRange;
typedef struct TypeAggregate TypeAggregate;
typedef struct Entity Entity;
typedef struct Scope Scope;
typedef struct ConstValue ConstValue;

typedef enum TypeKind TypeKind;
typedef enum TypeFlag TypeFlag;

// IMPORTANT NOTE(bill): Order does matter
enum TypeKind {
	Type_Invalid,

	Type_Bool,
	Type_Int,
	Type_Rune,
	Type_Float,
	Type_String,
	Type_Nil,

	Type_Named,
	Type_Ptr,
	Type_Array,
	Type_Slice,
	Type_Set,
	Type_Range,
	Type_Struct,
	Type_Enum,
	Type_Proc,

	Type_COUNT
};

enum TypeFlag {
	TypeFlag_Untyped  = 1<<0,
	TypeFlag_Unsigned = 1<<1,
};

struct TypeRange {
	i64 lower;
	i64 upper;
};

struct TypeAggregate {
	Scope *  scope;
	Entity **fields;
	isize    field_count;
};

struct Type {
	TypeKind kind;
	u32      flags;
	i64      size;
	i64      align;
	String   name;
	union {
		struct {
			Type *  base;
			Entity *entity;
		} named;
		struct {
			Type *elem; // NULL if `rawptr`
		} ptr;
		struct {
			Type *elem;
			i64   len;
		} array;
		struct {
			Type *elem;
		} slice;
		struct {
			TypeRange *ranges;
			isize      range_count;
		} set;
		TypeRange range;
		TypeAggregate structure;
		TypeAggregate enumeration;
		struct {
			Scope *  scope;
			Entity **fields;
			isize    field_count;
			Type *   ret;
		} proc;
	};
};


Type *t_untyped_bool   = NULL;
Type *t_untyped_int    = NULL;
Type *t_untyped_float  = NULL;
Type *t_untyped_string = NULL;
Type *t_untyped_rune   = NULL;
Type *t_untyped_nil    = NULL;

Type t__invalid = {0};
Type *t_invalid = &t__invalid;
Type *t_bool    = NULL;
Type *t_int     = NULL;
Type *t_uint    = NULL;
Type *t_uintptr = NULL;
Type *t_int8    = NULL;
Type *t_int16   = NULL;
Type *t_int32   = NULL;
Type *t_int64   = NULL;
Type *t_uint8   = NULL;
Type *t_uint16  = NULL;
Type *t_uint32  = NULL;
Type *t_uint64  = NULL;
Type *t_float32 = NULL;
Type *t_float64 = NULL;
Type *t_string  = NULL;
Type *t_rune    = NULL;
Type *t_rawptr  = NULL;



Type *alloc_type(TypeKind kind) {
	Type *t = MEM_NEW(Type);
	t->kind = kind;
	return t;
}

i64 const PTR_SIZE  = 8;
i64 const PTR_ALIGN = 8;


void complete_type(Type *t);
Type *default_type(Type *t);
bool are_types_equal(Type *x, Type *y);

i64 type_size_of(Type *t) {
	t = default_type(t);
	ASSERT(t->size >= 0);
	return t->size;
}
i64 type_align_of(Type *t) {
	t = default_type(t);
	ASSERT(t->align >= 0);
	return t->align;
}

Type *base_type(Type *t) {
	for (;;) {
		if (t == NULL) {
			return NULL;
		}
		if (t->kind == Type_Named) {
			t = t->named.base;
		} else {
			return t;
		}
	}
}

void set_base_type(Type *t, Type *base) {
	if (t && t->kind == Type_Named) {
		t->named.base = base_type(base);
	}
}


bool is_type_untyped(Type *t) {
	if (t == NULL) return false;
	return t->flags & TypeFlag_Untyped;
}
bool is_type_typed(Type *t) {
	if (t == NULL) return false;
	return (t->flags & TypeFlag_Untyped) == 0;
}
bool is_type_unsigned(Type *t) {
	if (t == NULL) return false;
	return t->flags & TypeFlag_Unsigned;
}
bool is_type_integer(Type *t) {
	if (t == NULL) return false;
	return t->kind == Type_Int;
}
bool is_type_boolean(Type *t) {
	if (t == NULL) return false;
	return t->kind == Type_Bool;
}
bool is_type_numeric(Type *t) {
	if (t == NULL) return false;
	switch (t->kind) {
	case Type_Int:
	case Type_Float:
	case Type_Rune:
		return true;
	}
	return false;
}
bool is_type_constant_type(Type *t) {
	if (t == NULL) return false;
	switch (t->kind) {
	case Type_Bool:
	case Type_Int:
	case Type_Float:
	case Type_Rune:
	case Type_String:
		return true;
	}
	return false;
}
bool type_has_nil(Type *t) {
	if (t == NULL) return false;
	switch (t->kind) {
	case Type_Ptr:
	case Type_Slice:
		return true;
	}
	return false;
}



Type *default_type(Type *t) {
	ASSERT(t != NULL);
	if (is_type_untyped(t)) {
		switch (t->kind) {
		case Type_Bool:   return t_bool;
		case Type_Int:    return t_int;
		case Type_Float:  return t_float64;
		case Type_String: return t_string;
		case Type_Rune:   return t_rune;
		}
	}
	return t;
}

Type *type_deref(Type *t) {
	ASSERT(!is_type_untyped(t));
	if (t->kind != Type_Ptr) {
		return t;
	}
	return t->ptr.elem;
}



typedef struct CachedTypePtr {
	Type *type;
	Type *elem;
} CachedTypePtr;
typedef struct CachedTypeArray {
	Type *type;
	Type *elem;
	i64   len;
} CachedTypeArray;
typedef struct CachedTypeSlice {
	Type *type;
	Type *elem;
} CachedTypeSlice;
typedef struct CachedTypeRange {
	Type *type;
	i64   lower;
	i64   upper;
} CachedTypeRange;

static CachedTypePtr *  cached_type_ptrs   = NULL;
static CachedTypeArray *cached_type_arrays = NULL;
static CachedTypeSlice *cached_type_slices = NULL;
static CachedTypeRange *cached_type_ranges = NULL;



Type *alloc_type_ptr(Type *elem) {
	CachedTypePtr cached = {0};
	Type *type = NULL;
	isize i;
	for (i = 0; i < buf_len(cached_type_ptrs); i++) {
		CachedTypePtr *c = &cached_type_ptrs[i];
		if (c->elem == elem) {
			return c->type;
		}
	}
	type = alloc_type(Type_Ptr);
	type->size  = PTR_SIZE;
	type->align = PTR_ALIGN;
	type->ptr.elem = elem;
	cached.type = type;
	cached.elem = elem;
	buf_push(cached_type_ptrs, cached);
	return type;
}

Type *alloc_type_array(Type *elem, i64 len) {
	CachedTypeArray cached = {0};
	Type *type = NULL;
	isize i;
	for (i = 0; i < buf_len(cached_type_arrays); i++) {
		CachedTypeArray *c = &cached_type_arrays[i];
		if (c->elem == elem && c->len == len) {
			return c->type;
		}
	}
	complete_type(elem);

	type = alloc_type(Type_Array);
	type->size  = len * type_size_of(elem);
	type->align = type_align_of(elem);
	type->array.elem = elem;
	type->array.len = len;
	cached.type = type;
	cached.elem = elem;
	cached.len = len;
	buf_push(cached_type_arrays, cached);
	return type;
}


Type *alloc_type_slice(Type *elem) {
	CachedTypeSlice cached = {0};
	Type *type = NULL;
	isize i;
	for (i = 0; i < buf_len(cached_type_slices); i++) {
		CachedTypeSlice *c = &cached_type_slices[i];
		if (c->elem == elem) {
			return c->type;
		}
	}
	type = alloc_type(Type_Array);
	type->size  = 2 * PTR_SIZE;
	type->align = PTR_ALIGN;
	type->slice.elem = elem;
	cached.type = type;
	cached.elem = elem;
	buf_push(cached_type_slices, cached);
	return type;
}

Type *alloc_type_proc(Scope *scope, Entity **fields, isize field_count, Type *ret) {
	Type *type  = alloc_type(Type_Proc);
	type->size  = PTR_SIZE;
	type->align = PTR_ALIGN;
	type->proc.scope = scope;
	type->proc.fields = MEM_DUP_ARRAY(fields, field_count);
	type->proc.field_count = field_count;
	type->proc.ret = ret;
	return type;
}

i64 calc_range_size(i64 lower, i64 upper) {
	i64 diff = upper-lower;
	i64 bits = ceil_log2(diff);
	i64 bytes = next_pow2((bits+7)/8);
	return bytes;
}

Type *alloc_type_range(i64 lower, i64 upper) {
	CachedTypeRange cached = {0};
	Type *type = NULL;
	isize i;
	for (i = 0; i < buf_len(cached_type_ranges); i++) {
		CachedTypeRange *c = &cached_type_ranges[i];
		if (c->lower == lower && c->upper == upper) {
			return c->type;
		}
	}

	type = alloc_type(Type_Range);
	type->size  = calc_range_size(lower, upper);
	type->align = type->size;
	type->range.lower = lower;
	type->range.upper = upper;
	cached.type = type;
	cached.lower = lower;
	cached.upper = upper;
	buf_push(cached_type_ranges, cached);
	return type;
}


bool are_types_equal(Type *x, Type *y) {
	if (x == NULL && y != NULL) return false;
	if (x != NULL && y == NULL) return false;
	if (x == y) return true;
	if (x->kind == y->kind) {
		switch (x->kind) {
		case Type_Proc:
			if (x->proc.field_count == y->proc.field_count &&
			    are_types_equal(x->proc.ret, y->proc.ret)) {
				isize i;
				for (i = 0; i < x->proc.field_count; i++) {
					Type *a = x->proc.fields[i]->type;
					Type *b = y->proc.fields[i]->type;
					if (!are_types_equal(a, b)) {
						return false;
					}
				}
				return true;
			}
			return false;
		case Type_Struct:
			if (x->structure.field_count == y->structure.field_count) {
				isize i;
				for (i = 0; i < x->structure.field_count; i++) {
					Type *a = x->structure.fields[i]->type;
					Type *b = y->structure.fields[i]->type;
					if (!are_types_equal(a, b)) {
						return false;
					}
				}
				return true;
			}
			return false;
		case Type_Enum:
			if (x->enumeration.field_count == y->enumeration.field_count) {
				isize i;
				for (i = 0; i < x->enumeration.field_count; i++) {
					Type *a = x->enumeration.fields[i]->type;
					Type *b = y->enumeration.fields[i]->type;
					if (!are_types_equal(a, b)) {
						return false;
					}
				}
				return true;
			}
			return false;
		}
	}
	return false;
}

char *type_to_string_internal(char *str, Type *t) {
	if (t == NULL) {
		return buf_printf(str, "<no type>");
	} else if (t->name.len > 0) {
		return buf_printf(str, "%.*s", LIT(t->name));
	}
	switch (t->kind) {
	case Type_Named:
		return buf_printf(str, "%.*s", LIT(t->named.entity->name));
	case Type_Ptr:
		if (t->ptr.elem) {
			buf_printf(str, "^");
			return type_to_string_internal(str, t->ptr.elem);
		} else {
			return buf_printf(str, "rawptr");
		}
	case Type_Array:
		buf_printf(str, "[%ld]", t->array.len);
		return type_to_string_internal(str, t->array.elem);
	case Type_Slice:
		buf_printf(str, "[]");
		return type_to_string_internal(str, t->slice.elem);
	case Type_Set:
		return buf_printf(str, "set[]");
	case Type_Range:
		return buf_printf(str, "range %ld..%d", t->range.lower, t->range.upper);
	case Type_Struct:
		return buf_printf(str, "struct{}");
	case Type_Enum:
		return buf_printf(str, "enum{}");
	case Type_Proc: {
		isize i;
		buf_printf(str, "proc(");
		for (i = 0; i < t->proc.field_count; i++) {
			Entity *f = t->proc.fields[i];
			if (i > 0) buf_printf(str, ", ");
			buf_printf(str, "%.*s: ", LIT(f->name));
			type_to_string_internal(str, f->type);
		}
		buf_printf(str, ")");
		if (t->proc.ret) {
			buf_printf(str, ": ");
			type_to_string_internal(str, t->proc.ret);
		}
		return str;
	}
	}
	return buf_printf(str, "<invalid type>");
}

char *type_to_string(Type *t) {
	char *buf, *str;
	buf = type_to_string_internal(NULL, t);
	buf_push(buf, 0);
	str = MEM_DUP_ARRAY(buf, buf_len(buf));
	buf_free(buf);
	return str;
}


