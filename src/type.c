typedef struct Type Type;
typedef struct TypeRange TypeRange;
typedef struct Entity Entity;
typedef struct Scope Scope;
typedef struct ConstValue ConstValue;

typedef enum TypeKind TypeKind;
typedef enum TypeFlag TypeFlag;

enum TypeKind {
	Type_Invalid,

	Type_Bool,
	Type_Int,
	Type_Float,
	Type_String,
	Type_Rune,
	Type_Ptr,
	Type_Array,
	Type_Slice,
	Type_Set,
	Type_Range,
	Type_Struct,
	Type_Enum,
	Type_Proc,

	Type_COUNT,
};

enum TypeFlag {
	TypeFlag_Unsigned = 1<<0,
	TypeFlag_Untyped  = 1<<1,
};

struct TypeRange {
	i64 lower;
	i64 upper;
};

struct Type {
	TypeKind kind;
	u32      flags;
	i64      size;
	i64      align;
	Entity * entity;
	union {
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
		struct {
			Type ** fields;
			isize   field_count;
			String *names; // field_count or NULL
		} structure;
		struct {
			i64 *   values;
			isize   value_count;
			String *names; // value_count or NULL
		} enumeration;
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
Type *t_bool   = NULL;
Type *t_int    = NULL;
Type *t_uint   = NULL;
Type *t_f32    = NULL;
Type *t_f64    = NULL;
Type *t_string = NULL;
Type *t_rune   = NULL;
Type *t_rawptr = NULL;



Type *alloc_type(TypeKind kind) {
	Type *t = MEM_NEW(Type);
	t->kind = kind;
	return t;
}

i64 const PTR_SIZE  = 8;
i64 const PTR_ALIGN = 8;


void complete_type(Type *t);
Type *default_type(Type *t);

i64 type_size_of(Type *t) {
	t = default_type(t);
	assert(t->size >= 0);
	return t->size;
}
i64 type_align_of(Type *t) {
	t = default_type(t);
	assert(t->align >= 0);
	return t->align;
}

bool is_type_untyped(Type *t) {
	return t->flags & TypeFlag_Untyped;
}
bool is_type_integer(Type *t) {
	if (t == NULL) return false;
	return t->kind == Type_Int;
}


Type *default_type(Type *t) {
	assert(t != NULL);
	if (is_type_untyped(t)) {
		switch (t->kind) {
		case Type_Bool:   return t_bool;
		case Type_Int:    return t_int;
		case Type_Float:  return t_f64;
		case Type_String: return t_string;
		case Type_Rune:   return t_rune;
		}
	}
	return t;
}

Type *type_deref(Type *t) {
	assert(!is_type_untyped(t));
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
