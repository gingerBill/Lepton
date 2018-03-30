typedef struct ConstValue ConstValue;
typedef enum ConstValueKind ConstValueKind;


enum ConstValueKind {
	ConstValue_Invalid,

	ConstValue_Bool,
	ConstValue_Integer,
	ConstValue_Float,
	ConstValue_String,

	ConstValue_COUNT
};
struct ConstValue {
	ConstValueKind kind;
	union {
		bool   v_bool;
		i64    v_int;
		f64    v_float;
		String v_string;
	};
};

static ConstValue const empty_exact_value = {0};


ConstValue const_value_from_literal(Token lit);
ConstValue const_value_unary       (TokenKind op, ConstValue v, int precision);
int        const_value_order       (ConstValue v);
void       match_const_values      (ConstValue *x, ConstValue *y);
ConstValue const_value_binary      (TokenKind op, ConstValue x, ConstValue y);


ConstValue const_value_bool(bool b) {
	ConstValue v = {ConstValue_Bool};
	v.v_bool = b;
	return v;
}
ConstValue const_value_int(i64 i) {
	ConstValue v = {ConstValue_Integer};
	v.v_int = i;
	return v;
}
ConstValue const_value_float(f64 f) {
	ConstValue v = {ConstValue_Float};
	v.v_float = f;
	return v;
}
ConstValue const_value_string(String s) {
	ConstValue v = {ConstValue_String};
	v.v_string = s;
	return v;
}

ConstValue const_value_from_literal(Token lit) {
	ConstValue v = {0};
	switch (lit.kind) {
	case Token_Integer:
		return const_value_int(cast(i64)u64_from_string(lit.string));
	case Token_Float:
		return const_value_float(float_from_string(lit.string));
	case Token_Rune:
		PANIC("TODO: rune literal");
		break;
	case Token_String:
		return const_value_string(lit.string);
	default: PANIC("invalid literal constant"); break;
	}
	return v;
}

ConstValue const_value_unary(TokenKind op, ConstValue v, int precision) {
	ConstValue error_value = {0};

	switch (op) {
	case Token_Add:
		switch (v.kind) {
		case ConstValue_Invalid:
		case ConstValue_Integer:
		case ConstValue_Float:
			return v;
		}
		break;

	case Token_Sub:
		switch (v.kind) {
		case ConstValue_Invalid:
			return v;
		case ConstValue_Integer:
			return const_value_int(-v.v_int);
		case ConstValue_Float:
			return const_value_float(-v.v_float);
		}

	case Token_Xor: {
		i64 i = 0ll;
		switch (v.kind) {
		case ConstValue_Invalid:
			return v;
		case ConstValue_Integer:
			i = ~v.v_int;
			break;
		default:
			goto failure;
		}
		// NOTE(bill): unsigned integers will be negative and will need to be
		// limited to the types precision
		// IMPORTANT NOTE(bill): Max precision is 64 bits as that's how integers are stored
		if (0 < precision && precision < 64) {
			i = i & ~(-1ll << precision);
		}

		v.v_int = i;
		return v;
	}

	case Token_not:
		switch (v.kind) {
		case ConstValue_Invalid: return v;
		case ConstValue_Bool:
			return const_value_bool(!v.v_bool);
		}
		break;
	}

failure:
	PANIC("invalid unary operation");
	return error_value;
}

int const_value_order(ConstValue v) {
	switch (v.kind) {
	case ConstValue_Invalid:
		return 0;
	case ConstValue_Bool:
	case ConstValue_String:
		return 1;
	case ConstValue_Integer:
		return 2;
	case ConstValue_Float:
		return 3;
	}
	PANIC("How'd you get here? Invalid ConstValue.kind");
	return -1;
}



void match_const_values(ConstValue *x, ConstValue *y) {
	if (const_value_order(*y) < const_value_order(*x)) {
		match_const_values(y, x);
		return;
	}

	switch (x->kind) {
	case ConstValue_Invalid:
		*y = *x;
		return;

	case ConstValue_Bool:
	case ConstValue_String:
		return;

	case ConstValue_Integer:
		switch (y->kind) {
		case ConstValue_Integer:
			return;
		case ConstValue_Float:
			// TODO(bill): Is this good enough?
			x->kind = ConstValue_Float;
			x->v_float = cast(f64)x->v_int;
			return;
		}
		break;

	case ConstValue_Float:
		switch (y->kind) {
		case ConstValue_Float:
			return;
		}
		break;
	}

	PANIC("match_const_values: How'd you get here?");
}


ConstValue const_value_binary(TokenKind op, ConstValue x, ConstValue y) {
	match_const_values(&x, &y);

	switch (x.kind) {
	case ConstValue_Invalid:
		return x;
	case ConstValue_Bool:
		switch (op) {
		case Token_and: return const_value_bool(x.v_bool && y.v_bool);
		case Token_or:  return const_value_bool(x.v_bool || y.v_bool);
		}
	case ConstValue_Integer: {
		i64 a = x.v_int;
		i64 b = y.v_int;
		i64 c = 0ll;

		switch (op) {
		case Token_Add:   c = a + b; break;
		case Token_Sub:   c = a - b; break;
		case Token_Mul:   c = a * b; break;
		case Token_Div:   return const_value_float(fmod(cast(f64)a, cast(f64)b)); break;
		case Token_DivEq: c = a / b; break;
		case Token_Mod:   c = a % b; break;
		default: goto error;
		}

		return const_value_int(c);
	}
	case ConstValue_Float: {
		f64 a = x.v_float;
		f64 b = y.v_float;
		f64 c = 0.0;

		switch (op) {
		case Token_Add:   c = a + b; break;
		case Token_Sub:   c = a - b; break;
		case Token_Mul:   c = a * b; break;
		case Token_Div:   c = a / b; break;
		default: goto error;
		}

		return const_value_float(c);
	}
	}

error:;
	return empty_exact_value;
}

ConstValue const_value_to_integer(ConstValue v) {
	switch (v.kind) {
	case ConstValue_Integer:
		return v;
	case ConstValue_Float: {
		i64 i = cast(i64)v.v_float;
		f64 f = cast(f64)i;
		if (f == v.v_float) {
			return const_value_int(i);
		}
		break;
	}

	}
	return empty_exact_value;
}

ConstValue const_value_to_float(ConstValue v) {
	switch (v.kind) {
	case ConstValue_Integer:
		return const_value_float(cast(f64)v.v_int);
	case ConstValue_Float:
		return v;
	}
	return empty_exact_value;
}
