#include "checker.h"

bool is_blank_name(String name) {
	if (name.len == 1 && name.text[0] == '_') {
		return true;
	}
	return false;
}


Type *alloc_universal_type(char *name, TypeKind kind, i64 size, i64 align, u32 type_flags) {
	Entity *e = NULL;
	Entity *prev = NULL;
	Type *t = NULL;
	AstExpr *ident = NULL;
	Token token = {Token_Ident};

	ASSERT(universal_scope != NULL);

	token.string = make_string_c(name);
	ident = ast_expr_ident(token);
	t = alloc_type(kind);
	t->size  = size;
	t->align = align;
	t->flags = type_flags;

	e = alloc_entity(Entity_Type, ident, NULL);
	e->type = t;
	e->state = EntityState_Resolved;
	prev = scope_insert_entity(universal_scope, e);
	ASSERT(prev == NULL);
	return t;
}

void init_universal_scope(void) {
	universal_scope = alloc_scope(NULL, NULL);
	universal_scope->flags |= ScopeFlag_Global;

	ASSERT(t_untyped_bool == NULL);
	t_untyped_bool   = alloc_universal_type("untyped bool",   Type_Bool,   -1, -1, TypeFlag_Untyped);
	t_untyped_int    = alloc_universal_type("untyped int",    Type_Int,    -1, -1, TypeFlag_Untyped);
	t_untyped_float  = alloc_universal_type("untyped float",  Type_Float,  -1, -1, TypeFlag_Untyped);
	t_untyped_string = alloc_universal_type("untyped string", Type_String, -1, -1, TypeFlag_Untyped);
	t_untyped_rune   = alloc_universal_type("untyped rune",   Type_Rune,   -1, -1, TypeFlag_Untyped);

	t_bool   = alloc_universal_type("bool",   Type_Bool,   1, 1, 0);
	t_int    = alloc_universal_type("int",    Type_Int,    PTR_SIZE, PTR_ALIGN, 0);
	t_uint   = alloc_universal_type("uint",   Type_Int,    PTR_SIZE, PTR_ALIGN, TypeFlag_Unsigned);
	t_i8     = alloc_universal_type("i8",     Type_Int,    1, 1, 0);
	t_i16    = alloc_universal_type("i16",    Type_Int,    2, 2, 0);
	t_i32    = alloc_universal_type("i32",    Type_Int,    4, 4, 0);
	t_i64    = alloc_universal_type("i64",    Type_Int,    8, 8, 0);
	t_u8     = alloc_universal_type("u8",     Type_Int,    1, 1, TypeFlag_Unsigned);
	t_u16    = alloc_universal_type("u16",    Type_Int,    2, 2, TypeFlag_Unsigned);
	t_u32    = alloc_universal_type("u32",    Type_Int,    4, 4, TypeFlag_Unsigned);
	t_u64    = alloc_universal_type("u64",    Type_Int,    8, 8, TypeFlag_Unsigned);
	t_f32    = alloc_universal_type("f32",    Type_Float,  4, 4, 0);
	t_f64    = alloc_universal_type("f64",    Type_Float,  8, 8, 0);
	t_string = alloc_universal_type("string", Type_String, 2*PTR_SIZE, PTR_ALIGN, 0);
	t_rune   = alloc_universal_type("rune",   Type_Rune,   4, 4, 0);
	t_rawptr = alloc_universal_type("rawptr", Type_Ptr,    PTR_SIZE, PTR_SIZE, 0);
}

void checker_init(Checker *c) {
	c->global_scope = alloc_scope(universal_scope, NULL);
	c->global_scope->flags |= ScopeFlag_Global;
	c->context.scope = c->global_scope;

	map_init(&c->expr_info_map);
}


static Arena expr_info_arena = {0};

void *expr_info_arena_alloc(isize size) {
	if (size <= 0) {
		return NULL;
	} else {
		void *ptr = arena_alloc(&expr_info_arena, size);
		mem_zero(ptr, size);
		return ptr;
	}
}

void add_expr_info(Checker *c, AstExpr *expr, AddressingMode mode, Type *type, ConstValue value) {
	if (expr == NULL || mode == Addressing_Invalid) {
		return;
	}

	if (mode == Addressing_Const && type == t_invalid) {
		PANIC("add_expr_info - invalid type");
	} else {
		HashKey key = hash_ptr(expr);
		ExprInfo *info = map_get(&c->expr_info_map, key);
		if (info == NULL) {
			info = cast(ExprInfo *)expr_info_arena_alloc(sizeof(ExprInfo));
		}
		info->mode  = mode;
		info->type  = type;
		info->value = value;
		map_set(&c->expr_info_map, key, info);
	}
}

ExprInfo *get_expr_info(Checker *c, AstExpr *expr) {
	if (expr) {
		return cast(ExprInfo *)map_get(&c->expr_info_map, hash_ptr(expr));
	}
	return NULL;
}

void update_expr_value(Checker *c, AstExpr *expr, ConstValue value) {
	if (expr) {
		ExprInfo *found = get_expr_info(c, expr);
		if (found) found->value = value;
	}
}

void remove_expr_info(Checker *c, AstExpr *expr) {
	if (expr) {
		map_remove(&c->expr_info_map, hash_ptr(expr));
	}
}


void update_expr_type(Checker *c, AstExpr *expr, Type *type, bool final) {
	ExprInfo *found = get_expr_info(c, expr);
	ExprInfo old = {0};
	if (found == NULL) return;
	old = *found;
	switch (expr->kind) {
	case AstExpr_Paren:
		update_expr_type(c, expr->paren.expr, type, final);
		break;
	case AstExpr_Unary:
		if (old.value.kind != ConstValue_Invalid) {
			// NOTE(bill): if 'expr' is constant, the operands will be constant too.
			// They don't need to be updated as they will be updated later and
			// checked at the end of general checking stage.
			break;
		}
		update_expr_type(c, expr->unary.expr, type, final);
		break;
	case AstExpr_Binary:
		if (old.value.kind != ConstValue_Invalid) {
			// See above note in unary expr case
			break;
		}
		if (token_is_comparison(expr->binary.op.kind)) {
			// NOTE(bill): Do nothing as the types are fine
		} else {
			update_expr_type(c, expr->binary.left,  type, final);
			update_expr_type(c, expr->binary.right, type, final);
		}
		break;
	}

	if (!final && is_type_untyped(type)) {
		old.type = type;
		add_expr_info(c, expr, old.mode, old.type, old.value);
		return;
	}

#if 0
	// We need to remove it and then give it a new one (this will be needed later)
	remove_expr_info(c, expr);
	add_expr_info(c, expr, old.mode, type, old.value);
#else
	add_expr_info(c, expr, old.mode, type, old.value);
#endif
}



bool is_operand_value(Operand const *o) {
	switch (o->mode) {
	case Addressing_Value:
	case Addressing_Var:
	case Addressing_Const:
		return true;
	}
	return false;
}

Scope *alloc_scope(Scope *parent, AstStmt *node) {
	Scope *s = MEM_NEW(Scope);
	s->parent = parent;
	s->node = node;
	map_init(&s->elements);
	if (parent != NULL) {
		DLIST_APPEND(parent->first_child, parent->last_child, s);
	}
	return s;
}

void scope_destroy(Scope *scope) {
	Scope *child;
	for (child = scope->first_child; child != NULL; child = child->next) {
		scope_destroy(child);
	}

	map_destroy(&scope->elements);
}

Scope *push_scope(Checker *c, AstStmt *node) {
	Scope *s = alloc_scope(c->context.scope, node);
	c->context.scope = s;
	return s;
}
Scope *pop_scope(Checker *c) {
	Scope *s = c->context.scope;
	c->context.scope = c->context.scope->parent;
	return s;
}




Type *type_from_literal(Token lit) {
	switch (lit.kind) {
	case Token_Integer: return t_untyped_int;
	case Token_Float:   return t_untyped_float;
	case Token_Rune:    return t_untyped_rune;
	case Token_String:  return t_untyped_string;
	}
	PANIC("invalid literal constant");
	return NULL;
}



Entity *alloc_entity(EntityKind kind, AstExpr *ident, AstDecl *node) {
	Entity *e = MEM_NEW(Entity);
	ASSERT(ident->kind == AstExpr_Ident);
	e->kind  = kind;
	e->name  = ident->ident.token.string;
	e->ident = ident;
	e->node  = node;
	return e;
}

DeclInfo *alloc_decl_info(Checker *c, Entity *e, AstType *type_expr, AstExpr *init_expr) {
	DeclInfo *d = MEM_NEW(DeclInfo);
	d->parent    = c->context.decl;
	d->scope     = c->context.scope;
	d->entity    = e;
	d->type_expr = type_expr;
	d->init_expr = init_expr;

	// Back-ref stuff
	if (e != NULL) {
		e->decl = d;
		e->scope = d->scope;
	}
	return d;
}


Entity *scope_lookup_entity(Scope *scope, String name) {
	bool gone_thru_proc = false;
	HashKey key = hash_str(name);
	Scope *s = NULL;
	for (s = scope; s != NULL; s = s->parent) {
		Entity *found = map_get(&s->elements, key);
		if (found) {
			Entity *e = found;
			if (gone_thru_proc) {
				// IMPORTANT TODO(bill): Is this correct?!
				if (e->kind == Entity_Label) {
					continue;
				}
				if (e->kind == Entity_Var &&
				    !(e->scope->flags&ScopeFlag_Global)) {
					continue;
				}
			}

			return e;
		}

		if (s->flags&ScopeFlag_Proc) {
			gone_thru_proc = true;
		}
	}
	return NULL;
}

Entity *scope_insert_entity(Scope *s, Entity *e) {
	ASSERT(s != NULL);
	if (e != NULL) {
		String name = e->name;
		Entity *found = NULL;
		HashKey key = {0};
		if (name.len == 0) {
			return NULL;
		}
		key = hash_str(name);
		found = map_get(&s->elements, key);
		if (found) {
			return found;
		}
		map_set(&s->elements, key, e);
		if (e->scope == NULL) {
			e->scope = s;
		}
	}
	return NULL;
}

void add_entity(Checker *c, Entity *e) {
	buf_push(c->entities, e);
	scope_insert_entity(c->context.scope, e);
	if (e->ident != NULL) {
		ASSERT(e->ident->kind == AstExpr_Ident);
		e->ident->ident.entity = e;
	}
}

void add_entity_use(Checker *c, AstExpr *ident, Entity *e) {
	ASSERT(ident->kind == AstExpr_Ident);
	e->flags |= EntityFlag_Used;
	ident->ident.entity = e;
}



void collect_entity(Checker *c, AstDecl *decl) {
	isize i;
	ASSERT(decl != NULL);
	ASSERT(c->context.scope != NULL);

	switch (decl->kind) {
	case AstDecl_Var:
		if (decl->var_decl.rhs_count > 0) {
			if (decl->var_decl.lhs_count != decl->var_decl.rhs_count) {
				error(decl->pos, "expected %ld init values, got %ld", decl->var_decl.lhs_count, decl->var_decl.rhs_count);
			}
		} else {
			if (decl->var_decl.type == NULL) {
				error(decl->pos, "expected a type for variable declaration");
				return;
			}
		}

		for (i = 0; i < decl->var_decl.lhs_count; i++) {
			Entity *e = NULL;
			DeclInfo *d = NULL;
			AstExpr *name = decl->var_decl.lhs[i];
			AstType *type_expr = decl->var_decl.type;
			AstExpr *init_expr = NULL;
			if (name->kind != AstExpr_Ident) {
				error(name->pos, "var declarations must use identifiers for a name");
				continue;
			}

			if (decl->var_decl.lhs_count == decl->var_decl.rhs_count) {
				init_expr = decl->var_decl.rhs[i];
			}

			e = alloc_entity(Entity_Var, name, decl);
			d = alloc_decl_info(c, e, type_expr, init_expr);
			add_entity(c, e);
		}
		return;

	case AstDecl_Const:
		if (decl->const_decl.lhs_count != decl->const_decl.rhs_count) {
			error(decl->pos, "expected %ld init values, got %ld", decl->const_decl.lhs_count, decl->const_decl.rhs_count);
			return;
		}

		for (i = 0; i < decl->const_decl.lhs_count; i++) {
			Entity *e = NULL;
			DeclInfo *d = NULL;
			AstExpr *name = decl->const_decl.lhs[i];
			AstType *type_expr = decl->const_decl.type;
			AstExpr *init_expr = NULL;
			if (name->kind != AstExpr_Ident) {
				error(name->pos, "const declarations must use identifiers for a name");
				continue;
			}

				init_expr = decl->const_decl.rhs[i];

			e = alloc_entity(Entity_Const, name, decl);
			d = alloc_decl_info(c, e, type_expr, init_expr);
			add_entity(c, e);
		}
		return;

	case AstDecl_Type: {
		Entity *e = NULL;
		DeclInfo *d = NULL;
		AstExpr *name = decl->type_decl.name;
		if (name->kind != AstExpr_Ident) {
			error(name->pos, "type declarations must use identifiers for a name");
			return;
		}
		e = alloc_entity(Entity_Type, name, decl);
		d = alloc_decl_info(c, e, decl->type_decl.type, NULL);
		add_entity(c, e);
		return;
	}

	case AstDecl_Proc: {
		Entity *e = NULL;
		DeclInfo *d = NULL;
		AstExpr *name = decl->proc_decl.name;
		if (name->kind != AstExpr_Ident) {
			error(name->pos, "proc declarations must use identifiers for a name");
			return;
		}
		e = alloc_entity(Entity_Proc, name, decl);
		d = alloc_decl_info(c, e, decl->proc_decl.signature, NULL);
		add_entity(c, e);
		return;
	}
	case AstDecl_Import:
		error(decl->pos, "import declarations are not yet supported");
		return;
	}
}

void check_entity_decl(Checker *c, Entity *e) {
	CheckerContext prev_context = c->context;
	ASSERT (e != NULL);
	if (e->state == EntityState_Resolved) {
		return;
	}
	if (e->type != NULL || e->state != EntityState_Unresolved) {
		error(e->ident->pos, "Illegal declaration cycle of `%.*s`", LIT(e->name));
		return;
	}
	ASSERT(e->state == EntityState_Unresolved);

	e->type = t_invalid;
	e->state = EntityState_Processing;

	c->context.decl = e->decl;
	c->context.type_hint = NULL;

	switch (e->kind) {
	case Entity_Var: {
		AstType *type_expr = e->decl->type_expr;
		AstExpr *init_expr = e->decl->init_expr;
		Operand o = {0};
		if (type_expr) {
			e->type = check_type(c, type_expr);
			c->context.type_hint = e->type;
		}

		o = check_expr(c, init_expr);
		break;
	}
	case Entity_Const: {
		AstType *type_expr = e->decl->type_expr;
		AstExpr *init_expr = e->decl->init_expr;
		Operand o = {0};
		if (type_expr) {
			e->type = check_type(c, type_expr);
			c->context.type_hint = e->type;
		}
		o = check_expr(c, init_expr);
		break;
	}
	case Entity_Type: {
		e->type = check_type(c, e->decl->type_expr);
		break;
	}
	case Entity_Proc: {
		e->type = check_type(c, e->decl->type_expr);
		ASSERT(e->type->kind == Type_Proc);
		e->scope = e->type->proc.scope;

		if (e->node) ASSERT(e->node->kind == AstDecl_Proc);
		if (e->node->proc_decl.body) {
			ProcInfo proc_info = {0};
			proc_info.decl = e->decl;
			proc_info.type = e->type;
			proc_info.body = e->node->proc_decl.body;
			buf_push(c->procs, proc_info);
		}
		break;
	}
	}

	e->state = EntityState_Resolved;

	c->context = prev_context;
}


void check_package(Checker *c, AstPackage *p) {
	isize i;
	for (i = 0; i < p->decl_count; i++) {
		AstDecl *decl = p->decls[i];
		collect_entity(c, decl);
	}

	for (i = 0; i < buf_len(c->entities); i++) {
		Entity *e = c->entities[i];
		check_entity_decl(c, e);
	}

	for (i = 0; i < buf_len(c->procs); i++) {
		ProcInfo *p = &c->procs[i];
		CheckerContext prev = c->context;
		check_proc_body(c, p->decl, p->type, p->body);
		c->context = prev;
	}
}



void check_block(Checker *c, AstStmt *stmt, u32 flags) {
	isize i;
	ASSERT(stmt->kind == AstStmt_Block);
	for (i = 0; i < stmt->block.stmt_count; i++) {
		AstStmt *s = stmt->block.stmts[i];
		check_stmt(c, s, flags);
	}
}


void check_var_decl(Checker *c, AstExpr **lhs, isize lhs_count, AstType *type_expr, AstExpr **rhs, isize rhs_count) {

}

void check_stmt(Checker *c, AstStmt *stmt, u32 flags) {
	if (stmt == NULL) return;

	switch (stmt->kind) {
	case AstStmt_Invalid:
	case AstStmt_Empty:
		break;
	case AstStmt_Decl:
		check_decl(c, stmt->decl);
		break;
	case AstStmt_Expr:
		check_expr(c, stmt->expr);
		break;
	case AstStmt_Block:
		check_block(c, stmt, flags);
		break;

	case AstStmt_Assign: {
		if (stmt->assign.op.kind == Token_Define) {
			check_var_decl(c, &stmt->assign.lhs, 1, NULL, &stmt->assign.rhs, 1);
		} else {
			Operand rhs = check_expr(c, stmt->assign.rhs);
			Operand lhs = check_expr(c, stmt->assign.lhs);
		}
		break;
	}

	case AstStmt_Label: {

		break;
	}

	case AstStmt_If: {
		Operand cond = check_expr(c, stmt->if_stmt.cond);
		if (!is_operand_value(&cond)) {
			error(cond.expr->pos, "Expected a value for an if condition, got %.*s", LIT(addressing_mode_strings[cond.mode]));
		}
		check_stmt(c, stmt->if_stmt.then_block, flags);
		check_stmt(c, stmt->if_stmt.else_stmt, flags);
		break;
	}

	case AstStmt_For: {
		u32 new_flags = flags | StmtFlag_BreakAllowed | StmtFlag_ContinueAllowed;
		AstStmt *init = stmt->for_stmt.init;
		AstExpr *cond = stmt->for_stmt.cond;
		AstStmt *post = stmt->for_stmt.post;

		Scope *scope = push_scope(c, stmt);
		check_stmt(c, init, 0);
		if (cond) {
			Operand x = check_expr(c, cond);
			if (!is_operand_value(&x)) {
				error(x.expr->pos, "Expected a value for an if condition, got %.*s", LIT(addressing_mode_strings[x.mode]));
			}
		}
		check_stmt(c, post, 0);
		check_stmt(c, stmt->for_stmt.block, new_flags);

		ASSERT(pop_scope(c) == scope);
		break;
	}
	case AstStmt_While: {
		u32 new_flags = flags | StmtFlag_BreakAllowed | StmtFlag_ContinueAllowed;
		AstExpr *cond = stmt->while_stmt.cond;
		if (cond) {
			Operand x = check_expr(c, cond);
			if (!is_operand_value(&x)) {
				error(x.expr->pos, "Expected a value for an if condition, got %.*s", LIT(addressing_mode_strings[x.mode]));
			}
		}
		check_stmt(c, stmt->while_stmt.block, new_flags);
		break;
	}
	case AstStmt_Return: {
		AstExpr *expr = stmt->return_stmt.expr;
		if (expr) {
			Operand x = check_expr(c, expr);
		}
		break;
	}
	case AstStmt_Branch:
		break;
	case AstStmt_Goto:   break;
	}
}


void check_decl(Checker *c, AstDecl *decl) {
	if (decl == NULL) return;
	ASSERT(c->context.scope != c->global_scope);

	switch (decl->kind) {
	case AstDecl_Invalid: break;

	case AstDecl_Var:
		break;
	case AstDecl_Const:
		break;
	case AstDecl_Type:
		break;
	case AstDecl_Proc:
		error(decl->pos, "proc declarations are only allowed a file scope");
		break;
	case AstDecl_Import:
		error(decl->pos, "import declarations are only allowed a file scope");
		break;
	}
}

Entity *check_ident(Checker *c, AstExpr *expr) {
	String name;
	Entity *e;

	ASSERT(expr->kind == AstExpr_Ident);
	name = expr->ident.token.string;
	e = scope_lookup_entity(c->context.scope, name);
	if (e == NULL) {
		if (is_blank_name(name)) {
			error(expr->pos, "'_' cannot be used as a value type");
		} else {
			error(expr->pos, "undeclared name: %.*s", LIT(name));
		}

		return NULL;
	}
	check_entity_decl(c, e);
	add_entity_use(c, expr, e);
	return e;
}

bool check_unary_op(Checker *c, Operand *o, Token op) {
	if (o->type == NULL) {
		error(o->expr->pos, "expression has no value");
		return false;
	}

	switch (op.kind) {
	case Token_Add:
	case Token_Sub:
		if (!is_type_numeric(o->type)) {
			error(op.pos, "operator %.*s is not allowed with non-numeric expressions");
			return false;
		}
		break;
	case Token_Xor:
		if (!is_type_integer(o->type)) {
			error(op.pos, "operator %.*s is not allowed with non-integer expressions");
			return false;
		}
		break;
	case Token_not:
		if (!is_type_boolean(o->type)) {
			error(op.pos, "operator %.*s is not allowed with non-boolean expressions");
			return false;
		}
		break;
	default:
		error(op.pos, "unknown operator %.*s", LIT(op.string));
		return false;
	}
	return true;
}

Operand check_unary_expr(Checker *c, Operand *o, Token op) {
	Operand x = {0};
	x.expr = o->expr;
	switch (op.kind) {
	case Token_At:
		if (o->mode != Addressing_Var) {
			error(op.pos, "cannot take the pointer address of a non variable");
			x.mode = Addressing_Invalid;
			return x;
		}
		x.mode = Addressing_Value;
		x.type = alloc_type_ptr(o->type);
		return x;
	}

	if (!check_unary_op(c, o, op)) {
		x.mode = Addressing_Invalid;
		return x;
	}

	if (o->mode == Addressing_Const) {
		Type *t = o->type;
		if (!is_type_constant_type(t)) {
			error(op.pos, "invalid type for constant unary expression");
			x.mode = Addressing_Invalid;
			return x;
		} else {
			int precision = 0;
			if (is_type_unsigned(t)) {
				precision = cast(int)(8 * type_size_of(t));
			}
			if (op.kind == Token_Xor && is_type_untyped(t)) {
				error(op.pos, "bitwise not cannot be applied to untyped constants");
				x.mode = Addressing_Invalid;
				return x;
			}
			if (op.kind == Token_Sub && is_type_unsigned(t)) {
				error(op.pos, "an unsigned constant cannot be negated");
				x.mode = Addressing_Invalid;
				return x;
			}

			x.type = t;
			x.value = const_value_unary(op.kind, o->value, precision);
			x.mode = Addressing_Const;
			return x;
		}
	}
	x.mode = Addressing_Value;
	return x;
}

void convert_untyped_error(Checker *c, Operand *x, Type *type) {
	error(x->expr->pos, "cannot convert expression to typed");
}

bool check_representable_as_const(Checker *c, ConstValue value_in, Type *type, ConstValue *value_out) {
	if (value_in.kind == ConstValue_Invalid) {
		return false;
	}
	if (type == t_invalid) {
		return false;
	}
	switch (type->kind) {
	case Type_Bool:
		return value_in.kind == ConstValue_Bool;
	case Type_String:
		return value_in.kind == ConstValue_String;
	case Type_Int:
	case Type_Rune: {
		ConstValue v = const_value_to_integer(value_in);
		if (v.kind != ConstValue_Integer) {
			return false;
		}
		if (value_out) *value_out = v;


		if (is_type_untyped(type)) {
			return true;
		} else {
			i64 imin, imax;
			i64 i = v.v_int;
			u64 u = *(u64 *)&i;
			i64 s = 8*type_size_of(type);
			u64 umax = ~cast(u64)0ull;
			if (s < 64) {
				umax = (1ull << cast(u64)s) - 1ull;
			} else {
				// IMPORTANT TODO(bill): I NEED A PROPER BIG NUMBER LIBRARY OR SOMETHING BETTER THAN THIS
				s = 64;
			}
			imin = -1ll << (s-1ll);
			imax = (1ll << (s-1ll))-1ll;

			if (is_type_unsigned(type)) {
				if (s == 64) {
					return 0ull <= i;
				}
				return !(u < 0ull || u > umax);
			} else {
				if (s == 64) {
					return true;
				}
				return imin <= i && i <= imax;
			}
		}
		break;
	}
	case Type_Float: {
		ConstValue v = const_value_to_float(value_in);
		if (v.kind != ConstValue_Float) {
			return false;
		}
		if (value_out) *value_out = v;

	}
	}
	return false;
}

void check_is_expressible(Checker *c, Operand *x, Type *type) {
	ASSERT(is_type_constant_type(type));
	ASSERT(x->mode == Addressing_Const);
	if (!check_representable_as_const(c, x->value, type, &x->value)) {
		error(x->expr->pos, "cannot convert expression");
		x->mode = Addressing_Invalid;
	}
}


bool convert_to_typed(Checker *c, Operand *x, Type *target_type) {
	ASSERT(target_type != NULL);
	if (x->mode == Addressing_Invalid ||
	    x->mode == Addressing_Type ||
	    !is_type_untyped(x->type) ||
	    target_type == t_invalid) {
		return false;
	}

	if (is_type_untyped(target_type)) {
		if (is_type_numeric(x->type) && is_type_numeric(target_type)) {
			// IMPORTANT NOTE(bill): Order does matter
			if (x->type->kind < target_type->kind) {
				x->type = target_type;
				update_expr_type(c, x->expr, target_type, false);
			}
			return true;
		} else if (x->type->kind != target_type->kind) {
			x->mode = Addressing_Invalid;
			convert_untyped_error(c, x, target_type);
			return false;
		}
		return true;
	}

	switch (target_type->kind) {
	case Type_Bool:
	case Type_Int:
	case Type_Rune:
	case Type_Float:
	case Type_String:
		if (x->mode == Addressing_Const) {
			check_is_expressible(c, x, target_type);
			if (x->mode == Addressing_Invalid) {
				return false;
			}
			update_expr_value(c, x->expr, x->value);
		} else if (is_type_untyped(x->type)) {
			switch (x->type->kind) {
			case Type_Bool:
				if (!is_type_boolean(target_type)) {
					x->mode = Addressing_Invalid;
					convert_untyped_error(c, x, target_type);
					return false;
				}
				break;
			case Type_Int:
			case Type_Rune:
			case Type_Float:
				if (!is_type_numeric(target_type)) {
					x->mode = Addressing_Invalid;
					convert_untyped_error(c, x, target_type);
					return false;
				}
				break;
			}
		}
		break;
	default:
		x->mode = Addressing_Invalid;
		convert_untyped_error(c, x, target_type);
		return false;
	}

	x->type = target_type;
	return true;
}

Operand check_comparison(Checker *c, Operand x, Operand y, Token op) {
	// TODO(bill): check_comparison
	return x;
}

Operand check_binary_expr(Checker *c, Operand x, Operand y, Token op) {
	if (x.mode == Addressing_Invalid) {
		return x;
	}
	if (y.mode == Addressing_Invalid) {
		x.mode = Addressing_Invalid;
		x.expr = y.expr;
		return x;
	}

	if (!convert_to_typed(c, &x, y.type)) {
		return x;
	}
	if (!convert_to_typed(c, &y, x.type)) {
		x.mode = Addressing_Invalid;
		x.expr = y.expr;
		return x;
	}

	if (op.kind == Token_Ellipsis) {
		error(op.pos, "TODO: range expressions are not yet supported");
		return x;
	}

	if (token_is_comparison(op.kind)) {
		return check_comparison(c, x, y, op);
	}

	if (!are_types_equal(x.type, y.type)) {
		if (x.type != t_invalid &&
		    y.type != t_invalid) {
			error(op.pos, "mismatched types in binary expression");
		}
		x.mode = Addressing_Invalid;
		return x;
	}

	switch (op.kind) {
	case Token_Div:
	case Token_Mod:
	case Token_DivEq:
	case Token_ModEq:
		if ((x.mode == Addressing_Const || is_type_integer(x.type)) &&
		    y.mode == Addressing_Const) {
			bool fail = false;
			switch (y.value.kind) {
			case ConstValue_Integer:
				if (y.value.v_int == 0 ) {
					fail = true;
				}
				break;
			case ConstValue_Float:
				if (y.value.v_float == 0.0) {
					fail = true;
				}
				break;
			}

			if (fail) {
				error(y.expr->pos, "division by zero not allowed");
				x.mode = Addressing_Invalid;
				return x;
			}
		}
	}

	return x;
}

bool check_is_castable_to(Checker *c, Operand *x, Type *type) {
	return false;
}

bool check_cast_internal(Checker *c, Operand *x, Type *type) {
	bool is_const_expr = x->mode == Addressing_Const;
	bool can_convert = false;
	if (is_const_expr && is_type_constant_type(type)) {
		if (Type_Bool <= type->kind && type->kind <= Type_String) { // IMPORTANT NOTE(bill); Order does matter
			if (check_representable_as_const(c, x->value, type, &x->value)) {
				return true;
			} else if (type->kind == Type_Ptr && check_is_castable_to(c, x, type)) {
				return true;
			}
		}
	} else if (check_is_castable_to(c, x, type)) {
		if (x->mode != Addressing_Const) {
			x->mode = Addressing_Value;
		} else if (type->kind == Type_Slice && x->type->kind == Type_String) {
			x->mode = Addressing_Value;
		}
		return true;
	}
	return false;
}

void check_cast(Checker *c, Operand *o, Type *type) {
	if (!is_operand_value(o)) {
		error(o->expr->pos, "only values can be casted");
		o->mode = Addressing_Invalid;
		return;
	} else {
		bool is_const_expr = o->mode == Addressing_Const;
		bool can_convert = check_cast_internal(c, o, type);

		if (can_convert) {
			error(o->expr->pos, "cannot cast expression");
			o->mode = Addressing_Invalid;
			return;
		}

		if (is_type_untyped(o->type)) {
			Type *final_type = type;
			if (is_const_expr && !is_type_constant_type(type)) {
				final_type = default_type(o->type);
			}
			update_expr_type(c, o->expr, final_type, true);
		}

		o->type = type;
	}
}


bool check_assignment(Checker *c, Operand *x, Type *type) {
	return false;
}

Operand check_expr_base_internal(Checker *c, AstExpr *expr, Type *type_hint) {
	Operand o = {0};
	o.expr = expr;

	ASSERT(expr != NULL);
	switch (expr->kind) {
	case AstExpr_Literal:
		o.mode = Addressing_Const;
		o.value = const_value_from_literal(expr->literal);
		o.type = type_from_literal(expr->literal);
		return o;
	case AstExpr_Ident: {
		Entity *e = check_ident(c, expr);
		if (e == NULL) {
			o.type = t_invalid;
			o.mode = Addressing_Invalid;
			return o;
		}
		o.type = e->type;
		switch (e->kind) {
		case Entity_Var:   o.mode = Addressing_Var;     break;
		case Entity_Const: o.mode = Addressing_Const;   break;
		case Entity_Type:  o.mode = Addressing_Type;    break;
		case Entity_Proc:  o.mode = Addressing_Value;   break;
		case Entity_Label: o.mode = Addressing_NoValue; break; // NOTE(bill): Even though it's a label
		default:
			error(expr->pos, "invalid entity for identifier %.*s", LIT(e->name));
			break;
		}
		return o;
	}
	case AstExpr_TypeExpr: {
		Type *t = check_type(c, expr->type_expr);
		if (t != t_invalid) {
			o.mode = Addressing_Type;
		}
		o.type = t;
		return o;
	}
	case AstExpr_Paren:
		return check_expr(c, expr->paren.expr);
	case AstExpr_Call: {
		isize cargs = expr->call.arg_count;
		Operand p = check_expr_or_type(c, expr->call.expr, NULL);
		if (p.mode == Addressing_Type) {
			switch (cargs) {
			case 0:  error(p.expr->pos, "missing argument in type convertion");   break;
			default: error(p.expr->pos, "too many arguments in type convertion"); break;
			case 1: {
				AstExpr *arg = expr->call.args[0];
				Operand x = check_expr(c, arg);
				if (x.mode != Addressing_Invalid) {
					check_cast(c, &x, p.type);
				}
				return x;
			}
			}
			ASSERT(cargs != 1);
			o.mode = Addressing_Invalid;
			return o;
		}
		if (p.type == NULL || p.type == t_invalid || p.type->kind != Type_Proc) {
			error(p.expr->pos, "call expected procedure");
			return o;
		} else {
			isize pargs = p.type->proc.field_count;
			isize arg_count = MIN(pargs, cargs);
			isize i;
			if (cargs < pargs) {
				error(p.expr->pos, "too few arguments in call");
			} else if (cargs > pargs) {
				error(p.expr->pos, "too many arguments in call");
			}
			for (i = 0; i < arg_count; i++) {
				AstExpr *arg = expr->call.args[i];
				Entity *field = p.type->proc.fields[i];
				Operand x = check_expr(c, arg);
				if (!check_assignment(c, &x, field->type)) {
					String name = field->name;
					if (name.len == 0 || is_blank_name(name)) {
						error(arg->pos, "cannot assign to procedure argument");
					} else {
						error(arg->pos, "cannot assign to procedure argument '%.*s'", LIT(field->name));
					}
				}
			}
			if (p.type->proc.ret != NULL) {
				o.mode = Addressing_Value;
				o.type = p.type->proc.ret;
			} else {
				o.mode = Addressing_NoValue;
			}
		}
		break;
	}
	case AstExpr_Index:
		break;
	case AstExpr_Selector:
		break;
	case AstExpr_Deref: {
		Operand x = check_expr(c, expr->deref.expr);
		if (is_operand_value(&x)) {
			error(x.expr->pos, "Cannot derefence a non-pointer value");
			return o;
		}
		if (x.type == NULL || x.type == t_invalid || x.type->kind != Type_Ptr) {
			error(x.expr->pos, "Cannot derefence a non-pointer");
			return o;
		}
		if (x.type->ptr.elem == NULL) {
			error(x.expr->pos, "Cannot derefence a rawptr");
			return o;
		}
		o.mode = Addressing_Var;
		o.type = type_deref(x.type);
		return o;
	}
	case AstExpr_Unary: {
		Operand x = check_expr_base(c, expr->unary.expr, type_hint);
		if (x.mode == Addressing_Invalid) {
			x.expr = expr;
			return x;
		}
		return check_unary_expr(c, &x, expr->unary.op);
	}
	case AstExpr_Binary: {
		Token op = expr->binary.op;
		Operand x = check_expr(c, expr->binary.left);
		Operand y = check_expr(c, expr->binary.right);
		return check_binary_expr(c, x, y, op);
	}
	case AstExpr_Ternary: {
		Operand cond = check_expr(c, expr->ternary.cond);
		Operand x = check_expr(c, expr->ternary.left);
		Operand y = check_expr(c, expr->ternary.right);
		return x;
	}
	}

	return o;
}

Operand check_expr_base(Checker *c, AstExpr *expr, Type *type_hint) {
	Operand o = check_expr_base_internal(c, expr, type_hint);
	Type *type = NULL;
	ConstValue value = {0};
	switch (o.mode) {
	case Addressing_Invalid:
		type = t_invalid;
		break;
	case Addressing_NoValue:
		type = NULL;
		break;
	case Addressing_Const:
		type = o.type;
		value = o.value;
		break;
	default:
		type = o.type;
		break;
	}

	add_expr_info(c, expr, o.mode, type, value);
	return o;
}


void error_operand_no_value(Operand *o) {
	if (o->mode == Addressing_NoValue) {
		AstExpr *x = unparen_expr(o->expr);
		if (x->kind == AstExpr_Call) {
			error(o->expr->pos, "call does not return a value and cannot be used as a value");
		} else {
			error(o->expr->pos, "expression has no value");
		}
		o->mode = Addressing_Invalid;
	}
}

void error_operand_no_expr(Operand *o) {
	if (o->mode == Addressing_Type) {
		error(o->expr->pos, "expected an expression but got type");
		o->mode = Addressing_Invalid;
	}
}


Operand check_expr_or_type(Checker *c, AstExpr *expr, Type *type_hint) {
	Operand o = check_expr_base(c, expr, type_hint);
	error_operand_no_value(&o);
	return o;
}


Operand check_expr(Checker *c, AstExpr *expr) {
	Operand o = check_expr_base(c, expr, NULL);
	error_operand_no_value(&o);
	error_operand_no_expr(&o);
	return o;
}

Type *check_type(Checker *c, AstType *type_expr) {
	ASSERT(type_expr != NULL);
	switch (type_expr->kind) {
	case AstType_Ident: {
		Entity *e = check_ident(c, type_expr->ident);
		if (e->kind == Entity_Type) {
			return e->type;
		}
		error(type_expr->pos, "%.*s is not a type", LIT(e->name));
		return NULL;
	}
	case AstType_Array: {
		AstExpr *size = type_expr->array.size;
		AstType *elem = type_expr->array.elem;
		if (size != NULL) {
			i64 len = 0;
			Type *elem_type = NULL;
			Operand x = check_expr(c, size);
			if (x.mode == Addressing_Const && is_type_integer(x.type)) {
				len = x.value.v_int;
				if (len < 0) {
					error(x.expr->pos, "array count cannot be less than 0");
					len = 0;
				}
			} else {
				error(x.expr->pos, "expected a constant integer");
			}
			elem_type = check_type(c, elem);
			return alloc_type_array(elem_type, len);
		} else {
			Type *elem_type = check_type(c, elem);
			return alloc_type_slice(elem_type);
		}
		break;
	}
	case AstType_Set:
		error(type_expr->pos, "TODO: set type");
		break;
	case AstType_Range: {
		i64 lower, upper;
		Operand x = check_expr(c, type_expr->range.from);
		Operand y = check_expr(c, type_expr->range.to);
		if (x.mode != Addressing_Const || !is_type_integer(x.type)) {
			error(x.expr->pos, "range fields must be constant integers");
			return t_invalid;
		}
		if (y.mode != Addressing_Const || !is_type_integer(y.type)) {
			error(y.expr->pos, "range fields must be constant integers");
			return t_invalid;
		}
		lower = x.value.v_int;
		upper = y.value.v_int;
		if (lower > upper) {
			i64 temp;
			error(type_expr->pos, "lower range value greater than upper, %ld vs %ld", lower, upper);
			// NOTE(bill): swap to make sure the mathematics is fine
			temp = lower;
			lower = upper;
			upper = temp;
		}
		error(type_expr->pos, "TODO: range type");
		return alloc_type_range(lower, upper);
	}
	case AstType_Pointer: {
		Type *elem = check_type(c, type_expr->pointer.elem);
		return alloc_type_ptr(elem);
	}
	case AstType_Signature: {
		Type *proc_type = NULL;
		isize i;
		Entity **fields = NULL;
		Type *ret = NULL;

		Scope *scope = push_scope(c, NULL);

		for (i = 0; i < type_expr->signature.param_count; i++) {
			AstField f = type_expr->signature.params[i];
			Type *t = check_type(c, f.type);
			Entity *e = alloc_entity(Entity_Var, f.name, NULL);
			e->type = t;
			e->state = EntityState_Resolved;
			e->flags |= EntityFlag_Param;
			add_entity(c, e);
			add_entity_use(c, f.name, e);
			buf_push(fields, e);
		}

		if (type_expr->signature.return_type != NULL) {
			ret = check_type(c, type_expr->signature.return_type);
		}

		ASSERT(pop_scope(c) == scope);

		proc_type = alloc_type_proc(scope, fields, buf_len(fields), ret);
		buf_free(fields);
		return proc_type;
	}
	}
	error(type_expr->pos, "expected a type");
	return t_invalid;
}


void complete_type(Type *t) {

}

bool check_is_terminating(AstStmt *stmt);
bool check_is_terminating_list(AstStmt **stmts, isize stmt_count);
bool check_has_break(AstStmt *stmt, bool implicit);
bool check_has_break_list(AstStmt **stmts, isize stmt_count, bool implicit);


bool check_has_break_list(AstStmt **stmts, isize stmt_count, bool implicit) {
	isize i;
	for (i = 0; i < stmt_count; i++) {
		AstStmt *stmt = stmts[i];
		if (check_has_break(stmt, implicit)) {
			return true;
		}
	}
	return false;
}


bool check_has_break(AstStmt *stmt, bool implicit) {
	switch (stmt->kind) {
	case AstStmt_Branch:
		if (stmt->branch_stmt.token.kind == Token_break) {
			return implicit;
		}
		break;
	case AstStmt_Block:
		return check_has_break_list(stmt->block.stmts, stmt->block.stmt_count, implicit);

	case AstStmt_If:
		if (check_has_break(stmt->if_stmt.then_block, implicit) ||
		    (stmt->if_stmt.else_stmt != NULL && check_has_break(stmt->if_stmt.else_stmt, implicit))) {
			return true;
		}
		break;
	}

	return false;
}

bool check_is_terminating_list(AstStmt **stmts, isize stmt_count) {
	// Iterate backwards
	isize n;
	for (n = stmt_count-1; n >= 0; n--) {
		AstStmt *stmt = stmts[n];
		switch (stmt->kind) {
		case AstStmt_Invalid:
		case AstStmt_Empty:
			break;
		default:
			return check_is_terminating(stmt);
		}
	}

	return false;
}


bool check_is_terminating(AstStmt *stmt) {
	switch (stmt->kind) {
	case AstStmt_Return:
		return true;

	case AstStmt_Block:
		return check_is_terminating_list(stmt->block.stmts, stmt->block.stmt_count);

	case AstStmt_If:
		if (stmt->if_stmt.else_stmt != NULL) {
			if (check_is_terminating(stmt->if_stmt.then_block) &&
			    check_is_terminating(stmt->if_stmt.else_stmt)) {
				return true;
			}
		}
		break;
	case AstStmt_For:
		if (stmt->for_stmt.cond == NULL && !check_has_break(stmt->for_stmt.block, true)) {
			return check_is_terminating(stmt->for_stmt.block);
		}
		break;
	case AstStmt_While:
		// TODO(bill): cond is `true`
		break;
	}

	return false;
}


void check_proc_body(Checker *c, DeclInfo *decl, Type *type, AstStmt *body) {
	if (body != NULL) {
		Scope *scope = NULL;
		String proc_name = str_lit("(anonymous-procedure)");
		if (decl->entity) {
			proc_name = decl->entity->name;
		}
		ASSERT(type->kind == Type_Proc);

		c->context.decl = decl;
		c->context.scope = type->proc.scope;
		c->context.curr_proc = decl->entity;
		c->context.proc_name = proc_name;
		c->context.type_hint = NULL;

		scope = push_scope(c, body);

		check_stmt(c, body, 0);
		if (type->proc.ret != NULL) {
			if (!check_is_terminating(body)) {
				AstStmt *end = body->block.stmts[body->block.stmt_count-1];
				if (decl->entity) {
					error(body->pos, "missing return statement at the end of the procedure '%.*s'", LIT(decl->entity->name));
				} else {
					error(body->pos, "missing return statement at the end of the procedure");
				}
			}
		}

		ASSERT(pop_scope(c) == scope);
	}
}





