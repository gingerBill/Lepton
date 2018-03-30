#include "checker.h"

bool is_blank_name(String name) {
	if (name.len == 1 && name.text[0] == '_') {
		return true;
	}
	return false;
}


Type *alloc_universal_type(char *name, TypeKind kind, i64 size, i64 align, u32 type_flags) {
	Entity *e = NULL;
	Type *t = NULL;
	AstExpr *ident = NULL;
	Token token = {Token_Ident};

	assert(universal_scope != NULL);

	token.string = make_string_c(name);
	ident = ast_expr_ident(token);
	t = alloc_type(kind);
	t->size  = size;
	t->align = align;
	t->flags = type_flags;

	e = alloc_entity(Entity_Type, ident, NULL);
	e->type = t;
	e->state = EntityState_Resolved;
	scope_insert_entity(universal_scope, e);
	return t;
}

void init_universal_scope(void) {
	universal_scope = alloc_scope(NULL, NULL);
	universal_scope->flags |= ScopeFlag_Global;

	assert(t_untyped_bool == NULL);
	t_untyped_bool   = alloc_universal_type("untyped bool",   Type_Bool,   -1, -1, TypeFlag_Untyped);
	t_untyped_int    = alloc_universal_type("untyped int",    Type_Int,    -1, -1, TypeFlag_Untyped);
	t_untyped_float  = alloc_universal_type("untyped float",  Type_Float,  -1, -1, TypeFlag_Untyped);
	t_untyped_string = alloc_universal_type("untyped string", Type_String, -1, -1, TypeFlag_Untyped);
	t_untyped_rune   = alloc_universal_type("untyped rune",   Type_Rune,   -1, -1, TypeFlag_Untyped);

	t_bool   = alloc_universal_type("bool",   Type_Bool,   1, 1, 0);
	t_int    = alloc_universal_type("int",    Type_Int,    PTR_SIZE, PTR_ALIGN, 0);
	t_uint   = alloc_universal_type("int",    Type_Int,    PTR_SIZE, PTR_ALIGN, TypeFlag_Unsigned);
	t_f32    = alloc_universal_type("f32",    Type_Float,  4, 4, 0);
	t_f64    = alloc_universal_type("f64",    Type_Float,  8, 8, 0);
	t_string = alloc_universal_type("string", Type_String, 2*PTR_SIZE, PTR_ALIGN, 0);
	t_rune   = alloc_universal_type("rune",   Type_Rune,   4, 4, 0);
	t_rawptr = alloc_universal_type("rawptr", Type_Ptr,    PTR_SIZE, PTR_SIZE, 0);
}

void checker_init(Checker *c) {
	c->global_scope = alloc_scope(universal_scope, NULL);
	c->context.scope = c->global_scope;
	universal_scope->flags |= ScopeFlag_Global;
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




ConstValue const_value_from_literal(Token lit) {
	ConstValue v = {0};
	switch (lit.kind) {
	case Token_Integer:
		v.kind = ConstValue_Int;
		v.v_int = cast(i64)u64_from_string(lit.string);
		break;
	case Token_Float:
		v.kind = ConstValue_Float;
		v.v_float = float_from_string(lit.string);
		break;
	case Token_Rune:
		v.kind = ConstValue_Rune;
		panic("TODO: rune literal");
		break;
	case Token_String:
		v.kind = ConstValue_String;
		panic("TODO: string literal");
		break;
	default: panic("invalid literal constant"); break;
	}
	return v;
}

Type *type_from_literal(Token lit) {
	switch (lit.kind) {
	case Token_Integer:
		return t_untyped_int;
	case Token_Float:
		return t_untyped_float;
	case Token_Rune:
		return t_untyped_rune;
	case Token_String:
		return t_untyped_string;
	}
	panic("invalid literal constant");
	return NULL;
}





Entity *alloc_entity(EntityKind kind, AstExpr *ident, AstDecl *node) {
	Entity *e = MEM_NEW(Entity);
	assert(ident->kind == AstExpr_Ident);
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
	assert(s != NULL);
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
		assert(e->ident->kind == AstExpr_Ident);
		e->ident->ident.entity = e;
	}
}

void add_entity_use(Checker *c, AstExpr *ident, Entity *e) {
	assert(ident->kind == AstExpr_Ident);
	e->flags |= EntityFlag_Used;
	ident->ident.entity = e;
}



void collect_entity(Checker *c, AstDecl *decl) {
	isize i;
	assert(decl != NULL);
	assert(c->context.scope != NULL);

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
	assert (e != NULL);
	if (e->state == EntityState_Resolved) {
		return;
	}
	if (e->type != NULL || e->state != EntityState_Unresolved) {
		error(e->ident->pos, "Illegal declaration cycle of `%.*s`", LIT(e->name));
		return;
	}
	assert(e->state == EntityState_Unresolved);

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
		assert(e->type->kind == Type_Proc);
		e->scope = e->type->proc.scope;

		if (e->node) assert(e->node->kind == AstDecl_Proc);
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



void check_block(Checker *c, AstStmt *stmt) {
	assert(stmt->kind == AstStmt_Block);
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
		check_block(c, stmt);
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

		assert(pop_scope(c) == scope);
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
	assert(c->context.scope != c->global_scope);

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

	assert(expr->kind == AstExpr_Ident);
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

Operand check_expr_base_internal(Checker *c, AstExpr *expr, Type *type_hint) {
	Operand o = {0};
	o.expr = expr;

	assert(expr != NULL);
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
		Operand p = check_expr(c, expr->call.expr);
		if (p.type == NULL || p.type == t_invalid || p.type->kind != Type_Proc) {
			error(p.expr->pos, "call expected procedure");
			return o;
		} else {
			isize pargs = p.type->proc.field_count;
			isize cargs = expr->call.arg_count;
			isize arg_count = MIN(pargs, cargs);
		}
		o.mode = Addressing_NoValue;
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
		Operand x = check_expr(c, expr->unary.expr);
		return x;
	}
	case AstExpr_Binary: {
		Operand x = check_expr(c, expr->binary.left);
		Operand y = check_expr(c, expr->binary.right);
		return x;
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

void add_type_and_value(Checker *c, AstExpr *expr, AddressingMode mode, Type *type, ConstValue value) {

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

	if (type != NULL && is_type_untyped(type)) {
		// TODO(bill): add_untyped
	} else {
		add_type_and_value(c, expr, o.mode, type, value);
	}
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
	assert(type_expr != NULL);
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
		// return alloc_type_range(lower, upper);
		break;
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

		assert(pop_scope(c) == scope);

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
	if (body == NULL) {
		return;
	} else {
		Scope *scope = NULL;
		String proc_name = str_lit("(anonymous-procedure)");
		if (decl->entity) {
			proc_name = decl->entity->name;
		}
		assert(type->kind == Type_Proc);

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

		assert(pop_scope(c) == scope);
	}
}
