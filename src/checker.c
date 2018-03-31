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
	t->name = token.string;

	e = alloc_entity(Entity_Type, ident, NULL);
	e->type = t;
	e->state = EntityState_Resolved;
	prev = scope_insert_entity(universal_scope, e);
	ASSERT(prev == NULL);
	return t;
}

void alloc_universal_constant(char *name, Type *type, ConstValue value) {
	Entity *e = NULL;
	Entity *prev = NULL;
	AstExpr *ident = NULL;
	Token token = {Token_Ident};

	ASSERT(universal_scope != NULL);

	token.string = make_string_c(name);
	ident = ast_expr_ident(token);

	e = alloc_entity(Entity_Const, ident, NULL);
	e->type = type;
	e->value = value;
	e->state = EntityState_Resolved;
	prev = scope_insert_entity(universal_scope, e);
	ASSERT(prev == NULL);
}

Entity *alloc_universal_entity(char *name, EntityKind kind, Type *type) {
	Entity *e = NULL;
	Entity *prev = NULL;
	AstExpr *ident = NULL;
	Token token = {Token_Ident};

	ASSERT(universal_scope != NULL);

	token.string = make_string_c(name);
	ident = ast_expr_ident(token);

	e = alloc_entity(kind, ident, NULL);
	e->type = type;
	e->state = EntityState_Resolved;
	prev = scope_insert_entity(universal_scope, e);
	ASSERT(prev == NULL);
	return e;
}

static bool global_universal_scope_init = false;
void init_universal_scope(void) {
	ASSERT(global_universal_scope_init == false);
	global_universal_scope_init = true;

	universal_scope = alloc_scope(NULL, NULL);
	universal_scope->flags |= ScopeFlag_Global;

	t_untyped_bool   = alloc_universal_type("untyped bool",   Type_Bool,   0, 0, TypeFlag_Untyped);
	t_untyped_int    = alloc_universal_type("untyped int",    Type_Int,    0, 0, TypeFlag_Untyped);
	t_untyped_float  = alloc_universal_type("untyped float",  Type_Float,  0, 0, TypeFlag_Untyped);
	t_untyped_string = alloc_universal_type("untyped string", Type_String, 0, 0, TypeFlag_Untyped);
	t_untyped_rune   = alloc_universal_type("untyped rune",   Type_Rune,   0, 0, TypeFlag_Untyped);
	t_untyped_nil    = alloc_universal_type("untyped nil",    Type_Nil,    0, 0, TypeFlag_Untyped);

	t_bool    = alloc_universal_type("bool",    Type_Bool,   1, 1, 0);
	t_int     = alloc_universal_type("int",     Type_Int,    PTR_SIZE, PTR_ALIGN, 0);
	t_uint    = alloc_universal_type("uint",    Type_Int,    PTR_SIZE, PTR_ALIGN, TypeFlag_Unsigned);
	t_uintptr = alloc_universal_type("uintptr", Type_Int,    PTR_SIZE, PTR_ALIGN, TypeFlag_Unsigned);
	t_int8    = alloc_universal_type("int8",    Type_Int,    1, 1, 0);
	t_int16   = alloc_universal_type("int16",   Type_Int,    2, 2, 0);
	t_int32   = alloc_universal_type("int32",   Type_Int,    4, 4, 0);
	t_int64   = alloc_universal_type("int64",   Type_Int,    8, 8, 0);
	t_uint8   = alloc_universal_type("uint8",   Type_Int,    1, 1, TypeFlag_Unsigned);
	t_uint16  = alloc_universal_type("uint16",  Type_Int,    2, 2, TypeFlag_Unsigned);
	t_uint32  = alloc_universal_type("uint32",  Type_Int,    4, 4, TypeFlag_Unsigned);
	t_uint64  = alloc_universal_type("uint64",  Type_Int,    8, 8, TypeFlag_Unsigned);
	t_float32 = alloc_universal_type("float32", Type_Float,  4, 4, 0);
	t_float64 = alloc_universal_type("float64", Type_Float,  8, 8, 0);
	t_string  = alloc_universal_type("string",  Type_String, 2*PTR_SIZE, PTR_ALIGN, 0);
	t_rune    = alloc_universal_type("rune",    Type_Rune,   4, 4, 0);
	t_rawptr  = alloc_universal_type("rawptr",  Type_Ptr,    PTR_SIZE, PTR_SIZE, 0);

	alloc_universal_constant("false", t_untyped_bool, const_value_bool(false));
	alloc_universal_constant("true",  t_untyped_bool, const_value_bool(true));

	alloc_universal_entity("nil", Entity_Nil, t_untyped_nil);
}

void checker_init(Checker *c) {
	c->global_scope = alloc_scope(universal_scope, NULL);
	c->global_scope->flags |= ScopeFlag_Global;
	c->context.scope = c->global_scope;

	map_init(&c->expr_info_map);
}

void check_type_path_push(Checker *c, Entity *e) {
	ASSERT(e != NULL);
	buf_push(c->context.type_path, e);
}
Entity *check_type_path_pop(Checker *c) {
	Entity *prev = NULL;
	isize n = buf_len(c->context.type_path);
	ASSERT(n > 0);
	prev = c->context.type_path[n-1];
	buf_pop(c->context.type_path);
	return prev;
}

bool check_cycle(Checker *c, Entity *curr, bool report) {
	isize i, j;
	if (curr->state != EntityState_Processing) {
		return false;
	}
	for (i = 0; i < buf_len(c->context.type_path); i++) {
		Entity *prev = c->context.type_path[i];
		if (prev == curr) {
			if (report) {
				error(curr->ident->pos, "illegal declaration cycle of '%.*s'", LIT(curr->name));
				for (j = i; j < buf_len(c->context.type_path); j++) {
					Entity *curr = c->context.type_path[j];
					error(curr->ident->pos, "\t%.*s refers to", LIT(curr->name));
				}
				error(curr->ident->pos, "\t%.*s", LIT(curr->name));
			}
			return true;
		}
	}
	return false;
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

Entity *alloc_entity_dummy_variable(Scope *s, AstExpr *ident) {
	Entity *e = alloc_entity(Entity_Var, ident, NULL);
	e->name = make_string_c("_");
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
Entity *current_scope_lookup_entity(Scope *s, String name) {
	HashKey key = hash_str(name);
	return map_get(&s->elements, key);
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
		error(e->ident->pos, "illegal declaration cycle of '%.*s'", LIT(e->name));
		return;
	}
	ASSERT(e->state == EntityState_Unresolved);

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
		check_expr(c, &o, init_expr);
		check_init_variable(c, e, &o, "variable declaration");
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
		check_expr(c, &o, init_expr);
		break;
	}
	case Entity_Type:
		check_type_decl(c, e, e->decl->type_expr);
		break;
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


bool check_arity_match(Checker *c, AstExpr **lhs, isize lhs_count, AstType *type_expr, AstExpr **rhs, isize rhs_count) {
	ASSERT(lhs_count != 0);

	if (rhs_count == 0) {
		if (type_expr == NULL) {
			error(lhs[0]->pos, "missing type or initial expression");
			return false;
		}
	} else if (lhs_count < rhs_count) {
		AstExpr *n = rhs[lhs_count];
		char *str = expr_to_string(n);
		error(n->pos, "extra initial expression '%s'", str);
		mem_free(str);
		return false;
	} else if (lhs_count > rhs_count) {
		AstExpr *n = lhs[rhs_count];
		char *str = expr_to_string(n);
		error(n->pos, "missing expression for '%s'", str);
		mem_free(str);
		return false;
	}

	return true;
}

void check_init_variable(Checker *c, Entity *e, Operand *o, char const *context_name) {
	if (o->mode == Addressing_Invalid ||
	    o->type == t_invalid ||
	    e->type == t_invalid) {
		if (e->type == NULL) {
			e->type = t_invalid;
		}
		return;
	}
	if (e->type == NULL) {
		Type *t = o->type;
		if (is_type_untyped(t)) {
			t = default_type(t);
		}
		ASSERT(is_type_typed(t));
		e->type = t;
	}

	check_assignment(c, o, e->type, context_name);
	if (o->mode == Addressing_Invalid) {
		return;
	}
}



void check_init_variables(Checker *c, Entity **lhs, isize lhs_count, AstExpr **rhs, isize rhs_count, char const *context_name) {
	if ((lhs == NULL || lhs_count == 0) && rhs_count == 0) {
		return;
	} else {
		isize i;
		isize count = MIN(lhs_count, rhs_count);
		for (i = 0; i < count; i++) {
			Entity *e = lhs[i];
			DeclInfo *d = e->decl;
			Operand o = {0};
			check_expr(c, &o, rhs[i]);
			check_init_variable(c, e, &o, context_name);
			if (d != NULL) {
				d->init_expr = o.expr;
			}
		}

		if (rhs_count > 0 && lhs_count != rhs_count) {
			error(lhs[0]->ident->pos, "assignment count mismatch '%ld' = '%ld'", lhs_count, rhs_count);
		}
	}
}


void check_var_decl(Checker *c, AstExpr **lhs, isize lhs_count, AstType *type_expr, AstExpr **rhs, isize rhs_count) {
	isize i;
	Type *init_type = NULL;
	Entity **entities = NULL; // dynamic buffer
	isize new_name_count = 0;

	if (lhs_count == 0) {
		return;
	}
	buf_reserve(entities, lhs_count);

	for (i = 0; i < lhs_count; i++) {
		AstExpr *name = lhs[i];
		Entity *entity = NULL;

		if (name->kind != AstExpr_Ident) {
			error(name->pos, "var declarations must use identifiers for a name");
		} else {
			Token token = name->ident.token;
			String str = token.string;
			Entity *found = NULL;
			if (!is_blank_name(str)) {
				found = current_scope_lookup_entity(c->context.scope, str);
				new_name_count += 1;
			}
			if (found == NULL) {
				entity = alloc_entity(Entity_Var, name, NULL);
			} else {
				TokenPos pos = found->ident->pos;
				error(pos,
				      "redeclaration of '%.*s' in this scope\n"
				      "\tat %.*s(%ld:%ld)",
				      LIT(str), LIT(pos.file), pos.line, pos.column);
				entity = found;
			}
		}
		if (entity == NULL) {
			entity = alloc_entity_dummy_variable(c->global_scope, name);
		}
		buf_push(entities, entity);
	}

	if (new_name_count == 0) {
		error(lhs[0]->pos, "no new declarations on the lhs");
	}

	init_type = NULL;
	if (type_expr != NULL) {
		init_type = check_type(c, type_expr);
		if (init_type == NULL) {
			init_type = t_invalid;
		}
	}

	for (i = 0; i < buf_len(entities); i++) {
		Entity *e = entities[i];
		ASSERT(e != NULL);
		if (e->flags & EntityFlag_Visited) {
			e->type = t_invalid;
			continue;
		}
		e->flags |= EntityFlag_Visited;
		e->state = EntityState_Processing;
		if (e->type == NULL) {
			e->type = init_type;
			e->state = EntityState_Resolved;
		}
	}

	check_arity_match(c, lhs, lhs_count, type_expr, rhs, rhs_count);
	check_init_variables(c, entities, buf_len(entities), rhs, rhs_count, "variable declaration");

	for (i = 0; i < buf_len(entities); i++) {
		Entity *e = entities[i];
		add_entity(c, e);
	}

}

void check_init_constant(Checker *c, Entity *e, Operand *o) {
	if (o->mode == Addressing_Invalid ||
	    o->type == t_invalid ||
	    e->type == t_invalid) {
		if (e->type == NULL) {
			e->type = t_invalid;
		}
		return;
	}
	if (o->mode != Addressing_Const) {
		char *str = expr_to_string(o->expr);
		error(o->expr->pos, "'%s' is not a constant", str);
		mem_free(str);
		if (e->type == NULL) {
			e->type = t_invalid;
		}
		return;
	}
	if (!is_type_constant_type(o->type)) {
		char *str = type_to_string(o->type);
		error(o->expr->pos, "invalid constant type: '%s'", str);
		mem_free(str);
		if (e->type == NULL) {
			e->type = t_invalid;
		}
		return;
	}

	if (e->type == NULL) {
		e->type = o->type;
	}

	check_assignment(c, o, e->type, "constant declaration");
	if (o->mode == Addressing_Invalid) {
		return;
	}
	e->value = o->value;
}



void check_init_constants(Checker *c, Entity **lhs, isize lhs_count, AstExpr **rhs, isize rhs_count) {
	if ((lhs == NULL || lhs_count == 0) && rhs_count == 0) {
		return;
	} else {
		isize i;
		isize count = MIN(lhs_count, rhs_count);
		for (i = 0; i < count; i++) {
			Entity *e = lhs[i];
			DeclInfo *d = e->decl;
			Operand o = {0};
			check_expr(c, &o, rhs[i]);
			check_init_constant(c, e, &o);
			if (d != NULL) {
				d->init_expr = o.expr;
			}
		}

		if (rhs_count > 0 && lhs_count != rhs_count) {
			error(lhs[0]->ident->pos, "assignment count mismatch '%ld' = '%ld'", lhs_count, rhs_count);
		}
	}
}


void check_const_decl(Checker *c, AstExpr **lhs, isize lhs_count, AstType *type_expr, AstExpr **rhs, isize rhs_count) {
	isize i;
	Type *init_type = NULL;
	Entity **entities = NULL; // dynamic buffer
	isize new_name_count = 0;

	if (lhs_count == 0) {
		return;
	}
	buf_reserve(entities, lhs_count);

	for (i = 0; i < lhs_count; i++) {
		AstExpr *name = lhs[i];
		Entity *entity = NULL;

		if (name->kind != AstExpr_Ident) {
			error(name->pos, "var declarations must use identifiers for a name");
		} else {
			Token token = name->ident.token;
			String str = token.string;
			Entity *found = NULL;
			if (!is_blank_name(str)) {
				found = current_scope_lookup_entity(c->context.scope, str);
				new_name_count += 1;
			}
			if (found == NULL) {
				entity = alloc_entity(Entity_Const, name, NULL);
			} else {
				TokenPos pos = found->ident->pos;
				error(pos,
				      "redeclaration of '%.*s' in this scope\n"
				      "\tat %.*s(%ld:%ld)",
				      LIT(str), LIT(pos.file), pos.line, pos.column);
				entity = found;
			}
		}
		if (entity == NULL) {
			entity = alloc_entity_dummy_variable(c->global_scope, name);
		}
		buf_push(entities, entity);
	}

	if (new_name_count == 0) {
		error(lhs[0]->pos, "no new declarations on the lhs");
	}

	init_type = NULL;
	if (type_expr != NULL) {
		init_type = check_type(c, type_expr);
		if (!is_type_constant_type(init_type)) {
			char *str = type_to_string(init_type);
			error(type_expr->pos, "invalid constant type '%s'", str);
			mem_free(str);
			init_type = t_invalid;
			return;
		}
	}

	for (i = 0; i < buf_len(entities); i++) {
		Entity *e = entities[i];
		ASSERT(e != NULL);
		if (e->flags & EntityFlag_Visited) {
			e->type = t_invalid;
			continue;
		}
		e->flags |= EntityFlag_Visited;
		e->state = EntityState_Processing;
		if (e->type == NULL) {
			e->type = init_type;
			e->state = EntityState_Resolved;
		}
	}

	check_arity_match(c, lhs, lhs_count, type_expr, rhs, rhs_count);
	check_init_constants(c, entities, buf_len(entities), rhs, rhs_count);

	for (i = 0; i < buf_len(entities); i++) {
		Entity *e = entities[i];
		add_entity(c, e);
	}
}



void check_type_decl(Checker *c, Entity *e, AstType *type_expr) {
	Type *bt = NULL;
	Type *named = NULL;

	ASSERT(e->type == NULL);

	named = alloc_type(Type_Named);
	named->named.entity = e;
	e->type = named;

	check_type_path_push(c, e);
	bt = check_type_expr(c, type_expr, named);
	check_type_path_pop(c);

	named->named.base = base_type(bt);
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
	case AstStmt_Expr: {
		Operand o = {0};
		check_expr(c, &o, stmt->expr);
		break;
	}
	case AstStmt_Block:
		check_block(c, stmt, flags);
		break;

	case AstStmt_Assign: {
		if (stmt->assign.op.kind == Token_Define) {
			check_var_decl(c, &stmt->assign.lhs, 1, NULL, &stmt->assign.rhs, 1);
		} else {
			Operand lhs = {0};
			Operand rhs = {0};
			check_expr(c, &rhs, stmt->assign.rhs);
			check_expr(c, &lhs, stmt->assign.lhs);
			check_assignment(c, &rhs, lhs.type, "assignment");
		}
		break;
	}

	case AstStmt_Label: {

		break;
	}

	case AstStmt_If: {
		Operand cond = {0};
		check_expr(c, &cond, stmt->if_stmt.cond);
		if (!is_operand_value(&cond)) {
			error(cond.expr->pos, "expected a value in if condition, got %.*s", LIT(addressing_mode_strings[cond.mode]));
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
			Operand x = {0};
			check_expr(c, &x, cond);
			if (!is_operand_value(&x)) {
				error(x.expr->pos, "expected a value in for condition, got %.*s", LIT(addressing_mode_strings[x.mode]));
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
			Operand x = {0};
			check_expr(c, &x, cond);
			if (!is_operand_value(&x)) {
				error(x.expr->pos, "expected a value in while condition, got %.*s", LIT(addressing_mode_strings[x.mode]));
			}
		}
		check_stmt(c, stmt->while_stmt.block, new_flags);
		break;
	}
	case AstStmt_Return: {
		AstExpr *expr = stmt->return_stmt.expr;
		if (expr) {
			Operand x = {0};
			check_expr(c, &x, expr);
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

	case AstDecl_Var: {
		AstExpr **lhs = decl->var_decl.lhs;
		AstExpr **rhs = decl->var_decl.rhs;
		AstType *type_expr = decl->var_decl.type;
		isize lhs_count = decl->var_decl.lhs_count;
		isize rhs_count = decl->var_decl.rhs_count;
		check_var_decl(c, lhs, lhs_count, type_expr, rhs, rhs_count);
		return;
	}
	case AstDecl_Const: {
		AstExpr **lhs = decl->const_decl.lhs;
		AstExpr **rhs = decl->const_decl.rhs;
		AstType *type_expr = decl->const_decl.type;
		isize lhs_count = decl->const_decl.lhs_count;
		isize rhs_count = decl->const_decl.rhs_count;
		check_const_decl(c, lhs, lhs_count, type_expr, rhs, rhs_count);
		return;
	}

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
		check_type_decl(c, e, decl->type_decl.type);
		return;
	}
	case AstDecl_Proc:
		error(decl->pos, "proc declarations are only allowed a file scope");
		return;
	case AstDecl_Import:
		error(decl->pos, "import declarations are only allowed a file scope");
		return;
	}
}

Entity *check_ident(Checker *c, Operand *o, AstExpr *expr) {
	String name;
	Entity *e;
	Type *type;
	o->mode = Addressing_Invalid;
	o->expr = expr;

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

	e->flags |= EntityFlag_Used;
	type = e->type;
	ASSERT_MSG(type != NULL, "%.*s", LIT(e->name));

	switch (e->kind) {
	case Entity_Const:
		if (type == t_invalid) {
			o->type = t_invalid;
			return e;
		}
		o->value = e->value;
		if (o->value.kind == ConstValue_Invalid) {
			return e;
		}
		o->mode = Addressing_Const;
		break;

	case Entity_Var:
		if (type == t_invalid) {
			o->type = t_invalid;
			return e;
		}
		o->mode = Addressing_Var;
		break;

	case Entity_Proc:
		o->mode = Addressing_Value;
		break;

	case Entity_Type:
		o->mode = Addressing_Type;
		if (check_cycle(c, e, true)) {
			type = t_invalid;
		}
		break;

	case Entity_Nil:
		o->mode = Addressing_Value;
		break;

	default:
		PANIC("unknown EntityKind %d", e->kind);
		break;
	}

	o->type = type;
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
			char *t = type_to_string(o->type);
			error(op.pos, "operator %.*s is not allowed with non-numeric expressions, %s", LIT(op.string), t);
			mem_free(t);
			return false;
		}
		break;
	case Token_Xor:
		if (!is_type_integer(o->type)) {
			char *t = type_to_string(o->type);
			error(op.pos, "operator %.*s is not allowed with non-integer expressions, %s", LIT(op.string), t);
			mem_free(t);
			return false;
		}
		break;
	case Token_not:
		if (!is_type_boolean(o->type)) {
			char *t = type_to_string(o->type);
			error(op.pos, "operator %.*s is not allowed with non-boolean expressions, %s", LIT(op.string), t);
			mem_free(t);
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
			char *es = expr_to_string(o->expr);
			error(op.pos, "cannot take the pointer address of a non variable, %s", es);
			mem_free(es);
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
			char *ts = type_to_string(t);
			char *es = expr_to_string(o->expr);
			error(op.pos, "invalid type, %s, for constant unary expression, %s", ts, es);
			mem_free(es);
			mem_free(ts);
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
	char *es = expr_to_string(x->expr);
	char *ts = type_to_string(type);
	error(x->expr->pos, "cannot convert '%s' to '%s'", es, ts);
	mem_free(ts);
	mem_free(es);
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
		char *es = expr_to_string(x->expr);
		char *ts = type_to_string(type);
		error(x->expr->pos, "cannot convert '%s' to '%s'", es, ts);
		mem_free(ts);
		mem_free(es);

		x->mode = Addressing_Invalid;
	}
}


bool convert_to_typed(Checker *c, Operand *x, Type *target_type) {
	ASSERT(target_type != NULL);
	if (x->mode == Addressing_Invalid ||
	    x->mode == Addressing_Type ||
	    is_type_typed(x->type) ||
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
			char *xt = type_to_string(x.type);
			char *yt = type_to_string(y.type);
			error(op.pos, "mismatched types in binary expression, %s vs %s", xt, yt);
			mem_free(yt);
			mem_free(xt);
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
			char *es = expr_to_string(o->expr);
			char *ts = type_to_string(type);
			error(o->expr->pos, "cannot cast %s to %s", es, ts);
			mem_free(ts);
			mem_free(es);
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


bool check_is_assignable_to(Checker *c, Operand *x, Type *type) {
	Type *src = x->type;
	Type *dst = type;
	if (x->mode == Addressing_Invalid || type == t_invalid) {
		return false;
	}
	if (x->mode == Addressing_Type) {
		return false;
	}

	if (are_types_equal(src, dst)) {
		return true;
	}
	src = base_type(src);
	dst = base_type(dst);

	if (src == t_untyped_nil) {
		return type_has_nil(dst);
	}

	if (is_type_untyped(src)) {
		if (is_type_constant_type(dst)) {
			if (x->mode == Addressing_Const) {
				if (check_representable_as_const(c, x->value, dst, NULL)) {
					if (is_type_typed(dst) && is_type_constant_type(src)) {
						switch (src->kind) {
						case Type_Rune:
						case Type_Int:
							return (dst->kind == Type_Int || dst->kind == Type_Rune);
						case Type_Float:
							return (dst->kind == Type_Float);
						}
					}
					return true;
				}
				return false;
			}
			if (is_type_untyped(src) && src->kind == Type_Rune) {
				return (dst->kind == Type_Int || dst->kind == Type_Rune);
			}
			if (is_type_untyped(src) && src->kind == Type_Bool) {
				return dst->kind == Type_Bool;
			}
		}
	}

	if (are_types_equal(type, t_rawptr) && src->kind == Type_Ptr) {
		return true;
	}

	if (dst->kind == Type_Proc) {
		if (are_types_equal(src, dst)) {
			return true;
		}
	}

	return false;
}

bool check_assignment(Checker *c, Operand *x, Type *type, char const *context_name) {
	if (x->mode == Addressing_Invalid) {
		return false;
	}

	if (is_type_untyped(x->type)) {
		Type *target_type = type;
		if (type == NULL) {
			// if (x->type == t_untyped_nil) {
			// 	error(x->expr->pos, "use of untyped nil in %s", context_name);
			// 	x->mode = Addressing_Invalid;
			// 	return false;
			// }
			target_type = default_type(x->type);
		}

		if (!convert_to_typed(c, x, target_type)) {
			return false;
		}
	}

	if (type == NULL) {
		return false;
	}


	if (!check_is_assignable_to(c, x, type)) {
		char *expr_str    = expr_to_string(x->expr);
		char *op_type_str = type_to_string(x->type);
		char *type_str    = type_to_string(type);


		switch (x->mode) {
		case Addressing_Type:
			error(x->expr->pos, "cannot assign %s which is a type in %s",
			      op_type_str, context_name);
			break;
		default:
			error(x->expr->pos, "cannot assign value '%s' of type '%s' to '%s' in %s",
			      expr_str, op_type_str, type_str, context_name);
			break;
		}

		mem_free(type_str);
		mem_free(op_type_str);
		mem_free(expr_str);

		x->mode = Addressing_Invalid;
		return false;
	}

	return true;
}

void check_expr_base_internal(Checker *c, Operand *o, AstExpr *expr, Type *type_hint) {
	o->expr = expr;

	ASSERT(expr != NULL);
	switch (expr->kind) {
	case AstExpr_Literal:
		o->mode = Addressing_Const;
		o->value = const_value_from_literal(expr->literal);
		o->type = type_from_literal(expr->literal);
		return;
	case AstExpr_Ident: {
		Entity *e = check_ident(c, o, expr);
		if (e == NULL) {
			o->type = t_invalid;
			o->mode = Addressing_Invalid;
			return;
		}
		return;
	}
	case AstExpr_TypeExpr: {
		Type *t = check_type(c, expr->type_expr);
		if (t != t_invalid) {
			o->mode = Addressing_Type;
		}
		o->type = t;
		return;
	}
	case AstExpr_Paren:
		check_expr(c, o, expr->paren.expr);
		return;
	case AstExpr_Call: {
		isize cargs = expr->call.arg_count;
		Operand p = {0};
		check_expr_or_type(c, &p, expr->call.expr, NULL);
		if (p.mode == Addressing_Type) {
			switch (cargs) {
			case 0:  error(p.expr->pos, "missing argument in type convertion");   break;
			default: error(p.expr->pos, "too many arguments in type convertion"); break;
			case 1: {
				AstExpr *arg = expr->call.args[0];
				check_expr(c, o, arg);
				if (o->mode != Addressing_Invalid) {
					check_cast(c, o, p.type);
				}
				return;
			}
			}
			ASSERT(cargs != 1);
			o->mode = Addressing_Invalid;
			return;
		}
		if (p.type == NULL || p.type == t_invalid || p.type->kind != Type_Proc) {
			error(p.expr->pos, "call expected procedure");
			return;
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
				Operand x = {0};
				check_expr(c, &x, arg);
				if (!check_assignment(c, &x, field->type, "call")) {
					String name = field->name;
					char *st = type_to_string(field->type);
					if (name.len == 0 || is_blank_name(name)) {
						error(arg->pos, "cannot assign to procedure argument of type %s", st);
					} else {
						error(arg->pos, "cannot assign to procedure argument '%.*s' of type %s", LIT(field->name), st);
					}
					mem_free(st);
				}
			}
			if (p.type->proc.ret != NULL) {
				o->mode = Addressing_Value;
				o->type = p.type->proc.ret;
			} else {
				o->mode = Addressing_NoValue;
			}
		}
		break;
	}
	case AstExpr_Index:
		break;
	case AstExpr_Selector:
		break;
	case AstExpr_Deref: {
		check_expr(c, o, expr->deref.expr);
		if (is_operand_value(o)) {
			error(o->expr->pos, "Cannot derefence a non-pointer value");
			return;
		}
		if (o->type == NULL || o->type == t_invalid || o->type->kind != Type_Ptr) {
			error(o->expr->pos, "Cannot derefence a non-pointer");
			return;
		}
		if (o->type->ptr.elem == NULL) {
			error(o->expr->pos, "Cannot derefence a rawptr");
			return;
		}
		o->mode = Addressing_Var;
		o->type = type_deref(o->type);
		return;
	}
	case AstExpr_Unary: {
		check_expr_base(c, o, expr->unary.expr, type_hint);
		if (o->mode == Addressing_Invalid) {
			o->expr = expr;
			return;
		}
		check_unary_expr(c, o, expr->unary.op);
		return;
	}
	case AstExpr_Binary: {
		Token op = expr->binary.op;
		Operand x = {0};
		Operand y = {0};
		check_expr(c, &x, expr->binary.left);
		check_expr(c, &y, expr->binary.right);
		*o = check_binary_expr(c, x, y, op);
		return;
	}
	case AstExpr_Ternary: {
		Operand x = {0};
		Operand y = {0};
		check_expr(c, o, expr->ternary.cond);
		if (o->mode == Addressing_Invalid) {
			return;
		}
		if (o->type->kind != Type_Bool) {
			char *str = type_to_string(o->type);
			error(o->expr->pos, "boolean expected for ternary condition, got %s", str);
			mem_free(str);
		}
		check_expr(c, &x, expr->ternary.left);
		check_expr(c, &y, expr->ternary.right);
		if (!convert_to_typed(c, &x, y.type)) {
			o->mode = Addressing_Invalid;
			o->expr = x.expr;
			return;
		}
		if (!convert_to_typed(c, &y, x.type)) {
			o->mode = Addressing_Invalid;
			o->expr = y.expr;
			return;
		}

		if (!are_types_equal(x.type, y.type)) {
			if (x.type != t_invalid &&
			    y.type != t_invalid) {
				char *xt = type_to_string(x.type);
				char *yt = type_to_string(y.type);
				error(expr->pos, "mismatched types in ternary expression, %s vs %s", xt, yt);
				mem_free(yt);
				mem_free(xt);
			}
			o->mode = Addressing_Invalid;
			o->expr = x.expr;
			return;
		}

		*o = x;
		return;
	}
	}

	return;
}

void check_expr_base(Checker *c, Operand *o, AstExpr *expr, Type *type_hint) {
	Type *type = NULL;
	ConstValue value = {0};
	check_expr_base_internal(c, o, expr, type_hint);
	switch (o->mode) {
	case Addressing_Invalid:
		type = t_invalid;
		break;
	case Addressing_NoValue:
		type = NULL;
		break;
	case Addressing_Const:
		type = o->type;
		value = o->value;
		break;
	default:
		type = o->type;
		break;
	}

	add_expr_info(c, expr, o->mode, type, value);
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


void check_expr_or_type(Checker *c, Operand *o, AstExpr *expr, Type *type_hint) {
	check_expr_base(c, o, expr, type_hint);
	error_operand_no_value(o);
}


void check_expr(Checker *c, Operand *o, AstExpr *expr) {
	check_expr_base(c, o, expr, NULL);
	error_operand_no_value(o);
	error_operand_no_expr(o);
}

Type *check_type(Checker *c, AstType *type_expr) {
	return check_type_expr(c, type_expr, NULL);
}


Type *check_type_expr_internal(Checker *c, AstType *type_expr, Type *named_type) {
	ASSERT(type_expr != NULL);
	switch (type_expr->kind) {
	case AstType_Ident: {
		Entity *e;
		Operand o = {0};
		o.expr = type_expr->ident;
		e = check_ident(c, &o, type_expr->ident);
		if (e == NULL) {
			return NULL;
		}
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
			Operand x = {0};
			check_expr(c, &x, size);
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
		Operand x = {0};
		Operand y = {0};
		check_expr(c, &x, type_expr->range.from);
		check_expr(c, &y, type_expr->range.to);
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

Type *check_type_expr(Checker *c, AstType *type_expr, Type *named_type) {
	Type *type = check_type_expr_internal(c, type_expr, named_type);
	if (type == NULL) {
		char *str = type_expr_to_string(type_expr);
		error(type_expr->pos, "%s is not a type", str);
		mem_free(str);
		type = t_invalid;
	}

	if (type->kind == Type_Named && type->named.base == NULL) {
		type->named.base = t_invalid;
	}

	if (is_type_typed(type)) {
		// add_expr_info(c, type_expr, Addressing_Type, type, empty_const_value);
	} else {
		char *name = type_to_string(type);
		error(type_expr->pos, "invalid type definition of %s", name);
		mem_free(name);
		type = t_invalid;
	}
	set_base_type(named_type, type);
	return type;
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


char *expr_to_string_internal(char *str, AstExpr *expr) {
	isize i;
	if (expr == NULL) {
		return buf_printf(str, "<invalid expr>");
	}
	switch (expr->kind) {
	case AstExpr_Literal:
		return buf_printf(str, "%.*s", LIT(expr->literal.string));
	case AstExpr_Ident:
		return buf_printf(str, "%.*s", LIT(expr->ident.token.string));
	case AstExpr_TypeExpr:
		return str;
	case AstExpr_Paren:
		buf_printf(str, "(");
		expr_to_string_internal(str, expr->paren.expr);
		buf_printf(str, ")");
		return str;
	case AstExpr_Call:
		expr_to_string_internal(str, expr->call.expr);
		buf_printf(str, "(");
		for (i = 0; i < expr->call.arg_count; i++) {
			AstExpr *arg = expr->call.args[i];
			if (i > 0) buf_printf(str, ", ");
			expr_to_string_internal(str, arg);
		}
		buf_printf(str, ")");
		return str;
	case AstExpr_Index:
		expr_to_string_internal(str, expr->index.expr);
		buf_printf(str, "[");
		expr_to_string_internal(str, expr->index.index);
		buf_printf(str, "]");
		return str;
	case AstExpr_Selector:
		expr_to_string_internal(str, expr->selector.expr);
		buf_printf(str, ".");
		expr_to_string_internal(str, expr->selector.ident);
		return str;
	case AstExpr_Deref:
		expr_to_string_internal(str, expr->deref.expr);
		buf_printf(str, "^");
		return str;
	case AstExpr_Unary:
		buf_printf(str, "%.*s", LIT(expr->unary.op.string));
		expr_to_string_internal(str, expr->unary.expr);
		return str;
	case AstExpr_Binary:
		expr_to_string_internal(str, expr->binary.left);
		buf_printf(str, " %.*s ", LIT(expr->binary.op.string));
		expr_to_string_internal(str, expr->binary.right);
		return str;
	case AstExpr_Ternary:
		expr_to_string_internal(str, expr->ternary.cond);
		buf_printf(str, " ? ");
		expr_to_string_internal(str, expr->ternary.left);
		buf_printf(str, " : ");
		expr_to_string_internal(str, expr->ternary.right);
		return str;
	}
	return str;
}

char *type_expr_to_string_internal(char *str, AstType *type) {
	isize i;
	if (type == NULL) {
		return buf_printf(str, "<invalid type expr>");
	}
	switch (type->kind) {
	case AstType_Ident:
		return expr_to_string_internal(str, type->ident);
	case AstType_Array:
		buf_printf(str, "[");
		expr_to_string_internal(str, type->array.size);
		buf_printf(str, "]");
		type_expr_to_string_internal(str, type->array.elem);
		return str;
	case AstType_Set:
		buf_printf(str, "set[");
		for (i = 0; i < type->set.elem_count; i++) {
			if (i > 0) buf_printf(str, ", ");
			expr_to_string_internal(str, type->set.elems[i]);
		}
		buf_printf(str, "]");
		return str;
	case AstType_Range:
		buf_printf(str, "range ");
		expr_to_string_internal(str, type->range.from);
		buf_printf(str, "%.*s", LIT(type->range.token.string));
		expr_to_string_internal(str, type->range.to);
		return str;
	case AstType_Pointer:
		buf_printf(str, "^");
		type_expr_to_string_internal(str, type->pointer.elem);
		return str;
	case AstType_Signature:
		buf_printf(str, "proc(");
		for (i = 0; i < type->signature.param_count; i++) {
			AstField *p = &type->signature.params[i];
			if (i > 0) buf_printf(str, ", ");
			expr_to_string_internal(str, p->name);
			buf_printf(str, ": ");
			type_expr_to_string_internal(str, p->type);
		}
		buf_printf(str, ")");
		if (type->signature.return_type != NULL) {
			buf_printf(str, ": ");
			type_expr_to_string_internal(str, type->signature.return_type);
		}
		return str;
	}
	return str;
}

char *expr_to_string(AstExpr *expr) {
	char *buf, *str;
	buf = expr_to_string_internal(NULL, expr);
	buf_push(buf, 0);
	str = MEM_DUP_ARRAY(buf, buf_len(buf));
	buf_free(buf);
	return str;
}


char *type_expr_to_string(AstType *expr) {
	char *buf, *str;
	buf = type_expr_to_string_internal(NULL, expr);
	buf_push(buf, 0);
	str = MEM_DUP_ARRAY(buf, buf_len(buf));
	buf_free(buf);
	return str;
}




