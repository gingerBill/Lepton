#include "ast.h"

static Arena ast_arena = {0};

void *ast_alloc(isize size) {
	void *ptr;
	assert(size > 0);
	ptr = arena_alloc(&ast_arena, size);
	mem_zero(ptr, size);
	return ptr;
}

AstExpr *ast_expr_new(AstExprKind kind, TokenPos begin, TokenPos end) {
	AstExpr *e = ast_alloc(sizeof(AstExpr));
	e->kind  = kind;
	e->begin = begin;
	e->end   = end;
	return e;
}
AstType *ast_type_new(AstTypeKind kind, TokenPos begin, TokenPos end) {
	AstType *t = ast_alloc(sizeof(AstType));
	t->kind  = kind;
	t->begin = begin;
	t->end   = end;
	return t;
}
AstStmt *ast_stmt_new(AstStmtKind kind, TokenPos begin, TokenPos end) {
	AstStmt *s = ast_alloc(sizeof(AstStmt));
	s->kind  = kind;
	s->begin = begin;
	s->end   = end;
	return s;
}
AstDecl *ast_decl_new(AstDeclKind kind, TokenPos begin, TokenPos end) {
	AstDecl *d = ast_alloc(sizeof(AstDecl));
	d->kind  = kind;
	d->begin = begin;
	d->end   = end;
	return d;
}


AstExpr *ast_expr_literal(Token literal, TokenPos end) {
	AstExpr *e = ast_expr_new(AstExpr_Literal, literal.pos, end);
	e->literal = literal;
	return e;
}
AstExpr *ast_expr_ident(Token ident) {
	AstExpr *e;
	TokenPos end = ident.pos;
	end.column += ident.string.len;
	e = ast_expr_new(AstExpr_Ident, ident.pos, end);
	e->ident = ident;
	return e;
}
AstExpr *ast_expr_paren(TokenPos begin, AstExpr *expr, TokenPos end) {
	AstExpr *e = ast_expr_new(AstExpr_Paren, begin, end);
	e->paren.expr = expr;
	return e;
}
AstExpr *ast_expr_call(AstExpr *expr, AstExpr **args, isize arg_count, TokenPos end) {
	AstExpr *e = ast_expr_new(AstExpr_Call, expr->begin, end);
	e->call.expr = expr;
	e->call.args = args;
	e->call.arg_count = arg_count;
	return e;
}
AstExpr *ast_expr_index(AstExpr *expr, AstExpr *index, TokenPos end) {
	AstExpr *e = ast_expr_new(AstExpr_Index, expr->begin, end);
	e->index.expr = expr;
	e->index.index = index;
	return e;
}
AstExpr *ast_expr_selector(AstExpr *expr, AstExpr *ident) {
	AstExpr *e = ast_expr_new(AstExpr_Selector, expr->begin, ident->end);
	e->selector.expr = expr;
	e->selector.ident = ident;
	return e;
}
AstExpr *ast_expr_unary(Token op, AstExpr *expr) {
	AstExpr *e = ast_expr_new(AstExpr_Unary, op.pos, expr->end);
	e->unary.op = op;
	e->unary.expr = expr;
	return e;
}
AstExpr *ast_expr_binary(Token op, AstExpr *left, AstExpr *right) {
	AstExpr *e = ast_expr_new(AstExpr_Binary, left->begin, right->end);
	e->binary.op = op;
	e->binary.left = left;
	e->binary.right = right;
	return e;
}
AstExpr *ast_expr_ternary(AstExpr *cond, AstExpr *left, AstExpr *right) {
	AstExpr *e = ast_expr_new(AstExpr_Ternary, cond->begin, right->end);
	e->ternary.cond  = cond;
	e->ternary.left  = left;
	e->ternary.right = right;
	return e;
}


AstType *ast_type_ident(AstExpr *ident) {
	AstType *t = ast_type_new(AstType_Ident, ident->begin, ident->end);
	t->ident = ident;
	return t;
}
AstType *ast_type_array(Token token, AstExpr *size, AstType *elem) {
	AstType *t = ast_type_new(AstType_Array, token.pos, elem->end);
	t->array.token = token;
	t->array.size  = size;
	t->array.elem  = elem;
	return t;
}
AstType *ast_type_set(Token token, AstExpr **elems, isize elem_count, TokenPos end) {
	AstType *t = ast_type_new(AstType_Set, token.pos, end);
	t->set.token = token;
	t->set.elems = elems;
	t->set.elem_count = elem_count;
	return t;
}
AstType *ast_type_range(Token token, AstExpr *from, AstExpr *to) {
	AstType *t = ast_type_new(AstType_Range, token.pos, to->end);
	t->range.token = token;
	t->range.from  = from;
	t->range.to    = to;
	return t;
}
AstType *ast_type_pointer(Token token, AstType *elem) {
	AstType *t = ast_type_new(AstType_Pointer, token.pos, elem->end);
	t->pointer.token = token;
	t->pointer.elem  = elem;
	return t;
}
AstType *ast_type_signature(Token token, AstField *params, isize param_count, AstType *return_type, TokenPos end) {
	AstType *t = ast_type_new(AstType_Signature, token.pos, end);
	t->signature.token = token;
	t->signature.params = params;
	t->signature.param_count = param_count;
	t->signature.return_type = return_type;
	return t;
}



AstStmt *ast_stmt_empty(Token token) {
	AstStmt *s;
	TokenPos end = token.pos;
	end.column += token.string.len;
	s = ast_stmt_new(AstStmt_Empty, token.pos, end);
	return s;
}

AstStmt *ast_stmt_decl(AstDecl *decl) {
	AstStmt *s = ast_stmt_new(AstStmt_Decl, decl->begin, decl->end);
	s->decl = decl;
	return s;
}
AstStmt *ast_stmt_expr(AstExpr *expr) {
	AstStmt *s = ast_stmt_new(AstStmt_Expr, expr->begin, expr->end);
	s->expr = expr;
	return s;
}
AstStmt *ast_stmt_block(AstStmt **stmts, isize stmt_count, TokenPos begin, TokenPos end) {
	AstStmt *s = ast_stmt_new(AstStmt_Block, begin, end);
	s->block.stmts = stmts;
	s->block.stmt_count = stmt_count;
	return s;
}
AstStmt *ast_stmt_assign(Token op, AstExpr *lhs, AstExpr *rhs) {
	AstStmt *s = ast_stmt_new(AstStmt_Assign, lhs->begin, rhs->end);
	s->assign.op = op;
	s->assign.lhs = lhs;
	s->assign.rhs = rhs;
	return s;
}
AstStmt *ast_stmt_label(AstExpr *name, Token colon) {
	AstStmt *s;
	TokenPos end = colon.pos;
	end.column += colon.string.len;
	s = ast_stmt_new(AstStmt_Label, name->begin, end);
	s->label.name = name;
	return s;
}



AstStmt *ast_stmt_if(Token token, AstExpr *cond, AstStmt *then_block, AstStmt *else_stmt) {
	AstStmt *s;
	TokenPos end = then_block->end;
	if (else_stmt != NULL) {
		end = else_stmt->end;
	}

	s = ast_stmt_new(AstStmt_If, token.pos, end);
	s->if_stmt.token = token;
	s->if_stmt.cond = cond;
	s->if_stmt.then_block = then_block;
	s->if_stmt.else_stmt = else_stmt;
	return s;
}
AstStmt *ast_stmt_for(Token token, AstStmt *init, AstExpr *cond, AstStmt *post, AstStmt *block) {
	AstStmt *s = ast_stmt_new(AstStmt_For, token.pos, block->end);
	s->for_stmt.token = token;
	s->for_stmt.init = init;
	s->for_stmt.cond = cond;
	s->for_stmt.post = post;
	s->for_stmt.block = block;
	return s;
}
AstStmt *ast_stmt_while(Token token, AstExpr *cond, AstStmt *block) {
	AstStmt *s = ast_stmt_new(AstStmt_While, token.pos, block->end);
	s->while_stmt.token = token;
	s->while_stmt.cond = cond;
	s->while_stmt.block = block;
	return s;
}
AstStmt *ast_stmt_return(Token token, AstExpr *expr) {
	AstStmt *s;
	TokenPos end;
	if (expr != NULL) {
		end = expr->end;
	} else {
		end = token.pos;
		end.column += token.string.len;
	}

	s = ast_stmt_new(AstStmt_While, token.pos, end);
	s->return_stmt.token = token;
	s->return_stmt.expr  = expr;
	return s;
}
AstStmt *ast_stmt_branch(Token token) {
	AstStmt *s;
	TokenPos end = token.pos;
	end.column += token.string.len;
	s = ast_stmt_new(AstStmt_Branch, token.pos, end);
	s->branch_stmt.token = token;
	return s;
}
AstStmt *ast_stmt_goto(Token token, AstExpr *label) {
	AstStmt *s = ast_stmt_new(AstStmt_Goto, token.pos, label->end);
	s->goto_stmt.token = token;
	s->goto_stmt.label = label;
	return s;
}



AstDecl *ast_decl_var(Token token, AstExpr **lhs, isize lhs_count, AstType *type, AstExpr **rhs, isize rhs_count) {
	AstDecl *d;
	TokenPos end;

	assert(lhs_count > 0);
	end = lhs[lhs_count-1]->end;
	if (rhs_count > 0) {
		end = rhs[rhs_count-1]->end;
	}

	d = ast_decl_new(AstDecl_Var, token.pos, end);
	d->var_decl.token = token;
	d->var_decl.lhs = lhs;
	d->var_decl.lhs_count = lhs_count;
	d->var_decl.type = type;
	d->var_decl.rhs = rhs;
	d->var_decl.rhs_count = rhs_count;
	return d;
}
AstDecl *ast_decl_const(Token token, AstExpr **lhs, isize lhs_count, AstType *type, AstExpr **rhs, isize rhs_count) {
	AstDecl *d;
	TokenPos end;

	assert(lhs_count > 0);
	end = lhs[lhs_count-1]->end;
	if (rhs_count > 0) {
		end = rhs[rhs_count-1]->end;
	}

	d = ast_decl_new(AstDecl_Const, token.pos, end);
	d->const_decl.token = token;
	d->const_decl.lhs = lhs;
	d->const_decl.lhs_count = lhs_count;
	d->const_decl.type = type;
	d->const_decl.rhs = rhs;
	d->const_decl.rhs_count = rhs_count;
	return d;
}
AstDecl *ast_decl_type(Token token, AstExpr *name, AstType *type) {
	AstDecl *d = ast_decl_new(AstDecl_Type, token.pos, type->end);
	d->type_decl.token = token;
	d->type_decl.name = name;
	d->type_decl.type = type;
	return d;
}
AstDecl *ast_decl_proc(Token token, AstExpr *name, AstType *signature, AstStmt *body) {
	AstDecl *d;
	TokenPos end = signature->end;
	if (body != NULL) {
		end = body->end;
	}

	d = ast_decl_new(AstDecl_Proc, token.pos, end);
	d->proc_decl.token = token;
	d->proc_decl.name = name;
	d->proc_decl.signature = signature;
	d->proc_decl.body = body;
	return d;
}
AstDecl *ast_decl_import(Token token, AstExpr *name, AstExpr *path) {
	AstDecl *d = ast_decl_new(AstDecl_Import, token.pos, path->end);
	d->import_decl.token = token;
	d->import_decl.name  = name;
	d->import_decl.path  = path;
	return d;
}
