typedef struct AstFile  AstFile;
typedef struct AstExpr  AstExpr;
typedef struct AstType  AstType;
typedef struct AstStmt  AstStmt;
typedef struct AstDecl  AstDecl;
typedef struct AstField AstField;
typedef struct Entity   Entity;

typedef enum AstExprKind AstExprKind;
typedef enum AstTypeKind AstTypeKind;
typedef enum AstStmtKind AstStmtKind;
typedef enum AstDeclKind AstDeclKind;

enum AstExprKind {
	AstExpr_Invalid,

	AstExpr_Literal,
	AstExpr_Ident,
	AstExpr_TypeExpr,
	AstExpr_Paren,
	AstExpr_Call,
	AstExpr_Index,
	AstExpr_Selector,
	AstExpr_Deref,
	AstExpr_Unary,
	AstExpr_Binary,
	AstExpr_Ternary,

	AstExpr_COUNT
};

struct AstExpr {
	AstExprKind kind;
	TokenPos pos, end;
	union {
		Token literal;
		struct {
			Token token;
			Entity *entity;
		} ident;
		AstType *type_expr;
		struct {
			AstExpr *expr;
		} paren;
		struct {
			AstExpr *expr;
			AstExpr **args;
			isize     arg_count;
		} call;
		struct {
			AstExpr *expr;
			AstExpr *index;
		} index;
		struct {
			AstExpr *expr;
			AstExpr *ident;
		} selector;
		struct {
			AstExpr *expr;
			Token    token;
		} deref;
		struct {
			Token op;
			AstExpr *expr;
		} unary;
		struct {
			Token op;
			AstExpr *left;
			AstExpr *right;
		} binary;
		struct {
			AstExpr *cond;
			AstExpr *left;
			AstExpr *right;
		} ternary;
	};
};

enum AstTypeKind {
	AstType_Invalid,

	AstType_Ident,
	AstType_Array,
	AstType_Set,
	AstType_Range,
	AstType_Pointer,
	AstType_Signature,

	AstType_COUNT
};

struct AstField {
	AstExpr *name;
	AstType *type;
};

struct AstType {
	AstTypeKind kind;
	TokenPos    pos;
	TokenPos    end;
	union {
		AstExpr *ident;
		struct {
			Token token;
			AstExpr *size;
			AstType *elem;
		} array;
		struct {
			Token     token;
			AstExpr **elems;
			isize     elem_count;
		} set;
		struct {
			Token token;
			AstExpr *from;
			AstExpr *to;
		} range;
		struct {
			Token token;
			AstType *elem;
		} pointer;
		struct {
			Token token;
			AstField *params;
			isize     param_count;
			AstType * return_type;
		} signature;
	};
};

enum AstStmtKind {
	AstStmt_Invalid,

	AstStmt_Empty,
	AstStmt_Decl,
	AstStmt_Expr,
	AstStmt_Block,
	AstStmt_Assign,
	AstStmt_Label,

	AstStmt_If,
	AstStmt_For,
	AstStmt_While,
	AstStmt_Return,
	AstStmt_Branch,
	AstStmt_Goto,

	AstStmt_COUNT
};

struct AstStmt {
	AstStmtKind kind;
	TokenPos pos, end;
	union {
		AstDecl *decl;
		AstExpr *expr;
		struct {
			AstStmt **stmts;
			isize     stmt_count;
		} block;
		struct {
			// TODO(bill): Should this allow multiple values?
			Token op;
			AstExpr *lhs;
			AstExpr *rhs;
		} assign;
		struct {
			Token    token;
			AstExpr *name;
		} label;

		struct {
			Token token;
			AstExpr *cond;
			AstStmt *then_block;
			AstStmt *else_stmt;
		} if_stmt;
		struct {
			Token token;
			AstStmt *init;
			AstExpr *cond;
			AstStmt *post;
			AstStmt *block;
		} for_stmt;
		struct {
			Token token;
			AstExpr *cond;
			AstStmt *block;
		} while_stmt;
		struct {
			Token token;
			AstExpr *expr;
		} return_stmt;
		struct {
			Token token;
		} branch_stmt;
		struct {
			Token token;
			AstExpr *label;
		} goto_stmt;
	};
};

enum AstDeclKind {
	AstDecl_Invalid,

	AstDecl_Var,
	AstDecl_Const,
	AstDecl_Type,
	AstDecl_Proc,
	AstDecl_Import,

	AstDecl_COUNT
};

struct AstDecl {
	AstDeclKind kind;
	TokenPos pos, end;
	union {
		struct {
			Token token;
			AstExpr **lhs;
			isize lhs_count;
			AstType *type;
			AstExpr **rhs;
			isize rhs_count;
		} var_decl;
		struct {
			Token token;
			AstExpr **lhs;
			isize lhs_count;
			AstType *type;
			AstExpr **rhs;
			isize rhs_count;
		} const_decl;
		struct {
			Token token;
			AstExpr *name;
			AstType *type;
		} type_decl;
		struct {
			Token token;
			AstExpr *name;
			AstType *signature;
			AstStmt *body;
		} proc_decl;
		struct {
			Token token;
			AstExpr *name;
			AstExpr *path;
		} import_decl;
	};
};




static Arena ast_arena = {0};

void *ast_alloc(isize size) {
	if (size <= 0) {
		return NULL;
	} else {
		void *ptr = arena_alloc(&ast_arena, size);
		mem_zero(ptr, size);
		return ptr;
	}
}

void *ast_dup(void const *src, isize size) {
	if (size == 0) {
		return NULL;
	} else {
		void *dst = ast_alloc(size);
		memmove(dst, src, size);
		return dst;
	}
}

#define AST_DUP_ARRAY(src, length) ast_dup((src), sizeof(*(src))*(length))


AstExpr *alloc_ast_expr(AstExprKind kind, TokenPos pos, TokenPos end) {
	AstExpr *e = MEM_NEW(AstExpr);
	e->kind  = kind;
	e->pos = pos;
	e->end   = end;
	return e;
}
AstType *alloc_ast_type(AstTypeKind kind, TokenPos pos, TokenPos end) {
	AstType *t = MEM_NEW(AstType);
	t->kind  = kind;
	t->pos = pos;
	t->end   = end;
	return t;
}
AstStmt *alloc_ast_stmt(AstStmtKind kind, TokenPos pos, TokenPos end) {
	AstStmt *s = MEM_NEW(AstStmt);
	s->kind  = kind;
	s->pos = pos;
	s->end   = end;
	return s;
}
AstDecl *alloc_ast_decl(AstDeclKind kind, TokenPos pos, TokenPos end) {
	AstDecl *d = MEM_NEW(AstDecl);
	d->kind  = kind;
	d->pos = pos;
	d->end   = end;
	return d;
}


AstExpr *ast_expr_literal(Token literal) {
	AstExpr *e = alloc_ast_expr(AstExpr_Literal, literal.pos, token_end_pos(literal));
	e->literal = literal;
	return e;
}
AstExpr *ast_expr_ident(Token ident) {
	AstExpr *e = alloc_ast_expr(AstExpr_Ident, ident.pos, token_end_pos(ident));
	e->ident.token = ident;
	return e;
}
AstExpr *ast_expr_type_expr(AstType *type_expr) {
	AstExpr *e = alloc_ast_expr(AstExpr_TypeExpr, type_expr->pos, type_expr->end);
	e->type_expr = type_expr;
	return e;
}
AstExpr *ast_expr_paren(TokenPos pos, AstExpr *expr, TokenPos end) {
	AstExpr *e = alloc_ast_expr(AstExpr_Paren, pos, end);
	e->paren.expr = expr;
	return e;
}
AstExpr *ast_expr_call(AstExpr *expr, AstExpr **args, isize arg_count, TokenPos end) {
	AstExpr *e = alloc_ast_expr(AstExpr_Call, expr->pos, end);
	e->call.expr = expr;
	e->call.args = AST_DUP_ARRAY(args, arg_count);
	e->call.arg_count = arg_count;
	return e;
}
AstExpr *ast_expr_index(AstExpr *expr, AstExpr *index, TokenPos end) {
	AstExpr *e = alloc_ast_expr(AstExpr_Index, expr->pos, end);
	e->index.expr = expr;
	e->index.index = index;
	return e;
}
AstExpr *ast_expr_selector(AstExpr *expr, AstExpr *ident) {
	AstExpr *e = alloc_ast_expr(AstExpr_Selector, expr->pos, ident->end);
	e->selector.expr = expr;
	e->selector.ident = ident;
	return e;
}
AstExpr *ast_expr_deref(AstExpr *expr, Token token) {
	AstExpr *e = alloc_ast_expr(AstExpr_Deref, expr->pos, token_end_pos(token));
	e->deref.expr = expr;
	e->deref.token = token;
	return e;
}
AstExpr *ast_expr_unary(Token op, AstExpr *expr) {
	AstExpr *e = alloc_ast_expr(AstExpr_Unary, op.pos, expr->end);
	e->unary.op = op;
	e->unary.expr = expr;
	return e;
}
AstExpr *ast_expr_binary(Token op, AstExpr *left, AstExpr *right) {
	AstExpr *e = alloc_ast_expr(AstExpr_Binary, left->pos, right->end);
	e->binary.op = op;
	e->binary.left = left;
	e->binary.right = right;
	return e;
}
AstExpr *ast_expr_ternary(AstExpr *cond, AstExpr *left, AstExpr *right) {
	AstExpr *e = alloc_ast_expr(AstExpr_Ternary, cond->pos, right->end);
	e->ternary.cond  = cond;
	e->ternary.left  = left;
	e->ternary.right = right;
	return e;
}


AstType *ast_type_ident(AstExpr *ident) {
	AstType *t = alloc_ast_type(AstType_Ident, ident->pos, ident->end);
	t->ident = ident;
	return t;
}
AstType *ast_type_array(Token token, AstExpr *size, AstType *elem) {
	AstType *t = alloc_ast_type(AstType_Array, token.pos, elem->end);
	t->array.token = token;
	t->array.size  = size;
	t->array.elem  = elem;
	return t;
}
AstType *ast_type_set(Token token, AstExpr **elems, isize elem_count, TokenPos end) {
	AstType *t = alloc_ast_type(AstType_Set, token.pos, end);
	t->set.token = token;
	t->set.elems = AST_DUP_ARRAY(elems, elem_count);
	t->set.elem_count = elem_count;
	return t;
}
AstType *ast_type_range(Token token, AstExpr *from, AstExpr *to) {
	AstType *t = alloc_ast_type(AstType_Range, token.pos, to->end);
	t->range.token = token;
	t->range.from  = from;
	t->range.to    = to;
	return t;
}
AstType *ast_type_pointer(Token token, AstType *elem) {
	AstType *t = alloc_ast_type(AstType_Pointer, token.pos, elem->end);
	t->pointer.token = token;
	t->pointer.elem  = elem;
	return t;
}
AstType *ast_type_signature(Token token, AstField *params, isize param_count, AstType *return_type, TokenPos end) {
	AstType *t = alloc_ast_type(AstType_Signature, token.pos, end);
	t->signature.token = token;
	t->signature.params = AST_DUP_ARRAY(params, param_count);
	t->signature.param_count = param_count;
	t->signature.return_type = return_type;
	return t;
}



AstStmt *ast_stmt_empty(Token token) {
	AstStmt *s = alloc_ast_stmt(AstStmt_Empty, token.pos, token_end_pos(token));
	return s;
}

AstStmt *ast_stmt_decl(AstDecl *decl) {
	AstStmt *s = alloc_ast_stmt(AstStmt_Decl, decl->pos, decl->end);
	s->decl = decl;
	return s;
}
AstStmt *ast_stmt_expr(AstExpr *expr) {
	AstStmt *s = alloc_ast_stmt(AstStmt_Expr, expr->pos, expr->end);
	s->expr = expr;
	return s;
}
AstStmt *ast_stmt_block(AstStmt **stmts, isize stmt_count, TokenPos pos, TokenPos end) {
	AstStmt *s = alloc_ast_stmt(AstStmt_Block, pos, end);
	s->block.stmts = AST_DUP_ARRAY(stmts, stmt_count);
	s->block.stmt_count = stmt_count;
	return s;
}
AstStmt *ast_stmt_assign(Token op, AstExpr *lhs, AstExpr *rhs) {
	AstStmt *s = alloc_ast_stmt(AstStmt_Assign, lhs->pos, rhs->end);
	s->assign.op = op;
	s->assign.lhs = lhs;
	s->assign.rhs = rhs;
	return s;
}
AstStmt *ast_stmt_label(Token token, AstExpr *name) {
	AstStmt *s = alloc_ast_stmt(AstStmt_Label, token.pos, name->end);
	s->label.token = token;
	s->label.name = name;
	return s;
}



AstStmt *ast_stmt_if(Token token, AstExpr *cond, AstStmt *then_block, AstStmt *else_stmt) {
	AstStmt *s;
	TokenPos end = then_block->end;
	if (else_stmt != NULL) {
		end = else_stmt->end;
	}

	s = alloc_ast_stmt(AstStmt_If, token.pos, end);
	s->if_stmt.token = token;
	s->if_stmt.cond = cond;
	s->if_stmt.then_block = then_block;
	s->if_stmt.else_stmt = else_stmt;
	return s;
}
AstStmt *ast_stmt_for(Token token, AstStmt *init, AstExpr *cond, AstStmt *post, AstStmt *block) {
	AstStmt *s = alloc_ast_stmt(AstStmt_For, token.pos, block->end);
	s->for_stmt.token = token;
	s->for_stmt.init = init;
	s->for_stmt.cond = cond;
	s->for_stmt.post = post;
	s->for_stmt.block = block;
	return s;
}
AstStmt *ast_stmt_while(Token token, AstExpr *cond, AstStmt *block) {
	AstStmt *s = alloc_ast_stmt(AstStmt_While, token.pos, block->end);
	s->while_stmt.token = token;
	s->while_stmt.cond = cond;
	s->while_stmt.block = block;
	return s;
}
AstStmt *ast_stmt_return(Token token, AstExpr *expr) {
	AstStmt *s;
	TokenPos end = token_end_pos(token);
	if (expr != NULL) {
		end = expr->end;
	}
	s = alloc_ast_stmt(AstStmt_Return, token.pos, end);
	s->return_stmt.token = token;
	s->return_stmt.expr  = expr;
	return s;
}
AstStmt *ast_stmt_branch(Token token) {
	AstStmt *s;
	TokenPos end = token.pos;
	end.column += token.string.len;
	s = alloc_ast_stmt(AstStmt_Branch, token.pos, end);
	s->branch_stmt.token = token;
	return s;
}
AstStmt *ast_stmt_goto(Token token, AstExpr *label) {
	AstStmt *s = alloc_ast_stmt(AstStmt_Goto, token.pos, label->end);
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

	d = alloc_ast_decl(AstDecl_Var, token.pos, end);
	d->var_decl.token = token;
	d->var_decl.lhs = AST_DUP_ARRAY(lhs, lhs_count);
	d->var_decl.lhs_count = lhs_count;
	d->var_decl.type = type;
	d->var_decl.rhs = AST_DUP_ARRAY(rhs, rhs_count);
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

	d = alloc_ast_decl(AstDecl_Const, token.pos, end);
	d->const_decl.token = token;
	d->const_decl.lhs = AST_DUP_ARRAY(lhs, lhs_count);
	d->const_decl.lhs_count = lhs_count;
	d->const_decl.type = type;
	d->const_decl.rhs = AST_DUP_ARRAY(rhs, rhs_count);
	d->const_decl.rhs_count = rhs_count;
	return d;
}
AstDecl *ast_decl_type(Token token, AstExpr *name, AstType *type) {
	AstDecl *d = alloc_ast_decl(AstDecl_Type, token.pos, type->end);
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

	d = alloc_ast_decl(AstDecl_Proc, token.pos, end);
	d->proc_decl.token = token;
	d->proc_decl.name = name;
	d->proc_decl.signature = signature;
	d->proc_decl.body = body;
	return d;
}
AstDecl *ast_decl_import(Token token, AstExpr *name, AstExpr *path) {
	AstDecl *d = alloc_ast_decl(AstDecl_Import, token.pos, path->end);
	d->import_decl.token = token;
	d->import_decl.name  = name;
	d->import_decl.path  = path;
	return d;
}
