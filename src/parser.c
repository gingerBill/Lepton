typedef struct Parser {
	String fullpath;
	Tokenizer tokenizer;
	Token curr_token;
	Token prev_token;

	// >= 0: In Expression
	// <  0: In Control Clause
	// NOTE(bill): Used to prevent type literals in control clauses
	isize expr_level;
	bool  allow_type;
} Parser;

typedef enum ParserError {
	ParserError_None,

	ParserError_Empty,
	ParserError_Invalid,
	ParserError_NotExists,

	ParserError_COUNT
} ParserError;

typedef struct AstPackage {
	String    fullpath;
	AstDecl **decls;
	isize     decl_count;
} AstPackage;


Token next_token(Parser *p) {
	p->prev_token = p->curr_token;
	p->curr_token = scan_token(&p->tokenizer);
	return p->prev_token;
}

Token expect_token(Parser *p, TokenKind kind) {
	Token curr = p->curr_token;
	if (curr.kind != kind) {
		String c = token_strings[kind];
		String p = token_strings[curr.kind];
		error(curr.pos, "expected %.*s, got %.*s", LIT(c), LIT(p));
		if (curr.kind == Token_EOF) {
			exit(1);
		}
	}
	next_token(p);
	return curr;
}

Token expect_operator(Parser *p) {
	Token curr = p->curr_token;
	switch (curr.kind) {
	case Token_in:
	case Token_not:
	case Token_and:
	case Token_or:
		// ok
		break;
	default:
		if (!(Token__OperatorBegin < curr.kind && curr.kind < Token__OperatorEnd)) {
			error(curr.pos, "expected an operator, got '%.*s'", LIT(token_strings[curr.kind]));
		}
		break;
	}
		// ok
	next_token(p);
	return curr;
}

bool allow_token(Parser *p, TokenKind kind) {
	if (p->curr_token.kind == kind) {
		next_token(p);
		return true;
	}
	return false;
}

ParserError init_parser(Parser *p, char const *path) {
	TokenizerError err = init_tokenizer(&p->tokenizer, path);
	p->fullpath = p->tokenizer.fullpath;
	switch (err) {
	case TokenizerError_Empty:     return ParserError_Empty;
	case TokenizerError_Invalid:   return ParserError_Invalid;
	case TokenizerError_NotExists: return ParserError_NotExists;
	}

	next_token(p);

	return ParserError_None;
}


AstExpr *parse_expr(Parser *p, bool lhs);
AstType *parse_type(Parser *p);
AstType *parse_type_attempt(Parser *p);
AstDecl *parse_decl(Parser *p);
AstStmt *parse_stmt(Parser *p);

AstExpr *unparen_expr(AstExpr *e) {
	for (;;) {
		if (e == NULL) {
			return NULL;
		}
		if (e->kind == AstExpr_Paren) {
			return e->paren.expr;
		}
		return e;
	}
}

AstExpr *parse_ident(Parser *p) {
	return ast_expr_ident(expect_token(p, Token_Ident));
}
AstExpr *parse_literal(Parser *p, TokenKind kind) {
	return ast_expr_literal(expect_token(p, kind));
}

AstExpr *parse_operand(Parser *p, bool lhs) {
	AstType *t = NULL;
	Token curr = p->curr_token;
	switch (curr.kind) {
	case Token_Ident:   return parse_ident(p);
	case Token_Integer: return parse_literal(p, Token_Integer);
	case Token_Float:   return parse_literal(p, Token_Float);
	case Token_Rune:    return parse_literal(p, Token_Rune);
	case Token_String:  return parse_literal(p, Token_String);

	case Token_OpenParen: {
		Token open, close;
		AstExpr *expr;

		open = expect_token(p, Token_OpenParen);
		p->expr_level += 1;
		expr = parse_expr(p, lhs);
		p->expr_level -= 1;
		close = expect_token(p, Token_CloseParen);

		return ast_expr_paren(open.pos, expr, close.pos);
	}
	default:
		t = parse_type_attempt(p);
		if (t != NULL) {
			return ast_expr_type_expr(t);
		}
		return NULL;
	}
}

AstExpr *parse_call_expr(Parser *p, AstExpr *operand) {
	AstExpr *call = NULL;
	Token open, close;
	AstExpr **args = NULL;
	open = expect_token(p, Token_OpenParen);
	while (p->curr_token.kind != Token_CloseParen &&
	       p->curr_token.kind != Token_EOF) {
		AstExpr *arg = parse_expr(p, false);
		buf_push(args, arg);
		if (!allow_token(p, Token_Comma)) {
			break;
		}
	}
	close = expect_token(p, Token_CloseParen);
	call = ast_expr_call(operand, args, buf_len(args), token_end_pos(close));
	buf_free(args);
	return call;
}

AstExpr *parse_atom_expr(Parser *p, AstExpr *operand, bool lhs) {
	if (operand == NULL) {
		if (p->allow_type) {
			return NULL;
		} else {
			Token prev = p->curr_token;
			error(prev.pos, "expected an operand");
			next_token(p);
			operand = alloc_ast_expr(AstExpr_Invalid, prev.pos, p->curr_token.pos);
		}
	}

	for (;;) {
		switch (p->curr_token.kind) {
		case Token_OpenParen:
			operand = parse_call_expr(p, operand);
			break;

		case Token_Period: {
			Token token = next_token(p);
			if (p->curr_token.kind == Token_Ident) {
				operand = ast_expr_selector(operand, parse_ident(p));
			} else {
				error(p->curr_token.pos, "expected an identifier for selector");
				next_token(p);
				operand = alloc_ast_expr(AstExpr_Invalid, operand->pos, p->curr_token.pos);
			}
			break;
		}

		case Token_OpenBracket: {
			Token open = expect_token(p, Token_OpenBracket);
			AstExpr *index = parse_expr(p, false);
			Token close = expect_token(p, Token_CloseBracket);
			operand = ast_expr_index(operand, index, token_end_pos(close));
			break;
		}

		case Token_Pointer:
			operand = ast_expr_deref(operand, expect_token(p, Token_Pointer));
			break;

		default:
			goto end;
		}

		lhs = false;
	}

end:
	return operand;
}

AstExpr *parse_unary_expr(Parser *p, bool lhs) {
	switch (p->curr_token.kind) {
	case Token_At:
	case Token_Add:
	case Token_Sub:
	case Token_not: {
		Token op = next_token(p);
		AstExpr *expr = parse_unary_expr(p, lhs);
		return ast_expr_unary(op, expr);
	}
	}

	return parse_atom_expr(p, parse_operand(p, lhs), lhs);
}


AstExpr *parse_binary_expr(Parser *p, bool lhs, int prec_in) {
	int prec;
	AstExpr *expr = parse_unary_expr(p, lhs);
	for (prec = token_precedence(p->curr_token.kind); prec >= prec_in; prec--) {
		for (;;) {
			Token op = p->curr_token;
			int op_prec = token_precedence(op.kind);
			if (op_prec != prec) {
				// NOTE(bill): This will also catch operators that are not valid "binary" operators
				break;
			}
			expect_operator(p); // NOTE(bill): error checks too

			if (op.kind == Token_Question) {
				AstExpr *cond, *x, *y;
				cond = expr;
				x = parse_expr(p, lhs);
				expect_token(p, Token_Colon);
				y = parse_expr(p, lhs);
				expr = ast_expr_ternary(cond, x, y);
			} else {
				AstExpr *right = parse_binary_expr(p, false, prec+1);
				if (right == NULL) {
					error(op.pos, "expected expression on the right-hand side of the binary operator");
				}
				expr = ast_expr_binary(op, expr, right);
			}

			lhs = false;
		}
	}
	return expr;
}


AstExpr *parse_expr(Parser *p, bool lhs) {
	return parse_binary_expr(p, lhs, 0+1);
}


AstField parse_field(Parser *p) {
	AstField field = {0};
	field.name = parse_ident(p);
	expect_token(p, Token_Colon);
	field.type = parse_type(p);
	return field;
}

AstType *parse_signature(Parser *p, Token token) {
	Token open, close;
	TokenPos end;
	AstField *params = NULL;
	AstType *return_type = NULL;

	open = expect_token(p, Token_OpenParen);
	while (p->curr_token.kind != Token_CloseParen &&
	       p->curr_token.kind != Token_EOF) {
		buf_push(params, parse_field(p));
		if (!allow_token(p, Token_Comma)) {
			break;
		}
	}
	close = expect_token(p, Token_CloseParen);
	end = close.pos;

	if (allow_token(p, Token_Colon)) {
		return_type = parse_type(p);
		end = return_type->end;
	}

	return ast_type_signature(token, params, buf_len(params), return_type, end);
}

AstType *parse_type(Parser *p) {
	AstType *t = NULL;
	Token prev = p->curr_token;
	bool prev_allow_type = p->allow_type;
	p->allow_type = true;
	t = parse_type_attempt(p);
	p->allow_type = prev_allow_type;
	if (t == NULL) {
		error(prev.pos, "expected a type, got %.*s", LIT(prev.string));
		next_token(p);
		return alloc_ast_type(AstType_Invalid, prev.pos, p->curr_token.pos);
	}
	return t;
}


AstType *parse_type_attempt(Parser *p) {
	Token curr = p->curr_token;
	switch (curr.kind) {
	case Token_Ident:
		return ast_type_ident(parse_ident(p));

	case Token_OpenBracket: { // Array
		Token open, close;
		AstExpr *size = NULL;
		AstType *elem = NULL;
		open = expect_token(p, Token_OpenBracket);
		if (p->curr_token.kind != Token_CloseBracket) {
			size = parse_expr(p, true);
		}
		close = expect_token(p, Token_CloseBracket);
		elem = parse_type(p);
		return ast_type_array(open, size, elem);
	}
	case Token_Pointer: {
		Token token = expect_token(p, Token_Pointer);
		AstType *elem = parse_type(p);
		return ast_type_pointer(token, elem);
	}

	case Token_set: {
		Token token, open, close;
		AstExpr **elems = NULL;
		token = expect_token(p, Token_set);
		open = expect_token(p, Token_OpenBracket);
		while (p->curr_token.kind != Token_CloseBracket &&
		       p->curr_token.kind != Token_EOF) {
			buf_push(elems, parse_expr(p, true));
			if (!allow_token(p, Token_Comma)) {
				break;
			}
		}
		close = expect_token(p, Token_CloseBracket);

		return ast_type_set(token, elems, buf_len(elems), close.pos);
	}

	case Token_range: {
		Token token = expect_token(p, Token_range);
		AstExpr *expr = parse_expr(p, false);
		expr = unparen_expr(expr);
		if (expr != NULL && expr->kind == AstExpr_Binary &&
		    expr->binary.op.kind == Token_Ellipsis) {
			return ast_type_range(token, expr->binary.left, expr->binary.right);
		}
		error(p->curr_token.pos, "expected range expression");
		return alloc_ast_type(AstType_Invalid, token.pos, token.pos);

	}

	case Token_proc: {
		Token token = expect_token(p, Token_proc);
		return parse_signature(p, token);
	}
	}

	return NULL;
}

AstStmt *parse_body(Parser *p) {
	Token open, close;
	AstStmt **stmts = NULL;
	open = expect_token(p, Token_OpenBrace);
	while (p->curr_token.kind != Token_CloseBrace &&
	       p->curr_token.kind != Token_EOF) {
		buf_push(stmts, parse_stmt(p));
	}
	close = expect_token(p, Token_CloseBrace);

	return ast_stmt_block(stmts, buf_len(stmts), open.pos, close.pos);
}


AstStmt *parse_if_stmt(Parser *p) {
	Token token = expect_token(p, Token_if);
	AstExpr *cond = NULL;
	AstStmt *body = NULL;
	AstStmt *else_stmt = NULL;
	isize prev_level = p->expr_level;
	p->expr_level = -1;
	cond = parse_expr(p, false);
	p->expr_level = prev_level;

	if (cond == NULL) {
		error(p->curr_token.pos, "expected condition for if statement");
	}

	body = parse_body(p);

	if (allow_token(p, Token_else)) {
		switch (p->curr_token.kind) {
		case Token_if:
			else_stmt = parse_if_stmt(p);
			break;
		case Token_OpenBrace:
			else_stmt = parse_body(p);
			break;
		default:
			error(p->curr_token.pos, "expected if statement block statement");
			else_stmt = NULL;
			break;
		}
	}

	return ast_stmt_if(token, cond, body, else_stmt);
}

AstStmt *parse_for_stmt(Parser *p) {
	Token token = expect_token(p, Token_for);
	AstStmt *init = NULL;
	AstExpr *cond = NULL;
	AstStmt *post = NULL;
	AstStmt *body = NULL;
	isize prev_level = p->expr_level;

	p->expr_level = -1;
	// TODO(bill): for stmt
	p->expr_level = prev_level;

	return ast_stmt_for(token, init, cond, post, body);
}

AstStmt *parse_while_stmt(Parser *p) {
	Token token = expect_token(p, Token_while);
	AstExpr *cond = NULL;
	AstStmt *body = NULL;
	isize prev_level = p->expr_level;
	p->expr_level = -1;
	cond = parse_expr(p, false);
	p->expr_level = prev_level;

	if (cond == NULL) {
		error(p->curr_token.pos, "expected condition for while statement");
	}

	body = parse_body(p);

	return ast_stmt_while(token, cond, body);
}

AstStmt *parse_return_stmt(Parser *p) {
	Token token = expect_token(p, Token_return);
	AstExpr *expr = NULL;
	if (p->curr_token.kind != Token_Semicolon) {
		expr = parse_expr(p, false);
	}
	return ast_stmt_return(token, expr);
}

AstStmt *parse_simple_stmt(Parser *p) {
	AstExpr *lhs = NULL;
	AstExpr *rhs = NULL;
	Token token;

	lhs = parse_expr(p, true);
	token = p->curr_token;
	switch (token.kind) {
	case Token_Define:
	case Token_Assign:
	case Token_AddEq:
	case Token_SubEq:
	case Token_MulEq:
	case Token_DivEq:
	case Token_ModEq:
		next_token(p);
		rhs = parse_expr(p, false);
		return ast_stmt_assign(token, lhs, rhs);
	}
	return ast_stmt_expr(lhs);
}

AstStmt *parse_stmt(Parser *p) {
	switch (p->curr_token.kind) {
	case Token_var:
	case Token_const:
	case Token_type:
	case Token_proc:
	case Token_import:
		return ast_stmt_decl(parse_decl(p));

	case Token_label: {
		Token token = expect_token(p, Token_label);
		AstExpr *name = parse_ident(p);
		return ast_stmt_label(token, name);
	}

	case Token_Ident:
	case Token_Integer:
	case Token_Float:
	case Token_Rune:
	case Token_String:
	case Token_OpenParen:
	case Token_Pointer:
	case Token_Add:
	case Token_Sub:
	case Token_At:
		return parse_simple_stmt(p);

	case Token_OpenBrace:
		return parse_body(p);

	case Token_Semicolon:
		return ast_stmt_empty(expect_token(p, Token_Semicolon));

	case Token_if:     return parse_if_stmt(p);
	case Token_for:    return parse_for_stmt(p);
	case Token_while:  return parse_while_stmt(p);
	case Token_return: return parse_return_stmt(p);

	case Token_break:
	case Token_continue:
	case Token_fallthrough: {
		Token token = next_token(p);
		return ast_stmt_branch(token);
	}

	case Token_goto: {
		Token token = expect_token(p, Token_goto);
		AstExpr *name = parse_ident(p);
		return ast_stmt_goto(token, name);
	}

	}
	return ast_stmt_expr(parse_expr(p, true));
}




AstDecl *parse_decl_var(Parser *p) {
	Token token = expect_token(p, Token_var);
	AstExpr **names = NULL;
	AstType *type = NULL;
	AstExpr **values = NULL;

	do {
		buf_push(names, parse_ident(p));
		if (!allow_token(p, Token_Comma)) {
			break;
		}
	} while (p->curr_token.kind != Token_EOF);

	if (allow_token(p, Token_Colon)) {
		type = parse_type(p);
	}
	if (allow_token(p, Token_Assign)) {
		do {
			buf_push(values, parse_expr(p, false));
			if (!allow_token(p, Token_Comma)) {
				break;
			}
		} while (p->curr_token.kind != Token_EOF);
	}
	if (type == NULL && values == NULL) {
		error(p->curr_token.pos, "expected a type after var names");
	} else if (values != NULL) {
		int lhs = cast(int)buf_len(names);
		int rhs = cast(int)buf_len(values);
		if (lhs != rhs) {
			error(p->curr_token.pos, "unbalanced names and values, %d != %d", lhs, rhs);
		}
	}

	return ast_decl_var(token, names, buf_len(names), type, values, buf_len(values));
}

AstDecl *parse_decl_const(Parser *p) {
	Token token = expect_token(p, Token_const);
	AstExpr **names = NULL;
	AstType *type = NULL;
	AstExpr **values = NULL;
	do {
		buf_push(names, parse_ident(p));
		if (!allow_token(p, Token_Comma)) {
			break;
		}
	} while (p->curr_token.kind != Token_EOF);

	if (allow_token(p, Token_Colon)) {
		type = parse_type(p);
	}

	expect_token(p, Token_Assign);
	do {
		buf_push(values, parse_expr(p, false));
		if (!allow_token(p, Token_Comma)) {
			break;
		}
	} while (p->curr_token.kind != Token_EOF);

	{
		isize lhs = buf_len(names);
		isize rhs = buf_len(values);
		if (lhs != rhs) {
			error(p->curr_token.pos, "unbalanced names and values, %ld vs %ld", lhs, rhs);
		}
	}

	return ast_decl_const(token, names, buf_len(names), type, values, buf_len(values));
}
AstDecl *parse_decl_type(Parser *p) {
	Token token = expect_token(p, Token_type);
	AstExpr *name = parse_ident(p);
	AstType *type = parse_type(p);
	return ast_decl_type(token, name, type);
}
AstDecl *parse_decl_proc(Parser *p) {
	Token token = expect_token(p, Token_proc);
	AstExpr *name = parse_ident(p);
	AstType *signature = parse_signature(p, token);
	AstStmt *body = NULL;
	if (p->curr_token.kind == Token_OpenBrace) {
		body = parse_body(p);
	}
	return ast_decl_proc(token, name, signature, body);
}
AstDecl *parse_decl_import(Parser *p) {
	Token token = expect_token(p, Token_import);
	return NULL;
}

AstDecl *parse_decl(Parser *p) {
	switch (p->curr_token.kind) {
	case Token_var:    return parse_decl_var(p);
	case Token_const:  return parse_decl_const(p);
	case Token_type:   return parse_decl_type(p);
	case Token_proc:   return parse_decl_proc(p);
	case Token_import: return parse_decl_import(p);

	case Token_Semicolon:
		expect_token(p, Token_Semicolon);
		return parse_decl(p);
	case Token_EOF:
		return NULL;
	}

	error(p->curr_token.pos, "expected a declaration, got %.*s", LIT(token_strings[p->curr_token.kind]));
	next_token(p);
	return NULL;
}

ParserError parse_package(AstPackage *package, char const *package_path) {
	Parser p = {0};
	AstDecl **decls = NULL;
	ParserError err = init_parser(&p, package_path);
	package->fullpath = p.fullpath;
	if (err != ParserError_None) {
		return err;
	}
	while (p.curr_token.kind != Token_EOF) {
		AstStmt *stmt = parse_stmt(&p);
		if (stmt == NULL) {
			break;
		}

		switch (stmt->kind) {
		case AstStmt_Decl:
			buf_push(decls, stmt->decl);
			break;
		case AstStmt_Invalid:
		case AstStmt_Empty:
			break;
		default:
			error(stmt->pos, "only prefixed declarations are allowed at file scope");
			break;
		}

	}

	package->decls = AST_DUP_ARRAY(decls, buf_len(decls));
	package->decl_count = buf_len(decls);
	buf_free(decls);
	return err;
}
