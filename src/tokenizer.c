typedef struct TokenPos {
	String file;
	isize  line;
	isize  column;
} TokenPos;

TokenPos token_pos(String file, isize line, isize column) {
	TokenPos pos = {0};
	pos.file   = file;
	pos.line   = line;
	pos.column = column;
	return pos;
}
i32 token_pos_cmp(TokenPos a, TokenPos b) {
	if (a.line != b.line) return (a.line < b.line) ? -1 : +1;
	if (a.column != b.column) return (a.column < b.column) ? -1 : +1;
	return string_compare(a.file, b.file);
}
static isize global_error_count = 0;
static TokenPos global_error_prev_pos = {0};
void error_va(TokenPos pos, char *fmt, va_list va) {
	global_error_count += 1;
	// NOTE(bill): Duplicate error, skip it
	if (pos.line == 0) {
		fprintf(stderr, "Error: ");
		vfprintf(stderr, fmt, va);
		fprintf(stderr, "\n");
	} else if (token_pos_cmp(global_error_prev_pos, pos) != 0) {
		global_error_prev_pos = pos;
		fprintf(stderr, "%.*s(%d:%d): ", LIT(pos.file), cast(int)pos.line, cast(int)pos.column);
		vfprintf(stderr, fmt, va);
		fprintf(stderr, "\n");
	}
}
void error(TokenPos pos, char *fmt, ...) {
	va_list va;
	va_start(va, fmt);
	error_va(pos, fmt, va);
	va_end(va);
}



#define TOKEN_KINDS \
	TOKEN_KIND(Token_Invalid, "invalid token"), \
	TOKEN_KIND(Token_EOF, "EOF"), \
TOKEN_KIND(Token__LiteralBegin, ""), \
	TOKEN_KIND(Token_Ident,   "identifier"), \
	TOKEN_KIND(Token_Integer, "integer"), \
	TOKEN_KIND(Token_Float,   "float"), \
	TOKEN_KIND(Token_Rune,    "rune"), \
	TOKEN_KIND(Token_String,  "string"), \
TOKEN_KIND(Token__LiteralEnd, ""), \
	TOKEN_KIND(Token_OpenParen,    "("), \
	TOKEN_KIND(Token_CloseParen,   ")"), \
	TOKEN_KIND(Token_OpenBrace,    "{"), \
	TOKEN_KIND(Token_CloseBrace,   "}"), \
	TOKEN_KIND(Token_OpenBracket,  "["), \
	TOKEN_KIND(Token_CloseBracket, "]"), \
	TOKEN_KIND(Token_Semicolon,    ";"), \
	TOKEN_KIND(Token_Colon,        ":"), \
	TOKEN_KIND(Token_Comma,        ","), \
	TOKEN_KIND(Token_Period,       "."), \
	TOKEN_KIND(Token_Question,     "?"), \
	TOKEN_KIND(Token_Pointer,      "^"), \
	TOKEN_KIND(Token_At,           "@"), \
	TOKEN_KIND(Token_Inc,          "++"), \
	TOKEN_KIND(Token_Dec,          "--"), \
TOKEN_KIND(Token__AssignmentBegin, ""), \
	TOKEN_KIND(Token_Assign,       "="), \
	TOKEN_KIND(Token_Define,       ":="), \
	TOKEN_KIND(Token_AddEq,        "+="), \
	TOKEN_KIND(Token_SubEq,        "-="), \
	TOKEN_KIND(Token_MulEq,        "*="), \
	TOKEN_KIND(Token_DivEq,        "/="), \
	TOKEN_KIND(Token_ModEq,        "%="), \
TOKEN_KIND(Token__AssignmentEnd, ""), \
TOKEN_KIND(Token__OperatorBegin, ""), \
	TOKEN_KIND(Token_Ellipsis, ".."), \
	TOKEN_KIND(Token_Add,      "+"), \
	TOKEN_KIND(Token_Sub,      "-"), \
	TOKEN_KIND(Token_Mul,      "*"), \
	TOKEN_KIND(Token_Div,      "/"), \
	TOKEN_KIND(Token_Mod,      "%"), \
	TOKEN_KIND(Token_Xor,      "~"), \
	TOKEN_KIND(Token_Eq,       "=="), \
	TOKEN_KIND(Token_NotEq,    "!="), \
	TOKEN_KIND(Token_Lt,       "<"), \
	TOKEN_KIND(Token_Gt,       ">"), \
	TOKEN_KIND(Token_LtEq,     "<="), \
	TOKEN_KIND(Token_GtEq,     ">="), \
TOKEN_KIND(Token__OperatorEnd, ""), \
TOKEN_KIND(Token__KeywordBegin, ""), \
	TOKEN_KIND(Token_var,         "var"), \
	TOKEN_KIND(Token_const,       "const"), \
	TOKEN_KIND(Token_type,        "type"), \
	TOKEN_KIND(Token_proc,        "proc"), \
	TOKEN_KIND(Token_import,      "import"), \
	TOKEN_KIND(Token_label,       "label"), \
	TOKEN_KIND(Token_if,          "if"), \
	TOKEN_KIND(Token_else,        "else"), \
	TOKEN_KIND(Token_for,         "for"), \
	TOKEN_KIND(Token_while,       "while"), \
	TOKEN_KIND(Token_return,      "return"), \
	TOKEN_KIND(Token_switch,      "switch"), \
	TOKEN_KIND(Token_case,        "case"), \
	TOKEN_KIND(Token_break,       "break"), \
	TOKEN_KIND(Token_continue,    "continue"), \
	TOKEN_KIND(Token_fallthrough, "fallthrough"), \
	TOKEN_KIND(Token_goto,        "goto"), \
	TOKEN_KIND(Token_and,         "and"), \
	TOKEN_KIND(Token_or,          "or"), \
	TOKEN_KIND(Token_not,         "not"), \
	TOKEN_KIND(Token_in,          "in"), \
	TOKEN_KIND(Token_set,         "set"), \
	TOKEN_KIND(Token_range,       "range"), \
	TOKEN_KIND(Token_struct,      "struct"), \
	TOKEN_KIND(Token_enum,        "enum"), \
TOKEN_KIND(Token__KeywordEnd, ""), \
	TOKEN_KIND(Token_COUNT, "")


typedef enum TokenKind {
#define TOKEN_KIND(a, b) a
	TOKEN_KINDS
#undef TOKEN_KIND
} TokenKind;

static String token_strings[] = {
#define TOKEN_KIND(a, b) str_lit(b)
	TOKEN_KINDS
#undef TOKEN_KIND
};

typedef struct Token {
	TokenKind kind;
	String    string;
	TokenPos  pos;
} Token;

typedef struct Tokenizer {
	String fullpath;
	char *start;
	char *end;

	Rune  ch;          // current character
	char *curr;        // character pos
	char *read_curr;   // pos from start
	char *line;        // current line pos
	isize line_count;
	bool  insert_semi; // insert a semicolon before next newline

	isize error_count;
} Tokenizer;

typedef struct TokenizerState {
	Rune  ch;           // current character
	char *curr;        // character pos
	char *read_curr;   // pos from start
	char *line;        // current line pos
	isize line_count;
} TokenizerState;

typedef enum TokenizerError {
	TokenizerError_None,

	TokenizerError_Empty,
	TokenizerError_Invalid,
	TokenizerError_NotExists,

	TokenizerError_COUNT,
} TokenizerError;



TokenPos token_end_pos(Token t) {
	TokenPos end = t.pos;
	end.column += t.string.len;
	return end;
}

void tokenizer_err(Tokenizer *t, char *msg, ...) {
	va_list va;
	isize column = t->read_curr - t->line+1;
	TokenPos pos = {0};
	pos.file = t->fullpath;
	pos.line = t->line_count;
	pos.column = MAX(column, 1);

	va_start(va, msg);
	error_va(pos, msg, va);
	va_end(va);

	t->error_count++;
}

void next_rune(Tokenizer *t);



// NOTE(bill): result == priority
int token_precedence(TokenKind t) {
	switch (t) {
	case Token_Question:
		return 1;
	case Token_Ellipsis:
		return 2;
	case Token_or:
		return 3;
	case Token_and:
		return 4;
	case Token_in:
	case Token_Eq:
	case Token_NotEq:
	case Token_Lt:
	case Token_Gt:
	case Token_LtEq:
	case Token_GtEq:
		return 5;
	case Token_Add:
	case Token_Sub:
		return 6;
	case Token_Mul:
	case Token_Div:
	case Token_Mod:
		return 7;
	}
	return 0;
}

bool token_is_comparison(TokenKind op) {
	switch (op) {
	case Token_and:
	case Token_or:
	case Token_Eq:
	case Token_NotEq:
	case Token_Lt:
	case Token_Gt:
	case Token_LtEq:
	case Token_GtEq:
		return true;
	}
	return false;
}


TokenizerError init_tokenizer(Tokenizer *t, char const *path) {
	TokenizerError err = TokenizerError_None;
	String fc = {0};

	char *fullpath = get_fullpath(path);
	t->fullpath = make_string_c(fullpath);
	t->line_count = 1;

	fc = read_entire_file(fullpath);
	if (fc.len > 0) {
		t->start = fc.text;
		t->line = t->read_curr = t->curr = t->start;
		t->end = t->start + fc.len;
		t->insert_semi = false;
		t->error_count = 0;

		next_rune(t);
		if (t->ch == RUNE_BOM) {
			next_rune(t); // Ignore BOM at beginning of file
		}
	} else {
		FILE *f = fopen(fullpath, "rb");
		if (f) {
			err = TokenizerError_Invalid;
			fclose(f);
		} else {
			err = TokenizerError_NotExists;
		}
	}

	return err;
}

void destroy_tokenizer(Tokenizer *t) {
	mem_free(t->start);
}

TokenizerState save_tokenizer_state(Tokenizer *t) {
	TokenizerState state = {0};
	state.ch         = t->ch;
	state.curr       = t->curr;
	state.read_curr  = t->read_curr;
	state.line       = t->line;
	state.line_count = t->line_count;
	return state;
}

void restore_tokenizer_state(Tokenizer *t, TokenizerState *state) {
	 t->ch  = state->ch;
	 t->curr       = state->curr;
	 t->read_curr  = state->read_curr;
	 t->line       = state->line;
	 t->line_count = state->line_count;
}


void next_rune(Tokenizer *t) {
	if (t->read_curr < t->end) {
		Rune rune;
		isize width = 1;

		t->curr = t->read_curr;
		if (t->ch == '\n') {
			t->line = t->curr;
			t->line_count++;
		}
		rune = *t->read_curr;
		if (rune == 0) {
			tokenizer_err(t, "Illegal character NUL");
		} else if (rune >= 0x80) { // not ASCII
			width = utf8_decode(t->read_curr, t->end-t->read_curr, &rune);
			if (rune == RUNE_INVALID && width == 1)
				tokenizer_err(t, "Illegal UTF-8 encoding");
			else if (rune == RUNE_BOM && t->curr-t->start > 0)
				tokenizer_err(t, "Illegal byte order mark");
		}
		t->read_curr += width;
		t->ch = rune;
	} else {
		t->curr = t->end;
		if (t->ch == '\n') {
			t->line = t->curr;
			t->line_count++;
		}
		t->ch = RUNE_EOF;
	}
}

void skip_whitespace(Tokenizer *t) {
	while (t->ch == ' ' || t->ch == '\t' || t->ch == '\n' && !t->insert_semi || t->ch == '\r') {
		next_rune(t);
	}
}

bool allow_rune(Tokenizer *t, Rune r) {
	if (t->ch == r) {
		next_rune(t);
		return true;
	}
	return false;
}


void scan_mantissa(Tokenizer *t, int base) {
	while (digit_value(t->ch) < base || t->ch == '_') {
		next_rune(t);
	}
}

Token scan_number_to_token(Tokenizer *t, bool seen_decimal_point) {
	Token token = {0};
	token.kind = Token_Integer;
	token.string = make_string(t->curr, 1);
	token.pos.file = t->fullpath;
	token.pos.line = t->line_count;
	token.pos.column = t->curr-t->line+1;

	if (seen_decimal_point) {
		token.string.text -= 1;
		token.string.len  += 1;
		token.pos.column -= 1;
		token.kind = Token_Float;
		scan_mantissa(t, 10);
		goto exponent;
	}

	if (t->ch == '0') {
		char *prev = t->curr;
		next_rune(t);
		if (allow_rune(t, 'b')) { // Binary
			scan_mantissa(t, 2);
			if (t->curr - prev <= 2) {
				token.kind = Token_Invalid;
			}
		} else if (allow_rune(t, 'o')) { // Octal
			scan_mantissa(t, 8);
			if (t->curr - prev <= 2) {
				token.kind = Token_Invalid;
			}
		} else if (allow_rune(t, 'x')) { // Hexadecimal
			scan_mantissa(t, 16);
			if (t->curr - prev <= 2) {
				token.kind = Token_Invalid;
			}
		} else {
			seen_decimal_point = false;
			scan_mantissa(t, 10);

			if (t->ch == '.' || t->ch == 'e' || t->ch == 'E') {
				seen_decimal_point = true;
				goto fraction;
			}
		}

		goto end;
	}

	scan_mantissa(t, 10);


fraction:
	if (t->ch == '.') {
		// HACK(bill): This may be inefficient
		TokenizerState state = save_tokenizer_state(t);
		next_rune(t);
		if (t->ch == '.') {
			// TODO(bill): Clean up this shit
			restore_tokenizer_state(t, &state);
			goto end;
		}
		token.kind = Token_Float;
		scan_mantissa(t, 10);
	}

exponent:
	if (allow_rune(t, 'e') || allow_rune(t, 'E')) {
		token.kind = Token_Float;
		if (allow_rune(t, '-') || allow_rune(t, '+')) {
			// Okay
		}
		scan_mantissa(t, 10);
	}

end:
	token.string.len = t->curr - token.string.text;
	return token;
}

TokenKind token_kind_variant2(Tokenizer *t, TokenKind a, TokenKind b) {
	if (allow_rune(t, '=')) {
		return b;
	}
	return a;
}

void scan_comment(Tokenizer *t) {
	if (t->ch == '/') {
		//-style comment
		next_rune(t);
		while (t->ch != '\n' && t->ch >= 0) {
			next_rune(t);
		}
	} else if (t->ch == '*') {
		isize comment_depth = 1;
		next_rune(t);
		while (t->ch >= 0) {
			Rune ch = t->ch;
			next_rune(t);
			if (ch == '/' && t->ch == '*') {
				next_rune(t);
				comment_depth++;
			} else if (ch == '*' && t->ch == '/') {
				next_rune(t);
				comment_depth--;
				if (comment_depth <= 0) {
					break;
				}
			}
		}
	}
}

Token scan_token(Tokenizer *t) {
	Token token;
	Rune ch;
	bool insert_semi;
scan_again:
	skip_whitespace(t);

	mem_zero_item(&token);
	ch = 0;
	insert_semi = false;

	token.string = make_string(t->curr, 1);
	token.pos = token_pos(t->fullpath, t->line_count, t->curr-t->line + 1);

	ch = t->ch;
	if (rune_is_letter(ch)) {
		token.kind = Token_Ident;
		while (rune_is_letter(t->ch) || rune_is_digit(t->ch)) {
			next_rune(t);
		}
		token.string.len = t->curr - token.string.text;

		if (token.string.len >= 2) {
			TokenKind i;
			for (i = Token__KeywordBegin+1; i < Token__KeywordEnd; i++) {
				if (str_eq(token_strings[i], token.string)) {
					token.kind = cast(TokenKind)i;
					break;
				}
			}
		}
		switch (token.kind) {
		case Token_Ident:
		case Token_break:
		case Token_continue:
		case Token_return:
			insert_semi = true;
			break;
		}
	} else if (rune_is_digit(ch)) {
		insert_semi = true;
		token = scan_number_to_token(t, false);
	} else {
		next_rune(t);
		switch (ch) {
		case RUNE_EOF:
			if (t->insert_semi) {
				insert_semi = false;
				token.kind = Token_Semicolon;
				token.string = make_string_c("\n");
				return token;
			}
			token.kind = Token_EOF;
			break;

		case '\n':
			insert_semi = false;
			token.kind = Token_Semicolon;
			token.string = make_string_c("\n");
			return token;

		case '(': token.kind = Token_OpenParen;    break;
		case '{': token.kind = Token_OpenBrace;    break;
		case '}': token.kind = Token_CloseBrace;   break;
		case ')':
			token.kind = Token_CloseParen;
			insert_semi = true;
			break;
		case '[':
			token.kind = Token_OpenBracket;
			insert_semi = true;
			break;
		case ']':
			token.kind = Token_CloseBracket;
			insert_semi = true;
			break;

		case ':':
			token.kind = Token_Colon;
			if (allow_rune(t, '=')) {
				token.kind = Token_Define;
			}
			break;
		case ';':  token.kind = Token_Semicolon; break;
		case ',':  token.kind = Token_Comma;     break;
		case '.':
			token.kind = Token_Period;
			if (allow_rune(t, '.')) {
				token.kind = Token_Ellipsis;
			} else if ('0' <= t->ch && t->ch <= '9') {
				insert_semi = true;
				token = scan_number_to_token(t, true);
			}
			break;
		case '?': token.kind = Token_Question; break;
		case '=': token.kind = token_kind_variant2(t, Token_Assign, Token_Eq); break;

		case '^': token.kind = Token_Pointer; break;
		case '@': token.kind = Token_At;      break;
		case '~': token.kind = Token_Xor;     break;
		case '+':
			token.kind = Token_Add;
			if (allow_rune(t, '=')) {
				token.kind = Token_AddEq;
			} else if (allow_rune(t, '+')) {
				token.kind = Token_Inc;
				insert_semi = true;
			}
			break;
		case '-':
			token.kind = Token_Sub;
			if (allow_rune(t, '=')) {
				token.kind = Token_SubEq;
			} else if (allow_rune(t, '-')) {
				token.kind = Token_Dec;
				insert_semi = true;
			}
			break;

		case '*': token.kind = token_kind_variant2(t, Token_Mul, Token_MulEq); break;
		case '/':
			if (t->ch == '/' || t->ch == '*') {
				if (t->insert_semi && t->ch == '/') {
					scan_comment(t);
					t->insert_semi = false;
					token.kind = Token_Semicolon;
					token.string = make_string_c("\n");
					return token;
				}

				scan_comment(t);
				t->insert_semi = false;
				goto scan_again;

			} else {
				token.kind = token_kind_variant2(t, Token_Div, Token_DivEq);
			}
			break;
		case '%': token.kind = token_kind_variant2(t, Token_Mod, Token_ModEq); break;
		case '<': token.kind = token_kind_variant2(t, Token_Lt,  Token_LtEq);  break;
		case '>': token.kind = token_kind_variant2(t, Token_Gt,  Token_GtEq);  break;

		case '!':
			if (allow_rune(t, '=')) {
				token.kind = Token_NotEq;
				break;
			}
			goto invalid_rune;

		default:
		invalid_rune: {
			String s = alloc_string_from_rune(ch);
			if (ch != RUNE_BOM) {
				tokenizer_err(t, "Illegal character: %.*s (%d) ", LIT(s), ch);
			}
			insert_semi = t->insert_semi;
			token.kind = Token_Invalid;
			token.string = s;
			break;
		}
		}
	}

	t->insert_semi = insert_semi;

	token.string.len = t->curr - token.string.text;

	return token;
}
