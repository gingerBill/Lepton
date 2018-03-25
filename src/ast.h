typedef struct AstFile  AstFile;
typedef struct AstExpr  AstExpr;
typedef struct AstType  AstType;
typedef struct AstStmt  AstStmt;
typedef struct AstDecl  AstDecl;
typedef struct AstField AstField;

typedef enum AstExprKind AstExprKind;
typedef enum AstTypeKind AstTypeKind;
typedef enum AstStmtKind AstStmtKind;
typedef enum AstDeclKind AstDeclKind;




enum AstExprKind {
	AstExpr_Invalid,

	AstExpr_Literal,
	AstExpr_Ident,
	AstExpr_Paren,
	AstExpr_Call,
	AstExpr_Index,
	AstExpr_Selector,
	AstExpr_Unary,
	AstExpr_Binary,
	AstExpr_Ternary,

	AstExpr_COUNT
};

struct AstExpr {
	AstExprKind kind;
	TokenPos begin, end;
	union {
		Token literal;
		Token ident;
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
	TokenPos    begin;
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
	TokenPos begin, end;
	union {
		AstDecl *decl;
		AstExpr *expr;
		struct {
			AstStmt **stmts;
			isize     stmt_count;
		} block;
		struct {
			Token op;
			AstExpr *lhs;
			AstExpr *rhs;
		} assign;
		struct {
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
	TokenPos begin, end;
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
