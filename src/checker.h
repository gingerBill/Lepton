typedef struct Entity Entity;
typedef struct Type Type;
typedef struct DeclInfo DeclInfo;
typedef struct Scope Scope;
typedef struct Operand Operand;
typedef struct Checker Checker;
typedef struct CheckerContext CheckerContext;

typedef enum EntityKind  EntityKind;
typedef enum EntityState EntityState;
typedef enum EntityFlag  EntityFlag;
typedef enum AddressingMode AddressingMode;



typedef enum ScopeFlag {
	ScopeFlag_Global = 1<<0,
	ScopeFlag_Proc   = 1<<1,
	ScopeFlag_Type   = 1<<2
} ScopeFlag;


struct Scope {
	AstStmt *node;
	Scope *  parent;
	Scope *  prev;
	Scope *  next;
	Scope *  first_child;
	Scope *  last_child;

	Map      elements; // Key: String, Value: Entity *
	u32      flags;
	Entity **labels;
};

static Scope *universal_scope = NULL;




enum EntityKind {
	Entity_Invalid,

	Entity_Var,
	Entity_Const,
	Entity_Proc,
	Entity_Type,
	Entity_Label,
	Entity_ImportName,

	Entity_COUNT,
};

enum EntityState {
	EntityState_Unresolved,
	EntityState_Processing,
	EntityState_Resolved,
};

enum EntityFlag {
	EntityFlag_Used = 1<<0,
	EntityFlag_Param = 1<<1,
};

struct Entity {
	EntityKind  kind;
	EntityState state;
	u32         flags;
	String      name;
	AstDecl *   node;
	AstExpr *   ident;
	DeclInfo *  decl;
	Scope *     scope;
	Type *      type;
};


struct DeclInfo {
	DeclInfo *parent;
	Scope *   scope;

	Entity * entity;
	AstType *type_expr;
	AstExpr *init_expr;
};




enum AddressingMode {
	Addressing_Invalid,

	Addressing_NoValue,
	Addressing_Value,
	Addressing_Var,
	Addressing_Const,
	Addressing_Type,
	Addressing_Label,

	Addressing_COUNT
};
static String const addressing_mode_strings[Addressing_COUNT] = {
	str_lit("invalid mode"),
	str_lit("no value"),
	str_lit("value"),
	str_lit("variable"),
	str_lit("constant"),
	str_lit("type"),
	str_lit("label")
};

struct Operand {
	AddressingMode mode;
	AstExpr *      expr;
	Type *         type;
	ConstValue     value;
};

struct CheckerContext {
	Scope *   scope;
	DeclInfo *decl;
	Entity *  curr_proc;
	String    proc_name;
	Type *    type_hint;
};

typedef struct ProcInfo {
	DeclInfo *decl;
	Type *    type;
	AstStmt * body;
} ProcInfo;

struct Checker {
	Scope *global_scope;
	CheckerContext context;

	Entity **entities;

	ProcInfo *procs;

	Entity **type_path;
	isize    type_level;
};


typedef enum StmtFlag {
	StmtFlag_BreakAllowed       = 1<<0,
	StmtFlag_ContinueAllowed    = 1<<1,
	StmtFlag_FallthroughAllowed = 1<<2,
} StmtFlag;


void checker_init(Checker *c);
void check_package(Checker *c, AstPackage *p);
void check_proc_body(Checker *c, DeclInfo *decl, Type *type, AstStmt *body);


void init_universal_scope(void);


bool is_operand_value(Operand const *o);




Scope *alloc_scope(Scope *parent, AstStmt *node);
void scope_destroy(Scope *scope);

Type *type_from_literal(Token lit);

void    check_decl(Checker *c, AstDecl *decl);
Type *  check_type(Checker *c, AstType *type);
void    check_stmt(Checker *c, AstStmt *stmt, u32 flags);
Operand check_expr(Checker *c, AstExpr *expr);
Operand check_expr_base(Checker *c, AstExpr *expr, Type *type_hint);


Entity *alloc_entity(EntityKind kind, AstExpr *ident, AstDecl *node);
DeclInfo *alloc_decl_info(Checker *c, Entity *e, AstType *type_expr, AstExpr *init_expr);
Entity *scope_lookup_entity(Scope *scope, String name);
Entity *scope_insert_entity(Scope *s, Entity *e);

void add_entity(Checker *c, Entity *e);
void add_entity_use(Checker *c, AstExpr *ident, Entity *e);


#include "type.c"
