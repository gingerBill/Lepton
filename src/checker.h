typedef struct Entity Entity;
typedef struct Type Type;
typedef struct DeclInfo DeclInfo;
typedef struct Scope Scope;
typedef struct Operand Operand;
typedef struct CheckerContext CheckerContext;
typedef struct ProcInfo ProcInfo;
typedef struct ExprInfo ExprInfo;
typedef struct Checker Checker;

typedef enum EntityKind  EntityKind;
typedef enum EntityState EntityState;
typedef enum EntityFlag  EntityFlag;
typedef enum AddressingMode AddressingMode;
typedef enum StmtFlag StmtFlag;



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
	Entity_Nil,

	Entity_COUNT,
};

enum EntityState {
	EntityState_Unresolved,
	EntityState_Processing,
	EntityState_Resolved,
};

enum EntityFlag {
	EntityFlag_Used    = 1<<0,
	EntityFlag_Param   = 1<<1,
	EntityFlag_Visited = 1<<2,
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

	ConstValue value;
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

	Entity **type_path;
};

struct ProcInfo {
	DeclInfo *decl;
	Type *    type;
	AstStmt * body;
};

struct ExprInfo {
	AddressingMode mode;
	Type *         type;
	ConstValue     value;
};

struct Checker {
	Scope *global_scope;
	CheckerContext context;

	Entity **entities;

	ProcInfo *procs;
	Map       expr_info_map; // Key: AstExpr *; Value: ExprInfo *
};


enum StmtFlag {
	StmtFlag_BreakAllowed       = 1<<0,
	StmtFlag_ContinueAllowed    = 1<<1,
	StmtFlag_FallthroughAllowed = 1<<2,
};


void checker_init(Checker *c);
void check_package(Checker *c, AstPackage *p);
void check_proc_body(Checker *c, DeclInfo *decl, Type *type, AstStmt *body);


void init_universal_scope(void);


bool is_operand_value(Operand const *o);




Scope *alloc_scope(Scope *parent, AstStmt *node);
void scope_destroy(Scope *scope);

Type *type_from_literal(Token lit);

void  check_decl     (Checker *c, AstDecl *decl);
Type *check_type     (Checker *c, AstType *type);
Type *check_type_expr(Checker *c, AstType *type_expr, Type *named_type);
void  check_stmt     (Checker *c, AstStmt *stmt, u32 flags);
void  check_expr        (Checker *c, Operand *o, AstExpr *expr);
void  check_expr_base   (Checker *c, Operand *o, AstExpr *expr, Type *type_hint);
void  check_expr_or_type(Checker *c, Operand *o, AstExpr *expr, Type *type_hint);
bool  check_assignment  (Checker *c, Operand *o, Type *type, char const *context_name);
void check_init_variable(Checker *c, Entity *e, Operand *o, char const *context_name);
void check_init_constant(Checker *c, Entity *e, Operand *o);

void check_var_decl(Checker *c, AstExpr **lhs, isize lhs_count, AstType *type_expr, AstExpr **rhs, isize rhs_count);
void check_type_decl(Checker *c, Entity *e, AstType *type_expr);


Entity *alloc_entity(EntityKind kind, AstExpr *ident, AstDecl *node);
DeclInfo *alloc_decl_info(Checker *c, Entity *e, AstType *type_expr, AstExpr *init_expr);
Entity *scope_lookup_entity(Scope *scope, String name);
Entity *current_scope_lookup_entity(Scope *scope, String name);
Entity *scope_insert_entity(Scope *s, Entity *e);

void add_entity(Checker *c, Entity *e);
void add_entity_use(Checker *c, AstExpr *ident, Entity *e);

void      add_expr_info   (Checker *c, AstExpr *expr, AddressingMode mode, Type *type, ConstValue value);
ExprInfo *get_expr_info   (Checker *c, AstExpr *expr);
void      update_expr_info(Checker *c, AstExpr *expr, ConstValue value);
void      remove_expr_info(Checker *c, AstExpr *expr);


void check_type_path_push(Checker *c, Entity *e);
Entity *check_type_path_pop(Checker *c);


char *type_expr_to_string(AstType *expr);
char *expr_to_string(AstExpr *expr);
char *type_to_string(Type *type);


#include "type.c"
