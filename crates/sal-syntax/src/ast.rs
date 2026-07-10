//! Abstract syntax for SAL 3.3, mirroring the node structure the oracle's
//! parser produces (SXML tags in `sal-parser.scm`).

use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

/// `ctx` or `ctx{actual, ...}` — a reference to a (possibly instantiated)
/// context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextName {
    pub name: Ident,
    /// Kind (type vs. expression) of each actual is resolved later against
    /// the referenced context's parameter list.
    pub actuals: Vec<Actual>,
    pub span: Span,
}

/// A context actual parameter: disambiguated during name resolution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Actual {
    Expr(Expr),
    Type(Type),
}

/// `name` or `ctx!name` or `ctx{actuals}!name`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Name {
    pub ctx: Option<ContextName>,
    pub id: Ident,
    pub span: Span,
}

// ---------------------------------------------------------------------------
// Contexts and declarations
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SalContext {
    pub name: Ident,
    pub params: Vec<CtxParam>,
    pub decls: Vec<Decl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CtxParam {
    /// `T1, T2 : TYPE`
    Types(Vec<Ident>),
    /// `x, y : T`
    Vars(Vec<Ident>, Type),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    /// `t : TYPE [= typedef]`
    Type {
        name: Ident,
        def: Option<TypeDef>,
    },
    /// `c [(args)] : T [= expr]` — function sugar is kept: `args` non-empty
    /// means the declared type is `[domain -> T]` and the value (if any) is
    /// a lambda.
    Constant {
        name: Ident,
        args: Vec<VarDecl>,
        ty: Type,
        value: Option<Expr>,
    },
    /// `c : CONTEXT = ctx{actuals}`
    Context { name: Ident, ctx: ContextName },
    /// `m [vardecls] : MODULE = module`
    Module {
        name: Ident,
        params: Vec<VarDecl>,
        body: Module,
    },
    /// `a : THEOREM assertion`
    Assertion {
        name: Ident,
        form: AssertionForm,
        body: AssertionExpr,
    },
    /// `IMPORTING ctx [WITH a TO b, ...]`
    Import {
        ctx: ContextName,
        renames: Vec<(Ident, Ident)>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssertionForm {
    Obligation,
    Claim,
    Lemma,
    Theorem,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssertionExpr {
    /// `module |- expr`
    Models { module: Module, formula: Expr },
    /// `module IMPLEMENTS module`
    Implements { concrete: Module, abstract_: Module },
}

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeDef {
    Type(Type),
    /// `{a, b, c}`
    Scalar(Vec<Ident>),
    /// `DATATYPE cons(car: T, cdr: t), nil END`
    Datatype(Vec<Constructor>),
    /// `SCALARSET(expr)`
    Scalarset(Expr),
    /// `RINGSET(expr)`
    Ringset(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub name: Ident,
    pub accessors: Vec<VarDecl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    /// Type name, possibly qualified (`ctx{...}!t`). Builtins (BOOLEAN,
    /// INTEGER, ...) are just names resolved against the prelude.
    Name(Name),
    /// `[lo .. hi]`
    Subrange(Box<Expr>, Box<Expr>),
    /// `{x : T | pred}`
    Subtype(Box<SetPred>),
    /// `ARRAY idx OF elem`
    Array(Box<Type>, Box<Type>),
    /// `[T1, T2, ...]` (2+ components)
    Tuple(Vec<Type>),
    /// `[dom -> rng]` (unary domain only, per the oracle)
    Function(Box<Type>, Box<Type>),
    /// `[# f1: T1, ... #]`
    Record(Vec<FieldDecl>),
    /// `STATE_TYPE(module)`
    State(Box<Module>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldDecl {
    pub name: Ident,
    pub ty: Type,
}

/// `{x : T | e}` — used both as a set expression and as a subtype.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetPred {
    pub var: Ident,
    pub ty: Type,
    pub pred: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarDecl {
    pub names: Vec<Ident>,
    pub ty: Type,
    pub span: Span,
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    /// Number of explicit parentheses around this node (printer fidelity;
    /// the oracle records PARENS the same way).
    pub parens: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Iff,
    Implies,
    Or,
    Xor,
    And,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Mult,
    Div,
    IDiv,
    Mod,
}

impl BinOp {
    /// Operator name as it appears in the prelude (application head).
    pub fn name(self) -> &'static str {
        match self {
            BinOp::Iff => "<=>",
            BinOp::Implies => "=>",
            BinOp::Or => "OR",
            BinOp::Xor => "XOR",
            BinOp::And => "AND",
            BinOp::Eq => "=",
            BinOp::Neq => "/=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::Plus => "+",
            BinOp::Minus => "-",
            BinOp::Mult => "*",
            BinOp::Div => "/",
            BinOp::IDiv => "DIV",
            BinOp::Mod => "MOD",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    Minus,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    /// Name or qualified name.
    Name(Name),
    /// `x'`
    Next(Ident),
    /// Integer literal (decimal).
    Numeral(String),
    /// `n.d` float literal, represented as numerator/denominator strings
    /// (the oracle turns `1.25` into `125/100`).
    Float { numer: String, denom: String },
    /// String literal (rare; used by some tools).
    Str(String),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
    /// `f(a, b)` — multiple arguments form an implicit tuple.
    App(Box<Expr>, Vec<Expr>),
    /// `a[i]`
    ArraySelect(Box<Expr>, Box<Expr>),
    /// `r.field`
    RecordSelect(Box<Expr>, Ident),
    /// `t.2`
    TupleSelect(Box<Expr>, u32),
    /// `e WITH access+ := v`
    Update {
        target: Box<Expr>,
        accesses: Vec<Access>,
        value: Box<Expr>,
    },
    /// `LAMBDA (decls) : e`
    Lambda(Vec<VarDecl>, Box<Expr>),
    /// `FORALL/EXISTS (decls) : e`
    Quantified(Quantifier, Vec<VarDecl>, Box<Expr>),
    /// `LET x : T = e, ... IN body`
    Let(Vec<LetDecl>, Box<Expr>),
    /// `{x : T | e}`
    SetPred(Box<SetPred>),
    /// `{e1, e2, ...}`
    SetList(Vec<Expr>),
    /// `[[i : T] e]`
    ArrayLit(Box<VarDecl>, Box<Expr>),
    /// `(# f := e, ... #)`
    RecordLit(Vec<(Ident, Expr)>),
    /// `(e1, e2, ...)`
    TupleLit(Vec<Expr>),
    /// `IF c THEN a [ELSIF ...] ELSE b ENDIF` (elsifs desugared to nested
    /// conditionals, marked so the printer can reconstruct them).
    Conditional {
        cond: Box<Expr>,
        then: Box<Expr>,
        els: Box<Expr>,
        is_elsif: bool,
    },
    /// `INIT_PRED(module)` / `TRANS_PRED(module)`
    ModInit(Box<Module>),
    ModTrans(Box<Module>),
    /// `_` (unbounded)
    Unbounded,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quantifier {
    Forall,
    Exists,
}

/// One step in an update/lhs access path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Access {
    /// `[e]`
    Array(Expr),
    /// `.field`
    Record(Ident),
    /// `.2`
    Tuple(u32),
    /// `(args)` — function-position update.
    Args(Vec<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetDecl {
    pub name: Ident,
    pub ty: Type,
    pub value: Expr,
}

// ---------------------------------------------------------------------------
// Modules and transition language
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    pub kind: ModuleKind,
    pub span: Span,
    pub parens: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleKind {
    /// `name[actuals]` — module instance (actuals in square brackets).
    Instance(Name, Vec<Expr>),
    /// `m1 || m2`
    Sync(Box<Module>, Box<Module>),
    /// `m1 [] m2`
    Async(Box<Module>, Box<Module>),
    /// `(|| (i : T) : m)`
    MultiSync(Box<VarDecl>, Box<Module>),
    /// `([] (i : T) : m)`
    MultiAsync(Box<VarDecl>, Box<Module>),
    /// `LOCAL x, y IN m`
    Hide(Vec<Ident>, Box<Module>),
    /// `OUTPUT x, y IN m`
    NewOutput(Vec<Ident>, Box<Module>),
    /// `RENAME a TO b, ... IN m` (lhs paths allowed)
    Rename(Vec<(Lhs, Lhs)>, Box<Module>),
    /// `WITH decls m`
    With(Vec<NewVarDecl>, Box<Module>),
    /// `OBSERVE m1 WITH m2`
    Observe(Box<Module>, Box<Module>),
    Base(BaseModule),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NewVarDecl {
    pub class: VarClass,
    pub decls: Vec<VarDecl>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VarClass {
    Input,
    Output,
    Global,
    Local,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BaseModule {
    pub decls: Vec<BaseDecl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BaseDecl {
    Vars(VarClass, Vec<VarDecl>),
    Definition(Vec<Definition>),
    Initialization(Vec<DefOrCommand>),
    Transition(Vec<DefOrCommand>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Definition {
    Simple(SimpleDefinition),
    /// `(FORALL (decls) : defs)`
    Forall(Vec<VarDecl>, Vec<Definition>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpleDefinition {
    pub lhs: Lhs,
    pub rhs: Rhs,
    pub span: Span,
}

/// `x['] access*`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lhs {
    pub base: Ident,
    pub next: bool,
    pub accesses: Vec<Access>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rhs {
    /// `= e`
    Expr(Expr),
    /// `IN e` (nondeterministic selection from a set)
    Selection(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefOrCommand {
    Def(Definition),
    /// `[ cmd [] cmd [] ... ]`
    Commands(Vec<SomeCommand>, Span),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SomeCommand {
    Guarded(GuardedCommand),
    /// `([] (i : T) : cmd)`
    Multi(Vec<VarDecl>, Box<SomeCommand>, Span),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuardedCommand {
    pub label: Option<Ident>,
    /// `None` for ELSE commands.
    pub guard: Option<Expr>,
    pub assignments: Vec<Definition>,
    pub span: Span,
}
