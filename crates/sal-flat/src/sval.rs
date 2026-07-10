//! Symbolic values: the domain of the flattening evaluator. A symbolic
//! value is either ground, a scalar-typed expression over leaf variables,
//! a structural aggregate of symbolic values, a function closure, or a
//! temporal formula (used only while lowering assertion formulas).

use std::collections::HashMap;
use std::rc::Rc;

use sal_core::env::Instance;

use crate::ctype::CType;
use crate::fexpr::{FExpr, LeafType};
use crate::formula::TFormula;
use crate::value::Value;

/// Evaluation environment: lexical bindings on top of a context instance.
#[derive(Clone)]
pub struct EvalCtx {
    pub inst: Rc<Instance>,
    pub locals: Rc<Frame>,
}

/// Immutable linked frames so closures can capture cheaply.
pub enum Frame {
    Nil,
    Cons(HashMap<String, SVal>, Rc<Frame>),
}

impl EvalCtx {
    pub fn new(inst: Rc<Instance>) -> Self {
        EvalCtx {
            inst,
            locals: Rc::new(Frame::Nil),
        }
    }

    pub fn bind(&self, vars: HashMap<String, SVal>) -> EvalCtx {
        EvalCtx {
            inst: self.inst.clone(),
            locals: Rc::new(Frame::Cons(vars, self.locals.clone())),
        }
    }

    pub fn bind1(&self, name: &str, v: SVal) -> EvalCtx {
        let mut m = HashMap::new();
        m.insert(name.to_string(), v);
        self.bind(m)
    }

    pub fn lookup(&self, name: &str) -> Option<SVal> {
        let mut f = &self.locals;
        loop {
            match f.as_ref() {
                Frame::Nil => return None,
                Frame::Cons(m, rest) => {
                    if let Some(v) = m.get(name) {
                        return Some(v.clone());
                    }
                    f = rest;
                }
            }
        }
    }

    pub fn with_inst(&self, inst: Rc<Instance>) -> EvalCtx {
        EvalCtx {
            inst,
            locals: Rc::new(Frame::Nil),
        }
    }
}

/// A function value: user lambda or builtin.
#[derive(Clone)]
pub enum Closure {
    /// Lambda: parameter names (flattened), body AST, captured env.
    Lambda {
        params: Vec<String>,
        body: Rc<sal_syntax::ast::Expr>,
        ctx: EvalCtx,
        /// Name of the defining constant for recursion display/limits.
        name: Option<String>,
    },
    /// Datatype constructor.
    Ctor {
        ty: sal_core::types::TypeId,
        name: String,
        arity: usize,
    },
    /// Datatype recognizer `c?`.
    Recognizer {
        ctor: String,
        /// The datatype's concrete type, for symbolic dispatch.
        dty: CType,
    },
    /// Datatype accessor.
    Accessor {
        ctor: String,
        field_idx: usize,
        dty: CType,
    },
    /// Ringset successor/predecessor.
    RingOp { succ: bool },
    /// Prelude builtin identified by name (min, max, G, F, ...).
    Builtin(String),
    /// An explicit finite map (used when a ground function value is
    /// applied symbolically).
    Table {
        index: CType,
        elems: Vec<SVal>,
    },
}

#[derive(Clone)]
pub enum SVal {
    Ground(Value),
    /// Scalar-typed symbolic expression.
    Sym(FExpr, LeafType),
    Tuple(Vec<SVal>),
    /// Fields sorted by name.
    Record(Vec<(String, SVal)>),
    /// Array/finite function decomposed over its index enumeration.
    Array(Box<CType>, Vec<SVal>),
    /// Symbolic datatype value: encoded over the enumeration of the
    /// datatype (used rarely; finite datatypes only).
    Fun(Rc<Closure>),
    /// Set value (for `IN` selections and set exprs).
    Set(Rc<SetRepr>),
    /// Temporal formula (only during assertion lowering).
    Formula(TFormula),
}

/// Representation of set values; membership is evaluated by the
/// Flattener.
pub enum SetRepr {
    /// `{x : T | pred}`
    Pred {
        ctx: EvalCtx,
        var: String,
        pred: sal_syntax::ast::Expr,
    },
    /// `{e1, e2, ...}` (already evaluated).
    List(Vec<SVal>),
    /// `up_to(n)` / `below(n)` / `above(n)` from the prelude.
    Bound { kind: BoundKind, bound: FExpr },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundKind {
    UpTo,
    Below,
    Above,
}

impl std::fmt::Debug for SVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SVal::Ground(v) => write!(f, "Ground({})", v),
            SVal::Sym(e, _) => write!(f, "Sym({:?})", e),
            SVal::Tuple(vs) => f.debug_tuple("Tuple").field(vs).finish(),
            SVal::Record(vs) => f.debug_tuple("Record").field(vs).finish(),
            SVal::Array(_, vs) => f.debug_tuple("Array").field(vs).finish(),
            SVal::Fun(_) => write!(f, "Fun(..)"),
            SVal::Set(_) => write!(f, "Set(..)"),
            SVal::Formula(t) => write!(f, "Formula({:?})", t),
        }
    }
}

impl SVal {
    pub fn tt() -> SVal {
        SVal::Ground(Value::Bool(true))
    }

    pub fn ff() -> SVal {
        SVal::Ground(Value::Bool(false))
    }

    pub fn from_bool_expr(e: FExpr) -> SVal {
        match e {
            FExpr::Const(v) => SVal::Ground(v),
            other => SVal::Sym(other, LeafType::Bool),
        }
    }

    /// Convert a boolean-typed symbolic value to an FExpr.
    pub fn to_bool_fexpr(&self) -> Result<FExpr, String> {
        match self {
            SVal::Ground(Value::Bool(b)) => Ok(FExpr::Const(Value::Bool(*b))),
            SVal::Sym(e, LeafType::Bool) => Ok(e.clone()),
            other => Err(format!("boolean expression expected, found {:?}", other)),
        }
    }

    /// Convert to a scalar FExpr when this is a scalar-typed value.
    pub fn to_scalar_fexpr(&self) -> Option<(FExpr, LeafType)> {
        match self {
            SVal::Ground(Value::Bool(_)) => {
                Some((self.as_fexpr_const()?, LeafType::Bool))
            }
            SVal::Ground(Value::Num(_)) => Some((self.as_fexpr_const()?, LeafType::Int)),
            SVal::Ground(Value::Scalar(id, _)) => Some((
                self.as_fexpr_const()?,
                // element list unknown here; callers only need the id for
                // equality, so use an empty list placeholder
                LeafType::Scalar(id.clone(), Rc::new(Vec::new())),
            )),
            SVal::Sym(e, t) => Some((e.clone(), t.clone())),
            _ => None,
        }
    }

    fn as_fexpr_const(&self) -> Option<FExpr> {
        match self {
            SVal::Ground(v) => Some(FExpr::Const(v.clone())),
            _ => None,
        }
    }

    /// Structural equality as a boolean symbolic value.
    pub fn eq_sval(&self, other: &SVal) -> Result<FExpr, String> {
        match (self, other) {
            (SVal::Ground(a), SVal::Ground(b)) => {
                Ok(FExpr::Const(Value::Bool(a == b)))
            }
            (SVal::Tuple(a), SVal::Tuple(b)) => {
                if a.len() != b.len() {
                    return Err("tuple arity mismatch in equality".into());
                }
                let mut cs = Vec::new();
                for (x, y) in a.iter().zip(b) {
                    cs.push(x.eq_sval(y)?);
                }
                Ok(FExpr::and(cs))
            }
            (SVal::Record(a), SVal::Record(b)) => {
                if a.len() != b.len() {
                    return Err("record shape mismatch in equality".into());
                }
                let mut cs = Vec::new();
                for ((n1, x), (n2, y)) in a.iter().zip(b) {
                    if n1 != n2 {
                        return Err("record shape mismatch in equality".into());
                    }
                    cs.push(x.eq_sval(y)?);
                }
                Ok(FExpr::and(cs))
            }
            (SVal::Array(_, a), SVal::Array(_, b)) => {
                if a.len() != b.len() {
                    return Err("array size mismatch in equality".into());
                }
                let mut cs = Vec::new();
                for (x, y) in a.iter().zip(b) {
                    cs.push(x.eq_sval(y)?);
                }
                Ok(FExpr::and(cs))
            }
            _ => {
                // scalar-level equality (possibly mixing ground/symbolic)
                let (ea, _) = self
                    .to_scalar_fexpr()
                    .ok_or_else(|| format!("cannot compare {:?} and {:?}", self, other))?;
                let (eb, _) = other
                    .to_scalar_fexpr()
                    .ok_or_else(|| format!("cannot compare {:?} and {:?}", self, other))?;
                Ok(FExpr::eq(ea, eb))
            }
        }
    }

    /// Merge two structurally identical values under a symbolic condition.
    pub fn ite(cond: &FExpr, t: &SVal, e: &SVal) -> Result<SVal, String> {
        if cond.is_true() {
            return Ok(t.clone());
        }
        if cond.is_false() {
            return Ok(e.clone());
        }
        match (t, e) {
            (SVal::Tuple(a), SVal::Tuple(b)) if a.len() == b.len() => Ok(SVal::Tuple(
                a.iter()
                    .zip(b)
                    .map(|(x, y)| SVal::ite(cond, x, y))
                    .collect::<Result<_, _>>()?,
            )),
            (SVal::Record(a), SVal::Record(b)) if a.len() == b.len() => Ok(SVal::Record(
                a.iter()
                    .zip(b)
                    .map(|((n, x), (_, y))| Ok((n.clone(), SVal::ite(cond, x, y)?)))
                    .collect::<Result<_, String>>()?,
            )),
            (SVal::Array(it, a), SVal::Array(_, b)) if a.len() == b.len() => Ok(SVal::Array(
                it.clone(),
                a.iter()
                    .zip(b)
                    .map(|(x, y)| SVal::ite(cond, x, y))
                    .collect::<Result<_, _>>()?,
            )),
            (SVal::Formula(a), SVal::Formula(b)) => Ok(SVal::Formula(TFormula::ite(
                TFormula::Atom(cond.clone()),
                a.clone(),
                b.clone(),
            ))),
            _ => {
                let (ta, tta) = t
                    .to_scalar_fexpr()
                    .ok_or_else(|| format!("cannot merge {:?} / {:?}", t, e))?;
                let (eb, _) = e
                    .to_scalar_fexpr()
                    .ok_or_else(|| format!("cannot merge {:?} / {:?}", t, e))?;
                Ok(SVal::Sym(FExpr::ite(cond.clone(), ta, eb), tta))
            }
        }
    }

    /// Map every leaf `Var(l, primed)` through `f`.
    pub fn map_leaves(&self, f: &impl Fn(&FExpr) -> FExpr) -> SVal {
        match self {
            SVal::Ground(_) => self.clone(),
            SVal::Sym(e, t) => SVal::Sym(map_fexpr(e, f), t.clone()),
            SVal::Tuple(vs) => SVal::Tuple(vs.iter().map(|v| v.map_leaves(f)).collect()),
            SVal::Record(vs) => SVal::Record(
                vs.iter()
                    .map(|(n, v)| (n.clone(), v.map_leaves(f)))
                    .collect(),
            ),
            SVal::Array(it, vs) => SVal::Array(
                it.clone(),
                vs.iter().map(|v| v.map_leaves(f)).collect(),
            ),
            other => other.clone(),
        }
    }
}

pub fn map_fexpr(e: &FExpr, f: &impl Fn(&FExpr) -> FExpr) -> FExpr {
    match e {
        FExpr::Var(..) => f(e),
        FExpr::Const(_) => e.clone(),
        FExpr::Not(a) => FExpr::not(map_fexpr(a, f)),
        FExpr::Neg(a) => FExpr::Neg(Rc::new(map_fexpr(a, f))),
        FExpr::And(es) => FExpr::and(es.iter().map(|x| map_fexpr(x, f)).collect()),
        FExpr::Or(es) => FExpr::or(es.iter().map(|x| map_fexpr(x, f)).collect()),
        FExpr::Add(es) => FExpr::Add(es.iter().map(|x| map_fexpr(x, f)).collect()),
        FExpr::Mul(es) => FExpr::Mul(es.iter().map(|x| map_fexpr(x, f)).collect()),
        FExpr::Ite(a, b, c) => FExpr::ite(map_fexpr(a, f), map_fexpr(b, f), map_fexpr(c, f)),
        FExpr::Eq(a, b) => FExpr::eq(map_fexpr(a, f), map_fexpr(b, f)),
        FExpr::Lt(a, b) => FExpr::Lt(Rc::new(map_fexpr(a, f)), Rc::new(map_fexpr(b, f))),
        FExpr::Le(a, b) => FExpr::Le(Rc::new(map_fexpr(a, f)), Rc::new(map_fexpr(b, f))),
        FExpr::Div(a, b) => FExpr::Div(Rc::new(map_fexpr(a, f)), Rc::new(map_fexpr(b, f))),
        FExpr::IDiv(a, b) => FExpr::IDiv(Rc::new(map_fexpr(a, f)), Rc::new(map_fexpr(b, f))),
        FExpr::Mod(a, b) => FExpr::Mod(Rc::new(map_fexpr(a, f)), Rc::new(map_fexpr(b, f))),
    }
}

/// Replace current-state leaves with primed leaves.
pub fn prime(e: &FExpr) -> FExpr {
    map_fexpr(e, &|v| match v {
        FExpr::Var(l, false) => FExpr::Var(*l, true),
        other => other.clone(),
    })
}
