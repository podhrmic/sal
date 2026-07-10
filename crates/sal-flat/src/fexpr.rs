//! Flat expressions over leaf state variables.

use std::rc::Rc;

use num_rational::BigRational;

use sal_core::types::TypeId;

use crate::ctype::CType;
use crate::value::Value;

/// Index into the flat module's leaf table.
pub type LeafId = u32;

/// The scalar type of a leaf variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeafType {
    Bool,
    Range(num_bigint::BigInt, num_bigint::BigInt),
    Int,
    Real,
    Scalar(TypeId, Rc<Vec<String>>),
}

impl LeafType {
    pub fn from_ctype(t: &CType) -> Option<LeafType> {
        Some(match t {
            CType::Bool => LeafType::Bool,
            CType::Range(lo, hi) => LeafType::Range(lo.clone(), hi.clone()),
            CType::Int { .. } => LeafType::Int,
            CType::Real => LeafType::Real,
            CType::Scalar(id, elems) => LeafType::Scalar(id.clone(), elems.clone()),
            _ => return None,
        })
    }

    pub fn cardinality(&self) -> Option<u64> {
        match self {
            LeafType::Bool => Some(2),
            LeafType::Range(lo, hi) => {
                if hi < lo {
                    Some(0)
                } else {
                    u64::try_from((hi - lo) + 1i32).ok()
                }
            }
            LeafType::Scalar(_, e) => Some(e.len() as u64),
            _ => None,
        }
    }

    pub fn values(&self) -> Option<Vec<Value>> {
        match self {
            LeafType::Bool => Some(vec![Value::Bool(false), Value::Bool(true)]),
            LeafType::Range(lo, hi) => {
                let mut out = Vec::new();
                let mut i = lo.clone();
                while &i <= hi {
                    out.push(Value::Num(BigRational::from_integer(i.clone())));
                    i += 1;
                }
                Some(out)
            }
            LeafType::Scalar(id, elems) => Some(
                (0..elems.len())
                    .map(|i| Value::Scalar(id.clone(), i))
                    .collect(),
            ),
            _ => None,
        }
    }
}

/// Metadata for one leaf variable.
#[derive(Debug, Clone)]
pub struct LeafInfo {
    /// Display path, e.g. `pc[1].phase`.
    pub name: String,
    pub ty: LeafType,
    /// Variable class of the root state variable.
    pub class: sal_syntax::ast::VarClass,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FExpr {
    Const(Value),
    /// Leaf variable; `primed` = next-state.
    Var(LeafId, bool),
    Not(Rc<FExpr>),
    And(Vec<FExpr>),
    Or(Vec<FExpr>),
    Ite(Rc<FExpr>, Rc<FExpr>, Rc<FExpr>),
    /// Equality between two scalar-leaf-typed expressions.
    Eq(Rc<FExpr>, Rc<FExpr>),
    Lt(Rc<FExpr>, Rc<FExpr>),
    Le(Rc<FExpr>, Rc<FExpr>),
    Add(Vec<FExpr>),
    Mul(Vec<FExpr>),
    Neg(Rc<FExpr>),
    /// Division (rational).
    Div(Rc<FExpr>, Rc<FExpr>),
    /// Integer division / modulo.
    IDiv(Rc<FExpr>, Rc<FExpr>),
    Mod(Rc<FExpr>, Rc<FExpr>),
}

impl FExpr {
    pub fn tt() -> FExpr {
        FExpr::Const(Value::Bool(true))
    }

    pub fn ff() -> FExpr {
        FExpr::Const(Value::Bool(false))
    }

    pub fn is_true(&self) -> bool {
        matches!(self, FExpr::Const(Value::Bool(true)))
    }

    pub fn is_false(&self) -> bool {
        matches!(self, FExpr::Const(Value::Bool(false)))
    }

    pub fn not(e: FExpr) -> FExpr {
        match e {
            FExpr::Const(Value::Bool(b)) => FExpr::Const(Value::Bool(!b)),
            FExpr::Not(inner) => (*inner).clone(),
            other => FExpr::Not(Rc::new(other)),
        }
    }

    pub fn and(es: Vec<FExpr>) -> FExpr {
        let mut out = Vec::new();
        for e in es {
            if e.is_false() {
                return FExpr::ff();
            }
            if e.is_true() {
                continue;
            }
            if let FExpr::And(inner) = e {
                out.extend(inner);
            } else {
                out.push(e);
            }
        }
        match out.len() {
            0 => FExpr::tt(),
            1 => out.pop().unwrap(),
            _ => FExpr::And(out),
        }
    }

    pub fn or(es: Vec<FExpr>) -> FExpr {
        let mut out = Vec::new();
        for e in es {
            if e.is_true() {
                return FExpr::tt();
            }
            if e.is_false() {
                continue;
            }
            if let FExpr::Or(inner) = e {
                out.extend(inner);
            } else {
                out.push(e);
            }
        }
        match out.len() {
            0 => FExpr::ff(),
            1 => out.pop().unwrap(),
            _ => FExpr::Or(out),
        }
    }

    pub fn ite(c: FExpr, t: FExpr, e: FExpr) -> FExpr {
        if c.is_true() {
            return t;
        }
        if c.is_false() {
            return e;
        }
        if t == e {
            return t;
        }
        FExpr::Ite(Rc::new(c), Rc::new(t), Rc::new(e))
    }

    pub fn eq(a: FExpr, b: FExpr) -> FExpr {
        if let (FExpr::Const(x), FExpr::Const(y)) = (&a, &b) {
            return FExpr::Const(Value::Bool(x == y));
        }
        if a == b {
            return FExpr::tt();
        }
        FExpr::Eq(Rc::new(a), Rc::new(b))
    }

    /// Collect all leaves used, into `cur` and `next` sets.
    pub fn leaves(&self, cur: &mut std::collections::BTreeSet<LeafId>, next: &mut std::collections::BTreeSet<LeafId>) {
        match self {
            FExpr::Const(_) => {}
            FExpr::Var(l, primed) => {
                if *primed {
                    next.insert(*l);
                } else {
                    cur.insert(*l);
                }
            }
            FExpr::Not(a) | FExpr::Neg(a) => a.leaves(cur, next),
            FExpr::And(es) | FExpr::Or(es) | FExpr::Add(es) | FExpr::Mul(es) => {
                for e in es {
                    e.leaves(cur, next);
                }
            }
            FExpr::Ite(a, b, c) => {
                a.leaves(cur, next);
                b.leaves(cur, next);
                c.leaves(cur, next);
            }
            FExpr::Eq(a, b)
            | FExpr::Lt(a, b)
            | FExpr::Le(a, b)
            | FExpr::Div(a, b)
            | FExpr::IDiv(a, b)
            | FExpr::Mod(a, b) => {
                a.leaves(cur, next);
                b.leaves(cur, next);
            }
        }
    }
}
