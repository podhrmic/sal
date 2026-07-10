//! Concrete types with known structure, produced by resolving type ASTs
//! with all constants evaluated. Finite types can enumerate their values.

use num_bigint::BigInt;
use num_rational::BigRational;

use sal_core::types::TypeId;

use crate::value::Value;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CType {
    Bool,
    /// Finite integer range [lo, hi] (inclusive).
    Range(BigInt, BigInt),
    /// Unbounded integers (INTEGER, NATURAL — lower bounds tracked via
    /// `min`/`max` if one-sided).
    Int {
        min: Option<BigInt>,
        max: Option<BigInt>,
    },
    /// Mathematical reals (possibly predicate-constrained upstream).
    Real,
    /// Scalar (enumeration) type with element names; SCALARSET/RINGSET
    /// types enumerate `s0..s{n-1}` style names.
    Scalar(TypeId, std::rc::Rc<Vec<String>>),
    /// Non-recursive datatype: constructors with field types.
    Data(TypeId, std::rc::Rc<Vec<(String, Vec<CType>)>>),
    Array(Box<CType>, Box<CType>),
    /// Function type over a finite domain (treated like an array keyed by
    /// domain enumeration) or infinite domain (uninterpreted; rejected by
    /// finite engines).
    Fun(Box<CType>, Box<CType>),
    Tuple(Vec<CType>),
    /// Fields sorted by name.
    Record(Vec<(String, CType)>),
    /// Uninterpreted type (rejected by finite engines).
    Uninterp(TypeId),
}

impl CType {
    /// Number of values, if finite and reasonably sized.
    pub fn cardinality(&self) -> Option<u64> {
        match self {
            CType::Bool => Some(2),
            CType::Range(lo, hi) => {
                if hi < lo {
                    return Some(0);
                }
                let d = (hi - lo) + 1i32;
                u64::try_from(d).ok()
            }
            CType::Scalar(_, elems) => Some(elems.len() as u64),
            CType::Data(_, ctors) => {
                let mut total: u64 = 0;
                for (_, fields) in ctors.iter() {
                    let mut prod: u64 = 1;
                    for f in fields {
                        prod = prod.checked_mul(f.cardinality()?)?;
                    }
                    total = total.checked_add(prod)?;
                }
                Some(total)
            }
            CType::Array(i, e) | CType::Fun(i, e) => {
                let n = i.cardinality()?;
                e.cardinality()?.checked_pow(u32::try_from(n).ok()?)
            }
            CType::Tuple(ts) => {
                let mut prod: u64 = 1;
                for t in ts {
                    prod = prod.checked_mul(t.cardinality()?)?;
                }
                Some(prod)
            }
            CType::Record(fs) => {
                let mut prod: u64 = 1;
                for (_, t) in fs {
                    prod = prod.checked_mul(t.cardinality()?)?;
                }
                Some(prod)
            }
            CType::Int { .. } | CType::Real | CType::Uninterp(_) => None,
        }
    }

    pub fn is_finite(&self) -> bool {
        self.cardinality().is_some()
    }

    /// Enumerate all values of a finite type (index order defines the
    /// canonical value order used for array/function decomposition).
    pub fn enumerate(&self) -> Option<Vec<Value>> {
        match self {
            CType::Bool => Some(vec![Value::Bool(false), Value::Bool(true)]),
            CType::Range(lo, hi) => {
                let mut out = Vec::new();
                let mut i = lo.clone();
                while &i <= hi {
                    out.push(Value::Num(BigRational::from_integer(i.clone())));
                    i += 1;
                }
                Some(out)
            }
            CType::Scalar(id, elems) => Some(
                (0..elems.len())
                    .map(|i| Value::Scalar(id.clone(), i))
                    .collect(),
            ),
            CType::Data(id, ctors) => {
                let mut out = Vec::new();
                for (cname, fields) in ctors.iter() {
                    let mut args_enum: Vec<Vec<Value>> = vec![vec![]];
                    for f in fields {
                        let vs = f.enumerate()?;
                        let mut next = Vec::new();
                        for prefix in &args_enum {
                            for v in &vs {
                                let mut p = prefix.clone();
                                p.push(v.clone());
                                next.push(p);
                            }
                        }
                        args_enum = next;
                    }
                    for args in args_enum {
                        out.push(Value::Data(id.clone(), cname.clone(), args));
                    }
                }
                Some(out)
            }
            CType::Tuple(ts) => {
                let mut combos: Vec<Vec<Value>> = vec![vec![]];
                for t in ts {
                    let vs = t.enumerate()?;
                    let mut next = Vec::new();
                    for prefix in &combos {
                        for v in &vs {
                            let mut p = prefix.clone();
                            p.push(v.clone());
                            next.push(p);
                        }
                    }
                    combos = next;
                }
                Some(combos.into_iter().map(Value::Tuple).collect())
            }
            CType::Record(fs) => {
                let mut combos: Vec<Vec<(String, Value)>> = vec![vec![]];
                for (n, t) in fs {
                    let vs = t.enumerate()?;
                    let mut next = Vec::new();
                    for prefix in &combos {
                        for v in &vs {
                            let mut p = prefix.clone();
                            p.push((n.clone(), v.clone()));
                            next.push(p);
                        }
                    }
                    combos = next;
                }
                Some(combos.into_iter().map(Value::Record).collect())
            }
            CType::Array(i, e) | CType::Fun(i, e) => {
                let n = i.cardinality()? as usize;
                let ev = e.enumerate()?;
                let mut combos: Vec<Vec<Value>> = vec![vec![]];
                for _ in 0..n {
                    let mut next = Vec::new();
                    for prefix in &combos {
                        for v in &ev {
                            let mut p = prefix.clone();
                            p.push(v.clone());
                            next.push(p);
                        }
                    }
                    combos = next;
                }
                Some(combos.into_iter().map(Value::Array).collect())
            }
            CType::Int { .. } | CType::Real | CType::Uninterp(_) => None,
        }
    }

    /// Position of a value in the enumeration of this (finite) type.
    pub fn index_of(&self, v: &Value) -> Option<usize> {
        match (self, v) {
            (CType::Bool, Value::Bool(b)) => Some(usize::from(*b)),
            (CType::Range(lo, _), Value::Num(n)) if n.is_integer() => {
                let i = n.to_integer() - lo;
                usize::try_from(i).ok()
            }
            (CType::Scalar(..), Value::Scalar(_, i)) => Some(*i),
            _ => {
                // fall back to enumeration for structured values
                self.enumerate()?.iter().position(|x| x == v)
            }
        }
    }
}
