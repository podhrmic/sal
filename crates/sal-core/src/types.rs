//! Semantic types. `sal-wfc` checks compatibility at the level of
//! *maximal supertypes* (the prelude models INTEGER/REAL/NATURAL/... as
//! predicate subtypes of one uninterpreted `number` type, and subranges
//! erase to `number` too). Scalars, datatypes and uninterpreted types are
//! nominal; everything else is structural.

use std::fmt;

/// Identity of a nominal type: the context instance it was declared in
/// plus its name.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeId {
    pub ctx: String,
    pub name: String,
}

impl fmt::Display for TypeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.ctx == "prelude" {
            write!(f, "{}", self.name)
        } else {
            write!(f, "{}!{}", self.ctx, self.name)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SemType {
    Bool,
    /// All numeric types after subtype erasure (REAL, INTEGER, NATURAL,
    /// subranges, ...).
    Number,
    /// Enumeration type; elements are recorded in the declaring symbol
    /// table.
    Scalar(TypeId),
    Datatype(TypeId),
    /// Uninterpreted type declaration or context type parameter.
    Uninterp(TypeId),
    Array(Box<SemType>, Box<SemType>),
    Fun(Box<SemType>, Box<SemType>),
    Tuple(Vec<SemType>),
    /// Fields sorted by name.
    Record(Vec<(String, SemType)>),
    /// State type of a module (coarse).
    State,
    /// Top type used by `=`/`/=` and to keep going after errors.
    Any,
}

impl SemType {
    /// Compatibility relation used by the type checker: types are
    /// compatible when their maximal supertypes are equal. `Any` is
    /// compatible with everything.
    pub fn compatible(&self, other: &SemType) -> bool {
        use SemType::*;
        match (self, other) {
            (Any, _) | (_, Any) => true,
            (Bool, Bool) => true,
            (Number, Number) => true,
            (Scalar(a), Scalar(b)) => a == b,
            (Datatype(a), Datatype(b)) => a == b,
            (Uninterp(a), Uninterp(b)) => a == b,
            (Array(i1, e1), Array(i2, e2)) => i1.compatible(i2) && e1.compatible(e2),
            (Fun(d1, r1), Fun(d2, r2)) => d1.compatible(d2) && r1.compatible(r2),
            // arrays are functions
            (Array(i, e), Fun(d, r)) | (Fun(d, r), Array(i, e)) => {
                i.compatible(d) && e.compatible(r)
            }
            (Tuple(a), Tuple(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.compatible(y))
            }
            (Record(a), Record(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b)
                        .all(|((n1, t1), (n2, t2))| n1 == n2 && t1.compatible(t2))
            }
            (State, State) => true,
            _ => false,
        }
    }
}

impl fmt::Display for SemType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SemType::*;
        match self {
            Bool => write!(f, "bool"),
            Number => write!(f, "number"),
            Scalar(id) | Datatype(id) | Uninterp(id) => write!(f, "{}", id),
            Array(i, e) => write!(f, "ARRAY {} OF {}", i, e),
            Fun(d, r) => write!(f, "[{} -> {}]", d, r),
            Tuple(ts) => {
                write!(f, "[")?;
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", t)?;
                }
                write!(f, "]")
            }
            Record(fs) => {
                write!(f, "[# ")?;
                for (i, (n, t)) in fs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", n, t)?;
                }
                write!(f, " #]")
            }
            State => write!(f, "STATE_TYPE"),
            Any => write!(f, "any"),
        }
    }
}
