//! Ground values produced by constant evaluation.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use sal_core::types::TypeId;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Value {
    Bool(bool),
    Num(BigRational),
    /// Scalar element: type identity + element index.
    Scalar(TypeId, usize),
    /// Datatype value: type, constructor name, arguments.
    Data(TypeId, String, Vec<Value>),
    Tuple(Vec<Value>),
    /// Fields sorted by name.
    Record(Vec<(String, Value)>),
    /// Array/finite function value: element i corresponds to the i-th
    /// value of the index domain enumeration.
    Array(Vec<Value>),
}

impl Value {
    pub fn int(i: i64) -> Value {
        Value::Num(BigRational::from_integer(BigInt::from(i)))
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_num(&self) -> Option<&BigRational> {
        match self {
            Value::Num(n) => Some(n),
            _ => None,
        }
    }

    pub fn as_usize(&self) -> Option<usize> {
        match self {
            Value::Num(n) if n.is_integer() && !n.is_negative() => {
                n.to_integer().try_into().ok()
            }
            _ => None,
        }
    }

    pub fn as_bigint(&self) -> Option<BigInt> {
        match self {
            Value::Num(n) if n.is_integer() => Some(n.to_integer()),
            _ => None,
        }
    }

    pub fn is_integer(&self) -> bool {
        matches!(self, Value::Num(n) if n.is_integer())
    }

    pub fn num(n: BigRational) -> Value {
        Value::Num(n)
    }

    pub fn zero() -> Value {
        Value::Num(BigRational::zero())
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::Num(n) => {
                if n.is_integer() {
                    write!(f, "{}", n.to_integer())
                } else {
                    write!(f, "{}/{}", n.numer(), n.denom())
                }
            }
            Value::Scalar(_, i) => write!(f, "#{}", i),
            Value::Data(_, c, args) => {
                write!(f, "{}", c)?;
                if !args.is_empty() {
                    write!(f, "(")?;
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", a)?;
                    }
                    write!(f, ")")?;
                }
                Ok(())
            }
            Value::Tuple(vs) => {
                write!(f, "(")?;
                for (i, v) in vs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, ")")
            }
            Value::Record(fs) => {
                write!(f, "(# ")?;
                for (i, (n, v)) in fs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} := {}", n, v)?;
                }
                write!(f, " #)")
            }
            Value::Array(vs) => {
                write!(f, "[")?;
                for (i, v) in vs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
        }
    }
}
