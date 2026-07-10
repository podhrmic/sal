//! Flattening of SAL modules into transition systems.
//!
//! The flattener elaborates a module expression into a `FlatModule`:
//! a set of *leaf* state variables (booleans, bounded integer ranges,
//! scalars, or unbounded numerics) plus initialization and transition
//! constraints expressed as `FExpr` trees over those leaves. Aggregate
//! values (tuples, records, finite arrays, finite functions) are
//! decomposed structurally; quantifiers over finite domains are expanded;
//! defined constants are inlined and evaluated.

pub mod ctype;
pub mod eval;
pub mod fexpr;
pub mod flatten;
pub mod formula;
pub mod sval;
pub mod value;

pub use ctype::CType;
pub use eval::Flattener;
pub use fexpr::{FExpr, LeafId, LeafInfo, LeafType};
pub use flatten::{FlatCmd, FlatModule, TransNode};
pub use formula::TFormula;
pub use value::Value;
