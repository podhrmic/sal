//! Model-checking engines over flat SAL transition systems.

pub mod bdd;
pub mod bmc;
pub mod bounded;
pub mod explicit;
pub mod ltl;
pub mod ordering;
pub mod smt;
pub mod symbolic;

pub use explicit::{CheckResult, Explicit, Path, State};
