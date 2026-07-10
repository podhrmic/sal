//! Model-checking engines over flat SAL transition systems.

pub mod bdd;
pub mod explicit;
pub mod ltl;
pub mod symbolic;

pub use explicit::{CheckResult, Explicit, Path, State};
