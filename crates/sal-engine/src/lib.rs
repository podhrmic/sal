//! Model-checking engines over flat SAL transition systems.

pub mod explicit;

pub use explicit::{CheckResult, Explicit, Path, State};
