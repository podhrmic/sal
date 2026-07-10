//! Semantic layer for SAL 3.3: context environment (loading and
//! instantiation), name resolution, and type checking (the `sal-wfc`
//! analysis).

pub mod env;
pub mod error;
pub mod prelude;
pub mod types;
pub mod wfc;

pub use env::SalEnv;
pub use error::SalError;
