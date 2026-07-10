//! Lexer, parser, AST and pretty-printer for the SAL 3.3 language.
//!
//! The concrete syntax implemented here follows the *behavior of the
//! SAL 3.3 implementation* (`sal-parser.scm`), which deviates from the
//! language manual in several places; see `docs/grammar-notes.md` at the
//! repository root for the list of deviations.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod printer;
pub mod span;
pub mod token;

pub use parser::{parse_context, parse_expr, parse_module, ParseError};
