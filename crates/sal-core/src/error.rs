//! Error reporting in the oracle's format:
//!   parse errors:    `Error: [file.sal, line(L), column(C)] msg`
//!   semantic errors: `Error: [Context: name, line(L), column(C)]: msg`
//!   global errors:   `Error: msg`

use sal_syntax::span::Span;

#[derive(Debug, Clone)]
pub enum SalError {
    Parse {
        file: String,
        span: Span,
        msg: String,
    },
    Semantic {
        context: String,
        span: Span,
        msg: String,
    },
    Global(String),
}

impl SalError {
    pub fn semantic(context: &str, span: Span, msg: impl Into<String>) -> Self {
        SalError::Semantic {
            context: context.to_string(),
            span,
            msg: msg.into(),
        }
    }

    pub fn global(msg: impl Into<String>) -> Self {
        SalError::Global(msg.into())
    }
}

impl std::fmt::Display for SalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SalError::Parse { file, span, msg } => write!(
                f,
                "Error: [{}, line({}), column({})] {}",
                file, span.start.line, span.start.col, msg
            ),
            SalError::Semantic { context, span, msg } => write!(
                f,
                "Error: [Context: {}, line({}), column({})]: {}",
                context, span.start.line, span.start.col, msg
            ),
            SalError::Global(msg) => write!(f, "Error: {}", msg),
        }
    }
}

impl std::error::Error for SalError {}
