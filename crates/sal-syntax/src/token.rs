//! Token definitions mirroring the oracle's lexer (`*sal-lexer*`).

use crate::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Tok {
    // literals & names
    Identifier,
    Numeral,
    Str,
    // punctuation
    LParen,    // (
    RParen,    // )
    LBrack,    // [
    RBrack,    // ]
    LBrace,    // {
    RBrace,    // }
    RecTypeS,  // [#
    RecTypeE,  // #]
    RecLitS,   // (#
    RecLitE,   // #)
    Dot,       // .
    Comma,     // ,
    Colon,     // :
    Semi,      // ;
    Bang,      // !
    VBar,      // |
    Assign,    // :=
    DotDot,    // ..
    Eq,        // =
    Neq,       // /=
    Implies,   // =>
    Iff,       // <=>
    Lt,        // <
    Le,        // <=
    Gt,        // >
    Ge,        // >=
    Plus,      // +
    Minus,     // -
    Mult,      // *
    Div,       // /
    Arrow,     // ->
    LongArrow, // -->
    Sync,      // ||
    Async,     // [] (only when lexed adjacently)
    Turnstile, // |-
    Unbounded, // _
    Quote,     // '
    // word operators (exact-case lower or upper only)
    And,
    Or,
    Not,
    Xor,
    IDiv, // DIV / div
    Mod,  // MOD / mod
    // keywords (case-insensitive)
    Type,
    Array,
    Of,
    With,
    Lambda,
    Forall,
    Exists,
    Let,
    In,
    If,
    Then,
    Else,
    Elsif,
    Endif,
    Begin,
    End,
    Rename,
    To,
    Context,
    Module,
    Input,
    Output,
    Global,
    Local,
    Initialization,
    Definition,
    Transition,
    Theorem,
    Lemma,
    Claim,
    Obligation,
    Observe,
    Implements,
    Datatype,
    StateType,
    InitPred,
    TransPred,
    Scalarset,
    Ringset,
    Importing,
    Suffix,
    Prefix,
    Eof,
}

/// Case-insensitive keyword table (the oracle upcases and looks up).
pub fn keyword(upper: &str) -> Option<Tok> {
    Some(match upper {
        "TYPE" => Tok::Type,
        "ARRAY" => Tok::Array,
        "OF" => Tok::Of,
        "WITH" => Tok::With,
        "LAMBDA" => Tok::Lambda,
        "FORALL" => Tok::Forall,
        "EXISTS" => Tok::Exists,
        "LET" => Tok::Let,
        "IN" => Tok::In,
        "IF" => Tok::If,
        "THEN" => Tok::Then,
        "ELSE" => Tok::Else,
        "ELSIF" => Tok::Elsif,
        "ENDIF" => Tok::Endif,
        "BEGIN" => Tok::Begin,
        "END" => Tok::End,
        "RENAME" => Tok::Rename,
        "TO" => Tok::To,
        "CONTEXT" => Tok::Context,
        "MODULE" => Tok::Module,
        "INPUT" => Tok::Input,
        "OUTPUT" => Tok::Output,
        "GLOBAL" => Tok::Global,
        "LOCAL" => Tok::Local,
        "INITIALIZATION" => Tok::Initialization,
        "DEFINITION" => Tok::Definition,
        "TRANSITION" => Tok::Transition,
        "THEOREM" => Tok::Theorem,
        "LEMMA" => Tok::Lemma,
        "CLAIM" => Tok::Claim,
        "OBLIGATION" => Tok::Obligation,
        "OBSERVE" => Tok::Observe,
        "IMPLEMENTS" => Tok::Implements,
        "DATATYPE" => Tok::Datatype,
        "STATE_TYPE" => Tok::StateType,
        "INIT_PRED" => Tok::InitPred,
        "TRANS_PRED" => Tok::TransPred,
        "SCALARSET" => Tok::Scalarset,
        "RINGSET" => Tok::Ringset,
        "IMPORTING" => Tok::Importing,
        "SUFFIX" => Tok::Suffix,
        "PREFIX" => Tok::Prefix,
        _ => return None,
    })
}

/// Word operators recognized only in exact lower or exact upper case.
pub fn word_operator(text: &str) -> Option<Tok> {
    Some(match text {
        "and" | "AND" => Tok::And,
        "or" | "OR" => Tok::Or,
        "not" | "NOT" => Tok::Not,
        "xor" | "XOR" => Tok::Xor,
        "div" | "DIV" => Tok::IDiv,
        "mod" | "MOD" => Tok::Mod,
        _ => return None,
    })
}

#[derive(Debug, Clone)]
pub struct Token {
    pub tok: Tok,
    /// Source text (numeral value normalized to decimal for hex/binary).
    pub text: String,
    pub span: Span,
}
