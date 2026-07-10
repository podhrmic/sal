//! Lexer for the SAL 3.3 concrete syntax, mirroring `*sal-lexer*` in the
//! oracle. Longest-match; keywords case-insensitive; word operators
//! (AND/OR/NOT/XOR/DIV/MOD) exact lower/upper case only; opchar
//! identifiers must start with one of `$ & @ ^ ~`.

use crate::span::{Pos, Span};
use crate::token::{keyword, word_operator, Tok, Token};
use num_bigint::BigUint;

#[derive(Debug, Clone)]
pub struct LexError {
    pub pos: Pos,
    pub msg: String,
}

pub struct Lexer<'a> {
    src: &'a [u8],
    off: usize,
    line: u32,
    col: u32,
}

fn is_ident_start(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_'
}

fn is_ident_cont(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'?' || c == b'_'
}

/// opchar1 in the oracle: chars that may start an operator identifier.
fn is_opchar1(c: u8) -> bool {
    matches!(c, b'$' | b'&' | b'@' | b'^' | b'~')
}

/// opchar: anything that is not alnum, one of `()[]{}%,.:;#\!?_|`,
/// or whitespace.
fn is_opchar(c: u8) -> bool {
    !(c.is_ascii_alphanumeric()
        || matches!(
            c,
            b'(' | b')'
                | b'['
                | b']'
                | b'{'
                | b'}'
                | b'%'
                | b','
                | b'.'
                | b':'
                | b';'
                | b'#'
                | b'\\'
                | b'!'
                | b'?'
                | b'_'
                | b'|'
                | b' '
                | b'\t'
                | b'\n'
                | b'\r'
        ))
        && c.is_ascii()
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Lexer {
            src: src.as_bytes(),
            off: 0,
            line: 1,
            col: 0,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.src.get(self.off).copied()
    }

    fn peek_at(&self, k: usize) -> Option<u8> {
        self.src.get(self.off + k).copied()
    }

    fn pos(&self) -> Pos {
        Pos::new(self.line, self.col)
    }

    fn bump(&mut self) -> Option<u8> {
        let c = self.peek()?;
        self.off += 1;
        if c == b'\n' {
            self.line += 1;
            self.col = 0;
        } else {
            self.col += 1;
        }
        Some(c)
    }

    fn bump_n(&mut self, n: usize) {
        for _ in 0..n {
            self.bump();
        }
    }

    fn skip_trivia(&mut self) {
        loop {
            match self.peek() {
                Some(b' ') | Some(b'\t') | Some(b'\n') | Some(b'\r') | Some(0x0c) => {
                    self.bump();
                }
                Some(b'%') => {
                    while let Some(c) = self.peek() {
                        if c == b'\n' {
                            break;
                        }
                        self.bump();
                    }
                }
                _ => break,
            }
        }
    }

    fn token(&self, tok: Tok, text: impl Into<String>, start: Pos) -> Token {
        Token {
            tok,
            text: text.into(),
            span: Span::new(start, self.pos()),
        }
    }

    pub fn tokenize(mut self) -> Result<Vec<Token>, LexError> {
        let mut out = Vec::new();
        loop {
            self.skip_trivia();
            let start = self.pos();
            let Some(c) = self.peek() else {
                out.push(self.token(Tok::Eof, "", start));
                return Ok(out);
            };
            let t = match c {
                b'"' => self.lex_string(start)?,
                b'(' => {
                    if self.peek_at(1) == Some(b'#') {
                        self.bump_n(2);
                        self.token(Tok::RecLitS, "(#", start)
                    } else {
                        self.bump();
                        self.token(Tok::LParen, "(", start)
                    }
                }
                b')' => {
                    self.bump();
                    self.token(Tok::RParen, ")", start)
                }
                b'[' => {
                    if self.peek_at(1) == Some(b'#') {
                        self.bump_n(2);
                        self.token(Tok::RecTypeS, "[#", start)
                    } else if self.peek_at(1) == Some(b']') {
                        self.bump_n(2);
                        self.token(Tok::Async, "[]", start)
                    } else {
                        self.bump();
                        self.token(Tok::LBrack, "[", start)
                    }
                }
                b']' => {
                    self.bump();
                    self.token(Tok::RBrack, "]", start)
                }
                b'#' => {
                    if self.peek_at(1) == Some(b']') {
                        self.bump_n(2);
                        self.token(Tok::RecTypeE, "#]", start)
                    } else if self.peek_at(1) == Some(b')') {
                        self.bump_n(2);
                        self.token(Tok::RecLitE, "#)", start)
                    } else {
                        return Err(LexError {
                            pos: start,
                            msg: "invalid token `#'".into(),
                        });
                    }
                }
                b'{' => {
                    self.bump();
                    self.token(Tok::LBrace, "{", start)
                }
                b'}' => {
                    self.bump();
                    self.token(Tok::RBrace, "}", start)
                }
                b'.' => {
                    if self.peek_at(1) == Some(b'.') {
                        self.bump_n(2);
                        self.token(Tok::DotDot, "..", start)
                    } else {
                        self.bump();
                        self.token(Tok::Dot, ".", start)
                    }
                }
                b',' => {
                    self.bump();
                    self.token(Tok::Comma, ",", start)
                }
                b':' => {
                    if self.peek_at(1) == Some(b'=') {
                        self.bump_n(2);
                        self.token(Tok::Assign, ":=", start)
                    } else {
                        self.bump();
                        self.token(Tok::Colon, ":", start)
                    }
                }
                b';' => {
                    self.bump();
                    self.token(Tok::Semi, ";", start)
                }
                b'!' => {
                    self.bump();
                    self.token(Tok::Bang, "!", start)
                }
                b'|' => match self.peek_at(1) {
                    Some(b'|') => {
                        self.bump_n(2);
                        self.token(Tok::Sync, "||", start)
                    }
                    Some(b'-') => {
                        self.bump_n(2);
                        self.token(Tok::Turnstile, "|-", start)
                    }
                    _ => {
                        self.bump();
                        self.token(Tok::VBar, "|", start)
                    }
                },
                b'=' => {
                    if self.peek_at(1) == Some(b'>') {
                        self.bump_n(2);
                        self.token(Tok::Implies, "=>", start)
                    } else {
                        self.bump();
                        self.token(Tok::Eq, "=", start)
                    }
                }
                b'/' => {
                    if self.peek_at(1) == Some(b'=') {
                        self.bump_n(2);
                        self.token(Tok::Neq, "/=", start)
                    } else {
                        self.bump();
                        self.token(Tok::Div, "/", start)
                    }
                }
                b'<' => {
                    if self.peek_at(1) == Some(b'=') {
                        if self.peek_at(2) == Some(b'>') {
                            self.bump_n(3);
                            self.token(Tok::Iff, "<=>", start)
                        } else {
                            self.bump_n(2);
                            self.token(Tok::Le, "<=", start)
                        }
                    } else {
                        self.bump();
                        self.token(Tok::Lt, "<", start)
                    }
                }
                b'>' => {
                    if self.peek_at(1) == Some(b'=') {
                        self.bump_n(2);
                        self.token(Tok::Ge, ">=", start)
                    } else {
                        self.bump();
                        self.token(Tok::Gt, ">", start)
                    }
                }
                b'+' => {
                    self.bump();
                    self.token(Tok::Plus, "+", start)
                }
                b'-' => {
                    if self.peek_at(1) == Some(b'-') && self.peek_at(2) == Some(b'>') {
                        self.bump_n(3);
                        self.token(Tok::LongArrow, "-->", start)
                    } else if self.peek_at(1) == Some(b'>') {
                        self.bump_n(2);
                        self.token(Tok::Arrow, "->", start)
                    } else {
                        self.bump();
                        self.token(Tok::Minus, "-", start)
                    }
                }
                b'*' => {
                    self.bump();
                    self.token(Tok::Mult, "*", start)
                }
                b'\'' => {
                    self.bump();
                    self.token(Tok::Quote, "'", start)
                }
                b'0'..=b'9' => self.lex_number(start)?,
                c if is_ident_start(c) => {
                    let s = self.off;
                    self.bump();
                    while self.peek().map_or(false, is_ident_cont) {
                        self.bump();
                    }
                    let text = std::str::from_utf8(&self.src[s..self.off])
                        .unwrap()
                        .to_string();
                    // a lone `_` is UNBOUNDED
                    if text == "_" {
                        self.token(Tok::Unbounded, "_", start)
                    } else if let Some(op) = word_operator(&text) {
                        self.token(op, text, start)
                    } else if let Some(kw) = keyword(&text.to_ascii_uppercase()) {
                        self.token(kw, text, start)
                    } else {
                        self.token(Tok::Identifier, text, start)
                    }
                }
                c if is_opchar1(c) => {
                    let s = self.off;
                    self.bump();
                    while self.peek().map_or(false, is_opchar) {
                        self.bump();
                    }
                    let text = std::str::from_utf8(&self.src[s..self.off])
                        .unwrap()
                        .to_string();
                    self.token(Tok::Identifier, text, start)
                }
                _ => {
                    return Err(LexError {
                        pos: start,
                        msg: format!("invalid character `{}'", c as char),
                    })
                }
            };
            out.push(t);
        }
    }

    fn lex_string(&mut self, start: Pos) -> Result<Token, LexError> {
        self.bump(); // opening quote
        let s = self.off;
        loop {
            match self.peek() {
                None => {
                    return Err(LexError {
                        pos: start,
                        msg: "unterminated string".into(),
                    })
                }
                Some(b'"') => break,
                Some(b'\\') => {
                    self.bump();
                    self.bump();
                }
                _ => {
                    self.bump();
                }
            }
        }
        let text = std::str::from_utf8(&self.src[s..self.off])
            .map_err(|_| LexError {
                pos: start,
                msg: "invalid UTF-8 in string".into(),
            })?
            .to_string();
        self.bump(); // closing quote
        Ok(self.token(Tok::Str, text, start))
    }

    fn lex_number(&mut self, start: Pos) -> Result<Token, LexError> {
        let s = self.off;
        // hex / binary with 0x / 0b prefix (normalized to decimal, as the
        // oracle does)
        if self.peek() == Some(b'0') {
            match self.peek_at(1) {
                Some(b'x') | Some(b'X')
                    if self.peek_at(2).map_or(false, |c| c.is_ascii_hexdigit()) =>
                {
                    self.bump_n(2);
                    let d = self.off;
                    while self.peek().map_or(false, |c| c.is_ascii_hexdigit()) {
                        self.bump();
                    }
                    let digits = std::str::from_utf8(&self.src[d..self.off]).unwrap();
                    let v = BigUint::parse_bytes(digits.as_bytes(), 16).unwrap();
                    return Ok(self.token(Tok::Numeral, v.to_string(), start));
                }
                Some(b'b') | Some(b'B')
                    if self.peek_at(2).map_or(false, |c| c == b'0' || c == b'1') =>
                {
                    self.bump_n(2);
                    let d = self.off;
                    while self.peek().map_or(false, |c| c == b'0' || c == b'1') {
                        self.bump();
                    }
                    let digits = std::str::from_utf8(&self.src[d..self.off]).unwrap();
                    let v = BigUint::parse_bytes(digits.as_bytes(), 2).unwrap();
                    return Ok(self.token(Tok::Numeral, v.to_string(), start));
                }
                _ => {}
            }
        }
        while self.peek().map_or(false, |c| c.is_ascii_digit()) {
            self.bump();
        }
        let text = std::str::from_utf8(&self.src[s..self.off]).unwrap().to_string();
        Ok(self.token(Tok::Numeral, text, start))
    }
}

pub fn tokenize(src: &str) -> Result<Vec<Token>, LexError> {
    Lexer::new(src).tokenize()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> Vec<Tok> {
        tokenize(src).unwrap().into_iter().map(|t| t.tok).collect()
    }

    #[test]
    fn keywords_case_insensitive() {
        assert_eq!(
            kinds("begin Begin BEGIN"),
            vec![Tok::Begin, Tok::Begin, Tok::Begin, Tok::Eof]
        );
    }

    #[test]
    fn word_ops_exact_case_only() {
        assert_eq!(
            kinds("and AND And"),
            vec![Tok::And, Tok::And, Tok::Identifier, Tok::Eof]
        );
    }

    #[test]
    fn compound_tokens() {
        assert_eq!(
            kinds("[# #] (# #) [] || |- --> -> .. := <=> <= /="),
            vec![
                Tok::RecTypeS,
                Tok::RecTypeE,
                Tok::RecLitS,
                Tok::RecLitE,
                Tok::Async,
                Tok::Sync,
                Tok::Turnstile,
                Tok::LongArrow,
                Tok::Arrow,
                Tok::DotDot,
                Tok::Assign,
                Tok::Iff,
                Tok::Le,
                Tok::Neq,
                Tok::Eof
            ]
        );
    }

    #[test]
    fn numbers() {
        let ts = tokenize("42 0x1F 0b101").unwrap();
        assert_eq!(ts[0].text, "42");
        assert_eq!(ts[1].text, "31");
        assert_eq!(ts[2].text, "5");
    }

    #[test]
    fn identifiers() {
        assert_eq!(
            kinds("cons? _x _ x'"),
            vec![
                Tok::Identifier,
                Tok::Identifier,
                Tok::Unbounded,
                Tok::Identifier,
                Tok::Quote,
                Tok::Eof
            ]
        );
    }

    #[test]
    fn comments() {
        assert_eq!(kinds("x % comment\ny"), vec![Tok::Identifier, Tok::Identifier, Tok::Eof]);
        // comment at EOF without trailing newline
        assert_eq!(kinds("x % comment"), vec![Tok::Identifier, Tok::Eof]);
    }
}
