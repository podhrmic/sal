//! Recursive-descent parser for SAL 3.3, following the oracle's LALR
//! grammar (`sal-parser.scm`) including its precedence declarations.

use crate::ast::*;
use crate::lexer::{tokenize, LexError};
use crate::span::{Pos, Span};
use crate::token::{Tok, Token};

#[derive(Debug, Clone)]
pub struct ParseError {
    pub pos: Pos,
    pub msg: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "line({}), column({}): {}",
            self.pos.line, self.pos.col, self.msg
        )
    }
}

impl std::error::Error for ParseError {}

impl From<LexError> for ParseError {
    fn from(e: LexError) -> Self {
        ParseError {
            pos: e.pos,
            msg: e.msg,
        }
    }
}

type PResult<T> = Result<T, ParseError>;

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
}

// Binding powers, following the lalr precedence list (highest first):
// app/select > DOT > UMINUS > MULT DIV IDIV MOD > PLUS MINUS > WITH >
// EQ NEQ LT GT LE GE > NOT > AND > OR > XOR > IMPLIES(right) > IFF
const BP_MULT: u8 = 80;
const BP_ADD: u8 = 70;
const BP_WITH: u8 = 60;
const BP_CMP: u8 = 55;
const BP_NOT: u8 = 50;
const BP_AND: u8 = 45;
const BP_OR: u8 = 40;
const BP_XOR: u8 = 35;
const BP_IMPLIES: u8 = 30;
const BP_IFF: u8 = 25;

fn binop_of(tok: Tok) -> Option<(BinOp, u8, bool)> {
    // (op, binding power, right associative)
    Some(match tok {
        Tok::Mult => (BinOp::Mult, BP_MULT, false),
        Tok::Div => (BinOp::Div, BP_MULT, false),
        Tok::IDiv => (BinOp::IDiv, BP_MULT, false),
        Tok::Mod => (BinOp::Mod, BP_MULT, false),
        Tok::Plus => (BinOp::Plus, BP_ADD, false),
        Tok::Minus => (BinOp::Minus, BP_ADD, false),
        Tok::Eq => (BinOp::Eq, BP_CMP, false),
        Tok::Neq => (BinOp::Neq, BP_CMP, false),
        Tok::Lt => (BinOp::Lt, BP_CMP, false),
        Tok::Le => (BinOp::Le, BP_CMP, false),
        Tok::Gt => (BinOp::Gt, BP_CMP, false),
        Tok::Ge => (BinOp::Ge, BP_CMP, false),
        Tok::And => (BinOp::And, BP_AND, false),
        Tok::Or => (BinOp::Or, BP_OR, false),
        Tok::Xor => (BinOp::Xor, BP_XOR, false),
        Tok::Implies => (BinOp::Implies, BP_IMPLIES, true),
        Tok::Iff => (BinOp::Iff, BP_IFF, false),
        _ => return None,
    })
}

impl Parser {
    pub fn new(src: &str) -> PResult<Self> {
        Ok(Parser {
            toks: tokenize(src)?,
            pos: 0,
        })
    }

    // -- token helpers ------------------------------------------------------

    fn peek(&self) -> &Token {
        &self.toks[self.pos.min(self.toks.len() - 1)]
    }

    fn peek_at(&self, k: usize) -> &Token {
        &self.toks[(self.pos + k).min(self.toks.len() - 1)]
    }

    fn at(&self, tok: Tok) -> bool {
        self.peek().tok == tok
    }

    fn bump(&mut self) -> Token {
        let t = self.peek().clone();
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn eat(&mut self, tok: Tok) -> Option<Token> {
        if self.at(tok) {
            Some(self.bump())
        } else {
            None
        }
    }

    fn expect(&mut self, tok: Tok, what: &str) -> PResult<Token> {
        if self.at(tok) {
            Ok(self.bump())
        } else {
            Err(self.err(format!(
                "expected {}, found \"{}\"",
                what,
                self.peek().text
            )))
        }
    }

    fn err(&self, msg: String) -> ParseError {
        ParseError {
            pos: self.peek().span.start,
            msg,
        }
    }

    fn save(&self) -> usize {
        self.pos
    }

    fn restore(&mut self, p: usize) {
        self.pos = p;
    }

    fn span_from(&self, start: Pos) -> Span {
        let end = if self.pos > 0 {
            self.toks[self.pos - 1].span.end
        } else {
            start
        };
        Span::new(start, end)
    }

    // -- identifiers & names ------------------------------------------------

    fn ident(&mut self) -> PResult<Ident> {
        let t = self.expect(Tok::Identifier, "an identifier")?;
        Ok(Ident {
            name: t.text,
            span: t.span,
        })
    }

    fn ident_plus(&mut self) -> PResult<Vec<Ident>> {
        let mut ids = vec![self.ident()?];
        while self.eat(Tok::Comma).is_some() {
            ids.push(self.ident()?);
        }
        Ok(ids)
    }

    /// `IDENT`, `IDENT!IDENT` or `IDENT{actuals}!IDENT`.
    fn name(&mut self) -> PResult<Name> {
        let start = self.peek().span.start;
        let first = self.ident()?;
        if self.at(Tok::LBrace) && self.qualified_name_follows() {
            self.bump(); // {
            let actuals = self.actuals()?;
            self.expect(Tok::RBrace, "`}'")?;
            let ctx_span = self.span_from(start);
            self.expect(Tok::Bang, "`!'")?;
            let id = self.ident()?;
            Ok(Name {
                ctx: Some(ContextName {
                    name: first,
                    actuals,
                    span: ctx_span,
                }),
                span: self.span_from(start),
                id,
            })
        } else if self.at(Tok::Bang) {
            self.bump();
            let id = self.ident()?;
            Ok(Name {
                ctx: Some(ContextName {
                    span: first.span,
                    name: first,
                    actuals: vec![],
                }),
                span: self.span_from(start),
                id,
            })
        } else {
            Ok(Name {
                ctx: None,
                span: first.span,
                id: first,
            })
        }
    }

    /// After `IDENT`, decide whether a `{...}!ident` qualified name follows
    /// (as opposed to e.g. a set expression appearing after the name in some
    /// other production). We scan for the matching `}` followed by `!`.
    fn qualified_name_follows(&self) -> bool {
        debug_assert!(self.at(Tok::LBrace));
        let mut depth = 0usize;
        let mut k = 0usize;
        loop {
            let t = self.peek_at(k);
            match t.tok {
                Tok::LBrace => depth += 1,
                Tok::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return self.peek_at(k + 1).tok == Tok::Bang;
                    }
                }
                Tok::Eof => return false,
                _ => {}
            }
            k += 1;
        }
    }

    /// Context actuals: `opt-semi actual (,|; actual)* opt-semi`.
    fn actuals(&mut self) -> PResult<Vec<Actual>> {
        let mut out = Vec::new();
        self.eat(Tok::Semi);
        if self.at(Tok::RBrace) {
            return Ok(out);
        }
        loop {
            out.push(self.actual()?);
            if self.eat(Tok::Comma).is_some() {
                continue;
            }
            if self.eat(Tok::Semi).is_some() {
                if self.at(Tok::RBrace) {
                    break;
                }
                continue;
            }
            break;
        }
        Ok(out)
    }

    /// An actual is an expression or a composite type; plain names parse as
    /// expressions and are re-interpreted during resolution.
    fn actual(&mut self) -> PResult<Actual> {
        if self.starts_comp_type() {
            // try composite type first, fall back to expression (subranges
            // `[a..b]` and tuple types both start with `[`)
            let p = self.save();
            match self.type_expr() {
                Ok(t) => return Ok(Actual::Type(t)),
                Err(_) => self.restore(p),
            }
        }
        Ok(Actual::Expr(self.expr()?))
    }

    fn starts_comp_type(&self) -> bool {
        matches!(
            self.peek().tok,
            Tok::LBrack | Tok::RecTypeS | Tok::Array | Tok::StateType
        )
    }

    // -- types --------------------------------------------------------------

    pub fn type_expr(&mut self) -> PResult<Type> {
        let start = self.peek().span.start;
        match self.peek().tok {
            Tok::Identifier => {
                let name = self.name()?;
                Ok(Type {
                    span: name.span,
                    kind: TypeKind::Name(name),
                })
            }
            Tok::LBrace => {
                // subtype {x : T | e}
                self.bump();
                let var = self.ident()?;
                self.expect(Tok::Colon, "`:'")?;
                let ty = self.type_expr()?;
                self.expect(Tok::VBar, "`|'")?;
                let pred = self.expr()?;
                self.expect(Tok::RBrace, "`}'")?;
                let span = self.span_from(start);
                Ok(Type {
                    kind: TypeKind::Subtype(Box::new(SetPred {
                        var,
                        ty,
                        pred,
                        span,
                    })),
                    span,
                })
            }
            _ => self.comp_type_expr(),
        }
    }

    fn comp_type_expr(&mut self) -> PResult<Type> {
        let start = self.peek().span.start;
        match self.peek().tok {
            Tok::LBrack => {
                self.bump();
                // subrange? try `expr .. expr ]`
                let p = self.save();
                if let Ok(lo) = self.expr() {
                    if self.eat(Tok::DotDot).is_some() {
                        let hi = self.expr()?;
                        self.expect(Tok::RBrack, "`]'")?;
                        return Ok(Type {
                            kind: TypeKind::Subrange(Box::new(lo), Box::new(hi)),
                            span: self.span_from(start),
                        });
                    }
                }
                self.restore(p);
                // tuple or function type
                let mut tys = vec![self.type_expr()?];
                while self.eat(Tok::Comma).is_some() {
                    tys.push(self.type_expr()?);
                }
                if self.eat(Tok::Arrow).is_some() {
                    if tys.len() != 1 {
                        return Err(self.err(
                            "Invalid function type, only unary functions are supported in SAL. \
                             Use a tuple argument if you desire to provide more than one argument."
                                .into(),
                        ));
                    }
                    let rng = self.type_expr()?;
                    self.expect(Tok::RBrack, "`]'")?;
                    Ok(Type {
                        kind: TypeKind::Function(Box::new(tys.pop().unwrap()), Box::new(rng)),
                        span: self.span_from(start),
                    })
                } else {
                    self.expect(Tok::RBrack, "`]'")?;
                    Ok(Type {
                        kind: TypeKind::Tuple(tys),
                        span: self.span_from(start),
                    })
                }
            }
            Tok::Array => {
                self.bump();
                let idx = self.type_expr()?;
                self.expect(Tok::Of, "OF")?;
                let elem = self.type_expr()?;
                Ok(Type {
                    kind: TypeKind::Array(Box::new(idx), Box::new(elem)),
                    span: self.span_from(start),
                })
            }
            Tok::RecTypeS => {
                self.bump();
                let mut fields = vec![self.field_decl()?];
                while self.eat(Tok::Comma).is_some() {
                    fields.push(self.field_decl()?);
                }
                self.expect(Tok::RecTypeE, "`#]'")?;
                Ok(Type {
                    kind: TypeKind::Record(fields),
                    span: self.span_from(start),
                })
            }
            Tok::StateType => {
                self.bump();
                self.expect(Tok::LParen, "`('")?;
                let m = self.module()?;
                self.expect(Tok::RParen, "`)'")?;
                Ok(Type {
                    kind: TypeKind::State(Box::new(m)),
                    span: self.span_from(start),
                })
            }
            _ => Err(self.err(format!("Type expected, found \"{}\".", self.peek().text))),
        }
    }

    fn field_decl(&mut self) -> PResult<FieldDecl> {
        let name = self.ident()?;
        self.expect(Tok::Colon, "`:'")?;
        let ty = self.type_expr()?;
        Ok(FieldDecl { name, ty })
    }

    /// `x, y : T` — one var-decl group.
    fn var_decl(&mut self) -> PResult<VarDecl> {
        let start = self.peek().span.start;
        let names = self.ident_plus()?;
        self.expect(Tok::Colon, "`:'")?;
        let ty = self.type_expr()?;
        Ok(VarDecl {
            names,
            ty,
            span: self.span_from(start),
        })
    }

    /// `var-decl (, var-decl)*` where the identifier lists inside each decl
    /// also use commas: parse ids until `:`, then decide.
    fn var_decl_plus(&mut self) -> PResult<Vec<VarDecl>> {
        let mut out = vec![self.var_decl()?];
        while self.at(Tok::Comma) {
            // lookahead: `, id (, id)* :` continues with another decl
            self.bump();
            out.push(self.var_decl()?);
        }
        Ok(out)
    }

    // -- expressions ---------------------------------------------------------

    pub fn expr(&mut self) -> PResult<Expr> {
        self.expr_bp(0)
    }

    fn expr_bp(&mut self, min_bp: u8) -> PResult<Expr> {
        let start = self.peek().span.start;
        let mut lhs = match self.peek().tok {
            Tok::Not if BP_NOT >= min_bp => {
                self.bump();
                let operand = self.expr_bp(BP_NOT + 1)?;
                Expr {
                    span: self.span_from(start),
                    kind: ExprKind::Unary(UnOp::Not, Box::new(operand)),
                    parens: 0,
                }
            }
            Tok::Minus => {
                self.bump();
                // unary minus binds tighter than * (UMINUS above MULT)
                let operand = self.expr_bp(85)?;
                Expr {
                    span: self.span_from(start),
                    kind: ExprKind::Unary(UnOp::Minus, Box::new(operand)),
                    parens: 0,
                }
            }
            _ => self.expr_postfix()?,
        };

        loop {
            // WITH update: expr WITH access+ := expr
            if self.at(Tok::With) && BP_WITH >= min_bp {
                self.bump();
                let mut accesses = vec![self.access_argument()?];
                while matches!(self.peek().tok, Tok::LBrack | Tok::Dot | Tok::LParen) {
                    accesses.push(self.access_argument()?);
                }
                self.expect(Tok::Assign, "`:='")?;
                let value = self.expr_bp(BP_WITH + 1)?;
                lhs = Expr {
                    span: self.span_from(start),
                    kind: ExprKind::Update {
                        target: Box::new(lhs),
                        accesses,
                        value: Box::new(value),
                    },
                    parens: 0,
                };
                continue;
            }
            let Some((op, bp, right)) = binop_of(self.peek().tok) else {
                break;
            };
            if bp < min_bp {
                break;
            }
            self.bump();
            let next_min = if right { bp } else { bp + 1 };
            let rhs = self.expr_bp(next_min)?;
            lhs = Expr {
                span: self.span_from(start),
                kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)),
                parens: 0,
            };
        }
        Ok(lhs)
    }

    /// Primary expression followed by postfix application/selection.
    fn expr_postfix(&mut self) -> PResult<Expr> {
        let start = self.peek().span.start;
        let mut e = self.expr_primary()?;
        loop {
            match self.peek().tok {
                Tok::LParen => {
                    self.bump();
                    let args = self.expr_plus()?;
                    self.expect(Tok::RParen, "`)'")?;
                    e = Expr {
                        span: self.span_from(start),
                        kind: ExprKind::App(Box::new(e), args),
                        parens: 0,
                    };
                }
                Tok::LBrack => {
                    self.bump();
                    let idx = self.expr()?;
                    self.expect(Tok::RBrack, "`]'")?;
                    e = Expr {
                        span: self.span_from(start),
                        kind: ExprKind::ArraySelect(Box::new(e), Box::new(idx)),
                        parens: 0,
                    };
                }
                Tok::Dot => {
                    match self.peek_at(1).tok {
                        Tok::Identifier => {
                            self.bump();
                            let id = self.ident()?;
                            e = Expr {
                                span: self.span_from(start),
                                kind: ExprKind::RecordSelect(Box::new(e), id),
                                parens: 0,
                            };
                        }
                        Tok::Numeral => {
                            self.bump();
                            let t = self.bump();
                            e = Expr {
                                span: self.span_from(start),
                                kind: ExprKind::TupleSelect(
                                    Box::new(e),
                                    t.text.parse().map_err(|_| ParseError {
                                        pos: t.span.start,
                                        msg: "invalid tuple index".into(),
                                    })?,
                                ),
                                parens: 0,
                            };
                        }
                        _ => break,
                    }
                }
                _ => break,
            }
        }
        Ok(e)
    }

    fn expr_plus(&mut self) -> PResult<Vec<Expr>> {
        let mut out = vec![self.expr()?];
        while self.eat(Tok::Comma).is_some() {
            out.push(self.expr()?);
        }
        Ok(out)
    }

    fn expr_primary(&mut self) -> PResult<Expr> {
        let start = self.peek().span.start;
        let mk = |kind: ExprKind, span: Span| Expr {
            kind,
            span,
            parens: 0,
        };
        match self.peek().tok {
            Tok::Identifier => {
                // next-variable?
                if self.peek_at(1).tok == Tok::Quote {
                    let id = self.ident()?;
                    self.bump(); // '
                    return Ok(mk(ExprKind::Next(id), self.span_from(start)));
                }
                let name = self.name()?;
                Ok(mk(ExprKind::Name(name), self.span_from(start)))
            }
            Tok::Numeral => {
                let t = self.bump();
                // float literal `n.d`
                if self.at(Tok::Dot) && self.peek_at(1).tok == Tok::Numeral {
                    self.bump();
                    let d = self.bump();
                    let numer = format!("{}{}", t.text, d.text);
                    let denom = format!("1{}", "0".repeat(d.text.len()));
                    return Ok(mk(
                        ExprKind::Float { numer, denom },
                        self.span_from(start),
                    ));
                }
                Ok(mk(ExprKind::Numeral(t.text), t.span))
            }
            Tok::Str => {
                let t = self.bump();
                Ok(mk(ExprKind::Str(t.text), t.span))
            }
            Tok::Unbounded => {
                let t = self.bump();
                Ok(mk(ExprKind::Unbounded, t.span))
            }
            Tok::LParen => {
                self.bump();
                let e = self.expr()?;
                if self.eat(Tok::Comma).is_some() {
                    let mut elems = vec![e];
                    elems.extend(self.expr_plus()?);
                    self.expect(Tok::RParen, "`)'")?;
                    return Ok(mk(ExprKind::TupleLit(elems), self.span_from(start)));
                }
                self.expect(Tok::RParen, "`)'")?;
                let mut e = e;
                e.parens += 1;
                e.span = self.span_from(start);
                Ok(e)
            }
            Tok::Lambda => {
                self.bump();
                self.expect(Tok::LParen, "`('")?;
                let decls = self.var_decl_plus()?;
                self.expect(Tok::RParen, "`)'")?;
                self.expect(Tok::Colon, "`:'")?;
                let body = self.expr()?;
                Ok(mk(
                    ExprKind::Lambda(decls, Box::new(body)),
                    self.span_from(start),
                ))
            }
            Tok::Forall | Tok::Exists => {
                let q = if self.bump().tok == Tok::Forall {
                    Quantifier::Forall
                } else {
                    Quantifier::Exists
                };
                self.expect(Tok::LParen, "`('")?;
                let decls = self.var_decl_plus()?;
                self.expect(Tok::RParen, "`)'")?;
                self.expect(Tok::Colon, "`:'")?;
                let body = self.expr()?;
                Ok(mk(
                    ExprKind::Quantified(q, decls, Box::new(body)),
                    self.span_from(start),
                ))
            }
            Tok::Let => {
                self.bump();
                let mut decls = vec![self.let_decl()?];
                while self.eat(Tok::Comma).is_some() {
                    decls.push(self.let_decl()?);
                }
                self.expect(Tok::In, "IN")?;
                let body = self.expr()?;
                Ok(mk(
                    ExprKind::Let(decls, Box::new(body)),
                    self.span_from(start),
                ))
            }
            Tok::If => {
                self.bump();
                let cond = self.expr()?;
                self.expect(Tok::Then, "THEN")?;
                let then = self.expr()?;
                let els = self.conditional_tail(start)?;
                Ok(mk(
                    ExprKind::Conditional {
                        cond: Box::new(cond),
                        then: Box::new(then),
                        els: Box::new(els),
                        is_elsif: false,
                    },
                    self.span_from(start),
                ))
            }
            Tok::LBrace => {
                // set-pred {x : T | e} or set list {e1, ...}
                let p = self.save();
                self.bump();
                if self.at(Tok::Identifier) && self.peek_at(1).tok == Tok::Colon {
                    // could still be a set list whose first expr is... no:
                    // exprs cannot contain a top-level `:`, so this is a
                    // set-pred.
                    let var = self.ident()?;
                    self.bump(); // :
                    let ty = self.type_expr()?;
                    self.expect(Tok::VBar, "`|'")?;
                    let pred = self.expr()?;
                    self.expect(Tok::RBrace, "`}'")?;
                    let span = self.span_from(start);
                    return Ok(mk(
                        ExprKind::SetPred(Box::new(SetPred {
                            var,
                            ty,
                            pred,
                            span,
                        })),
                        span,
                    ));
                }
                self.restore(p);
                self.bump();
                let elems = self.expr_plus()?;
                self.expect(Tok::RBrace, "`}'")?;
                Ok(mk(ExprKind::SetList(elems), self.span_from(start)))
            }
            Tok::LBrack => {
                // array literal [[i : T] e]
                self.bump();
                self.expect(Tok::LBrack, "`['")?;
                let id = self.ident()?;
                self.expect(Tok::Colon, "`:'")?;
                let ty = self.type_expr()?;
                self.expect(Tok::RBrack, "`]'")?;
                let vspan = Span::new(start, ty.span.end);
                let body = self.expr()?;
                self.expect(Tok::RBrack, "`]'")?;
                Ok(mk(
                    ExprKind::ArrayLit(
                        Box::new(VarDecl {
                            names: vec![id],
                            ty,
                            span: vspan,
                        }),
                        Box::new(body),
                    ),
                    self.span_from(start),
                ))
            }
            Tok::RecLitS => {
                self.bump();
                let mut entries = Vec::new();
                loop {
                    let id = self.ident()?;
                    self.expect(Tok::Assign, "`:='")?;
                    let e = self.expr()?;
                    entries.push((id, e));
                    if self.eat(Tok::Comma).is_none() {
                        break;
                    }
                }
                self.expect(Tok::RecLitE, "`#)'")?;
                Ok(mk(ExprKind::RecordLit(entries), self.span_from(start)))
            }
            Tok::InitPred | Tok::TransPred => {
                let is_init = self.bump().tok == Tok::InitPred;
                self.expect(Tok::LParen, "`('")?;
                let m = self.module()?;
                self.expect(Tok::RParen, "`)'")?;
                let span = self.span_from(start);
                Ok(mk(
                    if is_init {
                        ExprKind::ModInit(Box::new(m))
                    } else {
                        ExprKind::ModTrans(Box::new(m))
                    },
                    span,
                ))
            }
            _ => Err(self.err(format!(
                "Unexpected token \"{}\".",
                self.peek().text
            ))),
        }
    }

    fn conditional_tail(&mut self, start: Pos) -> PResult<Expr> {
        if self.at(Tok::Elsif) {
            self.bump();
            let cond = self.expr()?;
            self.expect(Tok::Then, "THEN")?;
            let then = self.expr()?;
            let els = self.conditional_tail(start)?;
            Ok(Expr {
                span: self.span_from(start),
                kind: ExprKind::Conditional {
                    cond: Box::new(cond),
                    then: Box::new(then),
                    els: Box::new(els),
                    is_elsif: true,
                },
                parens: 0,
            })
        } else {
            self.expect(Tok::Else, "ELSE")?;
            let e = self.expr()?;
            self.expect(Tok::Endif, "ENDIF")?;
            Ok(e)
        }
    }

    fn let_decl(&mut self) -> PResult<LetDecl> {
        let name = self.ident()?;
        self.expect(Tok::Colon, "`:'")?;
        let ty = self.type_expr()?;
        self.expect(Tok::Eq, "`='")?;
        let value = self.expr()?;
        Ok(LetDecl { name, ty, value })
    }

    fn access_argument(&mut self) -> PResult<Access> {
        match self.peek().tok {
            Tok::LBrack => {
                self.bump();
                let e = self.expr()?;
                self.expect(Tok::RBrack, "`]'")?;
                Ok(Access::Array(e))
            }
            Tok::Dot => {
                self.bump();
                if self.at(Tok::Numeral) {
                    let t = self.bump();
                    Ok(Access::Tuple(t.text.parse().map_err(|_| ParseError {
                        pos: t.span.start,
                        msg: "invalid tuple index".into(),
                    })?))
                } else {
                    Ok(Access::Record(self.ident()?))
                }
            }
            Tok::LParen => {
                self.bump();
                let args = self.expr_plus()?;
                self.expect(Tok::RParen, "`)'")?;
                Ok(Access::Args(args))
            }
            _ => Err(self.err("expected an access (`[', `.' or `(')".into())),
        }
    }

    // -- modules -------------------------------------------------------------

    pub fn module(&mut self) -> PResult<Module> {
        let start = self.peek().span.start;
        match self.peek().tok {
            Tok::Local => {
                self.bump();
                let ids = self.ident_plus()?;
                self.expect(Tok::In, "IN")?;
                let m = self.module()?;
                Ok(Module {
                    span: self.span_from(start),
                    kind: ModuleKind::Hide(ids, Box::new(m)),
                    parens: 0,
                })
            }
            Tok::Output => {
                self.bump();
                let ids = self.ident_plus()?;
                self.expect(Tok::In, "IN")?;
                let m = self.module()?;
                Ok(Module {
                    span: self.span_from(start),
                    kind: ModuleKind::NewOutput(ids, Box::new(m)),
                    parens: 0,
                })
            }
            Tok::Rename => {
                self.bump();
                let mut renames = vec![self.rename()?];
                while self.eat(Tok::Comma).is_some() {
                    renames.push(self.rename()?);
                }
                self.expect(Tok::In, "IN")?;
                let m = self.module()?;
                Ok(Module {
                    span: self.span_from(start),
                    kind: ModuleKind::Rename(renames, Box::new(m)),
                    parens: 0,
                })
            }
            Tok::With => {
                self.bump();
                let mut decls = vec![self.new_var_decl()?];
                while self.at(Tok::Semi) {
                    self.bump();
                    decls.push(self.new_var_decl()?);
                }
                let m = self.module()?;
                Ok(Module {
                    span: self.span_from(start),
                    kind: ModuleKind::With(decls, Box::new(m)),
                    parens: 0,
                })
            }
            Tok::Observe => {
                self.bump();
                let m1 = self.module_binary()?;
                self.expect(Tok::With, "WITH")?;
                let m2 = self.module()?;
                Ok(Module {
                    span: self.span_from(start),
                    kind: ModuleKind::Observe(Box::new(m1), Box::new(m2)),
                    parens: 0,
                })
            }
            _ => self.module_binary(),
        }
    }

    fn at_module_prefix(&self) -> bool {
        matches!(
            self.peek().tok,
            Tok::Local | Tok::Output | Tok::Rename | Tok::With | Tok::Observe
        )
    }

    /// `m1 || m2` binds tighter than `m1 [] m2`; both left-associative.
    /// A prefix form (`RENAME … IN m`, `LOCAL … IN m`, …) as a right
    /// operand extends maximally to the right (its trailing module has the
    /// lowest precedence in the LALR grammar).
    fn module_binary(&mut self) -> PResult<Module> {
        let start = self.peek().span.start;
        let mut m = self.module_sync()?;
        while self.at(Tok::Async) {
            self.bump();
            let (rhs, last) = if self.at_module_prefix() {
                (self.module()?, true)
            } else {
                (self.module_sync()?, false)
            };
            m = Module {
                span: self.span_from(start),
                kind: ModuleKind::Async(Box::new(m), Box::new(rhs)),
                parens: 0,
            };
            if last {
                break;
            }
        }
        Ok(m)
    }

    fn module_sync(&mut self) -> PResult<Module> {
        let start = self.peek().span.start;
        let mut m = self.module_primary()?;
        while self.at(Tok::Sync) {
            self.bump();
            let (rhs, last) = if self.at_module_prefix() {
                (self.module()?, true)
            } else {
                (self.module_primary()?, false)
            };
            m = Module {
                span: self.span_from(start),
                kind: ModuleKind::Sync(Box::new(m), Box::new(rhs)),
                parens: 0,
            };
            if last {
                break;
            }
        }
        Ok(m)
    }

    fn module_primary(&mut self) -> PResult<Module> {
        let start = self.peek().span.start;
        match self.peek().tok {
            Tok::Begin => {
                let base = self.base_module()?;
                Ok(Module {
                    span: base.span,
                    kind: ModuleKind::Base(base),
                    parens: 0,
                })
            }
            Tok::LParen => {
                // multi-composition or parenthesized module
                match self.peek_at(1).tok {
                    Tok::Async | Tok::Sync => {
                        self.bump();
                        let is_async = self.bump().tok == Tok::Async;
                        self.expect(Tok::LParen, "`('")?;
                        let decls = self.var_decl_plus()?;
                        self.expect(Tok::RParen, "`)'")?;
                        self.expect(Tok::Colon, "`:'")?;
                        let m = self.module()?;
                        self.expect(Tok::RParen, "`)'")?;
                        let decl = self.single_var_decl(decls)?;
                        Ok(Module {
                            span: self.span_from(start),
                            kind: if is_async {
                                ModuleKind::MultiAsync(Box::new(decl), Box::new(m))
                            } else {
                                ModuleKind::MultiSync(Box::new(decl), Box::new(m))
                            },
                            parens: 0,
                        })
                    }
                    _ => {
                        self.bump();
                        let mut m = self.module()?;
                        self.expect(Tok::RParen, "`)'")?;
                        m.parens += 1;
                        m.span = self.span_from(start);
                        Ok(m)
                    }
                }
            }
            Tok::Identifier => {
                let name = self.name()?;
                let mut actuals = Vec::new();
                if self.at(Tok::LBrack) {
                    self.bump();
                    actuals = self.expr_plus()?;
                    self.expect(Tok::RBrack, "`]'")?;
                }
                Ok(Module {
                    span: self.span_from(start),
                    kind: ModuleKind::Instance(name, actuals),
                    parens: 0,
                })
            }
            _ => Err(self.err(format!(
                "Unexpected token \"{}\" (module expected).",
                self.peek().text
            ))),
        }
    }

    fn single_var_decl(&mut self, mut decls: Vec<VarDecl>) -> PResult<VarDecl> {
        if decls.len() != 1 || decls[0].names.len() != 1 {
            return Err(self.err(
                "A single variable declaration is expected in a multi-composition/multi-command."
                    .into(),
            ));
        }
        Ok(decls.pop().unwrap())
    }

    fn rename(&mut self) -> PResult<(Lhs, Lhs)> {
        let l1 = self.lhs()?;
        if l1.next {
            return Err(self.err("Invalid use of next operator in rename definition.".into()));
        }
        self.expect(Tok::To, "TO")?;
        let l2 = self.lhs()?;
        if l2.next {
            return Err(self.err("Invalid use of next operator in rename definition.".into()));
        }
        Ok((l1, l2))
    }

    fn new_var_decl(&mut self) -> PResult<NewVarDecl> {
        let class = match self.peek().tok {
            Tok::Input => VarClass::Input,
            Tok::Output => VarClass::Output,
            Tok::Global => VarClass::Global,
            _ => {
                return Err(self.err(
                    "expected INPUT, OUTPUT or GLOBAL declaration in WITH module".into(),
                ))
            }
        };
        self.bump();
        let decls = self.var_decl_plus()?;
        Ok(NewVarDecl { class, decls })
    }

    fn base_module(&mut self) -> PResult<BaseModule> {
        let start = self.peek().span.start;
        self.expect(Tok::Begin, "BEGIN")?;
        let mut decls = Vec::new();
        loop {
            match self.peek().tok {
                Tok::Input => {
                    self.bump();
                    decls.push(BaseDecl::Vars(VarClass::Input, self.var_decl_plus()?));
                }
                Tok::Output => {
                    self.bump();
                    decls.push(BaseDecl::Vars(VarClass::Output, self.var_decl_plus()?));
                }
                Tok::Global => {
                    self.bump();
                    decls.push(BaseDecl::Vars(VarClass::Global, self.var_decl_plus()?));
                }
                Tok::Local => {
                    self.bump();
                    decls.push(BaseDecl::Vars(VarClass::Local, self.var_decl_plus()?));
                }
                Tok::Definition => {
                    self.bump();
                    decls.push(BaseDecl::Definition(self.definition_plus()?));
                }
                Tok::Initialization => {
                    self.bump();
                    decls.push(BaseDecl::Initialization(self.def_or_command_plus()?));
                }
                Tok::Transition => {
                    self.bump();
                    decls.push(BaseDecl::Transition(self.def_or_command_plus()?));
                }
                Tok::End => {
                    self.bump();
                    return Ok(BaseModule {
                        decls,
                        span: self.span_from(start),
                    });
                }
                _ => {
                    return Err(self.err(format!(
                        "Unexpected token \"{}\" in base module.",
                        self.peek().text
                    )))
                }
            }
        }
    }

    fn section_ends(&self) -> bool {
        matches!(
            self.peek().tok,
            Tok::Input
                | Tok::Output
                | Tok::Global
                | Tok::Local
                | Tok::Definition
                | Tok::Initialization
                | Tok::Transition
                | Tok::End
        )
    }

    fn definition_plus(&mut self) -> PResult<Vec<Definition>> {
        let mut out = vec![self.definition()?];
        while self.at(Tok::Semi) {
            self.bump();
            if self.section_ends() {
                break; // trailing semicolon
            }
            out.push(self.definition()?);
        }
        Ok(out)
    }

    fn definition(&mut self) -> PResult<Definition> {
        if self.at(Tok::LParen) && self.peek_at(1).tok == Tok::Forall {
            self.bump();
            self.bump();
            self.expect(Tok::LParen, "`('")?;
            let decls = self.var_decl_plus()?;
            self.expect(Tok::RParen, "`)'")?;
            self.expect(Tok::Colon, "`:'")?;
            let defs = self.definition_plus()?;
            self.expect(Tok::RParen, "`)'")?;
            return Ok(Definition::Forall(decls, defs));
        }
        let start = self.peek().span.start;
        let lhs = self.lhs()?;
        let rhs = match self.peek().tok {
            Tok::Eq => {
                self.bump();
                Rhs::Expr(self.expr()?)
            }
            Tok::In => {
                self.bump();
                Rhs::Selection(self.expr()?)
            }
            _ => return Err(self.err("expected `=' or IN in definition".into())),
        };
        Ok(Definition::Simple(SimpleDefinition {
            lhs,
            rhs,
            span: self.span_from(start),
        }))
    }

    fn lhs(&mut self) -> PResult<Lhs> {
        let start = self.peek().span.start;
        let base = self.ident()?;
        let next = self.eat(Tok::Quote).is_some();
        let mut accesses = Vec::new();
        loop {
            match self.peek().tok {
                Tok::LBrack => {
                    self.bump();
                    let e = self.expr()?;
                    self.expect(Tok::RBrack, "`]'")?;
                    accesses.push(Access::Array(e));
                }
                Tok::Dot => {
                    self.bump();
                    if self.at(Tok::Numeral) {
                        let t = self.bump();
                        accesses.push(Access::Tuple(t.text.parse().map_err(|_| {
                            ParseError {
                                pos: t.span.start,
                                msg: "invalid tuple index".into(),
                            }
                        })?));
                    } else {
                        accesses.push(Access::Record(self.ident()?));
                    }
                }
                _ => break,
            }
        }
        Ok(Lhs {
            base,
            next,
            accesses,
            span: self.span_from(start),
        })
    }

    fn def_or_command_plus(&mut self) -> PResult<Vec<DefOrCommand>> {
        let mut out = vec![self.def_or_command()?];
        while self.at(Tok::Semi) {
            self.bump();
            if self.section_ends() {
                break; // trailing semicolon
            }
            out.push(self.def_or_command()?);
        }
        Ok(out)
    }

    fn def_or_command(&mut self) -> PResult<DefOrCommand> {
        if self.at(Tok::LBrack) {
            let start = self.peek().span.start;
            self.bump();
            let mut cmds = vec![self.some_command()?];
            while self.at(Tok::Async) {
                self.bump();
                cmds.push(self.some_command()?);
            }
            self.expect(Tok::RBrack, "`]'")?;
            // ELSE must be last
            for c in &cmds[..cmds.len() - 1] {
                if let SomeCommand::Guarded(g) = c {
                    if g.guard.is_none() {
                        return Err(ParseError {
                            pos: g.span.start,
                            msg: "Invalid occurrence of ELSE command. ELSE command must be \
                                  the last command in the command list."
                                .into(),
                        });
                    }
                }
            }
            Ok(DefOrCommand::Commands(cmds, self.span_from(start)))
        } else {
            Ok(DefOrCommand::Def(self.definition()?))
        }
    }

    fn some_command(&mut self) -> PResult<SomeCommand> {
        let start = self.peek().span.start;
        // multi-command `([] (decls) : cmd)`
        if self.at(Tok::LParen) && matches!(self.peek_at(1).tok, Tok::Async) {
            self.bump();
            self.bump();
            self.expect(Tok::LParen, "`('")?;
            let decls = self.var_decl_plus()?;
            self.expect(Tok::RParen, "`)'")?;
            self.expect(Tok::Colon, "`:'")?;
            let inner = self.some_command()?;
            self.expect(Tok::RParen, "`)'")?;
            if let SomeCommand::Guarded(g) = &inner {
                if g.guard.is_none() {
                    return Err(ParseError {
                        pos: start,
                        msg: "Invalid multi-command. ELSE commands cannot be nested in \
                              multi-commands."
                            .into(),
                    });
                }
            }
            return Ok(SomeCommand::Multi(
                decls,
                Box::new(inner),
                self.span_from(start),
            ));
        }
        // label?
        let label = if self.at(Tok::Identifier) && self.peek_at(1).tok == Tok::Colon {
            let id = self.ident()?;
            self.bump(); // :
            if self.at(Tok::LParen) && matches!(self.peek_at(1).tok, Tok::Async) {
                return Err(ParseError {
                    pos: id.span.start,
                    msg: "Only guarded commands can be labeled. Move the identifier to the \
                          nested guarded command."
                        .into(),
                });
            }
            Some(id)
        } else {
            None
        };
        // ELSE command
        if self.at(Tok::Else) {
            self.bump();
            self.expect(Tok::LongArrow, "`-->'")?;
            let assignments = self.assignments_opt()?;
            return Ok(SomeCommand::Guarded(GuardedCommand {
                label,
                guard: None,
                assignments,
                span: self.span_from(start),
            }));
        }
        let guard = self.expr()?;
        self.expect(Tok::LongArrow, "`-->'")?;
        let assignments = self.assignments_opt()?;
        Ok(SomeCommand::Guarded(GuardedCommand {
            label,
            guard: Some(guard),
            assignments,
            span: self.span_from(start),
        }))
    }

    /// Assignments after `-->`: possibly empty; SEMI-separated definitions
    /// with optional trailing SEMI. Ends at `[]`, `]`, or a section
    /// boundary.
    fn assignments_opt(&mut self) -> PResult<Vec<Definition>> {
        let mut out = Vec::new();
        if self.at(Tok::Async) || self.at(Tok::RBrack) || self.at(Tok::RParen) {
            return Ok(out);
        }
        out.push(self.definition()?);
        while self.at(Tok::Semi) {
            self.bump();
            if self.at(Tok::Async) || self.at(Tok::RBrack) || self.at(Tok::RParen) || self.section_ends() {
                break;
            }
            out.push(self.definition()?);
        }
        Ok(out)
    }

    // -- contexts -------------------------------------------------------------

    pub fn context(&mut self) -> PResult<SalContext> {
        let start = self.peek().span.start;
        let name = self.ident()?;
        let mut params = Vec::new();
        if self.at(Tok::LBrace) {
            self.bump();
            self.eat(Tok::Semi);
            loop {
                if self.at(Tok::RBrace) {
                    break;
                }
                params.push(self.ctx_param()?);
                if self.eat(Tok::Comma).is_some() || self.eat(Tok::Semi).is_some() {
                    continue;
                }
                break;
            }
            self.expect(Tok::RBrace, "`}'")?;
        }
        self.expect(Tok::Colon, "`:'")?;
        self.expect(Tok::Context, "CONTEXT")?;
        self.expect(Tok::Eq, "`='")?;
        self.expect(Tok::Begin, "BEGIN")?;
        let mut decls = Vec::new();
        while !self.at(Tok::End) {
            decls.push(self.declaration()?);
            self.expect(Tok::Semi, "`;'")?;
        }
        if decls.is_empty() {
            return Err(self.err("Invalid empty context.".into()));
        }
        self.expect(Tok::End, "END")?;
        if !self.at(Tok::Eof) {
            return Err(self.err(format!(
                "Unexpected token \"{}\" after end of context.",
                self.peek().text
            )));
        }
        Ok(SalContext {
            name,
            params,
            decls,
            span: self.span_from(start),
        })
    }

    fn ctx_param(&mut self) -> PResult<CtxParam> {
        let ids = self.ident_plus()?;
        self.expect(Tok::Colon, "`:'")?;
        if self.eat(Tok::Type).is_some() {
            Ok(CtxParam::Types(ids))
        } else {
            let ty = self.type_expr()?;
            Ok(CtxParam::Vars(ids, ty))
        }
    }

    fn declaration(&mut self) -> PResult<Decl> {
        if self.at(Tok::Importing) {
            self.bump();
            let ctx = self.context_name()?;
            let mut renames = Vec::new();
            if self.eat(Tok::With).is_some() {
                loop {
                    let a = self.ident()?;
                    self.expect(Tok::To, "TO")?;
                    let b = self.ident()?;
                    renames.push((a, b));
                    if self.eat(Tok::Comma).is_none() {
                        break;
                    }
                }
            }
            return Ok(Decl::Import { ctx, renames });
        }
        let name = self.ident()?;
        match self.peek().tok {
            Tok::LParen => {
                // function constant declaration
                self.bump();
                let args = self.var_decl_plus()?;
                self.expect(Tok::RParen, "`)'")?;
                self.expect(Tok::Colon, "`:'")?;
                let ty = self.type_expr()?;
                let value = if self.eat(Tok::Eq).is_some() {
                    Some(self.expr()?)
                } else {
                    None
                };
                Ok(Decl::Constant {
                    name,
                    args,
                    ty,
                    value,
                })
            }
            Tok::LBrack => {
                // parametric module declaration
                self.bump();
                let params = self.var_decl_plus()?;
                self.expect(Tok::RBrack, "`]'")?;
                self.expect(Tok::Colon, "`:'")?;
                self.expect(Tok::Module, "MODULE")?;
                self.expect(Tok::Eq, "`='")?;
                let body = self.module()?;
                Ok(Decl::Module { name, params, body })
            }
            Tok::Colon => {
                self.bump();
                match self.peek().tok {
                    Tok::Type => {
                        self.bump();
                        if self.eat(Tok::Eq).is_some() {
                            let def = self.type_def()?;
                            Ok(Decl::Type {
                                name,
                                def: Some(def),
                            })
                        } else {
                            Ok(Decl::Type { name, def: None })
                        }
                    }
                    Tok::Context => {
                        self.bump();
                        self.expect(Tok::Eq, "`='")?;
                        let ctx = self.context_name()?;
                        Ok(Decl::Context { name, ctx })
                    }
                    Tok::Module => {
                        self.bump();
                        self.expect(Tok::Eq, "`='")?;
                        let body = self.module()?;
                        Ok(Decl::Module {
                            name,
                            params: vec![],
                            body,
                        })
                    }
                    Tok::Theorem | Tok::Lemma | Tok::Claim | Tok::Obligation => {
                        let form = match self.bump().tok {
                            Tok::Theorem => AssertionForm::Theorem,
                            Tok::Lemma => AssertionForm::Lemma,
                            Tok::Claim => AssertionForm::Claim,
                            _ => AssertionForm::Obligation,
                        };
                        let m = self.module()?;
                        let body = if self.eat(Tok::Turnstile).is_some() {
                            AssertionExpr::Models {
                                module: m,
                                formula: self.expr()?,
                            }
                        } else {
                            self.expect(Tok::Implements, "|- or IMPLEMENTS")?;
                            AssertionExpr::Implements {
                                concrete: m,
                                abstract_: self.module()?,
                            }
                        };
                        Ok(Decl::Assertion { name, form, body })
                    }
                    _ => {
                        // constant declaration
                        let ty = self.type_expr()?;
                        let value = if self.eat(Tok::Eq).is_some() {
                            Some(self.expr()?)
                        } else {
                            None
                        };
                        Ok(Decl::Constant {
                            name,
                            args: vec![],
                            ty,
                            value,
                        })
                    }
                }
            }
            _ => Err(self.err(format!(
                "Unexpected token \"{}\" in declaration.",
                self.peek().text
            ))),
        }
    }

    fn context_name(&mut self) -> PResult<ContextName> {
        let start = self.peek().span.start;
        let name = self.ident()?;
        let mut actuals = Vec::new();
        if self.at(Tok::LBrace) {
            self.bump();
            actuals = self.actuals()?;
            self.expect(Tok::RBrace, "`}'")?;
        }
        Ok(ContextName {
            name,
            actuals,
            span: self.span_from(start),
        })
    }

    fn type_def(&mut self) -> PResult<TypeDef> {
        match self.peek().tok {
            Tok::LBrace => {
                // scalar type {a, b, c} — but `{x : T | e}` is a subtype
                if self.peek_at(1).tok == Tok::Identifier && self.peek_at(2).tok == Tok::Colon {
                    let t = self.type_expr()?;
                    return Ok(TypeDef::Type(t));
                }
                self.bump();
                let ids = self.ident_plus()?;
                self.expect(Tok::RBrace, "`}'")?;
                Ok(TypeDef::Scalar(ids))
            }
            Tok::Datatype => {
                self.bump();
                let mut ctors = vec![self.constructor()?];
                while self.eat(Tok::Comma).is_some() {
                    ctors.push(self.constructor()?);
                }
                self.expect(Tok::End, "END")?;
                Ok(TypeDef::Datatype(ctors))
            }
            Tok::Scalarset => {
                self.bump();
                self.expect(Tok::LParen, "`('")?;
                let e = self.expr()?;
                self.expect(Tok::RParen, "`)'")?;
                Ok(TypeDef::Scalarset(e))
            }
            Tok::Ringset => {
                self.bump();
                self.expect(Tok::LParen, "`('")?;
                let e = self.expr()?;
                self.expect(Tok::RParen, "`)'")?;
                Ok(TypeDef::Ringset(e))
            }
            _ => Ok(TypeDef::Type(self.type_expr()?)),
        }
    }

    fn constructor(&mut self) -> PResult<Constructor> {
        let name = self.ident()?;
        let mut accessors = Vec::new();
        if self.eat(Tok::LParen).is_some() {
            accessors = self.var_decl_plus()?;
            self.expect(Tok::RParen, "`)'")?;
        }
        Ok(Constructor { name, accessors })
    }
}

// ---------------------------------------------------------------------------
// Entry points (mirroring the oracle's @BTE@/@BTM@/... fragment parsing)
// ---------------------------------------------------------------------------

pub fn parse_context(src: &str) -> Result<SalContext, ParseError> {
    Parser::new(src)?.context()
}

pub fn parse_expr(src: &str) -> Result<Expr, ParseError> {
    let mut p = Parser::new(src)?;
    let e = p.expr()?;
    p.expect(Tok::Eof, "end of input")?;
    Ok(e)
}

pub fn parse_module(src: &str) -> Result<Module, ParseError> {
    let mut p = Parser::new(src)?;
    let m = p.module()?;
    p.expect(Tok::Eof, "end of input")?;
    Ok(m)
}
