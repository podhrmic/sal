//! Temporal formulas (LTL and CTL) over flat boolean atoms.

use std::rc::Rc;

use crate::fexpr::FExpr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TFormula {
    Atom(FExpr),
    Not(Rc<TFormula>),
    And(Rc<TFormula>, Rc<TFormula>),
    Or(Rc<TFormula>, Rc<TFormula>),
    // LTL
    X(Rc<TFormula>),
    G(Rc<TFormula>),
    F(Rc<TFormula>),
    U(Rc<TFormula>, Rc<TFormula>),
    W(Rc<TFormula>, Rc<TFormula>),
    R(Rc<TFormula>, Rc<TFormula>),
    /// M (strong release): `p M q  =  q U (p AND q)`.
    M(Rc<TFormula>, Rc<TFormula>),
    // CTL
    EX(Rc<TFormula>),
    AX(Rc<TFormula>),
    EG(Rc<TFormula>),
    AG(Rc<TFormula>),
    EF(Rc<TFormula>),
    AF(Rc<TFormula>),
    EU(Rc<TFormula>, Rc<TFormula>),
    AU(Rc<TFormula>, Rc<TFormula>),
    ER(Rc<TFormula>, Rc<TFormula>),
    AR(Rc<TFormula>, Rc<TFormula>),
}

impl TFormula {
    pub fn not(f: TFormula) -> TFormula {
        match f {
            TFormula::Atom(e) => TFormula::Atom(FExpr::not(e)),
            TFormula::Not(inner) => (*inner).clone(),
            other => TFormula::Not(Rc::new(other)),
        }
    }

    pub fn and(a: TFormula, b: TFormula) -> TFormula {
        match (&a, &b) {
            (TFormula::Atom(x), TFormula::Atom(y)) => {
                TFormula::Atom(FExpr::and(vec![x.clone(), y.clone()]))
            }
            _ => TFormula::And(Rc::new(a), Rc::new(b)),
        }
    }

    pub fn or(a: TFormula, b: TFormula) -> TFormula {
        match (&a, &b) {
            (TFormula::Atom(x), TFormula::Atom(y)) => {
                TFormula::Atom(FExpr::or(vec![x.clone(), y.clone()]))
            }
            _ => TFormula::Or(Rc::new(a), Rc::new(b)),
        }
    }

    pub fn ite(c: TFormula, t: TFormula, e: TFormula) -> TFormula {
        TFormula::or(
            TFormula::and(c.clone(), t),
            TFormula::and(TFormula::not(c), e),
        )
    }

    /// Purely propositional (no temporal operators)?
    pub fn as_atom(&self) -> Option<&FExpr> {
        match self {
            TFormula::Atom(e) => Some(e),
            _ => None,
        }
    }

    pub fn is_ctl(&self) -> bool {
        use TFormula::*;
        match self {
            Atom(_) => false,
            Not(a) | X(a) | G(a) | F(a) => a.is_ctl(),
            And(a, b) | Or(a, b) | U(a, b) | W(a, b) | R(a, b) | M(a, b) => {
                a.is_ctl() || b.is_ctl()
            }
            EX(_) | AX(_) | EG(_) | AG(_) | EF(_) | AF(_) | EU(..) | AU(..) | ER(..)
            | AR(..) => true,
        }
    }

    pub fn has_ltl(&self) -> bool {
        use TFormula::*;
        match self {
            Atom(_) => false,
            Not(a) => a.has_ltl(),
            And(a, b) | Or(a, b) => a.has_ltl() || b.has_ltl(),
            X(_) | G(_) | F(_) | U(..) | W(..) | R(..) | M(..) => true,
            EX(a) | AX(a) | EG(a) | AG(a) | EF(a) | AF(a) => a.has_ltl(),
            EU(a, b) | AU(a, b) | ER(a, b) | AR(a, b) => a.has_ltl() || b.has_ltl(),
        }
    }
}
