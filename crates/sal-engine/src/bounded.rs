//! Bounded LTL semantics (Biere et al.) over an abstract boolean algebra,
//! shared by the SAT-based (sal-bmc) and SMT-based (sal-inf-bmc) engines.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ltl::Ltl;

/// Abstract boolean sink: produces backend terms for the unrolled system.
pub trait BoolAlg {
    type B: Clone;
    fn tt(&mut self) -> Self::B;
    fn ff(&mut self) -> Self::B;
    fn and(&mut self, xs: Vec<Self::B>) -> Self::B;
    fn or(&mut self, xs: Vec<Self::B>) -> Self::B;
    fn not(&mut self, x: Self::B) -> Self::B;
    /// Truth of an atom (a boolean state predicate) at step `t`.
    fn atom(&mut self, e: &sal_flat::fexpr::FExpr, t: usize) -> Self::B;
}

/// Bounded-semantics expansion of an NNF LTL formula.
pub struct BoundedLtl<'a, A: BoolAlg> {
    pub alg: &'a mut A,
    pub k: usize,
    cache: HashMap<(usize, usize, usize), A::B>,
    ids: HashMap<*const Ltl, usize>,
    keep_alive: Vec<Rc<Ltl>>,
}

const NO_LOOP: usize = usize::MAX;

impl<'a, A: BoolAlg> BoundedLtl<'a, A> {
    pub fn new(alg: &'a mut A, k: usize) -> Self {
        BoundedLtl {
            alg,
            k,
            cache: HashMap::new(),
            ids: HashMap::new(),
            keep_alive: Vec::new(),
        }
    }

    fn id(&mut self, f: &Rc<Ltl>) -> usize {
        let p = Rc::as_ptr(f);
        if let Some(&i) = self.ids.get(&p) {
            return i;
        }
        let i = self.ids.len();
        self.ids.insert(p, i);
        self.keep_alive.push(f.clone());
        i
    }

    /// `[[f]]^{no-loop}_t`
    pub fn no_loop(&mut self, f: &Rc<Ltl>, t: usize) -> A::B {
        let fid = self.id(f);
        if let Some(b) = self.cache.get(&(fid, t, NO_LOOP)) {
            return b.clone();
        }
        let k = self.k;
        let r = match f.as_ref() {
            Ltl::True => self.alg.tt(),
            Ltl::False => self.alg.ff(),
            Ltl::Atom(e) => self.alg.atom(e, t),
            Ltl::NAtom(e) => {
                let a = self.alg.atom(e, t);
                self.alg.not(a)
            }
            Ltl::And(a, b) => {
                let x = self.no_loop(a, t);
                let y = self.no_loop(b, t);
                self.alg.and(vec![x, y])
            }
            Ltl::Or(a, b) => {
                let x = self.no_loop(a, t);
                let y = self.no_loop(b, t);
                self.alg.or(vec![x, y])
            }
            Ltl::X(a) => {
                if t < k {
                    self.no_loop(a, t + 1)
                } else {
                    self.alg.ff()
                }
            }
            Ltl::U(a, b) => {
                // ∨_{j=t..k} (b_j ∧ ∧_{i=t..j-1} a_i)
                let mut disj = Vec::new();
                for j in t..=k {
                    let mut conj = vec![self.no_loop(b, j)];
                    for i in t..j {
                        conj.push(self.no_loop(a, i));
                    }
                    disj.push(self.alg.and(conj));
                }
                self.alg.or(disj)
            }
            Ltl::R(a, b) => {
                // finite witness: a occurs at j with b holding t..j
                let mut disj = Vec::new();
                for j in t..=k {
                    let mut conj = vec![self.no_loop(a, j)];
                    for i in t..=j {
                        conj.push(self.no_loop(b, i));
                    }
                    disj.push(self.alg.and(conj));
                }
                self.alg.or(disj)
            }
        };
        self.cache.insert((fid, t, NO_LOOP), r.clone());
        r
    }

    /// `[[f]]^{loop l}_t`
    pub fn with_loop(&mut self, f: &Rc<Ltl>, t: usize, l: usize) -> A::B {
        let fid = self.id(f);
        if let Some(b) = self.cache.get(&(fid, t, l)) {
            return b.clone();
        }
        let k = self.k;
        let r = match f.as_ref() {
            Ltl::True => self.alg.tt(),
            Ltl::False => self.alg.ff(),
            Ltl::Atom(e) => self.alg.atom(e, t),
            Ltl::NAtom(e) => {
                let a = self.alg.atom(e, t);
                self.alg.not(a)
            }
            Ltl::And(a, b) => {
                let x = self.with_loop(a, t, l);
                let y = self.with_loop(b, t, l);
                self.alg.and(vec![x, y])
            }
            Ltl::Or(a, b) => {
                let x = self.with_loop(a, t, l);
                let y = self.with_loop(b, t, l);
                self.alg.or(vec![x, y])
            }
            Ltl::X(a) => {
                let succ = if t < k { t + 1 } else { l };
                self.with_loop(a, succ, l)
            }
            Ltl::U(a, b) => {
                // ∨_{j=t..k}(b_j ∧ ∧_{i=t..j-1}a_i)
                //   ∨ ∨_{j=l..t-1}(b_j ∧ ∧_{i=t..k}a_i ∧ ∧_{i=l..j-1}a_i)
                let mut disj = Vec::new();
                for j in t..=k {
                    let mut conj = vec![self.with_loop(b, j, l)];
                    for i in t..j {
                        conj.push(self.with_loop(a, i, l));
                    }
                    disj.push(self.alg.and(conj));
                }
                for j in l..t.min(k + 1) {
                    let mut conj = vec![self.with_loop(b, j, l)];
                    for i in t..=k {
                        conj.push(self.with_loop(a, i, l));
                    }
                    for i in l..j {
                        conj.push(self.with_loop(a, i, l));
                    }
                    disj.push(self.alg.and(conj));
                }
                self.alg.or(disj)
            }
            Ltl::R(a, b) => {
                // (∧_{j=min(t,l)..k} b_j)
                //   ∨ ∨_{j=t..k}(a_j ∧ ∧_{i=t..j}b_i)
                //   ∨ ∨_{j=l..t-1}(a_j ∧ ∧_{i=t..k}b_i ∧ ∧_{i=l..j}b_i)
                let mut disj = Vec::new();
                {
                    let mut conj = Vec::new();
                    for j in t.min(l)..=k {
                        conj.push(self.with_loop(b, j, l));
                    }
                    disj.push(self.alg.and(conj));
                }
                for j in t..=k {
                    let mut conj = vec![self.with_loop(a, j, l)];
                    for i in t..=j {
                        conj.push(self.with_loop(b, i, l));
                    }
                    disj.push(self.alg.and(conj));
                }
                for j in l..t.min(k + 1) {
                    let mut conj = vec![self.with_loop(a, j, l)];
                    for i in t..=k {
                        conj.push(self.with_loop(b, i, l));
                    }
                    for i in l..=j {
                        conj.push(self.with_loop(b, i, l));
                    }
                    disj.push(self.alg.and(conj));
                }
                self.alg.or(disj)
            }
        };
        self.cache.insert((fid, t, l), r.clone());
        r
    }
}
