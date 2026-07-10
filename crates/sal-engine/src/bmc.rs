//! SAT-based bounded model checking (sal-bmc): Tseitin CNF encoding of
//! the unrolled transition system, bounded LTL semantics, and
//! k-induction for invariants.

use std::collections::HashMap;

use sal_flat::fexpr::{FExpr, LeafType};
use sal_flat::flatten::{FlatModule, TransNode};
use sal_flat::value::Value;

use crate::bounded::{BoolAlg, BoundedLtl};
use crate::explicit::EngineError;
use crate::ltl::Ltl;

type EResult<T> = Result<T, EngineError>;

/// A literal: positive or negative variable index (1-based, DIMACS-like).
pub type Lit = i32;

pub struct Cnf {
    pub nvars: i32,
    pub clauses: Vec<Vec<Lit>>,
    /// (leaf, bit, step) -> var
    pub bitvars: HashMap<(u32, u32, usize), i32>,
    and_cache: HashMap<Vec<Lit>, Lit>,
    or_cache: HashMap<Vec<Lit>, Lit>,
    pub tt: Lit,
}

impl Cnf {
    pub fn new() -> Self {
        let mut c = Cnf {
            nvars: 1,
            clauses: vec![vec![1]],
            bitvars: HashMap::new(),
            and_cache: HashMap::new(),
            or_cache: HashMap::new(),
            tt: 1,
        };
        c.tt = 1;
        c
    }

    pub fn fresh(&mut self) -> Lit {
        self.nvars += 1;
        self.nvars
    }

    pub fn bitvar(&mut self, leaf: u32, bit: u32, step: usize) -> Lit {
        if let Some(&v) = self.bitvars.get(&(leaf, bit, step)) {
            return v;
        }
        let v = self.fresh();
        self.bitvars.insert((leaf, bit, step), v);
        v
    }

    pub fn and_lits(&mut self, mut xs: Vec<Lit>) -> Lit {
        xs.retain(|&l| l != self.tt);
        if xs.iter().any(|&l| l == -self.tt) {
            return -self.tt;
        }
        xs.sort_unstable();
        xs.dedup();
        if xs.is_empty() {
            return self.tt;
        }
        if xs.len() == 1 {
            return xs[0];
        }
        if let Some(&v) = self.and_cache.get(&xs) {
            return v;
        }
        let v = self.fresh();
        for &x in &xs {
            self.clauses.push(vec![-v, x]);
        }
        let mut cl: Vec<Lit> = xs.iter().map(|&x| -x).collect();
        cl.push(v);
        self.clauses.push(cl);
        self.and_cache.insert(xs, v);
        v
    }

    pub fn or_lits(&mut self, mut xs: Vec<Lit>) -> Lit {
        xs.retain(|&l| l != -self.tt);
        if xs.iter().any(|&l| l == self.tt) {
            return self.tt;
        }
        xs.sort_unstable();
        xs.dedup();
        if xs.is_empty() {
            return -self.tt;
        }
        if xs.len() == 1 {
            return xs[0];
        }
        if let Some(&v) = self.or_cache.get(&xs) {
            return v;
        }
        let v = self.fresh();
        for &x in &xs {
            self.clauses.push(vec![v, -x]);
        }
        let mut cl = xs.clone();
        cl.push(-v);
        self.clauses.push(cl);
        self.or_cache.insert(xs, v);
        v
    }

    pub fn ite_lit(&mut self, c: Lit, t: Lit, e: Lit) -> Lit {
        let ct = self.and_lits(vec![c, t]);
        let ne = self.and_lits(vec![-c, e]);
        self.or_lits(vec![ct, ne])
    }

    pub fn iff_lit(&mut self, a: Lit, b: Lit) -> Lit {
        let x = self.and_lits(vec![a, b]);
        let y = self.and_lits(vec![-a, -b]);
        self.or_lits(vec![x, y])
    }
}

impl Default for Cnf {
    fn default() -> Self {
        Self::new()
    }
}

/// Per-step FExpr encoder for a flat module (partition trick like the BDD
/// engine, but producing CNF literals).
pub struct BmcEnc<'m> {
    pub flat: &'m FlatModule,
    pub cnf: Cnf,
    bits: Vec<(u32, Vec<Value>)>, // per leaf: (#bits, values)
    part_cache: HashMap<(FExpr, usize, usize), PartsOrLit>,
}

#[derive(Clone)]
enum PartsOrLit {
    L(Lit),
    P(Vec<(Value, Lit)>),
}

fn bits_for(card: u64) -> u32 {
    let mut b = 0;
    while (1u64 << b) < card {
        b += 1;
    }
    b.max(1)
}

impl<'m> BmcEnc<'m> {
    pub fn new(flat: &'m FlatModule) -> EResult<Self> {
        let mut bits = Vec::new();
        for l in &flat.leaves {
            let values = l
                .ty
                .values()
                .ok_or_else(|| EngineError::InfiniteType(l.name.clone()))?;
            bits.push((bits_for(values.len() as u64), values));
        }
        Ok(BmcEnc {
            flat,
            cnf: Cnf::new(),
            bits,
            part_cache: HashMap::new(),
        })
    }

    /// Literal for `leaf == value index i` at step t.
    fn leaf_eq_index(&mut self, l: usize, t: usize, i: usize) -> Lit {
        let (nbits, _) = &self.bits[l];
        let nbits = *nbits;
        let mut lits = Vec::new();
        for b in 0..nbits {
            let v = self.cnf.bitvar(l as u32, b, t);
            lits.push(if (i >> b) & 1 == 1 { v } else { -v });
        }
        self.cnf.and_lits(lits)
    }

    /// Domain constraint for a step.
    pub fn domain(&mut self, t: usize) -> Lit {
        let mut cs = Vec::new();
        for l in 0..self.bits.len() {
            let n = self.bits[l].1.len();
            if n == 1 << self.bits[l].0 {
                continue;
            }
            let mut alts = Vec::new();
            for i in 0..n {
                alts.push(self.leaf_eq_index(l, t, i));
            }
            cs.push(self.cnf.or_lits(alts));
        }
        self.cnf.and_lits(cs)
    }

    /// Encode a boolean FExpr; `cur_step`/`next_step` give the steps for
    /// unprimed/primed leaves.
    pub fn enc_bool(&mut self, e: &FExpr, cur: usize, next: usize) -> EResult<Lit> {
        match self.enc(e, cur, next)? {
            PartsOrLit::L(l) => Ok(l),
            PartsOrLit::P(p) => {
                let mut alts = Vec::new();
                for (v, c) in p {
                    if v == Value::Bool(true) {
                        alts.push(c);
                    }
                }
                Ok(self.cnf.or_lits(alts))
            }
        }
    }

    fn enc_part(&mut self, e: &FExpr, cur: usize, next: usize) -> EResult<Vec<(Value, Lit)>> {
        match self.enc(e, cur, next)? {
            PartsOrLit::P(p) => Ok(p),
            PartsOrLit::L(l) => Ok(vec![(Value::Bool(true), l), (Value::Bool(false), -l)]),
        }
    }

    fn enc(&mut self, e: &FExpr, cur: usize, next: usize) -> EResult<PartsOrLit> {
        use FExpr::*;
        let key = (e.clone(), cur, next);
        if let Some(r) = self.part_cache.get(&key) {
            return Ok(r.clone());
        }
        let r = match e {
            Const(Value::Bool(b)) => {
                PartsOrLit::L(if *b { self.cnf.tt } else { -self.cnf.tt })
            }
            Const(v) => PartsOrLit::P(vec![(v.clone(), self.cnf.tt)]),
            Var(l, primed) => {
                let idx = *l as usize;
                let t = if *primed { next } else { cur };
                if matches!(self.flat.leaves[idx].ty, LeafType::Bool) {
                    PartsOrLit::L(self.cnf.bitvar(*l, 0, t))
                } else {
                    let n = self.bits[idx].1.len();
                    let mut parts = Vec::new();
                    for i in 0..n {
                        let c = self.leaf_eq_index(idx, t, i);
                        parts.push((self.bits[idx].1[i].clone(), c));
                    }
                    PartsOrLit::P(parts)
                }
            }
            Not(a) => {
                let x = self.enc_bool(a, cur, next)?;
                PartsOrLit::L(-x)
            }
            And(es) => {
                let mut xs = Vec::new();
                for x in es {
                    xs.push(self.enc_bool(x, cur, next)?);
                }
                PartsOrLit::L(self.cnf.and_lits(xs))
            }
            Or(es) => {
                let mut xs = Vec::new();
                for x in es {
                    xs.push(self.enc_bool(x, cur, next)?);
                }
                PartsOrLit::L(self.cnf.or_lits(xs))
            }
            Ite(c, t, f) => {
                let lc = self.enc_bool(c, cur, next)?;
                let pt = self.enc(t, cur, next)?;
                let pf = self.enc(f, cur, next)?;
                match (pt, pf) {
                    (PartsOrLit::L(a), PartsOrLit::L(b)) => {
                        PartsOrLit::L(self.cnf.ite_lit(lc, a, b))
                    }
                    (pt, pf) => {
                        let pt = as_parts(&mut self.cnf, pt);
                        let pf = as_parts(&mut self.cnf, pf);
                        let mut merged: Vec<(Value, Lit)> = Vec::new();
                        for (v, c) in pt {
                            let cc = self.cnf.and_lits(vec![lc, c]);
                            push_part(&mut self.cnf, &mut merged, v, cc);
                        }
                        for (v, c) in pf {
                            let cc = self.cnf.and_lits(vec![-lc, c]);
                            push_part(&mut self.cnf, &mut merged, v, cc);
                        }
                        PartsOrLit::P(merged)
                    }
                }
            }
            Eq(a, b) => {
                let pa = self.enc(a, cur, next)?;
                let pb = self.enc(b, cur, next)?;
                match (pa, pb) {
                    (PartsOrLit::L(x), PartsOrLit::L(y)) => {
                        PartsOrLit::L(self.cnf.iff_lit(x, y))
                    }
                    (pa, pb) => {
                        let pa = as_parts(&mut self.cnf, pa);
                        let pb = as_parts(&mut self.cnf, pb);
                        let mut alts = Vec::new();
                        for (v1, c1) in &pa {
                            for (v2, c2) in &pb {
                                if v1 == v2 {
                                    alts.push(self.cnf.and_lits(vec![*c1, *c2]));
                                }
                            }
                        }
                        PartsOrLit::L(self.cnf.or_lits(alts))
                    }
                }
            }
            Lt(a, b) | Le(a, b) => {
                let strict = matches!(e, Lt(..));
                let pa = self.enc_part(a, cur, next)?;
                let pb = self.enc_part(b, cur, next)?;
                let mut alts = Vec::new();
                for (v1, c1) in &pa {
                    for (v2, c2) in &pb {
                        let (Value::Num(x), Value::Num(y)) = (v1, v2) else {
                            return Err(EngineError::Eval("number expected".into()));
                        };
                        if if strict { x < y } else { x <= y } {
                            alts.push(self.cnf.and_lits(vec![*c1, *c2]));
                        }
                    }
                }
                PartsOrLit::L(self.cnf.or_lits(alts))
            }
            Add(es) | Mul(es) => {
                let is_add = matches!(e, Add(..));
                let unit = if is_add { 0 } else { 1 };
                let mut acc: Vec<(Value, Lit)> = vec![(
                    Value::Num(num_rational::BigRational::from_integer(unit.into())),
                    self.cnf.tt,
                )];
                for x in es {
                    let px = self.enc_part(x, cur, next)?;
                    let mut out: Vec<(Value, Lit)> = Vec::new();
                    for (v1, c1) in &acc {
                        for (v2, c2) in &px {
                            let (Value::Num(a), Value::Num(b)) = (v1, v2) else {
                                return Err(EngineError::Eval("number expected".into()));
                            };
                            let v = Value::Num(if is_add { a + b } else { a * b });
                            let c = self.cnf.and_lits(vec![*c1, *c2]);
                            if c != -self.cnf.tt {
                                push_part(&mut self.cnf, &mut out, v, c);
                            }
                        }
                    }
                    acc = out;
                }
                PartsOrLit::P(acc)
            }
            Neg(a) => {
                let pa = self.enc_part(a, cur, next)?;
                let mut out = Vec::new();
                for (v, c) in pa {
                    match v {
                        Value::Num(n) => out.push((Value::Num(-n), c)),
                        _ => return Err(EngineError::Eval("number expected".into())),
                    }
                }
                PartsOrLit::P(out)
            }
            Div(a, b) | IDiv(a, b) | Mod(a, b) => {
                use num_traits::Zero;
                let pa = self.enc_part(a, cur, next)?;
                let pb = self.enc_part(b, cur, next)?;
                let mut out: Vec<(Value, Lit)> = Vec::new();
                for (v1, c1) in &pa {
                    for (v2, c2) in &pb {
                        let (Value::Num(x), Value::Num(y)) = (v1, v2) else {
                            return Err(EngineError::Eval("number expected".into()));
                        };
                        if y.is_zero() {
                            continue;
                        }
                        let v = match e {
                            Div(..) => Value::Num(x / y),
                            _ => {
                                if !x.is_integer() || !y.is_integer() {
                                    continue;
                                }
                                let (xi, yi) = (x.to_integer(), y.to_integer());
                                let q = &xi / &yi;
                                let r = &xi - &q * &yi;
                                let (q, r) = if r < Zero::zero() {
                                    if yi > Zero::zero() {
                                        (q - 1, r + &yi)
                                    } else {
                                        (q + 1, r - &yi)
                                    }
                                } else {
                                    (q, r)
                                };
                                Value::Num(num_rational::BigRational::from_integer(
                                    if matches!(e, IDiv(..)) { q } else { r },
                                ))
                            }
                        };
                        let c = self.cnf.and_lits(vec![*c1, *c2]);
                        if c != -self.cnf.tt {
                            push_part(&mut self.cnf, &mut out, v, c);
                        }
                    }
                }
                PartsOrLit::P(out)
            }
        };
        self.part_cache.insert(key, r.clone());
        Ok(r)
    }

    /// Init constraint at step 0.
    pub fn init(&mut self) -> EResult<Lit> {
        let mut cs = vec![self.domain(0)];
        for i in &self.flat.invariants.clone() {
            cs.push(self.enc_bool(i, 0, 0)?);
        }
        for d in &self.flat.init_defs.clone() {
            cs.push(self.enc_bool(d, 0, 0)?);
        }
        for block in &self.flat.init_choices.clone() {
            let mut alts = Vec::new();
            for cmd in block {
                let g = self.enc_bool(&cmd.guard, 0, 0)?;
                let c = self.enc_bool(&cmd.constraint, 0, 0)?;
                alts.push(self.cnf.and_lits(vec![g, c]));
            }
            cs.push(self.cnf.or_lits(alts));
        }
        Ok(self.cnf.and_lits(cs))
    }

    /// Transition constraint between steps t and t+1 (or arbitrary pairs
    /// for loop closing).
    pub fn trans(&mut self, cur: usize, next: usize) -> EResult<Lit> {
        let node = self.flat.trans.clone();
        let mut cs = vec![self.enc_trans_node(&node, cur, next)?];
        for d in &self.flat.trans_defs.clone() {
            cs.push(self.enc_bool(d, cur, next)?);
        }
        cs.push(self.domain(next));
        for i in &self.flat.invariants.clone() {
            cs.push(self.enc_bool(i, next, next)?);
        }
        Ok(self.cnf.and_lits(cs))
    }

    fn enc_trans_node(&mut self, node: &TransNode, cur: usize, next: usize) -> EResult<Lit> {
        Ok(match node {
            TransNode::True => self.cnf.tt,
            TransNode::Cmds(cmds) => {
                let mut alts = Vec::new();
                for cmd in cmds {
                    let g = self.enc_bool(&cmd.guard, cur, next)?;
                    let c = self.enc_bool(&cmd.constraint, cur, next)?;
                    alts.push(self.cnf.and_lits(vec![g, c]));
                }
                self.cnf.or_lits(alts)
            }
            TransNode::All(nodes) => {
                let mut cs = Vec::new();
                for n in nodes {
                    cs.push(self.enc_trans_node(n, cur, next)?);
                }
                self.cnf.and_lits(cs)
            }
            TransNode::Interleave(branches) => {
                let mut alts = Vec::new();
                for (n, frame) in branches {
                    let e = self.enc_trans_node(n, cur, next)?;
                    let f = self.enc_bool(frame, cur, next)?;
                    alts.push(self.cnf.and_lits(vec![e, f]));
                }
                self.cnf.or_lits(alts)
            }
        })
    }

    /// Equality of the full states at two steps (for loop closing we use a
    /// transition from step k to a state equal to step l — here we encode
    /// state equality directly).
    pub fn state_eq(&mut self, s: usize, t: usize) -> Lit {
        let mut cs = Vec::new();
        for l in 0..self.bits.len() {
            let nbits = self.bits[l].0;
            for b in 0..nbits {
                let x = self.cnf.bitvar(l as u32, b, s);
                let y = self.cnf.bitvar(l as u32, b, t);
                cs.push(self.cnf.iff_lit(x, y));
            }
        }
        self.cnf.and_lits(cs)
    }

    /// Decode a model into per-step states.
    pub fn decode(&self, model: &dyn Fn(i32) -> bool, steps: usize) -> Vec<Vec<Value>> {
        let mut out = Vec::new();
        for t in 0..=steps {
            let mut state = Vec::new();
            for (l, (nbits, values)) in self.bits.iter().enumerate() {
                let mut idx = 0usize;
                for b in 0..*nbits {
                    if let Some(&v) = self.cnf.bitvars.get(&(l as u32, b, t)) {
                        if model(v) {
                            idx |= 1 << b;
                        }
                    }
                }
                let idx = idx.min(values.len().saturating_sub(1));
                state.push(values[idx].clone());
            }
            out.push(state);
        }
        out
    }
}

fn as_parts(cnf: &mut Cnf, p: PartsOrLit) -> Vec<(Value, Lit)> {
    match p {
        PartsOrLit::P(p) => p,
        PartsOrLit::L(l) => vec![(Value::Bool(true), l), (Value::Bool(false), -l)],
    }
}

fn push_part(cnf: &mut Cnf, parts: &mut Vec<(Value, Lit)>, v: Value, c: Lit) {
    for (v0, c0) in parts.iter_mut() {
        if *v0 == v {
            *c0 = cnf.or_lits(vec![*c0, c]);
            return;
        }
    }
    parts.push((v, c));
}

/// Adapter: bounded-LTL over the CNF encoder (atoms at absolute steps).
pub struct CnfAlg<'a, 'm> {
    pub enc: &'a mut BmcEnc<'m>,
}

impl<'a, 'm> BoolAlg for CnfAlg<'a, 'm> {
    type B = Lit;

    fn tt(&mut self) -> Lit {
        self.enc.cnf.tt
    }

    fn ff(&mut self) -> Lit {
        -self.enc.cnf.tt
    }

    fn and(&mut self, xs: Vec<Lit>) -> Lit {
        self.enc.cnf.and_lits(xs)
    }

    fn or(&mut self, xs: Vec<Lit>) -> Lit {
        self.enc.cnf.or_lits(xs)
    }

    fn not(&mut self, x: Lit) -> Lit {
        -x
    }

    fn atom(&mut self, e: &FExpr, t: usize) -> Lit {
        self.enc
            .enc_bool(e, t, t)
            .expect("atom encoding failed")
    }
}

/// Result of a BMC query.
pub enum BmcResult {
    NoCe(usize),
    Counterexample(Vec<Vec<Value>>),
    Proved,
    InductionFailed,
}

/// Solve with varisat.
pub fn solve(cnf: &Cnf, assumptions: &[Lit]) -> Option<Vec<bool>> {
    use varisat::{CnfFormula, ExtendFormula, Lit as VLit, Solver};
    let mut solver = Solver::new();
    let mut formula = CnfFormula::new();
    for cl in &cnf.clauses {
        let lits: Vec<VLit> = cl
            .iter()
            .map(|&l| VLit::from_dimacs(l as isize))
            .collect();
        formula.add_clause(&lits);
    }
    for &a in assumptions {
        formula.add_clause(&[VLit::from_dimacs(a as isize)]);
    }
    solver.add_formula(&formula);
    match solver.solve() {
        Ok(true) => {
            let model = solver.model().unwrap();
            let mut vals = vec![false; (cnf.nvars + 1) as usize];
            for l in model {
                let d = l.to_dimacs();
                if d > 0 {
                    vals[d as usize] = true;
                }
            }
            Some(vals)
        }
        _ => None,
    }
}

/// BMC search for a counterexample to `formula` up to `depth`.
pub fn bmc_search(
    flat: &FlatModule,
    formula: &sal_flat::formula::TFormula,
    depth: usize,
    lemmas: &[FExpr],
) -> EResult<BmcResult> {
    let neg = crate::ltl::to_nnf(formula, true).map_err(EngineError::Eval)?;
    let neg = std::rc::Rc::new(neg);
    for k in 0..=depth {
        let mut enc = BmcEnc::new(flat)?;
        let mut constraints = vec![enc.init()?];
        for t in 0..k {
            constraints.push(enc.trans(t, t + 1)?);
        }
        for t in 0..=k {
            for lemma in lemmas {
                constraints.push(enc.enc_bool(lemma, t, t)?);
            }
        }
        // property: no-loop case OR loop cases
        let (mut alts, loop_lits) = {
            let mut alts = Vec::new();
            let mut loops = Vec::new();
            {
                let mut alg = CnfAlg { enc: &mut enc };
                let mut bltl = BoundedLtl::new(&mut alg, k);
                let nl = bltl.no_loop(&neg, 0);
                alts.push((nl, None));
                for l in 0..=k {
                    let wl = {
                        let mut alg2 = CnfAlg { enc: bltl.alg.enc };
                        let mut b2 = BoundedLtl::new(&mut alg2, k);
                        b2.with_loop(&neg, 0, l)
                    };
                    loops.push((l, wl));
                }
            }
            (alts, loops)
        };
        for (l, wl) in loop_lits {
            // loop condition: trans(k, fresh state equal to state at l)
            let tk = enc.trans(k, k + 1)?;
            let eq = enc.state_eq(k + 1, l);
            let cond = enc.cnf.and_lits(vec![tk, eq, wl]);
            alts.push((cond, Some(l)));
        }
        let alt_lits: Vec<Lit> = alts.iter().map(|(l, _)| *l).collect();
        let prop = enc.cnf.or_lits(alt_lits);
        constraints.push(prop);
        let all = enc.cnf.and_lits(constraints);
        if let Some(model) = solve(&enc.cnf, &[all]) {
            let states = enc.decode(&|v| model[v as usize], k);
            return Ok(BmcResult::Counterexample(states));
        }
    }
    Ok(BmcResult::NoCe(depth))
}

/// k-induction for an invariant property `G p`.
pub fn k_induction(
    flat: &FlatModule,
    prop: &FExpr,
    k: usize,
    lemmas: &[FExpr],
) -> EResult<BmcResult> {
    // base: no counterexample within k steps
    let mut enc = BmcEnc::new(flat)?;
    {
        let mut cs = vec![enc.init()?];
        for t in 0..k {
            cs.push(enc.trans(t, t + 1)?);
        }
        let mut bad = Vec::new();
        for t in 0..=k {
            let p = enc.enc_bool(prop, t, t)?;
            bad.push(-p);
            for lemma in lemmas {
                cs.push(enc.enc_bool(lemma, t, t)?);
            }
        }
        cs.push(enc.cnf.or_lits(bad));
        let all = enc.cnf.and_lits(cs);
        if let Some(model) = solve(&enc.cnf, &[all]) {
            let states = enc.decode(&|v| model[v as usize], k);
            return Ok(BmcResult::Counterexample(states));
        }
    }
    // induction step: p at 0..k, path of length k+1, ¬p at k+1
    let mut enc = BmcEnc::new(flat)?;
    {
        let mut cs = vec![enc.domain(0)];
        for i in &flat.invariants.clone() {
            cs.push(enc.enc_bool(i, 0, 0)?);
        }
        for t in 0..=k {
            cs.push(enc.trans(t, t + 1)?);
        }
        for t in 0..=k {
            let p = enc.enc_bool(prop, t, t)?;
            cs.push(p);
            for lemma in lemmas {
                cs.push(enc.enc_bool(lemma, t, t)?);
            }
        }
        for lemma in lemmas {
            let l = enc.enc_bool(lemma, k + 1, k + 1)?;
            cs.push(l);
        }
        let p = enc.enc_bool(prop, k + 1, k + 1)?;
        cs.push(-p);
        let all = enc.cnf.and_lits(cs);
        if solve(&enc.cnf, &[all]).is_some() {
            return Ok(BmcResult::InductionFailed);
        }
    }
    Ok(BmcResult::Proved)
}
