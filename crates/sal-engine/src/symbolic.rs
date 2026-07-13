//! BDD-based symbolic engine: encodes the flat transition system into
//! BDDs and provides reachability, invariant checking, deadlock detection
//! and counterexample extraction.

use rustc_hash::FxHashMap as HashMap;

use sal_flat::fexpr::{FExpr, LeafId};
use sal_flat::flatten::{FlatModule, TransNode};
use sal_flat::value::Value;

use crate::bdd::{Mgr, NodeId, F, T};
use crate::explicit::EngineError;

type EResult<Tv> = Result<Tv, EngineError>;

/// Bit layout: leaf `l` with `bits` bits uses BDD variables
/// `base .. base + 2*bits`, alternating cur (even offset) / next (odd).
struct LeafEnc {
    base: u32,
    bits: u32,
    values: Vec<Value>,
}

pub struct Symbolic<'m> {
    pub flat: &'m FlatModule,
    pub mgr: Mgr,
    leaves: Vec<LeafEnc>,
    /// Domain constraint (valid encodings), current vars.
    domain: NodeId,
    pub init: NodeId,
    /// Disjunctive partition of the transition relation (each part
    /// includes the global conjuncts). `image`/`preimage` iterate the
    /// parts, avoiding one monolithic BDD.
    pub parts: Vec<NodeId>,
    /// Per-command relations for trace labeling: (provenance, relation).
    pub cmd_relations: Vec<(String, NodeId)>,
}

fn bits_for(card: u64) -> u32 {
    let mut b = 0;
    while (1u64 << b) < card {
        b += 1;
    }
    b.max(1)
}

impl<'m> Symbolic<'m> {
    pub fn new(flat: &'m FlatModule) -> EResult<Self> {
        let mut mgr = Mgr::new();
        let mut leaves = Vec::new();
        let mut base = 0u32;
        for l in &flat.leaves {
            let values = l.ty.values().ok_or_else(|| {
                EngineError::InfiniteType(l.name.clone())
            })?;
            let bits = bits_for(values.len() as u64);
            leaves.push(LeafEnc {
                base,
                bits,
                values,
            });
            base += 2 * bits;
        }
        let mut s = Symbolic {
            flat,
            mgr,
            leaves,
            domain: T,
            init: F,
            parts: Vec::new(),
            cmd_relations: Vec::new(),
        };
        s.build()?;
        Ok(s)
    }

    // -- encoding -----------------------------------------------------------

    /// BDD for `leaf (primed?) == value index i`.
    fn leaf_eq_index(&mut self, l: usize, primed: bool, i: usize) -> NodeId {
        let enc = &self.leaves[l];
        let base = enc.base;
        let bits = enc.bits;
        let mut r = T;
        for b in 0..bits {
            let var = base + 2 * b + if primed { 1 } else { 0 };
            let bit = (i >> b) & 1 == 1;
            let lit = if bit {
                self.mgr.var(var)
            } else {
                self.mgr.nvar(var)
            };
            r = self.mgr.and(r, lit);
        }
        r
    }

    fn domain_constraint(&mut self, l: usize, primed: bool) -> NodeId {
        let n = self.leaves[l].values.len();
        let bits = self.leaves[l].bits;
        if n == (1usize << bits) {
            return T;
        }
        let mut r = F;
        for i in 0..n {
            let c = self.leaf_eq_index(l, primed, i);
            r = self.mgr.or(r, c);
        }
        r
    }

    /// Symbolic value: boolean BDD or partition of concrete values.
    fn enc(&mut self, e: &FExpr) -> EResult<Enc> {
        use FExpr::*;
        Ok(match e {
            Const(Value::Bool(b)) => Enc::B(if *b { T } else { F }),
            Const(v) => Enc::P(vec![(v.clone(), T)]),
            Var(l, primed) => {
                let idx = *l as usize;
                let vals = self.leaves[idx].values.clone();
                if matches!(
                    self.flat.leaves[idx].ty,
                    sal_flat::fexpr::LeafType::Bool
                ) {
                    // single bit
                    let var = self.leaves[idx].base + if *primed { 1 } else { 0 };
                    Enc::B(self.mgr.var(var))
                } else {
                    let mut parts = Vec::new();
                    for (i, v) in vals.iter().enumerate() {
                        let c = self.leaf_eq_index(idx, *primed, i);
                        parts.push((v.clone(), c));
                    }
                    Enc::P(parts)
                }
            }
            Not(a) => {
                let ea = self.enc_bool(a)?;
                Enc::B(self.mgr.not(ea))
            }
            And(es) => {
                let mut r = T;
                for x in es {
                    let e = self.enc_bool(x)?;
                    r = self.mgr.and(r, e);
                    if r == F {
                        break;
                    }
                }
                Enc::B(r)
            }
            Or(es) => {
                let mut r = F;
                for x in es {
                    let e = self.enc_bool(x)?;
                    r = self.mgr.or(r, e);
                    if r == T {
                        break;
                    }
                }
                Enc::B(r)
            }
            Ite(c, t, f) => {
                let ec = self.enc_bool(c)?;
                let et = self.enc(t)?;
                let ef = self.enc(f)?;
                match (et, ef) {
                    (Enc::B(a), Enc::B(b)) => Enc::B(self.mgr.ite(ec, a, b)),
                    (t, f) => {
                        let pt = self.as_partition(t);
                        let pf = self.as_partition(f);
                        let mut merged: Vec<(Value, NodeId)> = Vec::new();
                        let nec = self.mgr.not(ec);
                        for (v, c) in pt {
                            let cc = self.mgr.and(ec, c);
                            push_part(&mut self.mgr, &mut merged, v, cc);
                        }
                        for (v, c) in pf {
                            let cc = self.mgr.and(nec, c);
                            push_part(&mut self.mgr, &mut merged, v, cc);
                        }
                        Enc::P(merged)
                    }
                }
            }
            Eq(a, b) => {
                let ea = self.enc(a)?;
                let eb = self.enc(b)?;
                match (ea, eb) {
                    (Enc::B(x), Enc::B(y)) => Enc::B(self.mgr.iff(x, y)),
                    (x, y) => {
                        let px = self.as_partition(x);
                        let py = self.as_partition(y);
                        let mut r = F;
                        for (v1, c1) in &px {
                            for (v2, c2) in &py {
                                if v1 == v2 {
                                    let c = self.mgr.and(*c1, *c2);
                                    r = self.mgr.or(r, c);
                                }
                            }
                        }
                        Enc::B(r)
                    }
                }
            }
            Lt(a, b) | Le(a, b) => {
                let strict = matches!(e, Lt(..));
                let pa = self.enc_part(a)?;
                let pb = self.enc_part(b)?;
                let mut r = F;
                for (v1, c1) in &pa {
                    for (v2, c2) in &pb {
                        let (Value::Num(x), Value::Num(y)) = (v1, v2) else {
                            return Err(EngineError::Eval(
                                "numeric comparison on non-numeric values".into(),
                            ));
                        };
                        let holds = if strict { x < y } else { x <= y };
                        if holds {
                            let c = self.mgr.and(*c1, *c2);
                            r = self.mgr.or(r, c);
                        }
                    }
                }
                Enc::B(r)
            }
            Add(es) => {
                let mut acc: Vec<(Value, NodeId)> =
                    vec![(Value::Num(num_rational::BigRational::from_integer(0.into())), T)];
                for x in es {
                    let px = self.enc_part(x)?;
                    acc = self.combine(&acc, &px, |a, b| match (a, b) {
                        (Value::Num(x), Value::Num(y)) => Some(Value::Num(x + y)),
                        _ => None,
                    })?;
                }
                Enc::P(acc)
            }
            Mul(es) => {
                let mut acc: Vec<(Value, NodeId)> =
                    vec![(Value::Num(num_rational::BigRational::from_integer(1.into())), T)];
                for x in es {
                    let px = self.enc_part(x)?;
                    acc = self.combine(&acc, &px, |a, b| match (a, b) {
                        (Value::Num(x), Value::Num(y)) => Some(Value::Num(x * y)),
                        _ => None,
                    })?;
                }
                Enc::P(acc)
            }
            Neg(a) => {
                let pa = self.enc_part(a)?;
                let mut out = Vec::new();
                for (v, c) in pa {
                    match v {
                        Value::Num(n) => out.push((Value::Num(-n), c)),
                        _ => return Err(EngineError::Eval("number expected".into())),
                    }
                }
                Enc::P(out)
            }
            Div(a, b) | IDiv(a, b) | Mod(a, b) => {
                use num_traits::Zero;
                let pa = self.enc_part(a)?;
                let pb = self.enc_part(b)?;
                let mut out: Vec<(Value, NodeId)> = Vec::new();
                for (v1, c1) in &pa {
                    for (v2, c2) in &pb {
                        let (Value::Num(x), Value::Num(y)) = (v1, v2) else {
                            return Err(EngineError::Eval("number expected".into()));
                        };
                        if y.is_zero() {
                            continue; // no transition where divisor is 0
                        }
                        let r = match e {
                            Div(..) => Value::Num(x / y),
                            _ => {
                                if !x.is_integer() || !y.is_integer() {
                                    continue;
                                }
                                let (xi, yi) = (x.to_integer(), y.to_integer());
                                let q = &xi / &yi;
                                let rr = &xi - &q * &yi;
                                let (q, rr) = if rr < Zero::zero() {
                                    if yi > Zero::zero() {
                                        (q - 1, rr + &yi)
                                    } else {
                                        (q + 1, rr - &yi)
                                    }
                                } else {
                                    (q, rr)
                                };
                                Value::Num(num_rational::BigRational::from_integer(
                                    if matches!(e, IDiv(..)) { q } else { rr },
                                ))
                            }
                        };
                        let c = self.mgr.and(*c1, *c2);
                        push_part(&mut self.mgr, &mut out, r, c);
                    }
                }
                Enc::P(out)
            }
        })
    }

    fn combine(
        &mut self,
        a: &[(Value, NodeId)],
        b: &[(Value, NodeId)],
        f: impl Fn(&Value, &Value) -> Option<Value>,
    ) -> EResult<Vec<(Value, NodeId)>> {
        let mut out: Vec<(Value, NodeId)> = Vec::new();
        for (v1, c1) in a {
            for (v2, c2) in b {
                let Some(v) = f(v1, v2) else {
                    return Err(EngineError::Eval("number expected".into()));
                };
                let c = self.mgr.and(*c1, *c2);
                if c != F {
                    push_part(&mut self.mgr, &mut out, v, c);
                }
            }
        }
        Ok(out)
    }

    pub fn enc_bool(&mut self, e: &FExpr) -> EResult<NodeId> {
        match self.enc(e)? {
            Enc::B(b) => Ok(b),
            Enc::P(p) => {
                // partition of booleans?
                let mut r = F;
                for (v, c) in p {
                    match v {
                        Value::Bool(true) => r = self.mgr.or(r, c),
                        Value::Bool(false) => {}
                        _ => {
                            return Err(EngineError::Eval(
                                "boolean expression expected".into(),
                            ))
                        }
                    }
                }
                Ok(r)
            }
        }
    }

    fn enc_part(&mut self, e: &FExpr) -> EResult<Vec<(Value, NodeId)>> {
        let enc = self.enc(e)?;
        Ok(self.as_partition(enc))
    }

    fn as_partition(&mut self, e: Enc) -> Vec<(Value, NodeId)> {
        match e {
            Enc::P(p) => p,
            Enc::B(b) => {
                let nb = self.mgr.not(b);
                vec![(Value::Bool(true), b), (Value::Bool(false), nb)]
            }
        }
    }

    // -- system construction --------------------------------------------------

    fn build(&mut self) -> EResult<()> {
        // domain constraints
        let mut dom_cur = T;
        let mut dom_next = T;
        for l in 0..self.leaves.len() {
            let c = self.domain_constraint(l, false);
            dom_cur = self.mgr.and(dom_cur, c);
            let n = self.domain_constraint(l, true);
            dom_next = self.mgr.and(dom_next, n);
        }
        self.domain = dom_cur;

        // invariants (current form)
        let mut inv = T;
        for i in &self.flat.invariants.clone() {
            let b = self.enc_bool(i)?;
            inv = self.mgr.and(inv, b);
        }
        let inv_next = self.prime(inv);

        // init
        let mut init = self.mgr.and(dom_cur, inv);
        for d in &self.flat.init_defs.clone() {
            let b = self.enc_bool(d)?;
            init = self.mgr.and(init, b);
        }
        for block in &self.flat.init_choices.clone() {
            let mut alt = F;
            for cmd in block {
                let g = self.enc_bool(&cmd.guard)?;
                let c = self.enc_bool(&cmd.constraint)?;
                let gc = self.mgr.and(g, c);
                alt = self.mgr.or(alt, gc);
            }
            init = self.mgr.and(init, alt);
        }
        self.init = init;

        // transition relation: global conjuncts applied to every
        // disjunctive part
        let mut global = self.mgr.and(dom_cur, dom_next);
        global = self.mgr.and(global, inv);
        global = self.mgr.and(global, inv_next);
        for d in &self.flat.trans_defs.clone() {
            let b = self.enc_bool(d)?;
            global = self.mgr.and(global, b);
        }
        let node = self.flat.trans.clone();
        let mut parts = Vec::new();
        self.enc_trans_parts(&node, global, &mut parts)?;
        self.parts = parts;
        Ok(())
    }

    /// Split the top-level choice structure into disjuncts, conjoining
    /// `pre` (accumulated global/frame constraints) into each.
    fn enc_trans_parts(
        &mut self,
        node: &TransNode,
        pre: NodeId,
        out: &mut Vec<NodeId>,
    ) -> EResult<()> {
        match node {
            TransNode::Interleave(branches) => {
                for (n, frame) in branches {
                    let f = self.enc_bool(frame)?;
                    let pre2 = self.mgr.and(pre, f);
                    if pre2 != F {
                        self.enc_trans_parts(n, pre2, out)?;
                    }
                }
                Ok(())
            }
            TransNode::Cmds(cmds) => {
                for cmd in cmds {
                    let g = self.enc_bool(&cmd.guard)?;
                    let c = self.enc_bool(&cmd.constraint)?;
                    let gc = self.mgr.and(g, c);
                    self.cmd_relations
                        .push((cmd.label.clone().unwrap_or_default(), gc));
                    let part = self.mgr.and(pre, gc);
                    if part != F {
                        out.push(part);
                    }
                }
                Ok(())
            }
            other => {
                let t = self.enc_trans(other)?;
                let part = self.mgr.and(pre, t);
                if part != F {
                    out.push(part);
                }
                Ok(())
            }
        }
    }

    fn enc_trans(&mut self, node: &TransNode) -> EResult<NodeId> {
        Ok(match node {
            TransNode::True => T,
            TransNode::Cmds(cmds) => {
                let mut r = F;
                for cmd in cmds {
                    let g = self.enc_bool(&cmd.guard)?;
                    let c = self.enc_bool(&cmd.constraint)?;
                    let gc = self.mgr.and(g, c);
                    self.cmd_relations.push((
                        cmd.label.clone().unwrap_or_default(),
                        gc,
                    ));
                    r = self.mgr.or(r, gc);
                }
                r
            }
            TransNode::All(nodes) => {
                let mut r = T;
                for n in nodes {
                    let e = self.enc_trans(n)?;
                    r = self.mgr.and(r, e);
                }
                r
            }
            TransNode::Interleave(branches) => {
                let mut r = F;
                for (n, frame) in branches {
                    let e = self.enc_trans(n)?;
                    let f = self.enc_bool(frame)?;
                    let ef = self.mgr.and(e, f);
                    r = self.mgr.or(r, ef);
                }
                r
            }
        })
    }

    fn prime(&mut self, n: NodeId) -> NodeId {
        self.mgr.shift(n, 1)
    }

    fn unprime(&mut self, n: NodeId) -> NodeId {
        self.mgr.shift(n, -1)
    }

    fn exists_cur(&mut self, n: NodeId) -> NodeId {
        self.mgr.exists_where(n, &|v| v % 2 == 0, 1)
    }

    fn exists_next(&mut self, n: NodeId) -> NodeId {
        self.mgr.exists_where(n, &|v| v % 2 == 1, 2)
    }

    /// Image: successor states of `s` (over current vars).
    pub fn image(&mut self, s: NodeId) -> NodeId {
        let parts = self.parts.clone();
        let mut out = F;
        for p in parts {
            let step = self.mgr.and(p, s);
            if step == F {
                continue;
            }
            let next = self.exists_cur(step);
            let img = self.unprime(next);
            out = self.mgr.or(out, img);
        }
        out
    }

    /// Preimage of `s'` (given over current vars).
    pub fn preimage(&mut self, s: NodeId) -> NodeId {
        let sp = self.prime(s);
        let parts = self.parts.clone();
        let mut out = F;
        for p in parts {
            let step = self.mgr.and(p, sp);
            if step == F {
                continue;
            }
            let pre = self.exists_next(step);
            out = self.mgr.or(out, pre);
        }
        out
    }

    /// Forward reachability; returns (reach set, onion rings).
    pub fn reach(&mut self) -> (NodeId, Vec<NodeId>) {
        let mut rings = vec![self.init];
        let mut reach = self.init;
        let mut frontier = self.init;
        loop {
            let img = self.image(frontier);
            let nreach = self.mgr.or(reach, img);
            if nreach == reach {
                break;
            }
            let not_reach = self.mgr.not(reach);
            frontier = self.mgr.and(img, not_reach);
            rings.push(frontier);
            reach = nreach;
        }
        (reach, rings)
    }

    /// Check `G prop`. Returns Ok(None) if proved, Ok(Some(path)) with a
    /// shortest counterexample otherwise.
    pub fn check_invariant(&mut self, prop: &FExpr) -> EResult<Option<Vec<Vec<Value>>>> {
        let p = self.enc_bool(prop)?;
        let bad = self.mgr.not(p);
        let mut rings = vec![self.init];
        let mut reach = self.init;
        let mut frontier = self.init;
        loop {
            let hit = self.mgr.and(frontier, bad);
            if hit != F {
                return Ok(Some(self.extract_path(&rings, hit)));
            }
            let img = self.image(frontier);
            let nreach = self.mgr.or(reach, img);
            if nreach == reach {
                return Ok(None);
            }
            let not_reach = self.mgr.not(reach);
            frontier = self.mgr.and(img, not_reach);
            rings.push(frontier);
            reach = nreach;
        }
    }

    /// BDD for one concrete state (over current vars).
    pub fn state_bdd(&mut self, state: &[Value]) -> NodeId {
        let mut r = T;
        for (l, v) in state.iter().enumerate() {
            let i = self.leaves[l]
                .values
                .iter()
                .position(|x| x == v)
                .unwrap_or(0);
            let c = self.leaf_eq_index(l, false, i);
            r = self.mgr.and(r, c);
        }
        r
    }

    /// Shortest path (as concrete states) from a state in `start` to a
    /// state in `target`, with ring index in [min_depth, max_depth].
    /// Returns None when unreachable within the bound.
    pub fn find_path(
        &mut self,
        start: NodeId,
        target: NodeId,
        min_depth: usize,
        max_depth: Option<usize>,
    ) -> Option<Vec<Vec<Value>>> {
        let mut rings = vec![start];
        let mut reach = start;
        let mut frontier = start;
        let mut k = 0usize;
        loop {
            if k >= min_depth {
                let hit = self.mgr.and(frontier, target);
                if hit != F {
                    return Some(self.extract_path(&rings, hit));
                }
            }
            if let Some(max) = max_depth {
                if k >= max {
                    return None;
                }
            }
            let img = self.image(frontier);
            let nreach = self.mgr.or(reach, img);
            if nreach == reach {
                return None;
            }
            let nr = self.mgr.not(reach);
            frontier = self.mgr.and(img, nr);
            rings.push(frontier);
            reach = nreach;
            k += 1;
        }
    }

    /// Names/classes of the leaves (for ATG output).
    pub fn leaf_count(&self) -> usize {
        self.leaves.len()
    }

    /// Generate an execution path of up to `depth` steps (fewer only if a
    /// deadlock is reached).
    pub fn random_path(&mut self, depth: usize) -> EResult<Vec<Vec<Value>>> {
        if self.init == F {
            return Err(EngineError::Eval(
                "the module has no initial states".into(),
            ));
        }
        let mut out = Vec::new();
        let mut cube = self.state_cube(self.init);
        out.push(self.decode_state(&cube));
        for _ in 0..depth {
            let sb = self.assignment_bdd(&cube);
            let succ = self.image(sb);
            if succ == F {
                break;
            }
            cube = self.state_cube(succ);
            out.push(self.decode_state(&cube));
        }
        Ok(out)
    }

    /// Check that `prop` holds in every initial state.
    pub fn check_initial(&mut self, prop: &FExpr) -> EResult<Option<Vec<Vec<Value>>>> {
        let p = self.enc_bool(prop)?;
        let bad = self.mgr.not(p);
        let hit = self.mgr.and(self.init, bad);
        if hit == F {
            return Ok(None);
        }
        let cube = self.state_cube(hit);
        Ok(Some(vec![self.decode_state(&cube)]))
    }

    /// Check for reachable deadlock states.
    pub fn check_deadlock(&mut self) -> EResult<Option<Vec<Vec<Value>>>> {
        let has_succ = {
            let parts = self.parts.clone();
            let mut acc = F;
            for p in parts {
                let e = self.exists_next(p);
                acc = self.mgr.or(acc, e);
            }
            acc
        };
        let dead = self.mgr.not(has_succ);
        let dead = self.mgr.and(dead, self.domain);
        let mut rings = vec![self.init];
        let mut reach = self.init;
        let mut frontier = self.init;
        loop {
            let hit = self.mgr.and(frontier, dead);
            if hit != F {
                return Ok(Some(self.extract_path(&rings, hit)));
            }
            let img = self.image(frontier);
            let nreach = self.mgr.or(reach, img);
            if nreach == reach {
                return Ok(None);
            }
            let not_reach = self.mgr.not(reach);
            frontier = self.mgr.and(img, not_reach);
            rings.push(frontier);
            reach = nreach;
        }
    }

    /// Extract a concrete shortest path ending in a state of `target`
    /// (which must intersect the last ring).
    fn extract_path(&mut self, rings: &[NodeId], target: NodeId) -> Vec<Vec<Value>> {
        let k = rings.len() - 1;
        let mut states: Vec<HashMap<u32, bool>> = vec![HashMap::default(); k + 1];
        let hit = self.mgr.and(rings[k], target);
        let cube = self.state_cube(hit);
        states[k] = cube;
        for i in (0..k).rev() {
            // predecessor of states[i+1] within rings[i]
            let succ_state = self.assignment_bdd(&states[i + 1]);
            let pre = self.preimage(succ_state);
            let cand = self.mgr.and(pre, rings[i]);
            states[i] = self.state_cube(cand);
        }
        states
            .iter()
            .map(|a| self.decode_state(a))
            .collect()
    }

    /// Pick one full state assignment from a nonempty set.
    fn state_cube(&mut self, set: NodeId) -> HashMap<u32, bool> {
        let mut partial = self.mgr.pick(set).unwrap_or_default();
        // complete: unconstrained current bits default to false (valid if
        // in-domain; ensure by conjoining domain first)
        for l in &self.leaves {
            for b in 0..l.bits {
                partial.entry(l.base + 2 * b).or_insert(false);
            }
        }
        partial
    }

    fn assignment_bdd(&mut self, a: &HashMap<u32, bool>) -> NodeId {
        let mut r = T;
        for l in 0..self.leaves.len() {
            let (base, bits) = (self.leaves[l].base, self.leaves[l].bits);
            for b in 0..bits {
                let var = base + 2 * b;
                let val = a.get(&var).copied().unwrap_or(false);
                let lit = if val {
                    self.mgr.var(var)
                } else {
                    self.mgr.nvar(var)
                };
                r = self.mgr.and(r, lit);
            }
        }
        r
    }

    /// Decode a bit assignment into per-leaf values.
    pub fn decode_state(&self, a: &HashMap<u32, bool>) -> Vec<Value> {
        let mut out = Vec::new();
        for l in &self.leaves {
            let mut idx = 0usize;
            for b in 0..l.bits {
                if a.get(&(l.base + 2 * b)).copied().unwrap_or(false) {
                    idx |= 1 << b;
                }
            }
            let idx = idx.min(l.values.len().saturating_sub(1));
            out.push(l.values[idx].clone());
        }
        out
    }
}

impl<'m> Symbolic<'m> {
    // ------------------------------------------------------------------
    // CTL model checking (fixpoints)
    // ------------------------------------------------------------------

    /// Check a CTL formula: holds iff every initial state satisfies it.
    /// Returns a (single-state) counterexample when it fails.
    pub fn check_ctl(&mut self, f: &sal_flat::formula::TFormula) -> EResult<Option<Vec<Vec<Value>>>> {
        let sat = self.ctl_sat(f)?;
        let nsat = self.mgr.not(sat);
        let bad = self.mgr.and(self.init, nsat);
        if bad == F {
            return Ok(None);
        }
        let cube = self.state_cube(bad);
        Ok(Some(vec![self.decode_state(&cube)]))
    }

    fn ctl_sat(&mut self, f: &sal_flat::formula::TFormula) -> EResult<NodeId> {
        use sal_flat::formula::TFormula::*;
        Ok(match f {
            Atom(e) => {
                let b = self.enc_bool(e)?;
                self.mgr.and(b, self.domain)
            }
            Not(a) => {
                let s = self.ctl_sat(a)?;
                let n = self.mgr.not(s);
                self.mgr.and(n, self.domain)
            }
            And(a, b) => {
                let x = self.ctl_sat(a)?;
                let y = self.ctl_sat(b)?;
                self.mgr.and(x, y)
            }
            Or(a, b) => {
                let x = self.ctl_sat(a)?;
                let y = self.ctl_sat(b)?;
                self.mgr.or(x, y)
            }
            EX(a) => {
                let s = self.ctl_sat(a)?;
                self.preimage(s)
            }
            AX(a) => {
                let s = self.ctl_sat(a)?;
                let ns = self.mgr.not(s);
                let ex = self.preimage(ns);
                let nex = self.mgr.not(ex);
                self.mgr.and(nex, self.domain)
            }
            EG(a) => {
                let s = self.ctl_sat(a)?;
                self.eg(s)
            }
            EF(a) => {
                let s = self.ctl_sat(a)?;
                self.eu(self.domain, s)
            }
            AF(a) => {
                // AF f = ¬EG ¬f
                let s = self.ctl_sat(a)?;
                let ns = self.mgr.not(s);
                let nsd = self.mgr.and(ns, self.domain);
                let eg = self.eg(nsd);
                let r = self.mgr.not(eg);
                self.mgr.and(r, self.domain)
            }
            AG(a) => {
                // AG f = ¬EF ¬f
                let s = self.ctl_sat(a)?;
                let ns = self.mgr.not(s);
                let nsd = self.mgr.and(ns, self.domain);
                let ef = self.eu(self.domain, nsd);
                let r = self.mgr.not(ef);
                self.mgr.and(r, self.domain)
            }
            EU(a, b) => {
                let x = self.ctl_sat(a)?;
                let y = self.ctl_sat(b)?;
                self.eu(x, y)
            }
            AU(a, b) => {
                // A[f U g] = ¬(E[¬g U ¬f∧¬g] ∨ EG ¬g)
                let x = self.ctl_sat(a)?;
                let y = self.ctl_sat(b)?;
                let nx = self.mgr.not(x);
                let ny = self.mgr.not(y);
                let nxny = self.mgr.and(nx, ny);
                let nyd = self.mgr.and(ny, self.domain);
                let e1 = self.eu(nyd, nxny);
                let e2 = self.eg(nyd);
                let bad = self.mgr.or(e1, e2);
                let r = self.mgr.not(bad);
                self.mgr.and(r, self.domain)
            }
            ER(a, b) => {
                // E[f R g] = ¬A[¬f U ¬g]
                let na = Not(std::rc::Rc::new((**a).clone()));
                let nb = Not(std::rc::Rc::new((**b).clone()));
                let au = AU(std::rc::Rc::new(na), std::rc::Rc::new(nb));
                let s = self.ctl_sat(&au)?;
                let r = self.mgr.not(s);
                self.mgr.and(r, self.domain)
            }
            AR(a, b) => {
                // A[f R g] = ¬E[¬f U ¬g]
                let x = self.ctl_sat(a)?;
                let y = self.ctl_sat(b)?;
                let nx = self.mgr.not(x);
                let ny = self.mgr.not(y);
                let nxd = self.mgr.and(nx, self.domain);
                let nyd = self.mgr.and(ny, self.domain);
                let e = self.eu(nxd, nyd);
                let r = self.mgr.not(e);
                self.mgr.and(r, self.domain)
            }
            other => {
                return Err(EngineError::Eval(format!(
                    "LTL operator in CTL formula: {:?}",
                    other
                )))
            }
        })
    }

    fn eu(&mut self, f: NodeId, g: NodeId) -> NodeId {
        let mut z = g;
        loop {
            let pre = self.preimage(z);
            let fpre = self.mgr.and(f, pre);
            let nz = self.mgr.or(z, fpre);
            if nz == z {
                return z;
            }
            z = nz;
        }
    }

    fn eg(&mut self, f: NodeId) -> NodeId {
        let mut z = f;
        loop {
            let pre = self.preimage(z);
            let nz = self.mgr.and(f, pre);
            if nz == z {
                return z;
            }
            z = nz;
        }
    }

    // ------------------------------------------------------------------
    // LTL model checking (Büchi product + Emerson-Lei)
    // ------------------------------------------------------------------

    /// Check an LTL formula; returns None when proved, or a
    /// counterexample path (lasso prefix; loop appended) when refuted.
    pub fn check_ltl(
        &mut self,
        f: &sal_flat::formula::TFormula,
    ) -> EResult<Option<Vec<Vec<Value>>>> {
        use crate::ltl;
        let nnf = ltl::to_nnf(f, true).map_err(EngineError::Eval)?;
        let aut = ltl::translate(&nnf);
        let nq = aut.labels.len();
        if nq == 0 {
            // the negation is unsatisfiable: property holds
            return Ok(None);
        }
        // automaton state bits after all leaf bits
        let aut_base = self
            .leaves
            .last()
            .map(|l| l.base + 2 * l.bits)
            .unwrap_or(0);
        let abits = bits_for(nq as u64);
        let aut_eq = |s: &mut Self, q: usize, primed: bool| -> NodeId {
            let mut r = T;
            for b in 0..abits {
                let var = aut_base + 2 * b + if primed { 1 } else { 0 };
                let bit = (q >> b) & 1 == 1;
                let lit = if bit { s.mgr.var(var) } else { s.mgr.nvar(var) };
                r = s.mgr.and(r, lit);
            }
            r
        };

        // labels as BDDs over current state vars
        let mut label_bdd = Vec::with_capacity(nq);
        for l in &aut.labels {
            let e = ltl::label_expr(l);
            label_bdd.push(self.enc_bool(&e)?);
        }

        // product init
        let mut pinit = F;
        for &q in &aut.initial {
            let a = aut_eq(self, q, false);
            let al = self.mgr.and(a, label_bdd[q]);
            pinit = self.mgr.or(pinit, al);
        }
        pinit = self.mgr.and(pinit, self.init);

        // product transition
        let mut ptrans = F;
        for (q, succs) in aut.edges.iter().enumerate() {
            let aq = aut_eq(self, q, false);
            for &q2 in succs {
                let aq2 = aut_eq(self, q2, true);
                let lbl2 = self.mgr.shift(label_bdd[q2], 1);
                let mut t = self.mgr.and(aq, aq2);
                t = self.mgr.and(t, lbl2);
                ptrans = self.mgr.or(ptrans, t);
            }
        }
        // (product parts assembled below)

        // fairness sets as product-state predicates
        let mut fair = Vec::new();
        for set in &aut.accepting {
            let mut fset = F;
            for &q in set {
                let a = aut_eq(self, q, false);
                fset = self.mgr.or(fset, a);
            }
            fair.push(fset);
        }

        // reachable product states
        let saved_parts = self.parts.clone();
        let new_parts: Vec<NodeId> = saved_parts
            .iter()
            .map(|&p| self.mgr.and(p, ptrans))
            .filter(|&p| p != F)
            .collect();
        self.parts = new_parts;
        let (reach, rings) = {
            let mut rings = vec![pinit];
            let mut reach = pinit;
            let mut frontier = pinit;
            loop {
                let img = self.image(frontier);
                let nreach = self.mgr.or(reach, img);
                if nreach == reach {
                    break;
                }
                let nr = self.mgr.not(reach);
                frontier = self.mgr.and(img, nr);
                rings.push(frontier);
                reach = nreach;
            }
            (reach, rings)
        };

        // Emerson-Lei: states with a fair path
        let mut hull = reach;
        loop {
            let mut nhull = hull;
            for fset in &fair {
                let target = self.mgr.and(nhull, *fset);
                // states in hull that can reach target within hull
                let reach_f = self.eu(nhull, target);
                let pre = self.preimage(reach_f);
                nhull = self.mgr.and(nhull, pre);
            }
            if nhull == hull {
                break;
            }
            hull = nhull;
        }

        let witness = self.mgr.and(hull, reach);
        if witness == F {
            self.parts = saved_parts;
            return Ok(None);
        }

        // counterexample: shortest prefix to the hull, then a bounded walk
        // inside the hull touching every fairness set
        let mut path_states: Vec<HashMap<u32, bool>> = Vec::new();
        // find earliest ring intersecting the hull
        let mut k = 0;
        let mut hit = F;
        for (i, r) in rings.iter().enumerate() {
            let h = self.mgr.and(*r, witness);
            if h != F {
                k = i;
                hit = h;
                break;
            }
        }
        let mut cube = self.pick_product_state(hit, aut_base, abits);
        path_states.push(cube.clone());
        for i in (0..k).rev() {
            let sb = self.product_assignment_bdd(&cube, aut_base, abits);
            let pre = self.preimage(sb);
            let cand = self.mgr.and(pre, rings[i]);
            cube = self.pick_product_state(cand, aut_base, abits);
            path_states.insert(0, cube.clone());
        }
        // loop part: from the hull entry point, walk forward hitting each
        // fairness set (bounded)
        let mut cur = path_states.last().unwrap().clone();
        for fset in fair.clone() {
            // BFS from cur within hull to fset
            let start = self.product_assignment_bdd(&cur, aut_base, abits);
            let mut seen = start;
            let mut frontier = start;
            let mut fringes = vec![start];
            let mut found = self.mgr.and(start, fset);
            let mut steps = 0;
            while found == F && steps < 10_000 {
                let img0 = self.image(frontier);
                let img = self.mgr.and(img0, hull);
                let ns = self.mgr.or(seen, img);
                if ns == seen {
                    break;
                }
                let nseen = self.mgr.not(seen);
                frontier = self.mgr.and(img, nseen);
                fringes.push(frontier);
                seen = ns;
                found = self.mgr.and(frontier, fset);
                steps += 1;
            }
            if found != F && fringes.len() > 1 {
                // walk back through fringes to build the segment
                let mut seg: Vec<HashMap<u32, bool>> = Vec::new();
                let mut c = self.pick_product_state(found, aut_base, abits);
                seg.push(c.clone());
                for i in (0..fringes.len() - 1).rev() {
                    let sb = self.product_assignment_bdd(&c, aut_base, abits);
                    let pre = self.preimage(sb);
                    let cand = self.mgr.and(pre, fringes[i]);
                    if cand == F {
                        break;
                    }
                    c = self.pick_product_state(cand, aut_base, abits);
                    seg.insert(0, c.clone());
                }
                // drop the first (== cur) and append
                for s in seg.into_iter().skip(1) {
                    path_states.push(s);
                }
                cur = path_states.last().unwrap().clone();
            }
        }
        self.parts = saved_parts;
        Ok(Some(
            path_states.iter().map(|a| self.decode_state(a)).collect(),
        ))
    }

    fn pick_product_state(
        &mut self,
        set: NodeId,
        aut_base: u32,
        abits: u32,
    ) -> HashMap<u32, bool> {
        let mut partial = self.mgr.pick(set).unwrap_or_default();
        for l in &self.leaves {
            for b in 0..l.bits {
                partial.entry(l.base + 2 * b).or_insert(false);
            }
        }
        for b in 0..abits {
            partial.entry(aut_base + 2 * b).or_insert(false);
        }
        partial
    }

    fn product_assignment_bdd(
        &mut self,
        a: &HashMap<u32, bool>,
        aut_base: u32,
        abits: u32,
    ) -> NodeId {
        let mut r = self.assignment_bdd(a);
        for b in 0..abits {
            let var = aut_base + 2 * b;
            let val = a.get(&var).copied().unwrap_or(false);
            let lit = if val { self.mgr.var(var) } else { self.mgr.nvar(var) };
            r = self.mgr.and(r, lit);
        }
        r
    }
}

enum Enc {
    B(NodeId),
    P(Vec<(Value, NodeId)>),
}

fn push_part(mgr: &mut Mgr, parts: &mut Vec<(Value, NodeId)>, v: Value, c: NodeId) {
    if c == F {
        return;
    }
    for (v0, c0) in parts.iter_mut() {
        if *v0 == v {
            *c0 = mgr.or(*c0, c);
            return;
        }
    }
    parts.push((v, c));
}
