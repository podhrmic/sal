//! Explicit-state engine: BFS reachability with constraint propagation.
//!
//! States are full assignments to the flat module's leaf variables.
//! Constraint solving is propagation (unit equations) followed by bounded
//! enumeration of the remaining unknowns.

use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use num_traits::Zero;

use sal_flat::fexpr::{FExpr, LeafId};
use sal_flat::flatten::{FlatCmd, FlatModule, TransNode};
use sal_flat::value::Value;

pub type State = Rc<Vec<Value>>;

#[derive(Debug, Clone)]
pub struct Path {
    /// (state, provenance of the transition that produced it).
    pub steps: Vec<(State, Option<String>)>,
}

pub enum CheckResult {
    Proved,
    Counterexample(Path),
    Deadlock(Path),
    Ok,
}

pub struct Explicit<'m> {
    pub flat: &'m FlatModule,
    /// Cap on states explored.
    pub max_states: usize,
    /// Cap on the enumeration product for unknown leaves per solve.
    pub max_enum: u64,
}

#[derive(Debug)]
pub enum EngineError {
    /// A leaf has an infinite domain: the explicit/BDD engines cannot run.
    InfiniteType(String),
    /// Resource limits exceeded.
    TooLarge(String),
    /// Evaluation error (division by zero etc.).
    Eval(String),
}

impl std::fmt::Display for EngineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EngineError::InfiniteType(v) => {
                write!(f, "Finite type expected. The type of the variable \"{}\" is not finite.", v)
            }
            EngineError::TooLarge(m) => write!(f, "State space too large: {}", m),
            EngineError::Eval(m) => write!(f, "{}", m),
        }
    }
}

type EResult<T> = Result<T, EngineError>;

/// Partial assignment during solving.
struct PartialEnv<'a> {
    cur: &'a [Option<Value>],
    next: &'a [Option<Value>],
}

/// Three-valued evaluation: `None` = not yet determined.
fn peval(e: &FExpr, env: &PartialEnv) -> EResult<Option<Value>> {
    use FExpr::*;
    Ok(match e {
        Const(v) => Some(v.clone()),
        Var(l, primed) => {
            let slot = if *primed {
                &env.next[*l as usize]
            } else {
                &env.cur[*l as usize]
            };
            slot.clone()
        }
        Not(a) => match peval(a, env)? {
            Some(Value::Bool(b)) => Some(Value::Bool(!b)),
            Some(_) => return Err(EngineError::Eval("boolean expected".into())),
            None => None,
        },
        And(es) => {
            let mut unknown = false;
            for x in es {
                match peval(x, env)? {
                    Some(Value::Bool(false)) => return Ok(Some(Value::Bool(false))),
                    Some(Value::Bool(true)) => {}
                    Some(_) => return Err(EngineError::Eval("boolean expected".into())),
                    None => unknown = true,
                }
            }
            if unknown {
                None
            } else {
                Some(Value::Bool(true))
            }
        }
        Or(es) => {
            let mut unknown = false;
            for x in es {
                match peval(x, env)? {
                    Some(Value::Bool(true)) => return Ok(Some(Value::Bool(true))),
                    Some(Value::Bool(false)) => {}
                    Some(_) => return Err(EngineError::Eval("boolean expected".into())),
                    None => unknown = true,
                }
            }
            if unknown {
                None
            } else {
                Some(Value::Bool(false))
            }
        }
        Ite(c, t, f) => match peval(c, env)? {
            Some(Value::Bool(true)) => peval(t, env)?,
            Some(Value::Bool(false)) => peval(f, env)?,
            Some(_) => return Err(EngineError::Eval("boolean expected".into())),
            None => {
                // both branches equal and known?
                let vt = peval(t, env)?;
                let vf = peval(f, env)?;
                match (vt, vf) {
                    (Some(a), Some(b)) if a == b => Some(a),
                    _ => None,
                }
            }
        },
        Eq(a, b) => match (peval(a, env)?, peval(b, env)?) {
            (Some(x), Some(y)) => Some(Value::Bool(x == y)),
            _ => None,
        },
        Lt(a, b) => cmp(a, b, env, |o| o == std::cmp::Ordering::Less)?,
        Le(a, b) => cmp(a, b, env, |o| o != std::cmp::Ordering::Greater)?,
        Add(es) => {
            let mut acc = num_rational::BigRational::zero();
            for x in es {
                match peval(x, env)? {
                    Some(Value::Num(n)) => acc += n,
                    Some(_) => return Err(EngineError::Eval("number expected".into())),
                    None => return Ok(None),
                }
            }
            Some(Value::Num(acc))
        }
        Mul(es) => {
            let mut acc = num_rational::BigRational::from_integer(1.into());
            for x in es {
                match peval(x, env)? {
                    Some(Value::Num(n)) => acc *= n,
                    Some(_) => return Err(EngineError::Eval("number expected".into())),
                    None => return Ok(None),
                }
            }
            Some(Value::Num(acc))
        }
        Neg(a) => match peval(a, env)? {
            Some(Value::Num(n)) => Some(Value::Num(-n)),
            Some(_) => return Err(EngineError::Eval("number expected".into())),
            None => None,
        },
        Div(a, b) => match (peval(a, env)?, peval(b, env)?) {
            (Some(Value::Num(x)), Some(Value::Num(y))) => {
                if y.is_zero() {
                    return Err(EngineError::Eval("Division by zero.".into()));
                }
                Some(Value::Num(x / y))
            }
            _ => None,
        },
        IDiv(a, b) | Mod(a, b) => match (peval(a, env)?, peval(b, env)?) {
            (Some(Value::Num(x)), Some(Value::Num(y))) => {
                if !x.is_integer() || !y.is_integer() || y.is_zero() {
                    return Err(EngineError::Eval(
                        "DIV/MOD require integer operands and nonzero divisor.".into(),
                    ));
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
                Some(Value::Num(num_rational::BigRational::from_integer(
                    if matches!(e, IDiv(..)) { q } else { r },
                )))
            }
            _ => None,
        },
    })
}

fn cmp(
    a: &FExpr,
    b: &FExpr,
    env: &PartialEnv,
    f: impl Fn(std::cmp::Ordering) -> bool,
) -> EResult<Option<Value>> {
    match (peval(a, env)?, peval(b, env)?) {
        (Some(Value::Num(x)), Some(Value::Num(y))) => {
            Ok(Some(Value::Bool(f(x.cmp(&y)))))
        }
        (Some(_), Some(_)) => Err(EngineError::Eval("number expected".into())),
        _ => Ok(None),
    }
}

impl<'m> Explicit<'m> {
    pub fn new(flat: &'m FlatModule) -> EResult<Self> {
        // all leaves must have finite domains
        for l in &flat.leaves {
            if l.ty.cardinality().is_none() {
                return Err(EngineError::InfiniteType(l.name.clone()));
            }
        }
        Ok(Explicit {
            flat,
            max_states: 20_000_000,
            max_enum: 2_000_000,
        })
    }

    /// Solve a conjunction of constraints for the unknown slots.
    /// `cur` is fully known for transition solving; for initial states both
    /// start unknown. Returns all solutions as (cur, next) pairs.
    fn solve(
        &self,
        constraints: &[FExpr],
        cur0: Vec<Option<Value>>,
        next0: Vec<Option<Value>>,
        solve_next: bool,
    ) -> EResult<Vec<(Vec<Value>, Vec<Value>)>> {
        let mut cur = cur0;
        let mut next = next0;
        let mut active: Vec<&FExpr> = Vec::new();
        for c in constraints {
            flatten_conj(c, &mut active);
        }
        // propagation
        loop {
            let mut progress = false;
            let mut remaining = Vec::new();
            for c in active.drain(..) {
                let env = PartialEnv {
                    cur: &cur,
                    next: &next,
                };
                match peval(c, &env)? {
                    Some(Value::Bool(true)) => {
                        progress = true;
                        continue;
                    }
                    Some(Value::Bool(false)) => return Ok(vec![]),
                    Some(_) => return Err(EngineError::Eval("boolean expected".into())),
                    None => {}
                }
                // unit equation?
                if let FExpr::Eq(a, b) = c {
                    let env = PartialEnv {
                        cur: &cur,
                        next: &next,
                    };
                    let assigned = match (a.as_ref(), peval(b, &env)?) {
                        (FExpr::Var(l, p), Some(v)) => Some((*l, *p, v)),
                        _ => match (peval(a, &env)?, b.as_ref()) {
                            (Some(v), FExpr::Var(l, p)) => Some((*l, *p, v)),
                            _ => None,
                        },
                    };
                    if let Some((l, p, v)) = assigned {
                        let slot = if p {
                            &mut next[l as usize]
                        } else {
                            &mut cur[l as usize]
                        };
                        match slot {
                            Some(existing) => {
                                if *existing != v {
                                    return Ok(vec![]);
                                }
                            }
                            None => {
                                *slot = Some(v);
                                progress = true;
                                continue; // constraint satisfied by assignment
                            }
                        }
                        continue;
                    }
                }
                remaining.push(c);
            }
            active = remaining;
            if !progress {
                break;
            }
        }
        // enumerate remaining unknowns
        let mut unknown: Vec<(usize, bool, Vec<Value>)> = Vec::new();
        let mut product: u64 = 1;
        // determine which unknowns actually matter (appear in constraints or
        // are state variables that need values)
        for (i, slot) in cur.iter().enumerate() {
            if slot.is_none() {
                let vals = self.flat.leaves[i].ty.values().unwrap();
                product = product.saturating_mul(vals.len() as u64);
                unknown.push((i, false, vals));
            }
        }
        if solve_next {
            for (i, slot) in next.iter().enumerate() {
                if slot.is_none() {
                    let vals = self.flat.leaves[i].ty.values().unwrap();
                    product = product.saturating_mul(vals.len() as u64);
                    unknown.push((i, true, vals));
                }
            }
        }
        if product > self.max_enum {
            return Err(EngineError::TooLarge(format!(
                "{} combinations to enumerate",
                product
            )));
        }
        let mut out = Vec::new();
        let mut odometer = vec![0usize; unknown.len()];
        'outer: loop {
            let mut c2 = cur.clone();
            let mut n2 = next.clone();
            for (k, (i, p, vals)) in unknown.iter().enumerate() {
                let v = vals[odometer[k]].clone();
                if *p {
                    n2[*i] = Some(v);
                } else {
                    c2[*i] = Some(v);
                }
            }
            // final check
            let envx = PartialEnv { cur: &c2, next: &n2 };
            let mut ok = true;
            for c in &active {
                match peval(c, &envx)? {
                    Some(Value::Bool(true)) => {}
                    Some(Value::Bool(false)) | None => {
                        ok = false;
                        break;
                    }
                    Some(_) => return Err(EngineError::Eval("boolean expected".into())),
                }
            }
            if ok {
                let cvals: Vec<Value> = c2.into_iter().map(|x| x.unwrap()).collect();
                let nvals: Vec<Value> = if solve_next {
                    n2.into_iter().map(|x| x.unwrap()).collect()
                } else {
                    Vec::new()
                };
                out.push((cvals, nvals));
            }
            for k in (0..unknown.len()).rev() {
                odometer[k] += 1;
                if odometer[k] < unknown[k].2.len() {
                    continue 'outer;
                }
                odometer[k] = 0;
            }
            break;
        }
        Ok(out)
    }

    /// All initial states.
    pub fn initial_states(&self) -> EResult<Vec<State>> {
        let n = self.flat.leaves.len();
        // conjunction: invariants + init_defs + one command per block
        let blocks = &self.flat.init_choices;
        let mut base: Vec<FExpr> = Vec::new();
        base.extend(self.flat.invariants.iter().cloned());
        base.extend(self.flat.init_defs.iter().cloned());

        let mut out = Vec::new();
        let mut chosen = vec![0usize; blocks.len()];
        'outer: loop {
            let mut cs = base.clone();
            let mut feasible = true;
            for (bi, block) in blocks.iter().enumerate() {
                if block.is_empty() {
                    feasible = false;
                    break;
                }
                let cmd = &block[chosen[bi]];
                cs.push(cmd.guard.clone());
                cs.push(cmd.constraint.clone());
            }
            if feasible {
                for (c, _) in self.solve(&cs, vec![None; n], vec![], false)? {
                    out.push(Rc::new(c));
                }
            }
            for k in (0..blocks.len()).rev() {
                chosen[k] += 1;
                if chosen[k] < blocks[k].len() {
                    continue 'outer;
                }
                chosen[k] = 0;
            }
            break;
        }
        out.sort();
        out.dedup();
        Ok(out)
    }

    /// Enumerate command combinations of a transition node. Each result is
    /// (constraints, provenance).
    fn trans_alternatives<'a>(
        &self,
        node: &'a TransNode,
        acc: &mut Vec<(Vec<&'a FExpr>, Vec<&'a FlatCmd>)>,
    ) {
        match node {
            TransNode::True => acc.push((vec![], vec![])),
            TransNode::Cmds(cmds) => {
                for c in cmds {
                    acc.push((vec![&c.guard, &c.constraint], vec![c]));
                }
            }
            TransNode::All(nodes) => {
                let mut result: Vec<(Vec<&FExpr>, Vec<&FlatCmd>)> =
                    vec![(vec![], vec![])];
                for n in nodes {
                    let mut sub = Vec::new();
                    self.trans_alternatives(n, &mut sub);
                    let mut next = Vec::new();
                    for (cs, ps) in &result {
                        for (cs2, ps2) in &sub {
                            let mut c = cs.clone();
                            c.extend(cs2.iter().cloned());
                            let mut p = ps.clone();
                            p.extend(ps2.iter().cloned());
                            next.push((c, p));
                        }
                    }
                    result = next;
                }
                acc.extend(result);
            }
            TransNode::Interleave(branches) => {
                for (n, frame) in branches {
                    let mut sub = Vec::new();
                    self.trans_alternatives(n, &mut sub);
                    for (mut cs, ps) in sub {
                        cs.push(frame);
                        acc.push((cs, ps));
                    }
                }
            }
        }
    }

    /// Successors of a state.
    pub fn successors(&self, s: &State) -> EResult<Vec<(State, String)>> {
        let n = self.flat.leaves.len();
        let cur: Vec<Option<Value>> = s.iter().cloned().map(Some).collect();
        let mut alts = Vec::new();
        self.trans_alternatives(&self.flat.trans, &mut alts);
        let mut out: Vec<(State, String)> = Vec::new();
        for (cs, prov) in alts {
            let mut constraints: Vec<FExpr> = cs.into_iter().cloned().collect();
            constraints.extend(self.flat.trans_defs.iter().cloned());
            // next state must satisfy the invariants
            for inv in &self.flat.invariants {
                constraints.push(sal_flat::sval::prime(inv));
            }
            let sols = self.solve(&constraints, cur.clone(), vec![None; n], true)?;
            let provenance = prov
                .iter()
                .filter_map(|c| c.label.clone())
                .collect::<Vec<_>>()
                .join(" || ");
            for (_, next) in sols {
                out.push((Rc::new(next), provenance.clone()));
            }
        }
        out.sort_by(|a, b| a.0.cmp(&b.0));
        out.dedup_by(|a, b| a.0 == b.0);
        Ok(out)
    }

    /// BFS reachability checking that `prop` holds in every reachable
    /// state.
    pub fn check_invariant(&self, prop: &FExpr) -> EResult<CheckResult> {
        let mut visited: HashMap<State, (Option<State>, Option<String>)> = HashMap::new();
        let mut queue: VecDeque<State> = VecDeque::new();
        for s in self.initial_states()? {
            if visited.len() >= self.max_states {
                return Err(EngineError::TooLarge("too many states".into()));
            }
            if visited.contains_key(&s) {
                continue;
            }
            visited.insert(s.clone(), (None, None));
            if !self.holds(prop, &s)? {
                return Ok(CheckResult::Counterexample(
                    self.reconstruct(&visited, s),
                ));
            }
            queue.push_back(s);
        }
        while let Some(s) = queue.pop_front() {
            for (t, prov) in self.successors(&s)? {
                if visited.contains_key(&t) {
                    continue;
                }
                if visited.len() >= self.max_states {
                    return Err(EngineError::TooLarge("too many states".into()));
                }
                visited.insert(t.clone(), (Some(s.clone()), Some(prov)));
                if !self.holds(prop, &t)? {
                    return Ok(CheckResult::Counterexample(
                        self.reconstruct(&visited, t),
                    ));
                }
                queue.push_back(t);
            }
        }
        Ok(CheckResult::Proved)
    }

    /// Search for a reachable deadlock state (no successors).
    pub fn check_deadlock(&self) -> EResult<CheckResult> {
        let mut visited: HashMap<State, (Option<State>, Option<String>)> = HashMap::new();
        let mut queue: VecDeque<State> = VecDeque::new();
        for s in self.initial_states()? {
            if visited.contains_key(&s) {
                continue;
            }
            visited.insert(s.clone(), (None, None));
            queue.push_back(s);
        }
        while let Some(s) = queue.pop_front() {
            let succs = self.successors(&s)?;
            if succs.is_empty() {
                return Ok(CheckResult::Deadlock(self.reconstruct(&visited, s)));
            }
            for (t, prov) in succs {
                if visited.contains_key(&t) {
                    continue;
                }
                if visited.len() >= self.max_states {
                    return Err(EngineError::TooLarge("too many states".into()));
                }
                visited.insert(t.clone(), (Some(s.clone()), Some(prov)));
                queue.push_back(t);
            }
        }
        Ok(CheckResult::Ok)
    }

    pub fn holds(&self, prop: &FExpr, s: &State) -> EResult<bool> {
        let cur: Vec<Option<Value>> = s.iter().cloned().map(Some).collect();
        let env = PartialEnv {
            cur: &cur,
            next: &[],
        };
        match peval(prop, &env)? {
            Some(Value::Bool(b)) => Ok(b),
            _ => Err(EngineError::Eval(
                "property must be a boolean state predicate".into(),
            )),
        }
    }

    fn reconstruct(
        &self,
        visited: &HashMap<State, (Option<State>, Option<String>)>,
        end: State,
    ) -> Path {
        let mut steps = Vec::new();
        let mut cur = Some(end);
        while let Some(s) = cur {
            let (parent, prov) = visited.get(&s).cloned().unwrap_or((None, None));
            steps.push((s, prov));
            cur = parent;
        }
        steps.reverse();
        Path { steps }
    }
}

fn flatten_conj<'a>(e: &'a FExpr, out: &mut Vec<&'a FExpr>) {
    if let FExpr::And(es) = e {
        for x in es {
            flatten_conj(x, out);
        }
    } else {
        out.push(e);
    }
}
