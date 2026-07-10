//! LTL to (state-labeled, generalized) Büchi automata via the classic
//! GPVW tableau construction.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use sal_flat::fexpr::FExpr;
use sal_flat::formula::TFormula;

/// LTL in negation normal form.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Ltl {
    True,
    False,
    Atom(FExpr),
    NAtom(FExpr),
    And(Rc<Ltl>, Rc<Ltl>),
    Or(Rc<Ltl>, Rc<Ltl>),
    X(Rc<Ltl>),
    U(Rc<Ltl>, Rc<Ltl>),
    R(Rc<Ltl>, Rc<Ltl>),
}

impl Ltl {
    fn rc(self) -> Rc<Ltl> {
        Rc::new(self)
    }
}

/// Convert a TFormula (LTL fragment) into NNF, negating if `negate`.
pub fn to_nnf(f: &TFormula, negate: bool) -> Result<Ltl, String> {
    use TFormula::*;
    Ok(match (f, negate) {
        (Atom(e), false) => Ltl::Atom(e.clone()),
        (Atom(e), true) => Ltl::NAtom(e.clone()),
        (Not(a), n) => to_nnf(a, !n)?,
        (And(a, b), false) => Ltl::And(to_nnf(a, false)?.rc(), to_nnf(b, false)?.rc()),
        (And(a, b), true) => Ltl::Or(to_nnf(a, true)?.rc(), to_nnf(b, true)?.rc()),
        (Or(a, b), false) => Ltl::Or(to_nnf(a, false)?.rc(), to_nnf(b, false)?.rc()),
        (Or(a, b), true) => Ltl::And(to_nnf(a, true)?.rc(), to_nnf(b, true)?.rc()),
        (X(a), n) => Ltl::X(to_nnf(a, n)?.rc()),
        (G(a), false) => Ltl::R(Ltl::False.rc(), to_nnf(a, false)?.rc()),
        (G(a), true) => Ltl::U(Ltl::True.rc(), to_nnf(a, true)?.rc()),
        (F(a), false) => Ltl::U(Ltl::True.rc(), to_nnf(a, false)?.rc()),
        (F(a), true) => Ltl::R(Ltl::False.rc(), to_nnf(a, true)?.rc()),
        (U(a, b), false) => Ltl::U(to_nnf(a, false)?.rc(), to_nnf(b, false)?.rc()),
        (U(a, b), true) => Ltl::R(to_nnf(a, true)?.rc(), to_nnf(b, true)?.rc()),
        (R(a, b), false) => Ltl::R(to_nnf(a, false)?.rc(), to_nnf(b, false)?.rc()),
        (R(a, b), true) => Ltl::U(to_nnf(a, true)?.rc(), to_nnf(b, true)?.rc()),
        // p W q = (q R (q ∨ p))
        (W(a, b), false) => {
            let p = to_nnf(a, false)?;
            let q = to_nnf(b, false)?;
            Ltl::R(q.clone().rc(), Ltl::Or(q.rc(), p.rc()).rc())
        }
        // ¬(p W q) = (¬q U (¬q ∧ ¬p))
        (W(a, b), true) => {
            let np = to_nnf(a, true)?;
            let nq = to_nnf(b, true)?;
            Ltl::U(nq.clone().rc(), Ltl::And(nq.rc(), np.rc()).rc())
        }
        // p M q (strong release) = q U (p ∧ q)
        (M(a, b), false) => {
            let p = to_nnf(a, false)?;
            let q = to_nnf(b, false)?;
            Ltl::U(q.clone().rc(), Ltl::And(p.rc(), q.rc()).rc())
        }
        (M(a, b), true) => {
            // ¬(p M q) = ¬q R (¬p ∨ ¬q)
            let np = to_nnf(a, true)?;
            let nq = to_nnf(b, true)?;
            Ltl::R(nq.clone().rc(), Ltl::Or(np.rc(), nq.rc()).rc())
        }
        _ => return Err("CTL operators cannot appear in an LTL formula".into()),
    })
}

/// A state-labeled generalized Büchi automaton from GPVW.
pub struct Lgba {
    /// Per node: literals that must hold at this position
    /// (positive/negative atoms).
    pub labels: Vec<Vec<Ltl>>,
    /// Per node: incoming edges (list of source node ids; usize::MAX =
    /// initial).
    pub initial: Vec<usize>,
    pub edges: Vec<Vec<usize>>,
    /// Acceptance sets (indices of nodes) — one per Until subformula.
    pub accepting: Vec<Vec<usize>>,
}

#[derive(Clone)]
struct GNode {
    incoming: BTreeSet<usize>, // usize::MAX = init
    new: BTreeSet<Rc<Ltl>>,
    old: BTreeSet<Rc<Ltl>>,
    next: BTreeSet<Rc<Ltl>>,
}

const INIT: usize = usize::MAX;

/// GPVW expansion.
pub fn translate(f: &Ltl) -> Lgba {
    let mut nodes: Vec<GNode> = Vec::new(); // completed nodes
    let mut stack: Vec<GNode> = vec![GNode {
        incoming: [INIT].into_iter().collect(),
        new: [Rc::new(f.clone())].into_iter().collect(),
        old: BTreeSet::new(),
        next: BTreeSet::new(),
    }];

    while let Some(mut node) = stack.pop() {
        let Some(cur) = node.new.iter().next().cloned() else {
            // node fully expanded: merge with an existing equivalent node?
            if let Some(i) = nodes
                .iter()
                .position(|n| n.old == node.old && n.next == node.next)
            {
                let inc = node.incoming.clone();
                nodes[i].incoming.extend(inc);
                continue;
            }
            let id = nodes.len();
            nodes.push(node);
            // successor node
            let succ = GNode {
                incoming: [id].into_iter().collect(),
                new: nodes[id].next.clone(),
                old: BTreeSet::new(),
                next: BTreeSet::new(),
            };
            stack.push(succ);
            continue;
        };
        node.new.remove(&cur);
        match cur.as_ref() {
            Ltl::False => continue, // contradiction: drop node
            Ltl::True => {
                stack.push(node);
            }
            Ltl::Atom(_) | Ltl::NAtom(_) => {
                // check for contradiction
                let negated = match cur.as_ref() {
                    Ltl::Atom(e) => Ltl::NAtom(e.clone()),
                    Ltl::NAtom(e) => Ltl::Atom(e.clone()),
                    _ => unreachable!(),
                };
                if node.old.contains(&Rc::new(negated)) {
                    continue;
                }
                node.old.insert(cur);
                stack.push(node);
            }
            Ltl::And(a, b) => {
                for x in [a, b] {
                    if !node.old.contains(x) {
                        node.new.insert(x.clone());
                    }
                }
                node.old.insert(cur);
                stack.push(node);
            }
            Ltl::X(a) => {
                node.next.insert(a.clone());
                node.old.insert(cur);
                stack.push(node);
            }
            Ltl::Or(a, b) => {
                let mut n1 = node.clone();
                if !n1.old.contains(a) {
                    n1.new.insert(a.clone());
                }
                n1.old.insert(cur.clone());
                let mut n2 = node;
                if !n2.old.contains(b) {
                    n2.new.insert(b.clone());
                }
                n2.old.insert(cur);
                stack.push(n1);
                stack.push(n2);
            }
            Ltl::U(a, b) => {
                // U = b ∨ (a ∧ X(a U b))
                let mut n1 = node.clone();
                if !n1.old.contains(a) {
                    n1.new.insert(a.clone());
                }
                n1.next.insert(cur.clone());
                n1.old.insert(cur.clone());
                let mut n2 = node;
                if !n2.old.contains(b) {
                    n2.new.insert(b.clone());
                }
                n2.old.insert(cur);
                stack.push(n1);
                stack.push(n2);
            }
            Ltl::R(a, b) => {
                // R = (a ∧ b) ∨ (b ∧ X(a R b))
                let mut n1 = node.clone();
                if !n1.old.contains(b) {
                    n1.new.insert(b.clone());
                }
                n1.next.insert(cur.clone());
                n1.old.insert(cur.clone());
                let mut n2 = node;
                for x in [a, b] {
                    if !n2.old.contains(x) {
                        n2.new.insert(x.clone());
                    }
                }
                n2.old.insert(cur);
                stack.push(n1);
                stack.push(n2);
            }
        }
    }

    // collect Untils for acceptance
    let mut untils: Vec<Rc<Ltl>> = Vec::new();
    let mut seen = BTreeSet::new();
    for n in &nodes {
        for f in &n.old {
            if matches!(f.as_ref(), Ltl::U(..)) && seen.insert(f.clone()) {
                untils.push(f.clone());
            }
        }
    }

    let mut labels = Vec::new();
    let mut initial = Vec::new();
    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
    for (i, n) in nodes.iter().enumerate() {
        labels.push(
            n.old
                .iter()
                .filter(|f| matches!(f.as_ref(), Ltl::Atom(_) | Ltl::NAtom(_)))
                .map(|f| (**f).clone())
                .collect(),
        );
        for &src in &n.incoming {
            if src == INIT {
                initial.push(i);
            } else {
                edges[src].push(i);
            }
        }
    }
    // acceptance: for each until (a U b): nodes where ¬(aUb ∈ old) ∨ b ∈ old
    let mut accepting = Vec::new();
    for u in &untils {
        let Ltl::U(_, b) = u.as_ref() else {
            unreachable!()
        };
        let mut set = Vec::new();
        for (i, n) in nodes.iter().enumerate() {
            let has_u = n.old.contains(u);
            let has_b = n
                .old
                .iter()
                .any(|f| f.as_ref() == b.as_ref());
            if !has_u || has_b {
                set.push(i);
            }
        }
        accepting.push(set);
    }
    if accepting.is_empty() {
        accepting.push((0..nodes.len()).collect());
    }

    Lgba {
        labels,
        initial,
        edges,
        accepting,
    }
}

/// Label of node i as a conjunction FExpr.
pub fn label_expr(l: &[Ltl]) -> FExpr {
    let mut cs = Vec::new();
    for f in l {
        match f {
            Ltl::Atom(e) => cs.push(e.clone()),
            Ltl::NAtom(e) => cs.push(FExpr::not(e.clone())),
            _ => {}
        }
    }
    FExpr::and(cs)
}

/// Map used by tests.
pub fn _unused() -> HashMap<u32, u32> {
    HashMap::new()
}
