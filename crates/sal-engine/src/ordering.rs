//! Static BDD variable-ordering heuristics, ported from the oracle's
//! `ordering.scm`.
//!
//! The unit of ordering is the *component* (one base-module instance in
//! the composition). A component permutation is chosen greedily
//! (`min-supp`: minimize the input variables crossing the cut;
//! `min-comm`: minimize communication, penalizing backward edges
//! exponentially), then variables are laid out per component: each owned
//! variable preceded by the not-yet-placed input variables its next-state
//! value depends on, both sorted by weight = relevance / support.

use std::collections::{BTreeMap, BTreeSet};

use sal_flat::fexpr::LeafId;
use sal_flat::flatten::{FlatModule, TransNode};
use sal_syntax::ast::VarClass;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StaticOrder {
    /// Declaration order (no reordering).
    None,
    /// Component order as elaborated + weight layout.
    Simple,
    /// Greedy min-support component permutation (oracle default).
    MinSupp,
    /// min-supp with look-ahead 2.
    MinSupp2,
    /// Greedy min-communication permutation.
    MinComm,
    /// min-comm with look-ahead 2.
    MinComm2,
}

impl StaticOrder {
    pub fn parse(s: &str) -> Option<StaticOrder> {
        Some(match s {
            "none" => StaticOrder::None,
            "simple" => StaticOrder::Simple,
            "min-supp" => StaticOrder::MinSupp,
            "min-supp2" => StaticOrder::MinSupp2,
            "min-comm" => StaticOrder::MinComm,
            "min-comm2" => StaticOrder::MinComm2,
            _ => return None,
        })
    }
}

const BIG: f64 = 99999999999.0;

/// Next→current dependency edges of the transition relation
/// (self-edges excluded), as adjacency next-leaf → set of current leaves.
fn dependency_graph(flat: &FlatModule) -> BTreeMap<LeafId, BTreeSet<LeafId>> {
    let mut deps: BTreeMap<LeafId, BTreeSet<LeafId>> = BTreeMap::new();
    let mut add_conjunct = |e: &sal_flat::fexpr::FExpr| {
        let mut cur = BTreeSet::new();
        let mut next = BTreeSet::new();
        e.leaves(&mut cur, &mut next);
        for &n in &next {
            for &c in &cur {
                if n != c {
                    deps.entry(n).or_default().insert(c);
                }
            }
        }
    };
    fn conjuncts<'a>(e: &'a sal_flat::fexpr::FExpr, out: &mut Vec<&'a sal_flat::fexpr::FExpr>) {
        if let sal_flat::fexpr::FExpr::And(es) = e {
            for x in es {
                conjuncts(x, out);
            }
        } else {
            out.push(e);
        }
    }
    fn walk<'a>(
        n: &'a TransNode,
        add: &mut impl FnMut(&'a sal_flat::fexpr::FExpr),
    ) {
        match n {
            TransNode::True => {}
            TransNode::Cmds(cmds) => {
                for c in cmds {
                    // the guard supports every variable the command assigns
                    let mut parts = Vec::new();
                    conjuncts(&c.constraint, &mut parts);
                    for p in parts {
                        add(p);
                    }
                    // guard edges: approximate by pairing guard with the
                    // whole constraint (its next leaves)
                    add(&c.guard);
                    // pair guard's current leaves with assigned leaves
                    // handled below by the caller through guard_pairs
                }
            }
            TransNode::All(ns) => {
                for x in ns {
                    walk(x, add);
                }
            }
            TransNode::Interleave(bs) => {
                for (x, _) in bs {
                    walk(x, add);
                }
            }
        }
    }
    walk(&flat.trans, &mut add_conjunct);
    // guard → assigned-variable support edges
    fn walk_guards(n: &TransNode, deps: &mut BTreeMap<LeafId, BTreeSet<LeafId>>) {
        match n {
            TransNode::True => {}
            TransNode::Cmds(cmds) => {
                for c in cmds {
                    let mut gcur = BTreeSet::new();
                    let mut gnext = BTreeSet::new();
                    c.guard.leaves(&mut gcur, &mut gnext);
                    let mut ccur = BTreeSet::new();
                    let mut cnext = BTreeSet::new();
                    c.constraint.leaves(&mut ccur, &mut cnext);
                    for &n in &cnext {
                        for &g in &gcur {
                            if n != g {
                                deps.entry(n).or_default().insert(g);
                            }
                        }
                    }
                }
            }
            TransNode::All(ns) => {
                for x in ns {
                    walk_guards(x, deps);
                }
            }
            TransNode::Interleave(bs) => {
                for (x, _) in bs {
                    walk_guards(x, deps);
                }
            }
        }
    }
    for d in &flat.trans_defs {
        add_conjunct(d);
    }
    drop(add_conjunct);
    walk_guards(&flat.trans, &mut deps);
    deps
}

/// weight(v) = relevance(v) / support(v); BIG when support = 0.
fn weights(flat: &FlatModule, deps: &BTreeMap<LeafId, BTreeSet<LeafId>>) -> Vec<f64> {
    let n = flat.leaves.len();
    let mut relevance = vec![0usize; n]; // how many next-vars read me
    let mut support = vec![0usize; n]; // how many vars my next depends on
    for (&src, targets) in deps {
        support[src as usize] = targets.len();
        for &t in targets {
            relevance[t as usize] += 1;
        }
    }
    (0..n)
        .map(|i| {
            if support[i] == 0 {
                BIG
            } else {
                relevance[i] as f64 / support[i] as f64
            }
        })
        .collect()
}

/// Sort descending by weight (stable, like the oracle's sort).
fn sort_by_weight(mut ls: Vec<LeafId>, w: &[f64]) -> Vec<LeafId> {
    ls.sort_by(|a, b| {
        w[*b as usize]
            .partial_cmp(&w[*a as usize])
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    ls
}

struct Comm {
    /// per component: (input leaf, owner component) pairs
    in_edges: Vec<Vec<(LeafId, usize)>>,
    /// per component: (output leaf, consumer component) pairs
    out_edges: Vec<Vec<(LeafId, usize)>>,
    n: usize,
}

/// Communication graph over components with deduplicated ownership.
fn communication(flat: &FlatModule, owned: &[BTreeSet<LeafId>]) -> Comm {
    let n = owned.len();
    let mut owner: BTreeMap<LeafId, usize> = BTreeMap::new();
    for (i, o) in owned.iter().enumerate() {
        for &l in o {
            owner.entry(l).or_insert(i);
        }
    }
    let mut in_edges = vec![Vec::new(); n];
    let mut out_edges = vec![Vec::new(); n];
    for (i, comp) in flat.components.iter().enumerate() {
        for &l in &comp.reads {
            if let Some(&src) = owner.get(&l) {
                if src != i {
                    in_edges[i].push((l, src));
                    out_edges[src].push((l, i));
                }
            }
        }
    }
    Comm {
        in_edges,
        out_edges,
        n,
    }
}

/// Greedy permutation search (look-ahead 1 or 2), as in the oracle.
fn find_permutation(
    n: usize,
    la2: bool,
    cost: &mut impl FnMut(&[usize], usize) -> f64,
) -> Vec<usize> {
    let mut perm: Vec<usize> = (0..n).collect();
    if la2 {
        let max = (n / 2) * 2;
        let mut loc = 0;
        while loc < max {
            let mut best = cost(&perm, loc);
            let (mut b0, mut b1) = (loc, loc + 1);
            for i in loc..n {
                perm.swap(loc, i);
                for j in (loc + 1)..n {
                    perm.swap(loc + 1, j);
                    let c = cost(&perm, loc);
                    if c < best {
                        best = c;
                        b0 = i;
                        b1 = j;
                    }
                    perm.swap(loc + 1, j);
                }
                perm.swap(loc, i);
            }
            perm.swap(loc, b0);
            perm.swap(loc + 1, b1);
            loc += 2;
        }
    } else {
        for loc in 0..n.saturating_sub(1) {
            let mut best = cost(&perm, loc);
            let mut bi = loc;
            for i in loc..n {
                perm.swap(loc, i);
                let c = cost(&perm, loc);
                if c < best {
                    best = c;
                    bi = i;
                }
                perm.swap(loc, i);
            }
            perm.swap(loc, bi);
        }
    }
    perm
}

/// min-supp cut cost: distinct input leaves of the components straddling
/// the cut whose source lies on the other side.
fn min_supp_cost(comm: &Comm, perm: &[usize], cut: usize) -> f64 {
    // partition: position ≤ cut → prefix(false side), else suffix
    let mut suffix = vec![false; comm.n];
    for (pos, &c) in perm.iter().enumerate() {
        suffix[c] = pos > cut;
    }
    let count = |comp: usize, my_side_suffix: bool| -> usize {
        let mut vars = BTreeSet::new();
        for &(l, src) in &comm.in_edges[comp] {
            if suffix[src] != my_side_suffix {
                vars.insert(l);
            }
        }
        vars.len()
    };
    let c1 = count(perm[cut], false);
    let c2 = if cut + 1 < comm.n {
        count(perm[cut + 1], true)
    } else {
        0
    };
    (c1 + c2) as f64
}

/// min-comm cut cost: forward-crossing vars + 2^(backward-crossing vars).
fn min_comm_cost(comm: &Comm, perm: &[usize], cut: usize) -> f64 {
    let mut suffix = vec![false; comm.n];
    for (pos, &c) in perm.iter().enumerate() {
        suffix[c] = pos > cut;
    }
    let mut fwd = BTreeSet::new();
    let mut bwd = BTreeSet::new();
    for (comp, edges) in comm.out_edges.iter().enumerate() {
        for &(l, dst) in edges {
            if suffix[comp] != suffix[dst] {
                if !suffix[comp] {
                    fwd.insert(l); // prefix → suffix
                } else {
                    bwd.insert(l); // suffix → prefix
                }
            }
        }
    }
    fwd.len() as f64 + (2f64).powi(bwd.len() as i32)
}

/// Compute the leaf order for the given strategy. Every leaf appears
/// exactly once.
pub fn compute_order(flat: &FlatModule, strategy: StaticOrder) -> Vec<LeafId> {
    let n = flat.leaves.len();
    if matches!(strategy, StaticOrder::None) || flat.components.is_empty() {
        return (0..n as LeafId).collect();
    }
    let deps = dependency_graph(flat);
    let w = weights(flat, &deps);

    // deduplicated ownership (first writer owns a shared leaf)
    let mut owned: Vec<BTreeSet<LeafId>> = Vec::new();
    let mut taken: BTreeSet<LeafId> = BTreeSet::new();
    for comp in &flat.components {
        let mine: BTreeSet<LeafId> = comp
            .owned
            .iter()
            .filter(|l| taken.insert(**l))
            .cloned()
            .collect();
        owned.push(mine);
    }

    // component permutation
    let ncomp = flat.components.len();
    let perm: Vec<usize> = match strategy {
        StaticOrder::Simple | StaticOrder::None => (0..ncomp).collect(),
        StaticOrder::MinSupp | StaticOrder::MinSupp2 => {
            let comm = communication(flat, &owned);
            let la2 = matches!(strategy, StaticOrder::MinSupp2);
            find_permutation(ncomp, la2, &mut |p, c| min_supp_cost(&comm, p, c))
        }
        StaticOrder::MinComm | StaticOrder::MinComm2 => {
            let comm = communication(flat, &owned);
            let la2 = matches!(strategy, StaticOrder::MinComm2);
            find_permutation(ncomp, la2, &mut |p, c| min_comm_cost(&comm, p, c))
        }
    };

    // per-component variable layout
    let mut placed: BTreeSet<LeafId> = BTreeSet::new();
    let mut order: Vec<LeafId> = Vec::new();
    for &ci in &perm {
        let owned_sorted = sort_by_weight(owned[ci].iter().cloned().collect(), &w);
        for x in owned_sorted {
            if placed.contains(&x) {
                continue;
            }
            placed.insert(x);
            // not-yet-placed input/global leaves that x' depends on
            let mut used: Vec<LeafId> = deps
                .get(&x)
                .map(|s| {
                    s.iter()
                        .filter(|l| {
                            !placed.contains(l)
                                && matches!(
                                    flat.leaves[**l as usize].class,
                                    VarClass::Input | VarClass::Global
                                )
                        })
                        .cloned()
                        .collect()
                })
                .unwrap_or_default();
            used = sort_by_weight(used, &w);
            for u in used {
                placed.insert(u);
                order.push(u);
            }
            order.push(x);
        }
    }
    // unreferenced leaves go first, sorted by weight
    let unref: Vec<LeafId> = (0..n as LeafId).filter(|l| !placed.contains(l)).collect();
    let unref = sort_by_weight(unref, &w);
    let mut result = unref;
    result.extend(order);
    debug_assert_eq!(result.len(), n);
    result
}

/// Parse a `.ord` order file: a parenthesized list of variable names;
/// `name!i` refers to `name[i]`. Returns the leaf order; leaves not
/// mentioned keep declaration order at the end.
pub fn order_from_file(flat: &FlatModule, text: &str) -> Result<Vec<LeafId>, String> {
    let mut order = Vec::new();
    let mut placed = BTreeSet::new();
    for tok in text
        .replace('(', " ")
        .replace(')', " ")
        .split_whitespace()
    {
        let candidates: Vec<LeafId> = if let Some((base, idx)) = tok.rsplit_once('!') {
            // `name!i` = the i-th (1-based) element of the array variable
            // in declaration order (as the oracle's order files use)
            let i: usize = idx
                .parse()
                .map_err(|_| format!("bad index in \"{}\" in order file", tok))?;
            // group leaves by element key `base[<elem>]`
            let mut groups: Vec<(String, Vec<LeafId>)> = Vec::new();
            for (li, l) in flat.leaves.iter().enumerate() {
                if let Some(rest) = l.name.strip_prefix(&format!("{}[", base)) {
                    if let Some(close) = rest.find(']') {
                        let key = rest[..close].to_string();
                        match groups.iter_mut().find(|(k, _)| *k == key) {
                            Some((_, v)) => v.push(li as LeafId),
                            None => groups.push((key, vec![li as LeafId])),
                        }
                    }
                }
            }
            if i >= 1 && i <= groups.len() {
                groups[i - 1].1.clone()
            } else {
                Vec::new()
            }
        } else {
            flat.leaves
                .iter()
                .enumerate()
                .filter(|(_, l)| {
                    l.name == tok
                        || l.name.starts_with(&format!("{}.", tok))
                        || l.name.starts_with(&format!("{}[", tok))
                })
                .map(|(i, _)| i as LeafId)
                .collect()
        };
        // names that do not resolve are ignored, like the oracle (order
        // files may mention variables sliced away or absent at this
        // instantiation size)
        for c in candidates {
            if placed.insert(c) {
                order.push(c);
            }
        }
    }
    for l in 0..flat.leaves.len() as LeafId {
        if placed.insert(l) {
            order.push(l);
        }
    }
    Ok(order)
}

#[cfg(test)]
mod tests {
    use super::*;
    use sal_flat::fexpr::{LeafInfo, LeafType};
    use sal_flat::flatten::{FlatModule, TransNode};
    use sal_syntax::ast::VarClass;

    fn leaf(name: &str) -> LeafInfo {
        LeafInfo {
            name: name.into(),
            ty: LeafType::Bool,
            class: VarClass::Local,
        }
    }

    fn module(names: &[&str]) -> FlatModule {
        FlatModule {
            leaves: names.iter().map(|n| leaf(n)).collect(),
            vars: vec![],
            invariants: vec![],
            init_defs: vec![],
            init_choices: vec![],
            trans_defs: vec![],
            trans: TransNode::True,
            controlled: Default::default(),
            components: vec![],
        }
    }

    #[test]
    fn order_file_positional_bang_syntax() {
        // pc!2 = second element group of pc[...]
        let m = module(&["pc[a]", "pc[b]", "forks[a]", "forks[b]"]);
        let order = order_from_file(&m, "(\npc!2\nforks!1\n)").unwrap();
        assert_eq!(order[0], 1); // pc[b]
        assert_eq!(order[1], 2); // forks[a]
        assert_eq!(order.len(), 4); // rest appended
    }

    #[test]
    fn order_file_ignores_unknown_names() {
        let m = module(&["x"]);
        let order = order_from_file(&m, "(zz x)").unwrap();
        assert_eq!(order, vec![0]);
    }

    #[test]
    fn compute_order_is_a_permutation() {
        let m = module(&["a", "b", "c"]);
        let order = compute_order(&m, StaticOrder::MinSupp);
        let mut sorted = order.clone();
        sorted.sort();
        assert_eq!(sorted, vec![0, 1, 2]);
    }
}
