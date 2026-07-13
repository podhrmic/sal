//! A compact hash-consed BDD manager.
//!
//! Variables are `u32` levels; ordering is the numeric order. State
//! encodings pair current/next bits adjacently (cur = even, next = odd),
//! so priming/unpriming is the structural map `v ↔ v±1`, which preserves
//! level order.

use rustc_hash::FxHashMap as HashMap;

pub type NodeId = u32;
pub const F: NodeId = 0;
pub const T: NodeId = 1;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Node {
    var: u32,
    lo: NodeId,
    hi: NodeId,
}

const SENTINEL_VAR: u32 = u32::MAX;

pub struct Mgr {
    nodes: Vec<Node>,
    unique: HashMap<Node, NodeId>,
    ite_cache: HashMap<(NodeId, NodeId, NodeId), NodeId>,
    exists_cache: HashMap<(NodeId, u64), NodeId>,
    shift_cache: HashMap<(NodeId, i8), NodeId>,
    /// Variable classes for quantification: bit i of the mask key selects
    /// groups; we store the set of quantified vars per group id.
    pub num_vars: u32,
}

impl Mgr {
    pub fn new() -> Self {
        let mut m = Mgr {
            nodes: Vec::new(),
            unique: HashMap::default(),
            ite_cache: HashMap::default(),
            exists_cache: HashMap::default(),
            shift_cache: HashMap::default(),
            num_vars: 0,
        };
        // 0 = false, 1 = true
        m.nodes.push(Node {
            var: SENTINEL_VAR,
            lo: F,
            hi: F,
        });
        m.nodes.push(Node {
            var: SENTINEL_VAR,
            lo: T,
            hi: T,
        });
        m
    }

    fn var_of(&self, n: NodeId) -> u32 {
        self.nodes[n as usize].var
    }

    fn mk(&mut self, var: u32, lo: NodeId, hi: NodeId) -> NodeId {
        if lo == hi {
            return lo;
        }
        let node = Node { var, lo, hi };
        if let Some(&id) = self.unique.get(&node) {
            return id;
        }
        let id = self.nodes.len() as NodeId;
        self.nodes.push(node);
        self.unique.insert(node, id);
        id
    }

    pub fn var(&mut self, v: u32) -> NodeId {
        self.num_vars = self.num_vars.max(v + 1);
        self.mk(v, F, T)
    }

    pub fn nvar(&mut self, v: u32) -> NodeId {
        self.num_vars = self.num_vars.max(v + 1);
        self.mk(v, T, F)
    }

    pub fn ite(&mut self, c: NodeId, t: NodeId, e: NodeId) -> NodeId {
        // terminal cases
        if c == T {
            return t;
        }
        if c == F {
            return e;
        }
        if t == e {
            return t;
        }
        if t == T && e == F {
            return c;
        }
        let key = (c, t, e);
        if let Some(&r) = self.ite_cache.get(&key) {
            return r;
        }
        let vc = self.var_of(c);
        let vt = self.var_of(t);
        let ve = self.var_of(e);
        let top = vc.min(vt).min(ve);
        let (c0, c1) = self.cofactor(c, top);
        let (t0, t1) = self.cofactor(t, top);
        let (e0, e1) = self.cofactor(e, top);
        let lo = self.ite(c0, t0, e0);
        let hi = self.ite(c1, t1, e1);
        let r = self.mk(top, lo, hi);
        self.ite_cache.insert(key, r);
        r
    }

    fn cofactor(&self, n: NodeId, var: u32) -> (NodeId, NodeId) {
        let node = self.nodes[n as usize];
        if node.var == var {
            (node.lo, node.hi)
        } else {
            (n, n)
        }
    }

    pub fn and(&mut self, a: NodeId, b: NodeId) -> NodeId {
        self.ite(a, b, F)
    }

    pub fn or(&mut self, a: NodeId, b: NodeId) -> NodeId {
        self.ite(a, T, b)
    }

    pub fn not(&mut self, a: NodeId) -> NodeId {
        self.ite(a, F, T)
    }

    pub fn xor(&mut self, a: NodeId, b: NodeId) -> NodeId {
        let nb = self.not(b);
        self.ite(a, nb, b)
    }

    pub fn iff(&mut self, a: NodeId, b: NodeId) -> NodeId {
        let nb = self.not(b);
        self.ite(a, b, nb)
    }

    pub fn and_many(&mut self, xs: &[NodeId]) -> NodeId {
        let mut r = T;
        for &x in xs {
            r = self.and(r, x);
            if r == F {
                break;
            }
        }
        r
    }

    pub fn or_many(&mut self, xs: &[NodeId]) -> NodeId {
        let mut r = F;
        for &x in xs {
            r = self.or(r, x);
            if r == T {
                break;
            }
        }
        r
    }

    /// Existentially quantify all variables for which `keep(var)` is false.
    /// `cache_key` must uniquely identify the predicate.
    pub fn exists_where(
        &mut self,
        n: NodeId,
        quantify: &impl Fn(u32) -> bool,
        cache_key: u64,
    ) -> NodeId {
        if n <= T {
            return n;
        }
        let key = (n, cache_key);
        if let Some(&r) = self.exists_cache.get(&key) {
            return r;
        }
        let node = self.nodes[n as usize];
        let lo = self.exists_where(node.lo, quantify, cache_key);
        let hi = self.exists_where(node.hi, quantify, cache_key);
        let r = if quantify(node.var) {
            self.or(lo, hi)
        } else {
            self.mk(node.var, lo, hi)
        };
        self.exists_cache.insert(key, r);
        r
    }

    /// Structural shift: `delta = +1` maps cur→next (even→odd), `-1` maps
    /// next→cur. Only valid when the BDD contains exclusively vars of the
    /// source parity.
    pub fn shift(&mut self, n: NodeId, delta: i8) -> NodeId {
        if n <= T {
            return n;
        }
        let key = (n, delta);
        if let Some(&r) = self.shift_cache.get(&key) {
            return r;
        }
        let node = self.nodes[n as usize];
        let lo = self.shift(node.lo, delta);
        let hi = self.shift(node.hi, delta);
        let v = (node.var as i64 + delta as i64) as u32;
        let r = self.mk(v, lo, hi);
        self.shift_cache.insert(key, r);
        r
    }

    /// One satisfying assignment (as var → bool for all vars ≤ max seen in
    /// the BDD; unlisted vars are unconstrained).
    pub fn pick(&self, n: NodeId) -> Option<HashMap<u32, bool>> {
        if n == F {
            return None;
        }
        let mut out = HashMap::default();
        let mut cur = n;
        while cur > T {
            let node = self.nodes[cur as usize];
            if node.lo != F {
                out.insert(node.var, false);
                cur = node.lo;
            } else {
                out.insert(node.var, true);
                cur = node.hi;
            }
        }
        Some(out)
    }

    /// Restrict a BDD by a (partial) assignment.
    pub fn restrict(&mut self, n: NodeId, assignment: &HashMap<u32, bool>) -> NodeId {
        if n <= T {
            return n;
        }
        let node = self.nodes[n as usize];
        let child = match assignment.get(&node.var) {
            Some(false) => return self.restrict(node.lo, assignment),
            Some(true) => return self.restrict(node.hi, assignment),
            None => node,
        };
        let lo = self.restrict(child.lo, assignment);
        let hi = self.restrict(child.hi, assignment);
        self.mk(node.var, lo, hi)
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
}

impl Default for Mgr {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_ops() {
        let mut m = Mgr::new();
        let a = m.var(0);
        let b = m.var(2);
        let ab = m.and(a, b);
        let na = m.not(a);
        assert_eq!(m.and(ab, na), F);
        let aob = m.or(a, b);
        assert_eq!(m.or(aob, na), T);
    }

    #[test]
    fn shift_roundtrip() {
        let mut m = Mgr::new();
        let a = m.var(0);
        let b = m.var(4);
        let ab = m.and(a, b);
        let shifted = m.shift(ab, 1);
        let back = m.shift(shifted, -1);
        assert_eq!(ab, back);
    }

    #[test]
    fn exists() {
        let mut m = Mgr::new();
        let a = m.var(0);
        let b = m.var(2);
        let ab = m.and(a, b);
        // exists a. a&b == b
        let r = m.exists_where(ab, &|v| v == 0, 100);
        assert_eq!(r, b);
    }
}
