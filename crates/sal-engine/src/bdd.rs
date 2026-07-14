//! A hash-consed BDD manager with dynamic variable reordering
//! (Rudell-style group sifting).
//!
//! Variables are `u32` identities; their position in the order is a
//! separate *level* (`level_of`/`var_at`). State encodings pair
//! current/next bits as variables `2k`/`2k+1`; the pair is sifted as an
//! indivisible group with fixed internal order (cur above next), so
//! priming/unpriming stays the structural map `v ↔ v±1`.
//!
//! Reordering swaps adjacent levels *in place*: `NodeId`s remain valid
//! and keep denoting the same function. A rewritten node that collides
//! with an existing node becomes a *forward*; all entry points resolve
//! forwards, and nodes are lazily repaired (children re-resolved,
//! subtable keys renormalized) on first use, preserving canonicity.

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

const SENTINEL_VAR: u32 = u32::MAX; // terminals
const FWD: u32 = u32::MAX - 1; // forwarded node; `lo` is the target
const FREE: u32 = u32::MAX - 2; // garbage-collected slot
const MAX_GROWTH: f64 = 1.2;

pub struct Mgr {
    nodes: Vec<Node>,
    /// Unique tables, one per variable: (lo, hi) → id.
    subtables: Vec<HashMap<(NodeId, NodeId), NodeId>>,
    level_of: Vec<u32>,
    var_at: Vec<u32>,
    ite_cache: HashMap<(NodeId, NodeId, NodeId), NodeId>,
    exists_cache: HashMap<(NodeId, u64), NodeId>,
    shift_cache: HashMap<(NodeId, i8), NodeId>,
    /// Live (non-forwarded, non-freed) node count.
    live: usize,
    free_list: Vec<NodeId>,
    /// Reference counts, active only during sifting (eager dead-node
    /// reclamation keeps the size metric honest).
    rc: Vec<u32>,
    rc_active: bool,
    reorder_enabled: bool,
    next_reorder: usize,
    reordering: bool,
    pub num_vars: u32,
    pub reorder_count: usize,
}

impl Mgr {
    pub fn new() -> Self {
        let mut m = Mgr {
            nodes: Vec::new(),
            subtables: Vec::new(),
            level_of: Vec::new(),
            var_at: Vec::new(),
            ite_cache: HashMap::default(),
            exists_cache: HashMap::default(),
            shift_cache: HashMap::default(),
            live: 0,
            free_list: Vec::new(),
            rc: Vec::new(),
            rc_active: false,
            reorder_enabled: false,
            next_reorder: 150_000,
            reordering: false,
            num_vars: 0,
            reorder_count: 0,
        };
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

    pub fn set_reorder(&mut self, on: bool) {
        self.reorder_enabled = on;
    }

    // -- forwards, levels, repair ------------------------------------------

    /// Follow forward pointers to the canonical node.
    pub fn resolve(&self, mut n: NodeId) -> NodeId {
        while self.nodes[n as usize].var == FWD {
            n = self.nodes[n as usize].lo;
        }
        n
    }

    /// Same function? (compares canonical representatives)
    pub fn same(&self, a: NodeId, b: NodeId) -> bool {
        self.resolve(a) == self.resolve(b)
    }

    fn level(&self, n: NodeId) -> u32 {
        let v = self.nodes[n as usize].var;
        if v == SENTINEL_VAR {
            u32::MAX
        } else {
            self.level_of[v as usize]
        }
    }

    fn var_of(&self, n: NodeId) -> u32 {
        self.nodes[n as usize].var
    }

    fn ensure_var(&mut self, v: u32) {
        // grow in complete (cur,next) pairs so groups are always whole
        let want = ((v | 1) + 1) as usize;
        while self.subtables.len() < want {
            let nv = self.subtables.len() as u32;
            self.subtables.push(HashMap::default());
            self.level_of.push(nv);
            self.var_at.push(nv);
        }
        self.num_vars = self.num_vars.max(v + 1);
    }

    /// Repair a node whose stored children may have been forwarded:
    /// renormalize its subtable key; the node itself may become a
    /// forward on collision. Returns the canonical id.
    fn repair(&mut self, n: NodeId) -> NodeId {
        let n = self.resolve(n);
        if n <= T {
            return n;
        }
        let node = self.nodes[n as usize];
        let lo = self.resolve(node.lo);
        let hi = self.resolve(node.hi);
        if lo == node.lo && hi == node.hi {
            return n;
        }
        let st = &mut self.subtables[node.var as usize];
        st.remove(&(node.lo, node.hi));
        if lo == hi {
            self.nodes[n as usize] = Node {
                var: FWD,
                lo,
                hi: lo,
            };
            self.live -= 1;
            return lo;
        }
        match self.subtables[node.var as usize].get(&(lo, hi)) {
            Some(&m) if m != n => {
                self.nodes[n as usize] = Node {
                    var: FWD,
                    lo: m,
                    hi: m,
                };
                self.live -= 1;
                m
            }
            _ => {
                self.nodes[n as usize] = Node {
                    var: node.var,
                    lo,
                    hi,
                };
                self.subtables[node.var as usize].insert((lo, hi), n);
                n
            }
        }
    }

    fn mk(&mut self, var: u32, lo: NodeId, hi: NodeId) -> NodeId {
        let lo = self.resolve(lo);
        let hi = self.resolve(hi);
        if lo == hi {
            return lo;
        }
        debug_assert!(self.level_of[var as usize] < self.level(lo));
        debug_assert!(self.level_of[var as usize] < self.level(hi));
        if let Some(&id) = self.subtables[var as usize].get(&(lo, hi)) {
            return id;
        }
        let id = match self.free_list.pop() {
            Some(id) => {
                self.nodes[id as usize] = Node { var, lo, hi };
                id
            }
            None => {
                let id = self.nodes.len() as NodeId;
                self.nodes.push(Node { var, lo, hi });
                id
            }
        };
        self.subtables[var as usize].insert((lo, hi), id);
        self.live += 1;
        if self.rc_active {
            if self.rc.len() <= id as usize {
                self.rc.resize(id as usize + 1, 0);
            }
            self.rc[id as usize] = 0;
            self.rc_inc(lo);
            self.rc_inc(hi);
        }
        id
    }

    fn rc_inc(&mut self, n: NodeId) {
        if n > T {
            self.rc[n as usize] += 1;
        }
    }

    /// Decrement a reference; reclaim eagerly at zero.
    fn rc_dec(&mut self, n: NodeId) {
        if n <= T {
            return;
        }
        let i = n as usize;
        self.rc[i] = self.rc[i].saturating_sub(1);
        if self.rc[i] == 0 {
            let node = self.nodes[i];
            match node.var {
                FREE | SENTINEL_VAR => {}
                FWD => {
                    self.nodes[i] = Node { var: FREE, lo: F, hi: F };
                    self.free_list.push(n);
                    self.rc_dec(node.lo);
                }
                v => {
                    self.subtables[v as usize].remove(&(node.lo, node.hi));
                    self.nodes[i] = Node { var: FREE, lo: F, hi: F };
                    self.free_list.push(n);
                    self.live -= 1;
                    self.rc_dec(node.lo);
                    self.rc_dec(node.hi);
                }
            }
        }
    }

    /// Compute reference counts from subtables + roots (sift setup).
    fn rc_init(&mut self, roots: &[NodeId]) {
        self.rc = vec![0; self.nodes.len()];
        for st in &self.subtables {
            for (&(lo, hi), _) in st.iter() {
                if lo > T {
                    self.rc[lo as usize] += 1;
                }
                if hi > T {
                    self.rc[hi as usize] += 1;
                }
            }
        }
        for &r in roots {
            let mut n = r;
            // count the root reference on the whole forward chain head
            if n > T {
                self.rc[n as usize] += 1;
            }
            while self.nodes[n as usize].var == FWD {
                let t = self.nodes[n as usize].lo;
                if t > T {
                    self.rc[t as usize] += 1;
                }
                n = t;
            }
        }
        self.rc_active = true;
    }

    pub fn var(&mut self, v: u32) -> NodeId {
        self.ensure_var(v);
        self.mk(v, F, T)
    }

    pub fn nvar(&mut self, v: u32) -> NodeId {
        self.ensure_var(v);
        self.mk(v, T, F)
    }

    // -- core operations ----------------------------------------------------

    pub fn ite(&mut self, c: NodeId, t: NodeId, e: NodeId) -> NodeId {
        self.ite_rec(c, t, e)
    }

    fn ite_rec(&mut self, c: NodeId, t: NodeId, e: NodeId) -> NodeId {
        let c = self.repair(c);
        let t = self.repair(t);
        let e = self.repair(e);
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
        let top = self.level(c).min(self.level(t)).min(self.level(e));
        let var = self.var_at[top as usize];
        let (c0, c1) = self.cofactor(c, var);
        let (t0, t1) = self.cofactor(t, var);
        let (e0, e1) = self.cofactor(e, var);
        let lo = self.ite_rec(c0, t0, e0);
        let hi = self.ite_rec(c1, t1, e1);
        let r = self.mk(var, lo, hi);
        self.ite_cache.insert(key, r);
        r
    }

    fn cofactor(&mut self, n: NodeId, var: u32) -> (NodeId, NodeId) {
        let node = self.nodes[n as usize];
        if node.var == var {
            (self.resolve(node.lo), self.resolve(node.hi))
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

    /// Existentially quantify all variables for which `quantify(var)` is
    /// true. `cache_key` must uniquely identify the predicate.
    pub fn exists_where(
        &mut self,
        n: NodeId,
        quantify: &impl Fn(u32) -> bool,
        cache_key: u64,
    ) -> NodeId {
        self.exists_rec(n, quantify, cache_key)
    }

    fn exists_rec(
        &mut self,
        n: NodeId,
        quantify: &impl Fn(u32) -> bool,
        cache_key: u64,
    ) -> NodeId {
        let n = self.repair(n);
        if n <= T {
            return n;
        }
        let key = (n, cache_key);
        if let Some(&r) = self.exists_cache.get(&key) {
            return r;
        }
        let node = self.nodes[n as usize];
        let lo = self.exists_rec(node.lo, quantify, cache_key);
        let hi = self.exists_rec(node.hi, quantify, cache_key);
        let r = if quantify(node.var) {
            self.ite_rec(lo, T, hi)
        } else {
            self.mk(node.var, lo, hi)
        };
        self.exists_cache.insert(key, r);
        r
    }

    /// Structural shift: `delta = +1` maps cur→next (even→odd), `-1` maps
    /// next→cur. Valid because (cur,next) pairs occupy adjacent levels
    /// with cur above next, which group sifting preserves.
    pub fn shift(&mut self, n: NodeId, delta: i8) -> NodeId {
        self.shift_rec(n, delta)
    }

    fn shift_rec(&mut self, n: NodeId, delta: i8) -> NodeId {
        let n = self.repair(n);
        if n <= T {
            return n;
        }
        let key = (n, delta);
        if let Some(&r) = self.shift_cache.get(&key) {
            return r;
        }
        let node = self.nodes[n as usize];
        let lo = self.shift_rec(node.lo, delta);
        let hi = self.shift_rec(node.hi, delta);
        let v = (node.var as i64 + delta as i64) as u32;
        self.ensure_var(v);
        let r = self.mk(v, lo, hi);
        self.shift_cache.insert(key, r);
        r
    }

    /// One satisfying assignment (var → bool; unlisted vars are
    /// unconstrained).
    pub fn pick(&self, n: NodeId) -> Option<HashMap<u32, bool>> {
        let mut cur = self.resolve(n);
        if cur == F {
            return None;
        }
        let mut out = HashMap::default();
        while cur > T {
            let node = self.nodes[cur as usize];
            let lo = self.resolve(node.lo);
            if lo != F {
                out.insert(node.var, false);
                cur = lo;
            } else {
                out.insert(node.var, true);
                cur = self.resolve(node.hi);
            }
        }
        Some(out)
    }

    /// Restrict a BDD by a (partial) assignment.
    pub fn restrict(&mut self, n: NodeId, assignment: &HashMap<u32, bool>) -> NodeId {
        let n = self.repair(n);
        if n <= T {
            return n;
        }
        let node = self.nodes[n as usize];
        match assignment.get(&node.var) {
            Some(false) => return self.restrict(node.lo, assignment),
            Some(true) => return self.restrict(node.hi, assignment),
            None => {}
        }
        let lo = self.restrict(node.lo, assignment);
        let hi = self.restrict(node.hi, assignment);
        self.mk(node.var, lo, hi)
    }

    pub fn node_count(&self) -> usize {
        self.live
    }

    // -- dynamic reordering ---------------------------------------------------

    /// Reordering safe point: `roots` must enumerate every BDD the caller
    /// still needs (stored ids stay valid; forward chains are preserved).
    /// Garbage-collects, and sifts when the live size warrants it.
    pub fn reorder_if_needed(&mut self, roots: &[NodeId]) {
        if !self.reorder_enabled || self.reordering || self.live < self.next_reorder {
            return;
        }
        let before = self.live;
        let t = std::time::Instant::now();
        self.gc(roots);
        let after_gc = self.live;
        // sift whenever the retained working set itself is large
        if self.live >= 30_000 {
            self.sift_with_roots(roots);
            self.reorder_count += 1;
        }
        self.debug_log(&format!(
            "reorder #{}: {} -> gc {} -> sift {} live nodes in {:?}",
            self.reorder_count, before, after_gc, self.live, t.elapsed()
        ));
        self.next_reorder = (self.live * 3).max(150_000);
    }

    /// Mark-and-sweep garbage collection. Every needed BDD must be in
    /// `roots`; forward chains reachable from roots are preserved so
    /// stale ids stay resolvable.
    pub fn gc(&mut self, roots: &[NodeId]) {
        let mut marked = vec![false; self.nodes.len()];
        marked[F as usize] = true;
        marked[T as usize] = true;
        let mut stack: Vec<NodeId> = roots.to_vec();
        while let Some(start) = stack.pop() {
            let mut n = start;
            // keep forward chains alive
            while self.nodes[n as usize].var == FWD {
                if marked[n as usize] {
                    break;
                }
                marked[n as usize] = true;
                n = self.nodes[n as usize].lo;
            }
            if marked[n as usize] {
                continue;
            }
            marked[n as usize] = true;
            let node = self.nodes[n as usize];
            if node.var != SENTINEL_VAR && node.var != FREE {
                stack.push(node.lo);
                stack.push(node.hi);
            }
        }
        // sweep
        for st in &mut self.subtables {
            st.retain(|_, id| marked[*id as usize]);
        }
        let mut freed = 0usize;
        for (i, node) in self.nodes.iter_mut().enumerate() {
            if i as NodeId <= T || marked[i] {
                continue;
            }
            if node.var != FREE {
                if node.var != FWD {
                    freed += 1;
                }
                *node = Node {
                    var: FREE,
                    lo: F,
                    hi: F,
                };
                self.free_list.push(i as NodeId);
            }
        }
        self.live -= freed;
        self.ite_cache.clear();
        self.exists_cache.clear();
        self.shift_cache.clear();
    }

    fn debug_log(&self, msg: &str) {
        if std::env::var("SAL_BDD_DEBUG").is_ok() {
            eprintln!("[bdd] {}", msg);
        }
    }

    /// Force a reordering pass now. `roots` must enumerate every BDD the
    /// caller still holds (same contract as `reorder_if_needed`).
    pub fn reorder_now(&mut self, roots: &[NodeId]) {
        if !self.reordering {
            self.gc(roots);
            self.sift_with_roots(roots);
            self.reorder_count += 1;
        }
    }

    /// Swap adjacent levels `l` and `l+1` in place. Returns the number
    /// of nodes touched (the sifting work budget unit).
    fn swap_levels(&mut self, l: usize) -> usize {
        let x = self.var_at[l];
        let y = self.var_at[l + 1];
        let xnodes: Vec<NodeId> = self.subtables[x as usize].values().cloned().collect();
        self.subtables[x as usize].clear();
        // pass 1: nodes not involving y stay x-nodes (reinsert with
        // normalized keys)
        let mut affected = Vec::new();
        for n in xnodes {
            let node = self.nodes[n as usize];
            if node.var != x {
                continue; // already forwarded by a repair
            }
            let lo = self.resolve(node.lo);
            let hi = self.resolve(node.hi);
            if self.var_of(lo) != y && self.var_of(hi) != y {
                if lo == hi {
                    self.nodes[n as usize] = Node {
                        var: FWD,
                        lo,
                        hi: lo,
                    };
                    self.live -= 1;
                    if self.rc_active {
                        // n's two child refs collapse into one forward ref
                        self.rc_inc(lo);
                        self.rc_dec(node.lo);
                        self.rc_dec(node.hi);
                    }
                    continue;
                }
                match self.subtables[x as usize].get(&(lo, hi)) {
                    Some(&m) if m != n => {
                        self.nodes[n as usize] = Node {
                            var: FWD,
                            lo: m,
                            hi: m,
                        };
                        self.live -= 1;
                        if self.rc_active {
                            self.rc_inc(m);
                            self.rc_dec(node.lo);
                            self.rc_dec(node.hi);
                        }
                    }
                    _ => {
                        self.nodes[n as usize] = Node { var: x, lo, hi };
                        self.subtables[x as usize].insert((lo, hi), n);
                        if self.rc_active && (lo != node.lo || hi != node.hi) {
                            self.rc_inc(lo);
                            self.rc_inc(hi);
                            self.rc_dec(node.lo);
                            self.rc_dec(node.hi);
                        }
                    }
                }
            } else {
                affected.push((n, lo, hi));
            }
        }
        // pass 2: rewrite affected nodes with y on top
        for (n, f0, f1) in affected {
            let (f00, f01) = if self.var_of(f0) == y {
                let c = self.nodes[f0 as usize];
                (self.resolve(c.lo), self.resolve(c.hi))
            } else {
                (f0, f0)
            };
            let (f10, f11) = if self.var_of(f1) == y {
                let c = self.nodes[f1 as usize];
                (self.resolve(c.lo), self.resolve(c.hi))
            } else {
                (f1, f1)
            };
            let a = self.mk(x, f00, f10);
            let b = self.mk(x, f01, f11);
            debug_assert_ne!(a, b, "rewritten node cannot be redundant");
            // n's old child refs are released; the new shape's refs added
            let old = self.nodes[n as usize];
            match self.subtables[y as usize].get(&(a, b)) {
                Some(&m) => {
                    // collision with a surviving y-node
                    self.nodes[n as usize] = Node {
                        var: FWD,
                        lo: m,
                        hi: m,
                    };
                    self.live -= 1;
                    if self.rc_active {
                        self.rc_inc(m);
                        self.rc_dec(old.lo);
                        self.rc_dec(old.hi);
                    }
                }
                None => {
                    self.nodes[n as usize] = Node { var: y, lo: a, hi: b };
                    self.subtables[y as usize].insert((a, b), n);
                    if self.rc_active {
                        self.rc_inc(a);
                        self.rc_inc(b);
                        self.rc_dec(old.lo);
                        self.rc_dec(old.hi);
                    }
                }
            }
        }
        self.var_at.swap(l, l + 1);
        self.level_of[x as usize] = (l + 1) as u32;
        self.level_of[y as usize] = l as u32;
        self.subtables[x as usize].len() + self.subtables[y as usize].len()
    }

    /// Swap the (cur,next) groups at group positions `p` and `p+1`
    /// (levels 2p..2p+3), preserving internal cur-above-next order.
    fn swap_groups(&mut self, p: usize) -> usize {
        let l = 2 * p;
        let mut w = 0;
        w += self.swap_levels(l + 1);
        w += self.swap_levels(l);
        w += self.swap_levels(l + 2);
        w += self.swap_levels(l + 1);
        w
    }

    fn group_size(&self, p: usize) -> usize {
        let a = self.var_at[2 * p] as usize;
        let b = self.var_at[2 * p + 1] as usize;
        self.subtables[a].len() + self.subtables[b].len()
    }

    /// Rudell sifting over (cur,next) groups, bounded by a work budget
    /// (nodes touched) so a pass stays a small multiple of the live size.
    fn sift_with_roots(&mut self, roots: &[NodeId]) {
        self.reordering = true;
        self.ite_cache.clear();
        self.exists_cache.clear();
        self.shift_cache.clear();
        self.rc_init(roots);
        let ngroups = self.subtables.len() / 2;
        if ngroups >= 2 {
            // largest groups first; skip groups below 0.5% of live nodes
            let mut order: Vec<usize> = (0..ngroups).collect();
            order.sort_by_key(|&p| std::cmp::Reverse(self.group_size(p)));
            let min_size = self.live / 200;
            let max_groups: usize = std::env::var("SAL_BDD_SIFT_GROUPS")
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(16);
            let budget_factor: usize = std::env::var("SAL_BDD_SIFT_BUDGET")
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(12);
            let group_vars: Vec<u32> = order
                .iter()
                .filter(|&&p| self.group_size(p) > min_size)
                .map(|&p| self.var_at[2 * p])
                .take(max_groups)
                .collect();
            let mut budget: usize = self.live.saturating_mul(budget_factor);
            for gv in group_vars {
                if budget == 0 {
                    break;
                }
                let start = self.live as f64;
                let mut pos = (self.level_of[gv as usize] / 2) as usize;
                let mut best = self.live;
                let mut best_pos = pos;
                let group_budget = self
                    .live
                    .saturating_mul((budget_factor / 4).max(2))
                    .min(budget);
                let mut spent: usize = 0;
                // sift down
                while pos + 1 < ngroups && spent < group_budget {
                    spent += self.swap_groups(pos);
                    pos += 1;
                    if self.live < best {
                        best = self.live;
                        best_pos = pos;
                    }
                    if self.live as f64 > MAX_GROWTH * start {
                        break;
                    }
                }
                // sift up
                while pos > 0 && spent < group_budget {
                    spent += self.swap_groups(pos - 1);
                    pos -= 1;
                    if self.live < best {
                        best = self.live;
                        best_pos = pos;
                    }
                    if self.live as f64 > MAX_GROWTH * start {
                        break;
                    }
                }
                // move to the best position seen
                while pos < best_pos {
                    spent += self.swap_groups(pos);
                    pos += 1;
                }
                while pos > best_pos {
                    spent += self.swap_groups(pos - 1);
                    pos -= 1;
                }
                budget = budget.saturating_sub(spent);
            }
        }
        self.rc_active = false;
        self.rc.clear();
        self.ite_cache.clear();
        self.exists_cache.clear();
        self.shift_cache.clear();
        self.reordering = false;
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

    fn eval(m: &Mgr, n: NodeId, assign: &dyn Fn(u32) -> bool) -> bool {
        let mut cur = m.resolve(n);
        while cur > T {
            let node = m.nodes[cur as usize];
            cur = m.resolve(if assign(node.var) { node.hi } else { node.lo });
        }
        cur == T
    }

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
        assert!(m.same(ab, back));
    }

    #[test]
    fn exists() {
        let mut m = Mgr::new();
        let a = m.var(0);
        let b = m.var(2);
        let ab = m.and(a, b);
        let r = m.exists_where(ab, &|v| v == 0, 100);
        assert!(m.same(r, b));
    }

    #[test]
    fn gc_keeps_roots_and_frees_garbage() {
        let mut m = Mgr::new();
        let a = m.var(0);
        let b = m.var(2);
        let keep = m.and(a, b);
        // create garbage
        for v in [4u32, 6, 8] {
            let x = m.var(v);
            let _garbage = m.xor(keep, x);
        }
        let before = m.node_count();
        m.gc(&[keep]);
        assert!(m.node_count() < before, "gc freed nothing");
        // the kept function still works
        assert!(eval(&m, keep, &|v| v == 0 || v == 2));
        assert!(!eval(&m, keep, &|v| v == 0));
    }

    #[test]
    fn sift_preserves_functions() {
        // pseudo-random functions over 8 vars (4 groups), checked against
        // brute-force evaluation across repeated reorderings
        let mut m = Mgr::new();
        let vars: Vec<u32> = (0..8).collect();
        for v in &vars {
            m.var(*v);
        }
        let mut fns: Vec<(NodeId, Vec<(u32, u32, u32)>)> = Vec::new();
        let mut seed = 0x9e3779b9u64;
        let mut rnd = move || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (seed >> 33) as u32
        };
        for _ in 0..25 {
            // random 3-term formula: (va op vb) op2 vc
            let (a, b, c) = (rnd() % 8, rnd() % 8, rnd() % 8);
            let (op1, op2) = (rnd() % 3, rnd() % 3);
            let x = m.var(a);
            let y = m.var(b);
            let z = m.var(c);
            let t1 = match op1 {
                0 => m.and(x, y),
                1 => m.or(x, y),
                _ => m.xor(x, y),
            };
            let t2 = match op2 {
                0 => m.and(t1, z),
                1 => m.or(t1, z),
                _ => m.xor(t1, z),
            };
            fns.push((t2, vec![(a, b, c), (op1, op2, 0)]));
        }
        // truth tables before
        let table = |m: &Mgr, f: NodeId| -> Vec<bool> {
            (0..256u32)
                .map(|bits| eval(m, f, &|v| bits >> v & 1 == 1))
                .collect()
        };
        let before: Vec<Vec<bool>> = fns.iter().map(|(f, _)| table(&m, *f)).collect();
        for round in 0..3 {
            let roots: Vec<NodeId> = fns.iter().map(|(f, _)| *f).collect();
            m.reorder_now(&roots);
            for (i, (f, _)) in fns.iter().enumerate() {
                assert_eq!(before[i], table(&m, *f), "function {} changed after reorder round {}", i, round);
            }
            // interleave more operations
            let extra = {
                let a = m.var(round as u32 % 8);
                let (f0, _) = fns[round as usize % fns.len()];
                m.and(a, f0)
            };
            let _ = extra;
        }
        // shift still valid after reordering
        let a = m.var(0);
        let b = m.var(2);
        let ab = m.and(a, b);
        let sh = m.shift(ab, 1);
        let back = m.shift(sh, -1);
        assert!(m.same(ab, back));
    }
}
