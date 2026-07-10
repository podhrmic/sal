//! Elaboration of module expressions into flat transition systems.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use sal_core::env::{Entry, Instance};
use sal_core::error::SalError;
use sal_syntax::ast::*;
use sal_syntax::span::Span;

use crate::ctype::CType;
use crate::eval::{FResult, Flattener};
use crate::fexpr::{FExpr, LeafId, LeafInfo, LeafType};
use crate::formula::TFormula;
use crate::sval::{prime, EvalCtx, SVal};
use crate::value::Value;

/// One guarded command in the flat system.
#[derive(Debug, Clone)]
pub struct FlatCmd {
    pub label: Option<String>,
    /// Human-readable provenance for trace printing.
    pub provenance: String,
    pub guard: FExpr,
    /// Assignment conjunction (including frame conditions for
    /// transitions).
    pub constraint: FExpr,
}

/// Transition structure preserving composition shape.
#[derive(Debug, Clone)]
pub enum TransNode {
    /// True (module with no transition section).
    True,
    /// Choice among guarded commands of one `[ ... ]` block (ELSE guard
    /// already expanded).
    Cmds(Vec<FlatCmd>),
    /// Conjunction (synchronous composition / multiple blocks).
    All(Vec<TransNode>),
    /// Asynchronous choice; each branch paired with its frame condition
    /// (variables of the other branches held constant).
    Interleave(Vec<(TransNode, FExpr)>),
}

#[derive(Debug, Clone)]
pub struct TopVar {
    pub name: String,
    pub class: VarClass,
    pub ctype: CType,
    pub skel: SVal,
}

pub struct FlatModule {
    pub leaves: Vec<LeafInfo>,
    pub vars: Vec<TopVar>,
    /// DEFINITION constraints + subtype constraints (current state form);
    /// hold in every state.
    pub invariants: Vec<FExpr>,
    /// Initialization definitions (conjoined).
    pub init_defs: Vec<FExpr>,
    /// Initialization choice blocks (each block: choose one command).
    pub init_choices: Vec<Vec<FlatCmd>>,
    /// Transition definitions (conjoined to every step).
    pub trans_defs: Vec<FExpr>,
    pub trans: TransNode,
    /// Leaves controlled by the module (local/output/global).
    pub controlled: BTreeSet<LeafId>,
}

#[derive(Clone)]
struct VarEntry {
    class: VarClass,
    ctype: CType,
    skel: SVal,
}

#[derive(Default)]
struct Elab {
    vars: Vec<(String, VarEntry)>,
    invariants: Vec<FExpr>,
    init_defs: Vec<FExpr>,
    init_choices: Vec<Vec<FlatCmd>>,
    trans_defs: Vec<FExpr>,
    trans: TransNode,
    controlled: BTreeSet<LeafId>,
    /// Next-state leaves constrained by definitions (excluded from frames).
    def_next: BTreeSet<LeafId>,
}

impl Default for TransNode {
    fn default() -> Self {
        TransNode::True
    }
}

type Ambient = HashMap<String, VarEntry>;

impl<'e> Flattener<'e> {
    // ------------------------------------------------------------------
    // Public entry points
    // ------------------------------------------------------------------

    /// Flatten `module |- formula` for the named assertion.
    pub fn flatten_assertion(
        &self,
        inst: &Rc<Instance>,
        assertion: &str,
    ) -> FResult<(FlatModule, TFormula)> {
        self.checker.check_instance(inst)?;
        let entry = inst.symbols.borrow().get(assertion).cloned();
        let Some(Entry::Assertion { body, .. }) = entry else {
            return Err(SalError::global(format!(
                "Assertion \"{}\" was not found in context \"{}\".",
                assertion, inst.name
            )));
        };
        let AssertionExpr::Models { module, formula } = &body else {
            return Err(SalError::global(
                "IMPLEMENTS assertions are not supported.".to_string(),
            ));
        };
        let ctx = EvalCtx::new(inst.clone());
        let flat = self.flatten_module(&ctx, module)?;
        let fctx = self.state_ctx(&ctx, &flat);
        let v = self.eval(&fctx, formula)?;
        let f = self.to_formula(&fctx, v, formula.span)?;
        Ok((flat, f))
    }

    /// Lower another assertion's formula against an existing flat module
    /// (used for `-l` lemmas: the lemma must range over the same state
    /// variables).
    pub fn lower_assertion_in(
        &self,
        inst: &Rc<Instance>,
        assertion: &str,
        flat: &FlatModule,
    ) -> FResult<TFormula> {
        let entry = inst.symbols.borrow().get(assertion).cloned();
        let Some(Entry::Assertion { body, .. }) = entry else {
            return Err(SalError::global(format!(
                "Assertion \"{}\" was not found in context \"{}\".",
                assertion, inst.name
            )));
        };
        let AssertionExpr::Models { formula, .. } = &body else {
            return Err(SalError::global(
                "IMPLEMENTS assertions are not supported.".to_string(),
            ));
        };
        let ctx = EvalCtx::new(inst.clone());
        let fctx = self.state_ctx(&ctx, flat);
        let v = self.eval(&fctx, formula)?;
        self.to_formula(&fctx, v, formula.span)
    }

    /// Flatten a module expression (used by the deadlock checker &c).
    pub fn flatten_module(&self, ctx: &EvalCtx, m: &Module) -> FResult<FlatModule> {
        self.checker.check_instance(&ctx.inst)?;
        let mut ambient = Ambient::new();
        let e = self.elab(ctx, m, &mut ambient, "")?;
        Ok(FlatModule {
            leaves: self.leaves.borrow().clone(),
            vars: e
                .vars
                .iter()
                .map(|(n, v)| TopVar {
                    name: n.clone(),
                    class: v.class,
                    ctype: v.ctype.clone(),
                    skel: v.skel.clone(),
                })
                .collect(),
            invariants: e.invariants,
            init_defs: e.init_defs,
            init_choices: e.init_choices,
            trans_defs: e.trans_defs,
            trans: e.trans,
            controlled: e.controlled,
        })
    }

    /// Evaluation context with the module's state variables in scope
    /// (both current `x` and primed `x'`).
    pub fn state_ctx(&self, ctx: &EvalCtx, flat: &FlatModule) -> EvalCtx {
        let mut m = HashMap::new();
        for v in &flat.vars {
            m.insert(v.name.clone(), v.skel.clone());
            m.insert(format!("{}'", v.name), v.skel.map_leaves(&prime));
        }
        ctx.bind(m)
    }

    // ------------------------------------------------------------------
    // Skeleton allocation
    // ------------------------------------------------------------------

    fn alloc_skel(
        &self,
        ctx: &EvalCtx,
        path: &str,
        cty: &CType,
        class: VarClass,
        span: Span,
    ) -> FResult<SVal> {
        match cty {
            CType::Bool
            | CType::Range(..)
            | CType::Int { .. }
            | CType::Real
            | CType::Scalar(..) => {
                let lt = LeafType::from_ctype(cty).unwrap();
                let mut leaves = self.leaves.borrow_mut();
                let id = leaves.len() as LeafId;
                leaves.push(LeafInfo {
                    name: path.to_string(),
                    ty: lt.clone(),
                    class,
                });
                Ok(SVal::Sym(FExpr::Var(id, false), lt))
            }
            CType::Tuple(ts) => {
                let mut vs = Vec::new();
                for (i, t) in ts.iter().enumerate() {
                    vs.push(self.alloc_skel(
                        ctx,
                        &format!("{}.{}", path, i + 1),
                        t,
                        class,
                        span,
                    )?);
                }
                Ok(SVal::Tuple(vs))
            }
            CType::Record(fs) => {
                let mut vs = Vec::new();
                for (n, t) in fs {
                    vs.push((
                        n.clone(),
                        self.alloc_skel(ctx, &format!("{}.{}", path, n), t, class, span)?,
                    ));
                }
                Ok(SVal::Record(vs))
            }
            CType::Array(it, et) | CType::Fun(it, et) => {
                let vals = it.enumerate().ok_or_else(|| {
                    self.err(
                        ctx,
                        span,
                        format!(
                            "Finite type expected as the index of state variable \"{}\".",
                            path
                        ),
                    )
                })?;
                let mut vs = Vec::new();
                for v in &vals {
                    vs.push(self.alloc_skel(
                        ctx,
                        &format!("{}[{}]", path, self.display_value(v)),
                        et,
                        class,
                        span,
                    )?);
                }
                Ok(SVal::Array(it.clone(), vs))
            }
            CType::Data(tid, ctors) => {
                // finite datatype: encode as a pseudo-scalar over its
                // enumeration
                let card = cty.cardinality().ok_or_else(|| {
                    self.err(
                        ctx,
                        span,
                        format!(
                            "Finite type expected for state variable \"{}\" (recursive \
                             datatype).",
                            path
                        ),
                    )
                })?;
                let _ = (ctors, card);
                let vals = cty.enumerate().unwrap();
                let elems: Vec<String> =
                    vals.iter().map(|v| self.display_value(v)).collect();
                let elems_rc = Rc::new(elems);
                let pseudo = LeafType::Scalar(tid.clone(), elems_rc.clone());
                self.datatype_enums
                    .borrow_mut()
                    .entry(tid.clone())
                    .or_insert_with(|| Rc::new(vals.clone()));
                self.scalars
                    .borrow_mut()
                    .entry(tid.clone())
                    .or_insert_with(|| (elems_rc, false));
                let mut leaves = self.leaves.borrow_mut();
                let id = leaves.len() as LeafId;
                leaves.push(LeafInfo {
                    name: path.to_string(),
                    ty: pseudo.clone(),
                    class,
                });
                Ok(SVal::Sym(FExpr::Var(id, false), pseudo))
            }
            CType::Uninterp(tid) => Err(self.err(
                ctx,
                span,
                format!(
                    "Finite type expected for state variable \"{}\" (uninterpreted type {}).",
                    path, tid
                ),
            )),
        }
    }

    pub fn display_value(&self, v: &Value) -> String {
        match v {
            Value::Scalar(tid, i) => {
                let scalars = self.scalars.borrow();
                match scalars.get(tid) {
                    Some((elems, _)) if *i < elems.len() => elems[*i].clone(),
                    _ => format!("{}#{}", tid.name, i),
                }
            }
            Value::Tuple(vs) => {
                let parts: Vec<String> = vs.iter().map(|x| self.display_value(x)).collect();
                format!("({})", parts.join(", "))
            }
            Value::Record(fs) => {
                let parts: Vec<String> = fs
                    .iter()
                    .map(|(n, x)| format!("{} := {}", n, self.display_value(x)))
                    .collect();
                format!("(# {} #)", parts.join(", "))
            }
            Value::Array(vs) => {
                let parts: Vec<String> = vs.iter().map(|x| self.display_value(x)).collect();
                format!("[{}]", parts.join(", "))
            }
            Value::Data(_, c, args) => {
                if args.is_empty() {
                    c.clone()
                } else {
                    let parts: Vec<String> =
                        args.iter().map(|x| self.display_value(x)).collect();
                    format!("{}({})", c, parts.join(", "))
                }
            }
            other => format!("{}", other),
        }
    }

    /// Rewrite the display names of all leaves in a skeleton to live under
    /// a new path prefix (used when locals are tupled/arrayed by
    /// composition).
    fn rename_leaves(&self, skel: &SVal, new_path: &str) {
        self.rename_leaves_rec(skel, new_path);
    }

    fn rename_leaves_rec(&self, skel: &SVal, path: &str) {
        match skel {
            SVal::Sym(FExpr::Var(id, _), _) => {
                self.leaves.borrow_mut()[*id as usize].name = path.to_string();
            }
            SVal::Tuple(vs) => {
                for (i, v) in vs.iter().enumerate() {
                    self.rename_leaves_rec(v, &format!("{}.{}", path, i + 1));
                }
            }
            SVal::Record(vs) => {
                for (n, v) in vs {
                    self.rename_leaves_rec(v, &format!("{}.{}", path, n));
                }
            }
            SVal::Array(it, vs) => {
                if let Some(vals) = it.enumerate() {
                    for (v, val) in vs.iter().zip(vals) {
                        self.rename_leaves_rec(
                            v,
                            &format!("{}[{}]", path, self.display_value(&val)),
                        );
                    }
                }
            }
            _ => {}
        }
    }

    fn skel_leaves(skel: &SVal, out: &mut BTreeSet<LeafId>) {
        match skel {
            SVal::Sym(e, _) => {
                let mut cur = BTreeSet::new();
                let mut next = BTreeSet::new();
                e.leaves(&mut cur, &mut next);
                out.extend(cur);
                out.extend(next);
            }
            SVal::Tuple(vs) | SVal::Array(_, vs) => {
                for v in vs {
                    Self::skel_leaves(v, out);
                }
            }
            SVal::Record(vs) => {
                for (_, v) in vs {
                    Self::skel_leaves(v, out);
                }
            }
            _ => {}
        }
    }

    // ------------------------------------------------------------------
    // Module elaboration
    // ------------------------------------------------------------------

    fn elab(
        &self,
        ctx: &EvalCtx,
        m: &Module,
        ambient: &mut Ambient,
        prov: &str,
    ) -> FResult<Elab> {
        match &m.kind {
            ModuleKind::Base(b) => self.elab_base(ctx, b, ambient, prov),
            ModuleKind::Instance(name, actuals) => {
                let (def_inst, entry) = {
                    let mut scope = sal_core::wfc::Scope::default();
                    self.checker
                        .lookup_entry_pub(&ctx.inst, name, &mut scope)
                        .map_err(|e| e)?
                };
                let Entry::Module {
                    def, param_decls, ..
                } = entry
                else {
                    return Err(self.err(
                        ctx,
                        m.span,
                        format!("\"{}\" is not a module.", name.id.name),
                    ));
                };
                let mut bindings = HashMap::new();
                let mut ai = actuals.iter();
                for pd in &param_decls {
                    for n in &pd.names {
                        let a = ai.next().ok_or_else(|| {
                            self.err(ctx, m.span, "Wrong number of module actuals.")
                        })?;
                        bindings.insert(n.name.clone(), self.eval(ctx, a)?);
                    }
                }
                if ai.next().is_some() {
                    return Err(self.err(ctx, m.span, "Wrong number of module actuals."));
                }
                let child_ctx = ctx.with_inst(def_inst.clone()).bind(bindings);
                let prov2 = format!(
                    "{}(module instance at [Context: {}, {}]) ",
                    prov, ctx.inst.name, m.span
                );
                self.elab(&child_ctx, &def, ambient, &prov2)
            }
            ModuleKind::Sync(a, b) | ModuleKind::Async(a, b) => {
                let sync = matches!(m.kind, ModuleKind::Sync(..));
                let ea = self.elab(ctx, a, ambient, prov)?;
                // share non-local interface vars with the sibling
                let mut amb2 = ambient.clone();
                for (n, v) in &ea.vars {
                    if v.class != VarClass::Local {
                        amb2.insert(n.clone(), v.clone());
                    }
                }
                let eb = self.elab(ctx, b, &mut amb2, prov)?;
                // propagate newly-allocated shared vars back
                for (n, v) in &eb.vars {
                    if v.class != VarClass::Local && !ambient.contains_key(n) {
                        ambient.insert(n.clone(), v.clone());
                    }
                }
                for (n, v) in &ea.vars {
                    if v.class != VarClass::Local && !ambient.contains_key(n) {
                        ambient.insert(n.clone(), v.clone());
                    }
                }
                self.merge_binary(ctx, ea, eb, sync)
            }
            ModuleKind::MultiSync(d, sub) | ModuleKind::MultiAsync(d, sub) => {
                let sync = matches!(m.kind, ModuleKind::MultiSync(..));
                let it = self.resolve_ctype(ctx, &d.ty)?;
                let vals = it.enumerate().ok_or_else(|| {
                    self.err(ctx, m.span, "Finite type expected in multi-composition.")
                })?;
                let mut elabs = Vec::new();
                for v in &vals {
                    let c2 = ctx.bind1(&d.names[0].name, SVal::Ground(v.clone()));
                    let e = self.elab(&c2, sub, ambient, prov)?;
                    // share non-local vars across the instances
                    for (n, ve) in &e.vars {
                        if ve.class != VarClass::Local && !ambient.contains_key(n) {
                            ambient.insert(n.clone(), ve.clone());
                        }
                    }
                    elabs.push(e);
                }
                self.merge_multi(ctx, elabs, &it, &vals, sync)
            }
            ModuleKind::Hide(ids, sub) => {
                let mut e = self.elab(ctx, sub, ambient, prov)?;
                for id in ids {
                    if let Some((_, v)) = e.vars.iter_mut().find(|(n, _)| n == &id.name) {
                        v.class = VarClass::Local;
                    }
                }
                Ok(e)
            }
            ModuleKind::NewOutput(ids, sub) => {
                let mut e = self.elab(ctx, sub, ambient, prov)?;
                for id in ids {
                    if let Some((_, v)) = e.vars.iter_mut().find(|(n, _)| n == &id.name) {
                        v.class = VarClass::Output;
                    }
                }
                Ok(e)
            }
            ModuleKind::Rename(renames, sub) => {
                let mut amb2 = ambient.clone();
                let mut fresh: Vec<(String, String)> = Vec::new();
                for (from, to) in renames {
                    if let Some(target) = ambient.get(&to.base.name).cloned() {
                        let skel =
                            self.slice_skel(ctx, &target, &to.accesses, to.span)?;
                        let cty = self.slice_ctype(ctx, &target.ctype, &to.accesses, to.span)?;
                        amb2.insert(
                            from.base.name.clone(),
                            VarEntry {
                                class: target.class,
                                ctype: cty,
                                skel,
                            },
                        );
                    } else if to.accesses.is_empty() {
                        fresh.push((from.base.name.clone(), to.base.name.clone()));
                    } else {
                        return Err(self.err(
                            ctx,
                            to.span,
                            format!("Undeclared state variable \"{}\".", to.base.name),
                        ));
                    }
                }
                // fresh renames: expose the child's var under a new name;
                // pre-bind by renaming in the ambient used by the child
                let mut e = self.elab(ctx, sub, &mut amb2, prov)?;
                let mut renamed = Vec::new();
                for (n, v) in e.vars.drain(..) {
                    if let Some((from, to)) = renames
                        .iter()
                        .map(|(f, t)| (f.base.name.clone(), t))
                        .find(|(f, _)| *f == n)
                    {
                        let _ = from;
                        if to.accesses.is_empty() {
                            if ambient.contains_key(&to.base.name) {
                                // dissolves into an existing ambient var
                                continue;
                            }
                            self.rename_leaves(&v.skel, &to.base.name);
                            renamed.push((to.base.name.clone(), v));
                        }
                        // else: dissolved into an ambient var's component
                    } else {
                        renamed.push((n, v));
                    }
                }
                let _ = fresh;
                e.vars = renamed;
                Ok(e)
            }
            ModuleKind::With(decls, sub) => {
                let mut e_vars: Vec<(String, VarEntry)> = Vec::new();
                for nd in decls {
                    for d in &nd.decls {
                        let cty = self.resolve_ctype(ctx, &d.ty)?;
                        for n in &d.names {
                            let entry = if let Some(v) = ambient.get(&n.name) {
                                v.clone()
                            } else {
                                let skel = self.alloc_skel(
                                    ctx,
                                    &n.name,
                                    &cty,
                                    nd.class,
                                    d.span,
                                )?;
                                VarEntry {
                                    class: nd.class,
                                    ctype: cty.clone(),
                                    skel,
                                }
                            };
                            ambient.insert(n.name.clone(), entry.clone());
                            e_vars.push((n.name.clone(), entry));
                        }
                    }
                }
                let mut e = self.elab(ctx, sub, ambient, prov)?;
                // WITH vars are part of the interface
                for (n, v) in e_vars.into_iter().rev() {
                    if !e.vars.iter().any(|(n2, _)| n2 == &n) {
                        e.vars.insert(0, (n.clone(), v.clone()));
                    }
                    // controlled if not input
                    if v.class != VarClass::Input {
                        let mut ls = BTreeSet::new();
                        Self::skel_leaves(&v.skel, &mut ls);
                        e.controlled.extend(ls);
                    }
                }
                Ok(e)
            }
            ModuleKind::Observe(a, b) => {
                // OBSERVE m WITH monitor: synchronous composition where the
                // monitor cannot constrain m
                let ea = self.elab(ctx, a, ambient, prov)?;
                let mut amb2 = ambient.clone();
                for (n, v) in &ea.vars {
                    if v.class != VarClass::Local {
                        amb2.insert(n.clone(), v.clone());
                    }
                }
                let eb = self.elab(ctx, b, &mut amb2, prov)?;
                self.merge_binary(ctx, ea, eb, true)
            }
        }
    }

    fn slice_skel(
        &self,
        ctx: &EvalCtx,
        target: &VarEntry,
        accesses: &[Access],
        span: Span,
    ) -> FResult<SVal> {
        let mut cur = target.skel.clone();
        for a in accesses {
            cur = match a {
                Access::Array(ie) => {
                    let iv = self.eval(ctx, ie)?;
                    match cur {
                        SVal::Array(it, elems) => {
                            self.select_indexed(ctx, &it, &elems, &iv, span)?
                        }
                        other => {
                            return Err(self.err(
                                ctx,
                                span,
                                format!("Invalid rename target access on {:?}.", other),
                            ))
                        }
                    }
                }
                Access::Record(f) => match cur {
                    SVal::Record(fs) => fs
                        .iter()
                        .find(|(n, _)| n == &f.name)
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| {
                            self.err(ctx, span, format!("Unknown field \"{}\".", f.name))
                        })?,
                    other => {
                        return Err(self.err(
                            ctx,
                            span,
                            format!("Invalid rename target access on {:?}.", other),
                        ))
                    }
                },
                Access::Tuple(i) => match cur {
                    SVal::Tuple(vs) => vs
                        .get(*i as usize - 1)
                        .cloned()
                        .ok_or_else(|| self.err(ctx, span, "Tuple index out of bounds."))?,
                    other => {
                        return Err(self.err(
                            ctx,
                            span,
                            format!("Invalid rename target access on {:?}.", other),
                        ))
                    }
                },
                Access::Args(_) => {
                    return Err(self.err(ctx, span, "Invalid rename target access."))
                }
            };
        }
        Ok(cur)
    }

    fn slice_ctype(
        &self,
        ctx: &EvalCtx,
        cty: &CType,
        accesses: &[Access],
        span: Span,
    ) -> FResult<CType> {
        let mut cur = cty.clone();
        for a in accesses {
            cur = match (a, cur) {
                (Access::Array(_), CType::Array(_, e)) | (Access::Array(_), CType::Fun(_, e)) => {
                    *e
                }
                (Access::Record(f), CType::Record(fs)) => fs
                    .iter()
                    .find(|(n, _)| n == &f.name)
                    .map(|(_, t)| t.clone())
                    .ok_or_else(|| {
                        self.err(ctx, span, format!("Unknown field \"{}\".", f.name))
                    })?,
                (Access::Tuple(i), CType::Tuple(ts)) => ts
                    .get(*i as usize - 1)
                    .cloned()
                    .ok_or_else(|| self.err(ctx, span, "Tuple index out of bounds."))?,
                (_, other) => {
                    return Err(self.err(
                        ctx,
                        span,
                        format!("Invalid rename target access on {:?}.", other),
                    ))
                }
            };
        }
        Ok(cur)
    }

    fn merge_binary(&self, ctx: &EvalCtx, ea: Elab, eb: Elab, sync: bool) -> FResult<Elab> {
        let mut vars: Vec<(String, VarEntry)> = Vec::new();
        let mut b_vars: Vec<(String, VarEntry)> = eb.vars;
        for (n, va) in ea.vars {
            if let Some(pos) = b_vars.iter().position(|(n2, _)| n2 == &n) {
                let (_, vb) = b_vars.remove(pos);
                if va.class == VarClass::Local && vb.class == VarClass::Local {
                    // pair locals into a tuple
                    self.rename_leaves(&va.skel, &format!("{}.1", n));
                    self.rename_leaves(&vb.skel, &format!("{}.2", n));
                    vars.push((
                        n,
                        VarEntry {
                            class: VarClass::Local,
                            ctype: CType::Tuple(vec![va.ctype.clone(), vb.ctype.clone()]),
                            skel: SVal::Tuple(vec![va.skel.clone(), vb.skel.clone()]),
                        },
                    ));
                } else {
                    // shared: same skeleton (b was elaborated with a's
                    // skeleton in ambient); merge class
                    let mut v = va;
                    if vb.class == VarClass::Output {
                        v.class = VarClass::Output;
                    } else if v.class == VarClass::Input && vb.class == VarClass::Global {
                        v.class = VarClass::Global;
                    }
                    vars.push((n, v));
                }
            } else {
                vars.push((n, va));
            }
        }
        vars.extend(b_vars);

        let controlled: BTreeSet<LeafId> =
            ea.controlled.union(&eb.controlled).cloned().collect();
        let def_next: BTreeSet<LeafId> = ea.def_next.union(&eb.def_next).cloned().collect();

        let trans = if sync {
            TransNode::All(vec![ea.trans, eb.trans])
        } else {
            // interleaving with frames
            let frame_b = self.frame_expr(&eb.controlled, &ea.controlled, &def_next);
            let frame_a = self.frame_expr(&ea.controlled, &eb.controlled, &def_next);
            TransNode::Interleave(vec![(ea.trans, frame_b), (eb.trans, frame_a)])
        };

        let mut invariants = ea.invariants;
        invariants.extend(eb.invariants);
        let mut init_defs = ea.init_defs;
        init_defs.extend(eb.init_defs);
        let mut init_choices = ea.init_choices;
        init_choices.extend(eb.init_choices);
        let mut trans_defs = ea.trans_defs;
        trans_defs.extend(eb.trans_defs);

        Ok(Elab {
            vars,
            invariants,
            init_defs,
            init_choices,
            trans_defs,
            trans,
            controlled,
            def_next,
        })
    }

    /// Frame: `x' = x` for `framed − stepping − defined` leaves.
    fn frame_expr(
        &self,
        framed: &BTreeSet<LeafId>,
        stepping: &BTreeSet<LeafId>,
        def_next: &BTreeSet<LeafId>,
    ) -> FExpr {
        let mut cs = Vec::new();
        for &l in framed {
            if stepping.contains(&l) || def_next.contains(&l) {
                continue;
            }
            cs.push(FExpr::eq(FExpr::Var(l, true), FExpr::Var(l, false)));
        }
        FExpr::and(cs)
    }

    fn merge_multi(
        &self,
        _ctx: &EvalCtx,
        elabs: Vec<Elab>,
        index_ty: &CType,
        vals: &[Value],
        sync: bool,
    ) -> FResult<Elab> {
        // locals across instances turn into arrays
        let mut vars: Vec<(String, VarEntry)> = Vec::new();
        let mut locals: HashMap<String, Vec<VarEntry>> = HashMap::new();
        let mut local_order: Vec<String> = Vec::new();
        for e in &elabs {
            for (n, v) in &e.vars {
                if v.class == VarClass::Local {
                    if !locals.contains_key(n) {
                        local_order.push(n.clone());
                    }
                    locals.entry(n.clone()).or_default().push(v.clone());
                } else if !vars.iter().any(|(n2, _)| n2 == n) {
                    vars.push((n.clone(), v.clone()));
                }
            }
        }
        for n in local_order {
            let entries = locals.remove(&n).unwrap();
            if entries.len() != vals.len() {
                // a local missing from some instance — keep the first
                vars.push((n.clone(), entries[0].clone()));
                continue;
            }
            for (ve, val) in entries.iter().zip(vals) {
                self.rename_leaves(&ve.skel, &format!("{}[{}]", n, self.display_value(val)));
            }
            vars.push((
                n.clone(),
                VarEntry {
                    class: VarClass::Local,
                    ctype: CType::Array(
                        Box::new(index_ty.clone()),
                        Box::new(entries[0].ctype.clone()),
                    ),
                    skel: SVal::Array(
                        Box::new(index_ty.clone()),
                        entries.iter().map(|e| e.skel.clone()).collect(),
                    ),
                },
            ));
        }

        let controlled: BTreeSet<LeafId> = elabs
            .iter()
            .flat_map(|e| e.controlled.iter().cloned())
            .collect();
        let def_next: BTreeSet<LeafId> = elabs
            .iter()
            .flat_map(|e| e.def_next.iter().cloned())
            .collect();

        let trans = if sync {
            TransNode::All(elabs.iter().map(|e| e.trans.clone()).collect())
        } else {
            let mut branches = Vec::new();
            for (i, e) in elabs.iter().enumerate() {
                // frame: all controlled leaves of other instances
                let mut others = BTreeSet::new();
                for (j, e2) in elabs.iter().enumerate() {
                    if j != i {
                        others.extend(e2.controlled.iter().cloned());
                    }
                }
                let frame = self.frame_expr(&others, &e.controlled, &def_next);
                branches.push((e.trans.clone(), frame));
            }
            TransNode::Interleave(branches)
        };

        let mut invariants = Vec::new();
        let mut init_defs = Vec::new();
        let mut init_choices = Vec::new();
        let mut trans_defs = Vec::new();
        for e in elabs {
            invariants.extend(e.invariants);
            init_defs.extend(e.init_defs);
            init_choices.extend(e.init_choices);
            trans_defs.extend(e.trans_defs);
        }

        Ok(Elab {
            vars,
            invariants,
            init_defs,
            init_choices,
            trans_defs,
            trans,
            controlled,
            def_next,
        })
    }

    // ------------------------------------------------------------------
    // Base modules
    // ------------------------------------------------------------------

    fn elab_base(
        &self,
        ctx: &EvalCtx,
        b: &BaseModule,
        ambient: &mut Ambient,
        prov: &str,
    ) -> FResult<Elab> {
        let mut e = Elab::default();
        // 1. variables
        for d in &b.decls {
            if let BaseDecl::Vars(class, decls) = d {
                for vd in decls {
                    let cty = self.resolve_ctype(ctx, &vd.ty)?;
                    for n in &vd.names {
                        if e.vars.iter().any(|(n2, _)| n2 == &n.name) {
                            continue;
                        }
                        let entry = if let Some(v) = ambient.get(&n.name) {
                            let mut v = v.clone();
                            v.class = *class;
                            v
                        } else {
                            let skel =
                                self.alloc_skel(ctx, &n.name, &cty, *class, vd.span)?;
                            VarEntry {
                                class: *class,
                                ctype: cty.clone(),
                                skel,
                            }
                        };
                        if *class != VarClass::Input {
                            let mut ls = BTreeSet::new();
                            Self::skel_leaves(&entry.skel, &mut ls);
                            e.controlled.extend(ls);
                        }
                        e.vars.push((n.name.clone(), entry));
                    }
                }
            }
        }
        // subtype constraints on state variables become invariants
        for d in &b.decls {
            if let BaseDecl::Vars(_, decls) = d {
                for vd in decls {
                    for n in &vd.names {
                        let skel = e
                            .vars
                            .iter()
                            .find(|(n2, _)| n2 == &n.name)
                            .map(|(_, v)| v.skel.clone())
                            .unwrap();
                        if let Some(c) =
                            self.subtype_constraint(ctx, &vd.ty, &skel, vd.span)?
                        {
                            e.invariants.push(c);
                        }
                    }
                }
            }
        }

        // state-variable scope for expression evaluation
        let mut state_map = HashMap::new();
        for (n, v) in &e.vars {
            state_map.insert(n.clone(), v.skel.clone());
            state_map.insert(format!("{}'", n), v.skel.map_leaves(&prime));
        }
        let sctx = ctx.bind(state_map);

        // 2. sections
        for d in &b.decls {
            match d {
                BaseDecl::Vars(..) => {}
                BaseDecl::Definition(defs) => {
                    for def in defs {
                        let (c_cur, next_leaves) =
                            self.elab_definition(&sctx, &e, def, false)?;
                        // invariant: hold at every state (cur form); the
                        // primed form is derived by engines
                        e.invariants.push(c_cur);
                        let _ = next_leaves;
                        // leaves defined invariantly are excluded from
                        // frames in their primed form
                        let mut lhs_leaves = BTreeSet::new();
                        self.definition_lhs_leaves(&sctx, &e, def, false, &mut lhs_leaves)?;
                        e.def_next.extend(lhs_leaves);
                    }
                }
                BaseDecl::Initialization(items) => {
                    for it in items {
                        match it {
                            DefOrCommand::Def(def) => {
                                let (c, _) = self.elab_definition(&sctx, &e, def, false)?;
                                e.init_defs.push(c);
                            }
                            DefOrCommand::Commands(cmds, span) => {
                                let block = self.elab_commands(
                                    &sctx, &e, cmds, *span, prov, false,
                                )?;
                                e.init_choices.push(block);
                            }
                        }
                    }
                }
                BaseDecl::Transition(items) => {
                    let mut blocks: Vec<Vec<FlatCmd>> = Vec::new();
                    let mut block_assigned: Vec<BTreeSet<LeafId>> = Vec::new();
                    for it in items {
                        match it {
                            DefOrCommand::Def(def) => {
                                let (c, _) = self.elab_definition(&sctx, &e, def, true)?;
                                e.trans_defs.push(c);
                                let mut lhs_leaves = BTreeSet::new();
                                self.definition_lhs_leaves(
                                    &sctx,
                                    &e,
                                    def,
                                    true,
                                    &mut lhs_leaves,
                                )?;
                                e.def_next.extend(lhs_leaves);
                            }
                            DefOrCommand::Commands(cmds, span) => {
                                let block = self.elab_commands(
                                    &sctx, &e, cmds, *span, prov, true,
                                )?;
                                let mut assigned = BTreeSet::new();
                                for c in &block {
                                    let mut cur = BTreeSet::new();
                                    let mut next = BTreeSet::new();
                                    c.constraint.leaves(&mut cur, &mut next);
                                    assigned.extend(next);
                                }
                                block_assigned.push(assigned);
                                blocks.push(block);
                            }
                        }
                    }
                    // add frame conditions per command
                    let own_controlled: BTreeSet<LeafId> = e.controlled.clone();
                    let n_blocks = blocks.len();
                    let mut nodes = Vec::new();
                    for (bi, block) in blocks.into_iter().enumerate() {
                        let mut other_assigned = BTreeSet::new();
                        for (bj, s) in block_assigned.iter().enumerate() {
                            if bi != bj {
                                other_assigned.extend(s.iter().cloned());
                            }
                        }
                        let mut framed_block = Vec::new();
                        for cmd in block {
                            let mut cur = BTreeSet::new();
                            let mut assigned = BTreeSet::new();
                            cmd.constraint.leaves(&mut cur, &mut assigned);
                            let mut frames = Vec::new();
                            for &l in &own_controlled {
                                if assigned.contains(&l)
                                    || e.def_next.contains(&l)
                                    || other_assigned.contains(&l)
                                {
                                    continue;
                                }
                                frames.push(FExpr::eq(
                                    FExpr::Var(l, true),
                                    FExpr::Var(l, false),
                                ));
                            }
                            framed_block.push(FlatCmd {
                                constraint: FExpr::and(
                                    std::iter::once(cmd.constraint)
                                        .chain(frames)
                                        .collect(),
                                ),
                                ..cmd
                            });
                        }
                        nodes.push(TransNode::Cmds(framed_block));
                    }
                    e.trans = match n_blocks {
                        0 => TransNode::True,
                        1 => nodes.pop().unwrap(),
                        _ => TransNode::All(nodes),
                    };
                }
            }
        }
        Ok(e)
    }

    /// Subtype predicates on state variable types become invariants.
    fn subtype_constraint(
        &self,
        ctx: &EvalCtx,
        t: &Type,
        skel: &SVal,
        span: Span,
    ) -> FResult<Option<FExpr>> {
        match &t.kind {
            TypeKind::Subtype(sp) => {
                let inner =
                    self.subtype_constraint(ctx, &sp.ty, skel, span)?;
                let c2 = ctx.bind1(&sp.var.name, skel.clone());
                let v = self.eval(&c2, &sp.pred)?;
                let c = v
                    .to_bool_fexpr()
                    .map_err(|m| self.err(ctx, span, m))?;
                Ok(Some(match inner {
                    Some(i) => FExpr::and(vec![i, c]),
                    None => c,
                }))
            }
            TypeKind::Name(n) => {
                // look through type aliases
                if n.ctx.is_none() {
                    // prelude names have no extra constraints beyond ctype
                    return Ok(None);
                }
                let _ = n;
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    fn elab_definition(
        &self,
        sctx: &EvalCtx,
        e: &Elab,
        def: &Definition,
        allow_next: bool,
    ) -> FResult<(FExpr, BTreeSet<LeafId>)> {
        match def {
            Definition::Forall(decls, defs) => {
                let mut cs = Vec::new();
                let mut all_next = BTreeSet::new();
                self.expand_bindings(sctx, decls, &mut |c2| {
                    for d in defs {
                        let (c, n) = self.elab_definition(c2, e, d, allow_next)?;
                        cs.push(c);
                        all_next.extend(n);
                    }
                    Ok(())
                })?;
                Ok((FExpr::and(cs), all_next))
            }
            Definition::Simple(s) => {
                match self.eval_lhs(sctx, e, &s.lhs) {
                    Ok(lhs_sv) => {
                        let mut assigned = BTreeSet::new();
                        Self::skel_leaves(&lhs_sv, &mut assigned);
                        match &s.rhs {
                            Rhs::Expr(rhs) => {
                                let rv = self.eval(sctx, rhs)?;
                                let c = self.eq_vals(sctx, &lhs_sv, &rv, s.span)?;
                                Ok((c, assigned))
                            }
                            Rhs::Selection(rhs) => {
                                let rv = self.eval(sctx, rhs)?;
                                let applied =
                                    self.apply(sctx, rv, vec![lhs_sv], s.span)?;
                                let c = applied
                                    .to_bool_fexpr()
                                    .map_err(|m| self.err(sctx, s.span, m))?;
                                Ok((c, assigned))
                            }
                        }
                    }
                    Err(_) => self.elab_symbolic_lhs(sctx, e, s, allow_next),
                }
            }
        }
    }

    /// Assignment whose LHS has a state-dependent index:
    /// `x'[i] = e` (with `i` symbolic) means `x' = x WITH [i] := e`
    /// (unspecified components unchanged) in transition position, and a
    /// component-only constraint `x[i] = e` in initialization position.
    fn elab_symbolic_lhs(
        &self,
        sctx: &EvalCtx,
        e: &Elab,
        s: &SimpleDefinition,
        allow_next: bool,
    ) -> FResult<(FExpr, BTreeSet<LeafId>)> {
        let base_cur = sctx.lookup(&s.lhs.base.name).ok_or_else(|| {
            self.err(
                sctx,
                s.lhs.span,
                format!("Undeclared state variable \"{}\".", s.lhs.base.name),
            )
        })?;
        let _ = e;
        let rv = match &s.rhs {
            Rhs::Expr(rhs) => self.eval(sctx, rhs)?,
            Rhs::Selection(_) => {
                return Err(self.err(
                    sctx,
                    s.span,
                    "IN selection with a state-dependent index is not supported.",
                ))
            }
        };
        if s.lhs.next && allow_next {
            // full-variable update semantics
            let primed = sctx
                .lookup(&format!("{}'", s.lhs.base.name))
                .ok_or_else(|| {
                    self.err(
                        sctx,
                        s.lhs.span,
                        format!("Undeclared state variable \"{}\".", s.lhs.base.name),
                    )
                })?;
            let updated = self.update_pub(sctx, base_cur, &s.lhs.accesses, rv, s.span)?;
            let c = self.eq_vals(sctx, &primed, &updated, s.span)?;
            let mut assigned = BTreeSet::new();
            Self::skel_leaves(&primed, &mut assigned);
            Ok((c, assigned))
        } else {
            // component-only constraint via symbolic selection
            let base = if s.lhs.next {
                sctx.lookup(&format!("{}'", s.lhs.base.name)).unwrap()
            } else {
                base_cur
            };
            let mut cur = base;
            for a in &s.lhs.accesses {
                cur = match a {
                    Access::Array(ie) => {
                        let iv = self.eval(sctx, ie)?;
                        self.select(sctx, cur, iv, s.span)?
                    }
                    Access::Record(f) => match cur {
                        SVal::Record(fs) => fs
                            .iter()
                            .find(|(n, _)| n == &f.name)
                            .map(|(_, v)| v.clone())
                            .ok_or_else(|| {
                                self.err(sctx, f.span, "Unknown record field.")
                            })?,
                        other => {
                            return Err(self.err(
                                sctx,
                                s.span,
                                format!("Invalid record access on {:?}.", other),
                            ))
                        }
                    },
                    Access::Tuple(i) => match cur {
                        SVal::Tuple(vs) => vs
                            .get(*i as usize - 1)
                            .cloned()
                            .ok_or_else(|| {
                                self.err(sctx, s.span, "Tuple index out of bounds.")
                            })?,
                        other => {
                            return Err(self.err(
                                sctx,
                                s.span,
                                format!("Invalid tuple access on {:?}.", other),
                            ))
                        }
                    },
                    Access::Args(_) => {
                        return Err(self.err(sctx, s.span, "Invalid LHS access."))
                    }
                };
            }
            let c = self.eq_vals(sctx, &cur, &rv, s.span)?;
            let mut assigned = BTreeSet::new();
            Self::skel_leaves(&cur, &mut assigned);
            Ok((c, assigned))
        }
    }

    fn definition_lhs_leaves(
        &self,
        sctx: &EvalCtx,
        e: &Elab,
        def: &Definition,
        _allow_next: bool,
        out: &mut BTreeSet<LeafId>,
    ) -> FResult<()> {
        match def {
            Definition::Forall(decls, defs) => {
                self.expand_bindings(sctx, decls, &mut |c2| {
                    for d in defs {
                        self.definition_lhs_leaves(c2, e, d, _allow_next, out)?;
                    }
                    Ok(())
                })?;
                Ok(())
            }
            Definition::Simple(s) => {
                match self.eval_lhs(sctx, e, &s.lhs) {
                    Ok(lhs_sv) => Self::skel_leaves(&lhs_sv, out),
                    Err(_) => {
                        let name = if s.lhs.next {
                            format!("{}'", s.lhs.base.name)
                        } else {
                            s.lhs.base.name.clone()
                        };
                        if let Some(sv) = sctx.lookup(&name) {
                            Self::skel_leaves(&sv, out);
                        }
                    }
                }
                Ok(())
            }
        }
    }

    /// Enumerate all assignments of the (finite) bound variables.
    fn expand_bindings(
        &self,
        ctx: &EvalCtx,
        decls: &[VarDecl],
        f: &mut impl FnMut(&EvalCtx) -> FResult<()>,
    ) -> FResult<()> {
        let mut vars: Vec<(String, Vec<Value>)> = Vec::new();
        for d in decls {
            let ct = self.resolve_ctype(ctx, &d.ty)?;
            let vals = ct.enumerate().ok_or_else(|| {
                self.err(ctx, d.span, "Finite type expected.")
            })?;
            for n in &d.names {
                vars.push((n.name.clone(), vals.clone()));
            }
        }
        let mut assignment = vec![0usize; vars.len()];
        'outer: loop {
            let mut m = HashMap::new();
            for (k, (name, vals)) in vars.iter().enumerate() {
                m.insert(name.clone(), SVal::Ground(vals[assignment[k]].clone()));
            }
            let c2 = ctx.bind(m);
            f(&c2)?;
            for k in (0..vars.len()).rev() {
                assignment[k] += 1;
                if assignment[k] < vars[k].1.len() {
                    continue 'outer;
                }
                assignment[k] = 0;
            }
            break;
        }
        Ok(())
    }

    /// Evaluate an assignment LHS to the skeleton slice it constrains
    /// (primed if `lhs.next`).
    fn eval_lhs(&self, sctx: &EvalCtx, e: &Elab, lhs: &Lhs) -> FResult<SVal> {
        let base_name = if lhs.next {
            format!("{}'", lhs.base.name)
        } else {
            lhs.base.name.clone()
        };
        let mut cur = sctx.lookup(&base_name).ok_or_else(|| {
            self.err(
                sctx,
                lhs.span,
                format!("Undeclared state variable \"{}\".", lhs.base.name),
            )
        })?;
        let _ = e;
        for a in &lhs.accesses {
            cur = match a {
                Access::Array(ie) => {
                    let iv = self.eval(sctx, ie)?;
                    match (cur, &iv) {
                        (SVal::Array(it, elems), SVal::Ground(v)) => {
                            let i = it.index_of(v).ok_or_else(|| {
                                self.err(
                                    sctx,
                                    lhs.span,
                                    format!("Index {} out of bounds.", v),
                                )
                            })?;
                            elems[i].clone()
                        }
                        (other, _) => {
                            return Err(self.err(
                                sctx,
                                lhs.span,
                                format!(
                                    "Assignment index must be a constant (on {:?}).",
                                    other
                                ),
                            ))
                        }
                    }
                }
                Access::Record(f) => match cur {
                    SVal::Record(fs) => fs
                        .iter()
                        .find(|(n, _)| n == &f.name)
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| {
                            self.err(
                                sctx,
                                f.span,
                                format!("Unknown record field \"{}\".", f.name),
                            )
                        })?,
                    other => {
                        return Err(self.err(
                            sctx,
                            lhs.span,
                            format!("Invalid record access on {:?}.", other),
                        ))
                    }
                },
                Access::Tuple(i) => match cur {
                    SVal::Tuple(vs) => vs
                        .get(*i as usize - 1)
                        .cloned()
                        .ok_or_else(|| {
                            self.err(sctx, lhs.span, "Tuple index out of bounds.")
                        })?,
                    other => {
                        return Err(self.err(
                            sctx,
                            lhs.span,
                            format!("Invalid tuple access on {:?}.", other),
                        ))
                    }
                },
                Access::Args(_) => {
                    return Err(self.err(
                        sctx,
                        lhs.span,
                        "Function-application LHS is not supported.",
                    ))
                }
            };
        }
        Ok(cur)
    }

    /// Elaborate a `[ ... ]` command block into flat commands (multi
    /// commands expanded, ELSE guard computed).
    fn elab_commands(
        &self,
        sctx: &EvalCtx,
        e: &Elab,
        cmds: &[SomeCommand],
        span: Span,
        prov: &str,
        is_trans: bool,
    ) -> FResult<Vec<FlatCmd>> {
        let mut flat: Vec<FlatCmd> = Vec::new();
        let mut else_cmds: Vec<(&GuardedCommand, String)> = Vec::new();
        for c in cmds {
            self.expand_command(sctx, e, c, prov, is_trans, &mut flat, &mut else_cmds)?;
        }
        // ELSE guard: negation of all other guards
        if !else_cmds.is_empty() {
            let others: Vec<FExpr> = flat.iter().map(|c| c.guard.clone()).collect();
            let neg = FExpr::not(FExpr::or(others));
            for (g, prov2) in else_cmds {
                let mut constraint = Vec::new();
                for a in &g.assignments {
                    let (c, _) = self.elab_definition(sctx, e, a, is_trans)?;
                    constraint.push(c);
                }
                flat.push(FlatCmd {
                    label: g.label.as_ref().map(|l| l.name.clone()),
                    provenance: prov2,
                    guard: neg.clone(),
                    constraint: FExpr::and(constraint),
                });
            }
        }
        let _ = span;
        Ok(flat)
    }

    fn expand_command<'a>(
        &self,
        sctx: &EvalCtx,
        e: &Elab,
        c: &'a SomeCommand,
        prov: &str,
        is_trans: bool,
        flat: &mut Vec<FlatCmd>,
        else_cmds: &mut Vec<(&'a GuardedCommand, String)>,
    ) -> FResult<()> {
        match c {
            SomeCommand::Multi(decls, inner, _) => {
                self.expand_bindings(sctx, decls, &mut |c2| {
                    // note: nested ELSE is rejected at parse time
                    let mut nested_else = Vec::new();
                    self.expand_command(c2, e, inner, prov, is_trans, flat, &mut nested_else)?;
                    Ok(())
                })
            }
            SomeCommand::Guarded(g) => {
                let prov2 = format!(
                    "{}(label {} transition at [Context: {}, {}])",
                    prov,
                    g.label.as_ref().map(|l| l.name.as_str()).unwrap_or("<unlabeled>"),
                    sctx.inst.name,
                    g.span
                );
                if g.guard.is_none() {
                    else_cmds.push((g, prov2));
                    return Ok(());
                }
                let gv = self.eval(sctx, g.guard.as_ref().unwrap())?;
                let guard = gv
                    .to_bool_fexpr()
                    .map_err(|m| self.err(sctx, g.span, m))?;
                let mut constraint = Vec::new();
                for a in &g.assignments {
                    let (c, _) = self.elab_definition(sctx, e, a, is_trans)?;
                    constraint.push(c);
                }
                flat.push(FlatCmd {
                    label: g.label.as_ref().map(|l| l.name.clone()),
                    provenance: prov2,
                    guard,
                    constraint: FExpr::and(constraint),
                });
                Ok(())
            }
        }
    }
}
