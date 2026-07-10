//! Name resolution and type checking (the `sal-wfc` analysis).
//!
//! Compatibility is checked at the maximal-supertype level (see
//! `types.rs`); subtype predicates and TCCs are not discharged, matching
//! the observable behavior of the oracle's well-formedness checker.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use sal_syntax::ast::*;
use sal_syntax::span::Span;

use crate::env::{instance_key, type_id, Binding, Entry, Instance, SalEnv};
use crate::error::SalError;
use crate::types::SemType;

pub struct Checker<'e> {
    pub env: &'e SalEnv,
    in_progress: RefCell<HashSet<String>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FrameKind {
    Plain,
    /// Module state variables: next-variable (`x'`) lookups only search
    /// these frames.
    State,
}

#[derive(Default)]
pub struct Scope {
    frames: Vec<(FrameKind, HashMap<String, SemType>)>,
}

impl Scope {
    fn push(&mut self, kind: FrameKind) {
        self.frames.push((kind, HashMap::new()));
    }

    fn pop(&mut self) {
        self.frames.pop();
    }

    fn bind(&mut self, name: &str, ty: SemType) {
        self.frames
            .last_mut()
            .expect("scope frame")
            .1
            .insert(name.to_string(), ty);
    }

    fn lookup(&self, name: &str) -> Option<&SemType> {
        self.frames.iter().rev().find_map(|(_, m)| m.get(name))
    }

    fn lookup_state(&self, name: &str) -> Option<&SemType> {
        self.frames
            .iter()
            .rev()
            .filter(|(k, _)| *k == FrameKind::State)
            .find_map(|(_, m)| m.get(name))
    }
}

type CResult<T> = Result<T, SalError>;

impl<'e> Checker<'e> {
    pub fn new(env: &'e SalEnv) -> Self {
        Checker {
            env,
            in_progress: RefCell::new(HashSet::new()),
        }
    }

    fn err(&self, inst: &Instance, span: Span, msg: impl Into<String>) -> SalError {
        SalError::semantic(&inst.name, span, msg)
    }

    // ------------------------------------------------------------------
    // Instances
    // ------------------------------------------------------------------

    /// Check a whole context instance, filling its symbol table.
    pub fn check_instance(&self, inst: &Rc<Instance>) -> CResult<()> {
        if !inst.order.borrow().is_empty() || inst.def.decls.is_empty() {
            return Ok(()); // already checked (or the builtin prelude)
        }
        if !self.in_progress.borrow_mut().insert(inst.key.clone()) {
            return Err(self.err(
                inst,
                inst.def.span,
                format!("Cyclic dependency on context \"{}\".", inst.name),
            ));
        }
        let result = self.check_instance_body(inst);
        self.in_progress.borrow_mut().remove(&inst.key);
        result
    }

    fn check_instance_body(&self, inst: &Rc<Instance>) -> CResult<()> {
        // parameters first
        for p in &inst.def.params {
            match p {
                CtxParam::Types(ids) => {
                    for id in ids {
                        let sem = match inst.bindings.get(&id.name) {
                            Some(Binding::Type(t, _)) => t.clone(),
                            _ => SemType::Uninterp(type_id(inst, &id.name)),
                        };
                        self.insert(
                            inst,
                            &id.name,
                            Entry::Type {
                                sem,
                                scalar_elems: None,
                                datatype: None,
                                def: None,
                            },
                        );
                    }
                }
                CtxParam::Vars(ids, ty) => {
                    let mut scope = Scope::default();
                    let sem = self.resolve_type(inst, ty, &mut scope)?;
                    for id in ids {
                        self.insert(
                            inst,
                            &id.name,
                            Entry::Const {
                                sem: sem.clone(),
                                value: None,
                            },
                        );
                    }
                }
            }
        }
        for d in &inst.def.decls {
            self.check_decl(inst, d)?;
        }
        Ok(())
    }

    fn insert(&self, inst: &Instance, name: &str, e: Entry) {
        inst.symbols.borrow_mut().insert(name.to_string(), e);
        inst.order.borrow_mut().push(name.to_string());
    }

    fn check_decl(&self, inst: &Rc<Instance>, d: &Decl) -> CResult<()> {
        let mut scope = Scope::default();
        match d {
            Decl::Type { name, def } => {
                let tid = type_id(inst, &name.name);
                match def {
                    None => self.insert(
                        inst,
                        &name.name,
                        Entry::Type {
                            sem: SemType::Uninterp(tid),
                            scalar_elems: None,
                            datatype: None,
                            def: None,
                        },
                    ),
                    Some(TypeDef::Type(t)) => {
                        let sem = self.resolve_type(inst, t, &mut scope)?;
                        self.insert(
                            inst,
                            &name.name,
                            Entry::Type {
                                sem,
                                scalar_elems: None,
                                datatype: None,
                                def: Some(TypeDef::Type(t.clone())),
                            },
                        );
                    }
                    Some(TypeDef::Scalar(ids)) => {
                        let sem = SemType::Scalar(tid);
                        self.insert(
                            inst,
                            &name.name,
                            Entry::Type {
                                sem: sem.clone(),
                                scalar_elems: Some(
                                    ids.iter().map(|i| i.name.clone()).collect(),
                                ),
                                datatype: None,
                                def: Some(TypeDef::Scalar(ids.clone())),
                            },
                        );
                        for id in ids {
                            self.insert(
                                inst,
                                &id.name,
                                Entry::Const {
                                    sem: sem.clone(),
                                    value: None,
                                },
                            );
                        }
                    }
                    Some(TypeDef::Datatype(ctors)) => {
                        let sem = SemType::Datatype(tid);
                        // pre-insert for recursive datatypes
                        self.insert(
                            inst,
                            &name.name,
                            Entry::Type {
                                sem: sem.clone(),
                                scalar_elems: None,
                                datatype: None,
                                def: Some(TypeDef::Datatype(ctors.clone())),
                            },
                        );
                        let mut dt_info = Vec::new();
                        for c in ctors {
                            let mut acc_info = Vec::new();
                            let mut args = Vec::new();
                            for a in &c.accessors {
                                let t = self.resolve_type(inst, &a.ty, &mut scope)?;
                                for n in &a.names {
                                    acc_info.push((n.name.clone(), t.clone()));
                                    args.push(t.clone());
                                }
                            }
                            // constructor
                            let cty = if args.is_empty() {
                                sem.clone()
                            } else if args.len() == 1 {
                                SemType::Fun(Box::new(args[0].clone()), Box::new(sem.clone()))
                            } else {
                                SemType::Fun(
                                    Box::new(SemType::Tuple(args.clone())),
                                    Box::new(sem.clone()),
                                )
                            };
                            self.insert(
                                inst,
                                &c.name.name,
                                Entry::Const {
                                    sem: cty,
                                    value: None,
                                },
                            );
                            // recognizer
                            self.insert(
                                inst,
                                &format!("{}?", c.name.name),
                                Entry::Const {
                                    sem: SemType::Fun(
                                        Box::new(sem.clone()),
                                        Box::new(SemType::Bool),
                                    ),
                                    value: None,
                                },
                            );
                            // accessors
                            for (an, at) in &acc_info {
                                self.insert(
                                    inst,
                                    an,
                                    Entry::Const {
                                        sem: SemType::Fun(
                                            Box::new(sem.clone()),
                                            Box::new(at.clone()),
                                        ),
                                        value: None,
                                    },
                                );
                            }
                            dt_info.push((c.name.name.clone(), acc_info));
                        }
                        // update datatype info
                        if let Some(Entry::Type { datatype, .. }) =
                            inst.symbols.borrow_mut().get_mut(&name.name)
                        {
                            *datatype = Some(dt_info);
                        }
                    }
                    Some(TypeDef::Scalarset(e)) | Some(TypeDef::Ringset(e)) => {
                        let ety = self.infer_expr(inst, e, &mut scope)?;
                        self.require(inst, e.span, &ety, &SemType::Number)?;
                        self.insert(
                            inst,
                            &name.name,
                            Entry::Type {
                                sem: SemType::Scalar(tid),
                                scalar_elems: None,
                                datatype: None,
                                def: Some(def.clone().unwrap()),
                            },
                        );
                    }
                }
            }
            Decl::Constant {
                name,
                args,
                ty,
                value,
            } => {
                let rng = self.resolve_type(inst, ty, &mut scope)?;
                let sem = if args.is_empty() {
                    rng.clone()
                } else {
                    let mut dom = Vec::new();
                    for a in args {
                        let t = self.resolve_type(inst, &a.ty, &mut scope)?;
                        for _ in &a.names {
                            dom.push(t.clone());
                        }
                    }
                    let dom = if dom.len() == 1 {
                        dom.pop().unwrap()
                    } else {
                        SemType::Tuple(dom)
                    };
                    SemType::Fun(Box::new(dom), Box::new(rng.clone()))
                };
                // pre-insert to allow recursive definitions; function
                // declarations store their value as an explicit lambda so
                // evaluation binds the parameters
                let stored_value = match value {
                    Some(v) if !args.is_empty() => Some(Expr {
                        span: v.span,
                        parens: 0,
                        kind: ExprKind::Lambda(args.clone(), Box::new(v.clone())),
                    }),
                    other => other.clone(),
                };
                self.insert(
                    inst,
                    &name.name,
                    Entry::Const {
                        sem: sem.clone(),
                        value: stored_value,
                    },
                );
                if let Some(v) = value {
                    scope.push(FrameKind::Plain);
                    for a in args {
                        let t = self.resolve_type(inst, &a.ty, &mut scope)?;
                        for n in &a.names {
                            scope.bind(&n.name, t.clone());
                        }
                    }
                    let vty = self.infer_expr(inst, v, &mut scope)?;
                    scope.pop();
                    self.require(inst, v.span, &vty, &rng)?;
                }
            }
            Decl::Context { name, ctx } => {
                let target = self.resolve_context_name(inst, ctx, &mut scope)?;
                self.insert(inst, &name.name, Entry::Ctx(target));
            }
            Decl::Module { name, params, body } => {
                scope.push(FrameKind::Plain);
                let mut psig = Vec::new();
                for p in params {
                    let t = self.resolve_type(inst, &p.ty, &mut scope)?;
                    for n in &p.names {
                        scope.bind(&n.name, t.clone());
                        psig.push((n.name.clone(), t.clone()));
                    }
                }
                let state = self.check_module(inst, body, &mut scope)?;
                scope.pop();
                self.insert(
                    inst,
                    &name.name,
                    Entry::Module {
                        params: psig,
                        state,
                        def: body.clone(),
                        param_decls: params.clone(),
                    },
                );
            }
            Decl::Assertion { name, form, body } => {
                match body {
                    AssertionExpr::Models { module, formula } => {
                        let state = self.check_module(inst, module, &mut scope)?;
                        scope.push(FrameKind::State);
                        for (n, _, t) in &state {
                            scope.bind(n, t.clone());
                        }
                        let fty = self.infer_expr(inst, formula, &mut scope)?;
                        scope.pop();
                        self.require(inst, formula.span, &fty, &SemType::Bool)?;
                    }
                    AssertionExpr::Implements {
                        concrete,
                        abstract_,
                    } => {
                        self.check_module(inst, concrete, &mut scope)?;
                        self.check_module(inst, abstract_, &mut scope)?;
                    }
                }
                self.insert(
                    inst,
                    &name.name,
                    Entry::Assertion {
                        form: *form,
                        body: body.clone(),
                    },
                );
            }
            Decl::Import { ctx, renames } => {
                let target = self.resolve_context_name(inst, ctx, &mut scope)?;
                let rename_map: HashMap<&str, &str> = renames
                    .iter()
                    .map(|(a, b)| (a.name.as_str(), b.name.as_str()))
                    .collect();
                let entries: Vec<(String, Entry)> = target
                    .symbols
                    .borrow()
                    .iter()
                    .map(|(k, v)| {
                        let name = rename_map.get(k.as_str()).map_or(k.as_str(), |v| v);
                        (name.to_string(), v.clone())
                    })
                    .collect();
                for (k, v) in entries {
                    self.insert(inst, &k, v);
                }
            }
        }
        Ok(())
    }

    // ------------------------------------------------------------------
    // Names & context references
    // ------------------------------------------------------------------

    /// Public wrapper used by the CLI tools to resolve qualified names
    /// like `bakery{5,15}`.
    pub fn resolve_context_name_pub(
        &self,
        inst: &Rc<Instance>,
        cn: &ContextName,
    ) -> CResult<Rc<Instance>> {
        let mut scope = Scope::default();
        self.resolve_context_name(inst, cn, &mut scope)
    }

    fn resolve_context_name(
        &self,
        inst: &Rc<Instance>,
        cn: &ContextName,
        scope: &mut Scope,
    ) -> CResult<Rc<Instance>> {
        // alias?
        if cn.actuals.is_empty() {
            if let Some(Entry::Ctx(target)) = inst.symbols.borrow().get(&cn.name.name) {
                return Ok(target.clone());
            }
        }
        let def = self.env.load_context(&cn.name.name)?;
        // collect formal parameters in order
        let mut formals: Vec<(String, Option<Type>)> = Vec::new();
        for p in &def.params {
            match p {
                CtxParam::Types(ids) => {
                    for id in ids {
                        formals.push((id.name.clone(), None));
                    }
                }
                CtxParam::Vars(ids, ty) => {
                    for id in ids {
                        formals.push((id.name.clone(), Some(ty.clone())));
                    }
                }
            }
        }
        if formals.len() != cn.actuals.len() {
            return Err(self.err(inst, cn.span, "Wrong number of actual parameters."));
        }
        let mut bindings = HashMap::new();
        for ((fname, fty), actual) in formals.iter().zip(&cn.actuals) {
            match (fty, actual) {
                (None, Actual::Type(t)) => {
                    let sem = self.resolve_type(inst, t, scope)?;
                    bindings.insert(
                        fname.clone(),
                        Binding::Type(sem, Some((inst.clone(), t.clone()))),
                    );
                }
                (None, Actual::Expr(e)) => {
                    // a plain name used as a type actual
                    if let ExprKind::Name(n) = &e.kind {
                        let t = Type {
                            kind: TypeKind::Name(n.clone()),
                            span: e.span,
                        };
                        let sem = self.resolve_type(inst, &t, scope)?;
                        bindings.insert(
                            fname.clone(),
                            Binding::Type(sem, Some((inst.clone(), t.clone()))),
                        );
                    } else {
                        return Err(self.err(inst, e.span, "Type expected."));
                    }
                }
                (Some(_), Actual::Expr(e)) => {
                    let ety = self.infer_expr(inst, e, scope)?;
                    bindings.insert(
                        fname.clone(),
                        Binding::Expr(inst.clone(), e.clone(), ety),
                    );
                }
                (Some(_), Actual::Type(t)) => {
                    return Err(self.err(inst, t.span, "Expression expected."));
                }
            }
        }
        // check expr actual types against declared param types *within the
        // target instance* (param types may mention type params)
        let key = instance_key(&def.name.name, &def, &bindings);
        let target = self.env.instance(def, bindings, key);
        self.check_instance(&target)?;
        // now that the target's symbols exist, verify expr actual types
        for ((fname, fty), actual) in formals.iter().zip(&cn.actuals) {
            if fty.is_some() {
                if let Actual::Expr(e) = actual {
                    if let Some(Entry::Const { sem, .. }) =
                        target.symbols.borrow().get(fname)
                    {
                        let ety = self.infer_expr(inst, e, scope)?;
                        self.require(inst, e.span, &ety, sem)?;
                    }
                }
            }
        }
        Ok(target)
    }

    /// Public entry-point for downstream crates (the flattener) that need
    /// the same name-resolution rules.
    pub fn lookup_entry_pub(
        &self,
        inst: &Rc<Instance>,
        name: &Name,
        scope: &mut Scope,
    ) -> CResult<(Rc<Instance>, Entry)> {
        self.lookup_entry(inst, name, scope)
    }

    fn lookup_entry(
        &self,
        inst: &Rc<Instance>,
        name: &Name,
        scope: &mut Scope,
    ) -> CResult<(Rc<Instance>, Entry)> {
        if let Some(cn) = &name.ctx {
            let target = self.resolve_context_name(inst, cn, scope)?;
            let e = target.symbols.borrow().get(&name.id.name).cloned();
            match e {
                Some(e) => Ok((target, e)),
                None => Err(self.err(
                    inst,
                    name.span,
                    format!(
                        "Undeclared identifier \"{}\" in context \"{}\".",
                        name.id.name, cn.name.name
                    ),
                )),
            }
        } else {
            if let Some(e) = inst.symbols.borrow().get(&name.id.name) {
                return Ok((inst.clone(), e.clone()));
            }
            if let Some(e) = self.env.prelude.symbols.borrow().get(&name.id.name) {
                return Ok((self.env.prelude.clone(), e.clone()));
            }
            Err(self.err(
                inst,
                name.span,
                format!("Unknown variable \"{}\".", name.id.name),
            ))
        }
    }

    // ------------------------------------------------------------------
    // Types
    // ------------------------------------------------------------------

    pub fn resolve_type(
        &self,
        inst: &Rc<Instance>,
        t: &Type,
        scope: &mut Scope,
    ) -> CResult<SemType> {
        match &t.kind {
            TypeKind::Name(n) => {
                let (_, e) = self.lookup_entry(inst, n, scope)?;
                match e {
                    Entry::Type { sem, .. } => Ok(sem),
                    _ => Err(self.err(
                        inst,
                        t.span,
                        format!("Unknown type \"{}\".", n.id.name),
                    )),
                }
            }
            TypeKind::Subrange(lo, hi) => {
                for b in [lo.as_ref(), hi.as_ref()] {
                    if matches!(b.kind, ExprKind::Unbounded) {
                        continue;
                    }
                    let bt = self.infer_expr(inst, b, scope)?;
                    self.require(inst, b.span, &bt, &SemType::Number)?;
                }
                Ok(SemType::Number)
            }
            TypeKind::Subtype(sp) => {
                let base = self.resolve_type(inst, &sp.ty, scope)?;
                scope.push(FrameKind::Plain);
                scope.bind(&sp.var.name, base.clone());
                let pt = self.infer_expr(inst, &sp.pred, scope)?;
                scope.pop();
                self.require(inst, sp.pred.span, &pt, &SemType::Bool)?;
                Ok(base)
            }
            TypeKind::Array(i, e) => {
                let it = self.resolve_type(inst, i, scope)?;
                let et = self.resolve_type(inst, e, scope)?;
                Ok(SemType::Array(Box::new(it), Box::new(et)))
            }
            TypeKind::Tuple(ts) => {
                let mut out = Vec::new();
                for t in ts {
                    out.push(self.resolve_type(inst, t, scope)?);
                }
                Ok(SemType::Tuple(out))
            }
            TypeKind::Function(d, r) => Ok(SemType::Fun(
                Box::new(self.resolve_type(inst, d, scope)?),
                Box::new(self.resolve_type(inst, r, scope)?),
            )),
            TypeKind::Record(fs) => {
                let mut out = Vec::new();
                for f in fs {
                    out.push((f.name.name.clone(), self.resolve_type(inst, &f.ty, scope)?));
                }
                out.sort_by(|a, b| a.0.cmp(&b.0));
                Ok(SemType::Record(out))
            }
            TypeKind::State(m) => {
                self.check_module(inst, m, scope)?;
                Ok(SemType::State)
            }
        }
    }

    fn require(
        &self,
        inst: &Instance,
        span: Span,
        actual: &SemType,
        expected: &SemType,
    ) -> CResult<()> {
        if actual.compatible(expected) {
            Ok(())
        } else {
            Err(self.err(
                inst,
                span,
                format!("Type mismatch: expected {}, found {}.", expected, actual),
            ))
        }
    }

    // ------------------------------------------------------------------
    // Expressions
    // ------------------------------------------------------------------

    pub fn infer_expr(
        &self,
        inst: &Rc<Instance>,
        e: &Expr,
        scope: &mut Scope,
    ) -> CResult<SemType> {
        use ExprKind::*;
        match &e.kind {
            Name(n) => {
                if n.ctx.is_none() {
                    if let Some(t) = scope.lookup(&n.id.name) {
                        return Ok(t.clone());
                    }
                }
                let (_, entry) = self.lookup_entry(inst, n, scope)?;
                match entry {
                    Entry::Const { sem, .. } => Ok(sem),
                    Entry::Type { .. } => Err(self.err(
                        inst,
                        e.span,
                        format!("Type \"{}\" used as an expression.", n.id.name),
                    )),
                    Entry::Module { .. } => Err(self.err(
                        inst,
                        e.span,
                        format!("Module \"{}\" used as an expression.", n.id.name),
                    )),
                    Entry::Assertion { .. } | Entry::Ctx(_) => Err(self.err(
                        inst,
                        e.span,
                        format!("Invalid use of \"{}\" in an expression.", n.id.name),
                    )),
                }
            }
            Next(id) => match scope.lookup_state(&id.name) {
                Some(t) => Ok(t.clone()),
                None => Err(self.err(
                    inst,
                    e.span,
                    format!("Undeclared state variable \"{}\".", id.name),
                )),
            },
            Numeral(_) | Float { .. } => Ok(SemType::Number),
            Str(_) => Ok(SemType::Tuple(vec![
                SemType::Number,
                SemType::Array(Box::new(SemType::Number), Box::new(SemType::Number)),
            ])),
            Binary(op, a, b) => {
                let ta = self.infer_expr(inst, a, scope)?;
                let tb = self.infer_expr(inst, b, scope)?;
                use BinOp::*;
                match op {
                    And | Or | Xor | Implies | Iff => {
                        self.require(inst, a.span, &ta, &SemType::Bool)?;
                        self.require(inst, b.span, &tb, &SemType::Bool)?;
                        Ok(SemType::Bool)
                    }
                    Eq | Neq => {
                        self.require(inst, e.span, &tb, &ta)?;
                        Ok(SemType::Bool)
                    }
                    Lt | Le | Gt | Ge => {
                        self.require(inst, a.span, &ta, &SemType::Number)?;
                        self.require(inst, b.span, &tb, &SemType::Number)?;
                        Ok(SemType::Bool)
                    }
                    Plus | Minus | Mult | Div | IDiv | Mod => {
                        self.require(inst, a.span, &ta, &SemType::Number)?;
                        self.require(inst, b.span, &tb, &SemType::Number)?;
                        Ok(SemType::Number)
                    }
                }
            }
            Unary(op, a) => {
                let ta = self.infer_expr(inst, a, scope)?;
                match op {
                    UnOp::Not => {
                        self.require(inst, a.span, &ta, &SemType::Bool)?;
                        Ok(SemType::Bool)
                    }
                    UnOp::Minus => {
                        self.require(inst, a.span, &ta, &SemType::Number)?;
                        Ok(SemType::Number)
                    }
                }
            }
            App(f, args) => {
                let ft = self.infer_expr(inst, f, scope)?;
                let mut ats = Vec::new();
                for a in args {
                    ats.push(self.infer_expr(inst, a, scope)?);
                }
                let at = if ats.len() == 1 {
                    ats.pop().unwrap()
                } else {
                    SemType::Tuple(ats)
                };
                match ft {
                    SemType::Fun(dom, rng) => {
                        self.require(inst, e.span, &at, &dom)?;
                        Ok(*rng)
                    }
                    SemType::Array(idx, elem) => {
                        self.require(inst, e.span, &at, &idx)?;
                        Ok(*elem)
                    }
                    SemType::Any => Ok(SemType::Any),
                    other => Err(self.err(
                        inst,
                        f.span,
                        format!("Function (array) type expected, found {}.", other),
                    )),
                }
            }
            ArraySelect(a, i) => {
                let ta = self.infer_expr(inst, a, scope)?;
                let ti = self.infer_expr(inst, i, scope)?;
                match ta {
                    SemType::Array(idx, elem) | SemType::Fun(idx, elem) => {
                        self.require(inst, i.span, &ti, &idx)?;
                        Ok(*elem)
                    }
                    SemType::Any => Ok(SemType::Any),
                    other => Err(self.err(
                        inst,
                        a.span,
                        format!("Function (array) type expected, found {}.", other),
                    )),
                }
            }
            RecordSelect(r, f) => {
                let tr = self.infer_expr(inst, r, scope)?;
                match tr {
                    SemType::Record(fs) => fs
                        .iter()
                        .find(|(n, _)| n == &f.name)
                        .map(|(_, t)| t.clone())
                        .ok_or_else(|| {
                            self.err(
                                inst,
                                f.span,
                                format!("Unknown record field \"{}\".", f.name),
                            )
                        }),
                    SemType::Any => Ok(SemType::Any),
                    other => Err(self.err(
                        inst,
                        r.span,
                        format!("Record type expected, found {}.", other),
                    )),
                }
            }
            TupleSelect(t, i) => {
                let tt = self.infer_expr(inst, t, scope)?;
                match tt {
                    SemType::Tuple(ts) => {
                        let idx = *i as usize;
                        if idx >= 1 && idx <= ts.len() {
                            Ok(ts[idx - 1].clone())
                        } else {
                            Err(self.err(inst, e.span, "Tuple index out of bounds."))
                        }
                    }
                    SemType::Any => Ok(SemType::Any),
                    other => Err(self.err(
                        inst,
                        t.span,
                        format!("Tuple type expected, found {}.", other),
                    )),
                }
            }
            Update {
                target,
                accesses,
                value,
            } => {
                let tt = self.infer_expr(inst, target, scope)?;
                let vt = self.access_type(inst, &tt, accesses, scope, e.span)?;
                let val_t = self.infer_expr(inst, value, scope)?;
                self.require(inst, value.span, &val_t, &vt)?;
                Ok(tt)
            }
            Lambda(decls, body) => {
                scope.push(FrameKind::Plain);
                let mut dom = Vec::new();
                for d in decls {
                    let t = self.resolve_type(inst, &d.ty, scope)?;
                    for n in &d.names {
                        scope.bind(&n.name, t.clone());
                        dom.push(t.clone());
                    }
                }
                let bt = self.infer_expr(inst, body, scope)?;
                scope.pop();
                let dom = if dom.len() == 1 {
                    dom.pop().unwrap()
                } else {
                    SemType::Tuple(dom)
                };
                Ok(SemType::Fun(Box::new(dom), Box::new(bt)))
            }
            Quantified(_, decls, body) => {
                scope.push(FrameKind::Plain);
                for d in decls {
                    let t = self.resolve_type(inst, &d.ty, scope)?;
                    for n in &d.names {
                        scope.bind(&n.name, t.clone());
                    }
                }
                let bt = self.infer_expr(inst, body, scope)?;
                scope.pop();
                self.require(inst, body.span, &bt, &SemType::Bool)?;
                Ok(SemType::Bool)
            }
            Let(decls, body) => {
                scope.push(FrameKind::Plain);
                for d in decls {
                    let t = self.resolve_type(inst, &d.ty, scope)?;
                    let vt = self.infer_expr(inst, &d.value, scope)?;
                    self.require(inst, d.value.span, &vt, &t)?;
                    scope.bind(&d.name.name, t);
                }
                let bt = self.infer_expr(inst, body, scope)?;
                scope.pop();
                Ok(bt)
            }
            SetPred(sp) => {
                let base = self.resolve_type(inst, &sp.ty, scope)?;
                scope.push(FrameKind::Plain);
                scope.bind(&sp.var.name, base.clone());
                let pt = self.infer_expr(inst, &sp.pred, scope)?;
                scope.pop();
                self.require(inst, sp.pred.span, &pt, &SemType::Bool)?;
                Ok(SemType::Fun(Box::new(base), Box::new(SemType::Bool)))
            }
            SetList(es) => {
                let mut elem = SemType::Any;
                for x in es {
                    let t = self.infer_expr(inst, x, scope)?;
                    self.require(inst, x.span, &t, &elem)?;
                    if elem == SemType::Any {
                        elem = t;
                    }
                }
                Ok(SemType::Fun(Box::new(elem), Box::new(SemType::Bool)))
            }
            ArrayLit(d, body) => {
                let it = self.resolve_type(inst, &d.ty, scope)?;
                scope.push(FrameKind::Plain);
                scope.bind(&d.names[0].name, it.clone());
                let bt = self.infer_expr(inst, body, scope)?;
                scope.pop();
                Ok(SemType::Array(Box::new(it), Box::new(bt)))
            }
            RecordLit(entries) => {
                let mut fs = Vec::new();
                for (n, x) in entries {
                    fs.push((n.name.clone(), self.infer_expr(inst, x, scope)?));
                }
                fs.sort_by(|a, b| a.0.cmp(&b.0));
                Ok(SemType::Record(fs))
            }
            TupleLit(es) => {
                let mut ts = Vec::new();
                for x in es {
                    ts.push(self.infer_expr(inst, x, scope)?);
                }
                Ok(SemType::Tuple(ts))
            }
            Conditional {
                cond, then, els, ..
            } => {
                let ct = self.infer_expr(inst, cond, scope)?;
                self.require(inst, cond.span, &ct, &SemType::Bool)?;
                let tt = self.infer_expr(inst, then, scope)?;
                let et = self.infer_expr(inst, els, scope)?;
                self.require(inst, els.span, &et, &tt)?;
                if tt == SemType::Any {
                    Ok(et)
                } else {
                    Ok(tt)
                }
            }
            ModInit(m) => {
                self.check_module(inst, m, scope)?;
                Ok(SemType::Fun(
                    Box::new(SemType::State),
                    Box::new(SemType::Bool),
                ))
            }
            ModTrans(m) => {
                self.check_module(inst, m, scope)?;
                Ok(SemType::Fun(
                    Box::new(SemType::Tuple(vec![SemType::State, SemType::State])),
                    Box::new(SemType::Bool),
                ))
            }
            Unbounded => Ok(SemType::Number),
        }
    }

    /// Type reached by following an access path from `base`.
    fn access_type(
        &self,
        inst: &Rc<Instance>,
        base: &SemType,
        accesses: &[Access],
        scope: &mut Scope,
        span: Span,
    ) -> CResult<SemType> {
        let mut cur = base.clone();
        for a in accesses {
            cur = match (a, cur) {
                (Access::Array(i), SemType::Array(idx, elem))
                | (Access::Array(i), SemType::Fun(idx, elem)) => {
                    let it = self.infer_expr(inst, i, scope)?;
                    self.require(inst, i.span, &it, &idx)?;
                    *elem
                }
                (Access::Args(args), SemType::Fun(dom, rng)) => {
                    let mut ats = Vec::new();
                    for x in args {
                        ats.push(self.infer_expr(inst, x, scope)?);
                    }
                    let at = if ats.len() == 1 {
                        ats.pop().unwrap()
                    } else {
                        SemType::Tuple(ats)
                    };
                    self.require(inst, span, &at, &dom)?;
                    *rng
                }
                (Access::Record(f), SemType::Record(fs)) => fs
                    .iter()
                    .find(|(n, _)| n == &f.name)
                    .map(|(_, t)| t.clone())
                    .ok_or_else(|| {
                        self.err(inst, f.span, format!("Unknown record field \"{}\".", f.name))
                    })?,
                (Access::Tuple(i), SemType::Tuple(ts)) => {
                    let idx = *i as usize;
                    if idx >= 1 && idx <= ts.len() {
                        ts[idx - 1].clone()
                    } else {
                        return Err(self.err(inst, span, "Tuple index out of bounds."));
                    }
                }
                (_, SemType::Any) => SemType::Any,
                (_, other) => {
                    return Err(self.err(
                        inst,
                        span,
                        format!("Invalid access on a value of type {}.", other),
                    ))
                }
            };
        }
        Ok(cur)
    }

    // ------------------------------------------------------------------
    // Modules
    // ------------------------------------------------------------------

    /// Check a module expression; returns its state variables
    /// (name, class, type).
    pub fn check_module(
        &self,
        inst: &Rc<Instance>,
        m: &Module,
        scope: &mut Scope,
    ) -> CResult<Vec<(String, VarClass, SemType)>> {
        use ModuleKind::*;
        match &m.kind {
            Base(b) => self.check_base_module(inst, b, scope),
            Instance(name, actuals) => {
                let (_, entry) = self.lookup_entry(inst, name, scope)?;
                match entry {
                    Entry::Module { params, state, .. } => {
                        if params.len() != actuals.len() {
                            return Err(self.err(
                                inst,
                                m.span,
                                format!(
                                    "Wrong number of module actuals for \"{}\": expected {}, \
                                     found {}.",
                                    name.id.name,
                                    params.len(),
                                    actuals.len()
                                ),
                            ));
                        }
                        for ((_, pt), a) in params.iter().zip(actuals) {
                            let at = self.infer_expr(inst, a, scope)?;
                            self.require(inst, a.span, &at, pt)?;
                        }
                        Ok(state)
                    }
                    _ => Err(self.err(
                        inst,
                        m.span,
                        format!("\"{}\" is not a module.", name.id.name),
                    )),
                }
            }
            Sync(a, b) | Async(a, b) => {
                let sa = self.check_module(inst, a, scope)?;
                let sb = self.check_module(inst, b, scope)?;
                self.merge_states(inst, m.span, sa, sb)
            }
            MultiSync(d, sub) | MultiAsync(d, sub) => {
                let it = self.resolve_type(inst, &d.ty, scope)?;
                scope.push(FrameKind::Plain);
                scope.bind(&d.names[0].name, it.clone());
                let mut s = self.check_module(inst, sub, scope)?;
                scope.pop();
                // local variables of the composed module are indexed by the
                // composition index: `([] (i: T): m)` turns a local `x : t`
                // into `x : ARRAY T OF t`.
                for v in &mut s {
                    if v.1 == VarClass::Local {
                        v.2 = SemType::Array(Box::new(it.clone()), Box::new(v.2.clone()));
                    }
                }
                Ok(s)
            }
            Hide(ids, sub) => {
                let mut s = self.check_module(inst, sub, scope)?;
                for id in ids {
                    match s.iter_mut().find(|(n, _, _)| n == &id.name) {
                        Some(v) => v.1 = VarClass::Local,
                        None => {
                            return Err(self.err(
                                inst,
                                id.span,
                                format!("Undeclared state variable \"{}\".", id.name),
                            ))
                        }
                    }
                }
                Ok(s)
            }
            NewOutput(ids, sub) => {
                let mut s = self.check_module(inst, sub, scope)?;
                for id in ids {
                    match s.iter_mut().find(|(n, _, _)| n == &id.name) {
                        Some(v) => v.1 = VarClass::Output,
                        None => {
                            return Err(self.err(
                                inst,
                                id.span,
                                format!("Undeclared state variable \"{}\".", id.name),
                            ))
                        }
                    }
                }
                Ok(s)
            }
            Rename(renames, sub) => {
                let mut s = self.check_module(inst, sub, scope)?;
                for (from, to) in renames {
                    let Some(pos) = s.iter().position(|(n, _, _)| n == &from.base.name) else {
                        return Err(self.err(
                            inst,
                            from.span,
                            format!("Undeclared state variable \"{}\".", from.base.name),
                        ));
                    };
                    let (_, class, ty) = s[pos].clone();
                    if to.accesses.is_empty() {
                        // simple rename
                        s.remove(pos);
                        s.push((to.base.name.clone(), class, ty));
                    } else {
                        // rename into a component of an enclosing variable
                        // (e.g. `RENAME pc TO pcs[i]` under WITH); the base
                        // variable must be visible in an enclosing scope.
                        let base_ty = scope.lookup(&to.base.name).cloned();
                        match base_ty {
                            Some(bt) => {
                                let target =
                                    self.access_type(inst, &bt, &to.accesses, scope, to.span)?;
                                self.require(inst, to.span, &ty, &target)?;
                                s.remove(pos);
                                if !s.iter().any(|(n, _, _)| n == &to.base.name) {
                                    s.push((to.base.name.clone(), class, bt));
                                }
                            }
                            None => {
                                return Err(self.err(
                                    inst,
                                    to.span,
                                    format!(
                                        "Undeclared state variable \"{}\".",
                                        to.base.name
                                    ),
                                ))
                            }
                        }
                    }
                }
                Ok(s)
            }
            With(decls, sub) => {
                scope.push(FrameKind::State);
                let mut added = Vec::new();
                for nd in decls {
                    for d in &nd.decls {
                        let t = self.resolve_type(inst, &d.ty, scope)?;
                        for n in &d.names {
                            scope.bind(&n.name, t.clone());
                            added.push((n.name.clone(), nd.class, t.clone()));
                        }
                    }
                }
                let s = self.check_module(inst, sub, scope)?;
                scope.pop();
                self.merge_states(inst, m.span, added, s)
            }
            Observe(a, b) => {
                let sa = self.check_module(inst, a, scope)?;
                let sb = self.check_module(inst, b, scope)?;
                self.merge_states(inst, m.span, sa, sb)
            }
        }
    }

    fn merge_states(
        &self,
        inst: &Instance,
        span: Span,
        mut a: Vec<(String, VarClass, SemType)>,
        b: Vec<(String, VarClass, SemType)>,
    ) -> CResult<Vec<(String, VarClass, SemType)>> {
        for (n, c, t) in b {
            if let Some((_, c0, t0)) = a.iter_mut().find(|(n0, _, _)| n0 == &n) {
                if *c0 == VarClass::Local && c == VarClass::Local {
                    // same-named locals of composed modules are paired into
                    // a tuple, nested along the composition tree:
                    // `(m1 [] m2)`'s local `x` is `[t1, t2]`.
                    *t0 = SemType::Tuple(vec![t0.clone(), t]);
                    continue;
                }
                if !t0.compatible(&t) {
                    return Err(self.err(
                        inst,
                        span,
                        format!(
                            "Variable \"{}\" is declared with incompatible types in composed \
                             modules.",
                            n
                        ),
                    ));
                }
                // class merge: output wins over input/global
                if c == VarClass::Output || *c0 == VarClass::Input && c == VarClass::Global {
                    *c0 = c;
                }
            } else {
                a.push((n, c, t));
            }
        }
        Ok(a)
    }

    fn check_base_module(
        &self,
        inst: &Rc<Instance>,
        b: &BaseModule,
        scope: &mut Scope,
    ) -> CResult<Vec<(String, VarClass, SemType)>> {
        let mut state: Vec<(String, VarClass, SemType)> = Vec::new();
        for d in &b.decls {
            if let BaseDecl::Vars(class, decls) = d {
                for vd in decls {
                    let t = self.resolve_type(inst, &vd.ty, scope)?;
                    for n in &vd.names {
                        if let Some((_, c0, t0)) =
                            state.iter().find(|(n0, _, _)| n0 == &n.name)
                        {
                            if *c0 != *class || !t0.compatible(&t) {
                                return Err(self.err(
                                    inst,
                                    n.span,
                                    format!("Variable \"{}\" is declared twice.", n.name),
                                ));
                            }
                        } else {
                            state.push((n.name.clone(), *class, t.clone()));
                        }
                    }
                }
            }
        }
        scope.push(FrameKind::State);
        for (n, _, t) in &state {
            scope.bind(n, t.clone());
        }
        let result = (|| {
            for d in &b.decls {
                match d {
                    BaseDecl::Vars(..) => {}
                    BaseDecl::Definition(defs) => {
                        for def in defs {
                            self.check_definition(inst, def, &state, scope, false)?;
                        }
                    }
                    BaseDecl::Initialization(items) | BaseDecl::Transition(items) => {
                        let is_trans = matches!(d, BaseDecl::Transition(_));
                        for it in items {
                            match it {
                                DefOrCommand::Def(def) => {
                                    self.check_definition(inst, def, &state, scope, is_trans)?
                                }
                                DefOrCommand::Commands(cmds, _) => {
                                    for c in cmds {
                                        self.check_command(inst, c, &state, scope, is_trans)?;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Ok(())
        })();
        scope.pop();
        result?;
        Ok(state)
    }

    fn check_definition(
        &self,
        inst: &Rc<Instance>,
        def: &Definition,
        state: &[(String, VarClass, SemType)],
        scope: &mut Scope,
        allow_next: bool,
    ) -> CResult<()> {
        match def {
            Definition::Forall(decls, defs) => {
                scope.push(FrameKind::Plain);
                for d in decls {
                    let t = self.resolve_type(inst, &d.ty, scope)?;
                    for n in &d.names {
                        scope.bind(&n.name, t.clone());
                    }
                }
                for d in defs {
                    self.check_definition(inst, d, state, scope, allow_next)?;
                }
                scope.pop();
                Ok(())
            }
            Definition::Simple(s) => {
                let Some((_, class, base_ty)) =
                    state.iter().find(|(n, _, _)| n == &s.lhs.base.name)
                else {
                    return Err(self.err(
                        inst,
                        s.lhs.span,
                        format!("Undeclared state variable \"{}\".", s.lhs.base.name),
                    ));
                };
                if *class == VarClass::Input {
                    return Err(self.err(
                        inst,
                        s.lhs.span,
                        format!(
                            "Input variable \"{}\" cannot be assigned.",
                            s.lhs.base.name
                        ),
                    ));
                }
                if s.lhs.next && !allow_next {
                    return Err(self.err(
                        inst,
                        s.lhs.span,
                        "Next-state variables are not allowed here.",
                    ));
                }
                let base_ty = base_ty.clone();
                let lhs_ty =
                    self.access_type(inst, &base_ty, &s.lhs.accesses, scope, s.lhs.span)?;
                match &s.rhs {
                    Rhs::Expr(e) => {
                        let t = self.infer_expr(inst, e, scope)?;
                        self.require(inst, e.span, &t, &lhs_ty)?;
                    }
                    Rhs::Selection(e) => {
                        let t = self.infer_expr(inst, e, scope)?;
                        self.require(
                            inst,
                            e.span,
                            &t,
                            &SemType::Fun(Box::new(lhs_ty), Box::new(SemType::Bool)),
                        )?;
                    }
                }
                Ok(())
            }
        }
    }

    fn check_command(
        &self,
        inst: &Rc<Instance>,
        c: &SomeCommand,
        state: &[(String, VarClass, SemType)],
        scope: &mut Scope,
        allow_next: bool,
    ) -> CResult<()> {
        match c {
            SomeCommand::Multi(decls, inner, _) => {
                scope.push(FrameKind::Plain);
                for d in decls {
                    let t = self.resolve_type(inst, &d.ty, scope)?;
                    for n in &d.names {
                        scope.bind(&n.name, t.clone());
                    }
                }
                self.check_command(inst, inner, state, scope, allow_next)?;
                scope.pop();
                Ok(())
            }
            SomeCommand::Guarded(g) => {
                if let Some(guard) = &g.guard {
                    let t = self.infer_expr(inst, guard, scope)?;
                    self.require(inst, guard.span, &t, &SemType::Bool)?;
                }
                for a in &g.assignments {
                    self.check_definition(inst, a, state, scope, allow_next)?;
                }
                Ok(())
            }
        }
    }
}
