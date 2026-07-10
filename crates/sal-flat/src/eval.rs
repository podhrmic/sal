//! The flattening evaluator: resolves concrete types and partially
//! evaluates SAL expressions into symbolic values over leaf variables.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use sal_core::env::{Binding, Entry, Instance, SalEnv};
use sal_core::error::SalError;
use sal_core::types::TypeId;
use sal_core::wfc::Checker;
use sal_syntax::ast::*;
use sal_syntax::span::Span;

use crate::ctype::CType;
use crate::fexpr::{FExpr, LeafInfo, LeafType};
use crate::formula::TFormula;
use crate::sval::{Closure, EvalCtx, SVal};
use crate::value::Value;

pub struct Flattener<'e> {
    pub env: &'e SalEnv,
    pub checker: Checker<'e>,
    pub leaves: RefCell<Vec<LeafInfo>>,
    /// Scalar registry: element names + ringset flag for every scalar
    /// TypeId seen (needed by rsucc/rpred and value printing).
    pub scalars: RefCell<HashMap<TypeId, (Rc<Vec<String>>, bool)>>,
    /// Cache of resolved ctypes per (instance key, printed type).
    ctype_cache: RefCell<HashMap<(String, String), CType>>,
    depth: Cell<u32>,
}

pub type FResult<T> = Result<T, SalError>;

const MAX_DEPTH: u32 = 100_000;

impl<'e> Flattener<'e> {
    pub fn new(env: &'e SalEnv) -> Self {
        Flattener {
            env,
            checker: Checker::new(env),
            leaves: RefCell::new(Vec::new()),
            scalars: RefCell::new(HashMap::new()),
            ctype_cache: RefCell::new(HashMap::new()),
            depth: Cell::new(0),
        }
    }

    pub fn err(&self, ctx: &EvalCtx, span: Span, msg: impl Into<String>) -> SalError {
        SalError::semantic(&ctx.inst.name, span, msg)
    }

    // ------------------------------------------------------------------
    // Concrete type resolution
    // ------------------------------------------------------------------

    pub fn resolve_ctype(&self, ctx: &EvalCtx, t: &Type) -> FResult<CType> {
        match &t.kind {
            TypeKind::Name(n) => self.resolve_ctype_name(ctx, n, t.span),
            TypeKind::Subrange(lo, hi) => {
                let lo_v = self.eval_bound(ctx, lo)?;
                let hi_v = self.eval_bound(ctx, hi)?;
                match (lo_v, hi_v) {
                    (Some(a), Some(b)) => Ok(CType::Range(a, b)),
                    (a, b) => Ok(CType::Int { min: a, max: b }),
                }
            }
            TypeKind::Subtype(sp) => self.resolve_ctype(ctx, &sp.ty),
            TypeKind::Array(i, e) => Ok(CType::Array(
                Box::new(self.resolve_ctype(ctx, i)?),
                Box::new(self.resolve_ctype(ctx, e)?),
            )),
            TypeKind::Tuple(ts) => Ok(CType::Tuple(
                ts.iter()
                    .map(|x| self.resolve_ctype(ctx, x))
                    .collect::<FResult<_>>()?,
            )),
            TypeKind::Function(d, r) => Ok(CType::Fun(
                Box::new(self.resolve_ctype(ctx, d)?),
                Box::new(self.resolve_ctype(ctx, r)?),
            )),
            TypeKind::Record(fs) => {
                let mut out = Vec::new();
                for f in fs {
                    out.push((f.name.name.clone(), self.resolve_ctype(ctx, &f.ty)?));
                }
                out.sort_by(|a, b| a.0.cmp(&b.0));
                Ok(CType::Record(out))
            }
            TypeKind::State(_) => Err(self.err(ctx, t.span, "State types are not supported here.")),
        }
    }

    fn eval_bound(&self, ctx: &EvalCtx, e: &Expr) -> FResult<Option<BigInt>> {
        if matches!(e.kind, ExprKind::Unbounded) {
            return Ok(None);
        }
        let v = self.eval(ctx, e)?;
        match v {
            SVal::Ground(Value::Num(n)) if n.is_integer() => Ok(Some(n.to_integer())),
            _ => Err(self.err(
                ctx,
                e.span,
                "Subrange bounds must evaluate to integer constants.",
            )),
        }
    }

    fn resolve_ctype_name(&self, ctx: &EvalCtx, n: &Name, span: Span) -> FResult<CType> {
        // prelude built-ins
        if n.ctx.is_none() {
            match n.id.name.as_str() {
                "BOOLEAN" | "boolean" | "bool" => return Ok(CType::Bool),
                "INTEGER" | "integer" | "int" => {
                    return Ok(CType::Int {
                        min: None,
                        max: None,
                    })
                }
                "NATURAL" | "natural" | "nat" => {
                    return Ok(CType::Int {
                        min: Some(BigInt::zero()),
                        max: None,
                    })
                }
                "NZINTEGER" | "nzint" => {
                    return Ok(CType::Int {
                        min: None,
                        max: None,
                    })
                }
                "nznat" => {
                    return Ok(CType::Int {
                        min: Some(BigInt::from(1)),
                        max: None,
                    })
                }
                "REAL" | "real" | "NZREAL" | "nzreal" | "number" => return Ok(CType::Real),
                "CHAR" | "char" | "character" => {
                    return Ok(CType::Range(BigInt::zero(), BigInt::from(255)))
                }
                _ => {}
            }
        }
        let (def_inst, entry) = self.lookup(ctx, n, span)?;
        let Entry::Type { def, .. } = &entry else {
            // type parameter bound to a type?
            return Err(self.err(ctx, span, format!("Unknown type \"{}\".", n.id.name)));
        };
        let tid = TypeId {
            ctx: def_inst.key.clone(),
            name: n.id.name.clone(),
        };
        let cache_key = (def_inst.key.clone(), n.id.name.clone());
        if let Some(c) = self.ctype_cache.borrow().get(&cache_key) {
            return Ok(c.clone());
        }
        let def_ctx = ctx.with_inst(def_inst.clone());
        let result = match def {
            Some(TypeDef::Type(t)) => self.resolve_ctype(&def_ctx, t)?,
            Some(TypeDef::Scalar(ids)) => {
                let elems = Rc::new(ids.iter().map(|i| i.name.clone()).collect::<Vec<_>>());
                self.scalars
                    .borrow_mut()
                    .insert(tid.clone(), (elems.clone(), false));
                CType::Scalar(tid.clone(), elems)
            }
            Some(TypeDef::Scalarset(e)) | Some(TypeDef::Ringset(e)) => {
                let is_ring = matches!(def, Some(TypeDef::Ringset(_)));
                let v = self.eval(&def_ctx, e)?;
                let n = match v {
                    SVal::Ground(v) => v.as_usize().ok_or_else(|| {
                        self.err(ctx, span, "Scalarset size must be a natural constant.")
                    })?,
                    _ => {
                        return Err(self.err(
                            ctx,
                            span,
                            "Scalarset size must be a constant.",
                        ))
                    }
                };
                let elems =
                    Rc::new((0..n).map(|i| format!("{}_{}", n_name(&tid), i)).collect::<Vec<_>>());
                self.scalars
                    .borrow_mut()
                    .insert(tid.clone(), (elems.clone(), is_ring));
                CType::Scalar(tid.clone(), elems)
            }
            Some(TypeDef::Datatype(ctors)) => {
                // guard against recursion: mark in-progress as uninterp
                self.ctype_cache
                    .borrow_mut()
                    .insert(cache_key.clone(), CType::Uninterp(tid.clone()));
                let mut cs = Vec::new();
                for c in ctors {
                    let mut fields = Vec::new();
                    for a in &c.accessors {
                        let ft = self.resolve_ctype(&def_ctx, &a.ty)?;
                        for _ in &a.names {
                            fields.push(ft.clone());
                        }
                    }
                    cs.push((c.name.name.clone(), fields));
                }
                CType::Data(tid.clone(), Rc::new(cs))
            }
            None => {
                // uninterpreted type or a type parameter with a binding
                if let Some(Binding::Type(_, Some((bind_inst, bind_ty)))) =
                    def_inst.bindings.get(&n.id.name)
                {
                    let bctx = ctx.with_inst(bind_inst.clone());
                    self.resolve_ctype(&bctx, bind_ty)?
                } else {
                    CType::Uninterp(tid)
                }
            }
        };
        self.ctype_cache.borrow_mut().insert(cache_key, result.clone());
        Ok(result)
    }

    fn lookup(&self, ctx: &EvalCtx, n: &Name, span: Span) -> FResult<(Rc<Instance>, Entry)> {
        // reuse the checker's resolution machinery through a fresh scope
        let mut scope = sal_core::wfc::Scope::default();
        self.checker
            .lookup_entry_pub(&ctx.inst, n, &mut scope)
            .map_err(|_| self.err(ctx, span, format!("Unknown variable \"{}\".", n.id.name)))
    }

    // ------------------------------------------------------------------
    // Expression evaluation
    // ------------------------------------------------------------------

    pub fn eval(&self, ctx: &EvalCtx, e: &Expr) -> FResult<SVal> {
        self.depth.set(self.depth.get() + 1);
        if self.depth.get() > MAX_DEPTH {
            self.depth.set(0);
            return Err(self.err(ctx, e.span, "Evaluation depth exceeded (non-terminating recursion?)."));
        }
        let r = self.eval_inner(ctx, e);
        self.depth.set(self.depth.get().saturating_sub(1));
        r
    }

    fn eval_inner(&self, ctx: &EvalCtx, e: &Expr) -> FResult<SVal> {
        use ExprKind::*;
        match &e.kind {
            Name(n) => self.eval_name(ctx, n, e.span),
            Next(id) => {
                let sv = ctx
                    .lookup(&format!("{}'", id.name))
                    .ok_or_else(|| {
                        self.err(ctx, e.span, format!("Unknown variable \"{}'\".", id.name))
                    })?;
                Ok(sv)
            }
            Numeral(s) => Ok(SVal::Ground(Value::Num(BigRational::from_integer(
                s.parse::<BigInt>().unwrap(),
            )))),
            Float { numer, denom } => Ok(SVal::Ground(Value::Num(BigRational::new(
                numer.parse::<BigInt>().unwrap(),
                denom.parse::<BigInt>().unwrap(),
            )))),
            Str(_) => Err(self.err(ctx, e.span, "String literals are not supported here.")),
            Unbounded => Err(self.err(ctx, e.span, "Invalid use of `_'.")),
            Binary(op, a, b) => self.eval_binary(ctx, *op, a, b, e.span),
            Unary(op, a) => {
                let va = self.eval(ctx, a)?;
                match op {
                    UnOp::Not => self.not_sval(ctx, va, e.span),
                    UnOp::Minus => match va {
                        SVal::Ground(Value::Num(n)) => Ok(SVal::Ground(Value::Num(-n))),
                        _ => {
                            let (fa, t) = self.numeric_fexpr(ctx, &va, a.span)?;
                            Ok(SVal::Sym(FExpr::Neg(Rc::new(fa)), t))
                        }
                    },
                }
            }
            App(f, args) => {
                let vf = self.eval(ctx, f)?;
                let mut vargs = Vec::new();
                for a in args {
                    vargs.push(self.eval(ctx, a)?);
                }
                self.apply(ctx, vf, vargs, e.span)
            }
            ArraySelect(a, i) => {
                let va = self.eval(ctx, a)?;
                let vi = self.eval(ctx, i)?;
                self.select(ctx, va, vi, e.span)
            }
            RecordSelect(r, f) => {
                let vr = self.eval(ctx, r)?;
                match vr {
                    SVal::Record(fs) => fs
                        .iter()
                        .find(|(n, _)| n == &f.name)
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| {
                            self.err(ctx, f.span, format!("Unknown record field \"{}\".", f.name))
                        }),
                    SVal::Ground(Value::Record(fs)) => fs
                        .iter()
                        .find(|(n, _)| n == &f.name)
                        .map(|(_, v)| SVal::Ground(v.clone()))
                        .ok_or_else(|| {
                            self.err(ctx, f.span, format!("Unknown record field \"{}\".", f.name))
                        }),
                    other => Err(self.err(
                        ctx,
                        e.span,
                        format!("Record value expected, found {:?}.", other),
                    )),
                }
            }
            TupleSelect(t, i) => {
                let vt = self.eval(ctx, t)?;
                let idx = *i as usize;
                match vt {
                    SVal::Tuple(vs) if idx >= 1 && idx <= vs.len() => Ok(vs[idx - 1].clone()),
                    SVal::Ground(Value::Tuple(vs)) if idx >= 1 && idx <= vs.len() => {
                        Ok(SVal::Ground(vs[idx - 1].clone()))
                    }
                    other => Err(self.err(
                        ctx,
                        e.span,
                        format!("Invalid tuple selection on {:?}.", other),
                    )),
                }
            }
            Update {
                target,
                accesses,
                value,
            } => {
                let vt = self.eval(ctx, target)?;
                let vv = self.eval(ctx, value)?;
                self.update(ctx, vt, accesses, vv, e.span)
            }
            Lambda(decls, body) => {
                let mut params = Vec::new();
                for d in decls {
                    for n in &d.names {
                        params.push(n.name.clone());
                    }
                }
                Ok(SVal::Fun(Rc::new(Closure::Lambda {
                    params,
                    body: Rc::new((**body).clone()),
                    ctx: ctx.clone(),
                    name: None,
                })))
            }
            Quantified(q, decls, body) => self.eval_quantifier(ctx, *q, decls, body, e.span),
            Let(decls, body) => {
                let mut m = HashMap::new();
                for d in decls {
                    let v = self.eval(ctx, &d.value)?;
                    m.insert(d.name.name.clone(), v);
                }
                self.eval(&ctx.bind(m), body)
            }
            SetPred(sp) => Ok(SVal::Set(Rc::new(crate::sval::SetRepr::Pred {
                ctx: ctx.clone(),
                var: sp.var.name.clone(),
                pred: sp.pred.clone(),
            }))),
            SetList(es) => {
                let mut vals = Vec::new();
                for x in es {
                    vals.push(self.eval(ctx, x)?);
                }
                Ok(SVal::Set(Rc::new(crate::sval::SetRepr::List(vals))))
            }
            ArrayLit(d, body) => {
                let it = self.resolve_ctype(ctx, &d.ty)?;
                let vals = it.enumerate().ok_or_else(|| {
                    self.err(ctx, e.span, "Finite type expected in array literal index.")
                })?;
                let mut elems = Vec::new();
                for v in vals {
                    let c2 = ctx.bind1(&d.names[0].name, SVal::Ground(v));
                    elems.push(self.eval(&c2, body)?);
                }
                Ok(SVal::Array(Box::new(it), elems))
            }
            RecordLit(entries) => {
                let mut fs = Vec::new();
                for (n, x) in entries {
                    fs.push((n.name.clone(), self.eval(ctx, x)?));
                }
                fs.sort_by(|a, b| a.0.cmp(&b.0));
                Ok(SVal::Record(fs))
            }
            TupleLit(es) => Ok(SVal::Tuple(
                es.iter()
                    .map(|x| self.eval(ctx, x))
                    .collect::<FResult<_>>()?,
            )),
            Conditional {
                cond, then, els, ..
            } => {
                let vc = self.eval(ctx, cond)?;
                match &vc {
                    SVal::Ground(Value::Bool(true)) => self.eval(ctx, then),
                    SVal::Ground(Value::Bool(false)) => self.eval(ctx, els),
                    SVal::Formula(f) => {
                        let vt = self.eval(ctx, then)?;
                        let ve = self.eval(ctx, els)?;
                        let ft = self.to_formula(ctx, vt, then.span)?;
                        let fe = self.to_formula(ctx, ve, els.span)?;
                        Ok(SVal::Formula(TFormula::ite(f.clone(), ft, fe)))
                    }
                    _ => {
                        let fc = vc.to_bool_fexpr().map_err(|m| self.err(ctx, cond.span, m))?;
                        let vt = self.eval(ctx, then)?;
                        let ve = self.eval(ctx, els)?;
                        if matches!(vt, SVal::Formula(_)) || matches!(ve, SVal::Formula(_)) {
                            let ft = self.to_formula(ctx, vt, then.span)?;
                            let fe = self.to_formula(ctx, ve, els.span)?;
                            return Ok(SVal::Formula(TFormula::ite(
                                TFormula::Atom(fc),
                                ft,
                                fe,
                            )));
                        }
                        SVal::ite(&fc, &vt, &ve).map_err(|m| self.err(ctx, e.span, m))
                    }
                }
            }
            ModInit(_) | ModTrans(_) => {
                Err(self.err(ctx, e.span, "INIT_PRED/TRANS_PRED are not supported."))
            }
        }
    }

    pub fn eval_name(&self, ctx: &EvalCtx, n: &Name, span: Span) -> FResult<SVal> {
        if n.ctx.is_none() {
            if let Some(v) = ctx.lookup(&n.id.name) {
                return Ok(v);
            }
            // prelude builtins that are functions/temporal ops
            if let Some(b) = builtin(&n.id.name) {
                return Ok(b);
            }
        }
        let (def_inst, entry) = self.lookup(ctx, n, span)?;
        match entry {
            Entry::Const { value, sem } => {
                // context parameter?
                if let Some(binding) = def_inst.bindings.get(&n.id.name) {
                    match binding {
                        Binding::Expr(bctx, bexpr, _) => {
                            let c2 = ctx.with_inst(bctx.clone());
                            return self.eval(&c2, bexpr);
                        }
                        Binding::Type(..) => {}
                    }
                }
                if let Some(v) = value {
                    let c2 = ctx.with_inst(def_inst.clone());
                    return self.eval(&c2, &v);
                }
                // scalar element?
                if let sal_core::types::SemType::Scalar(tid) = &sem {
                    // find element index from the declaring type
                    if let Some(idx) = self.scalar_elem_index(&def_inst, tid, &n.id.name) {
                        return Ok(SVal::Ground(Value::Scalar(tid.clone(), idx)));
                    }
                    // datatype-like constructors are consts with values;
                    // otherwise fall through
                }
                // datatype constructor/recognizer/accessor?
                if let Some(v) = self.datatype_op(ctx, &def_inst, &n.id.name, span)? {
                    return Ok(v);
                }
                Err(self.err(
                    ctx,
                    span,
                    format!("Uninterpreted constant \"{}\" cannot be evaluated.", n.id.name),
                ))
            }
            Entry::Type { .. } => Err(self.err(
                ctx,
                span,
                format!("Type \"{}\" used as an expression.", n.id.name),
            )),
            _ => Err(self.err(
                ctx,
                span,
                format!("Invalid use of \"{}\" in an expression.", n.id.name),
            )),
        }
    }

    fn scalar_elem_index(
        &self,
        def_inst: &Rc<Instance>,
        tid: &TypeId,
        elem: &str,
    ) -> Option<usize> {
        let symbols = def_inst.symbols.borrow();
        let Entry::Type { scalar_elems, .. } = symbols.get(&tid.name)? else {
            return None;
        };
        let elems = scalar_elems.as_ref()?;
        let idx = elems.iter().position(|x| x == elem)?;
        // register scalar for printing
        self.scalars
            .borrow_mut()
            .entry(TypeId {
                ctx: def_inst.key.clone(),
                name: tid.name.clone(),
            })
            .or_insert_with(|| (Rc::new(elems.clone()), false));
        Some(idx)
    }

    /// Constructor / recognizer / accessor closures for datatype members.
    fn datatype_op(
        &self,
        _ctx: &EvalCtx,
        def_inst: &Rc<Instance>,
        name: &str,
        _span: Span,
    ) -> FResult<Option<SVal>> {
        let symbols = def_inst.symbols.borrow();
        for (tname, entry) in symbols.iter() {
            let Entry::Type {
                datatype: Some(ctors),
                ..
            } = entry
            else {
                continue;
            };
            let tid = TypeId {
                ctx: def_inst.key.clone(),
                name: tname.clone(),
            };
            for (cname, accs) in ctors {
                if name == cname {
                    if accs.is_empty() {
                        return Ok(Some(SVal::Ground(Value::Data(
                            tid.clone(),
                            cname.clone(),
                            vec![],
                        ))));
                    }
                    return Ok(Some(SVal::Fun(Rc::new(Closure::Ctor {
                        ty: tid.clone(),
                        name: cname.clone(),
                        arity: accs.len(),
                    }))));
                }
                if name == format!("{}?", cname) {
                    return Ok(Some(SVal::Fun(Rc::new(Closure::Recognizer {
                        ctor: cname.clone(),
                        dty: CType::Uninterp(tid.clone()),
                    }))));
                }
                if let Some(fi) = accs.iter().position(|(an, _)| an == name) {
                    return Ok(Some(SVal::Fun(Rc::new(Closure::Accessor {
                        ctor: cname.clone(),
                        field_idx: fi,
                        dty: CType::Uninterp(tid.clone()),
                    }))));
                }
            }
        }
        Ok(None)
    }

    // ------------------------------------------------------------------
    // Application and structural operations
    // ------------------------------------------------------------------

    pub fn apply(
        &self,
        ctx: &EvalCtx,
        f: SVal,
        mut args: Vec<SVal>,
        span: Span,
    ) -> FResult<SVal> {
        match f {
            SVal::Fun(cl) => match cl.as_ref() {
                Closure::Lambda {
                    params,
                    body,
                    ctx: cctx,
                    ..
                } => {
                    // multi-arg functions may be applied to a single tuple
                    if params.len() > 1 && args.len() == 1 {
                        if let SVal::Tuple(vs) = args.remove(0) {
                            args = vs;
                        } else {
                            return Err(self.err(ctx, span, "Wrong number of arguments."));
                        }
                    }
                    if params.len() != args.len() {
                        return Err(self.err(ctx, span, "Wrong number of arguments."));
                    }
                    let mut m = HashMap::new();
                    for (p, a) in params.iter().zip(args) {
                        m.insert(p.clone(), a);
                    }
                    self.eval(&cctx.bind(m), body)
                }
                Closure::Ctor { ty, name, arity } => {
                    if args.len() == 1 && *arity > 1 {
                        if let SVal::Tuple(vs) = args.remove(0) {
                            args = vs;
                        }
                    }
                    let mut ground = Vec::new();
                    for a in &args {
                        match a {
                            SVal::Ground(v) => ground.push(v.clone()),
                            _ => {
                                return Err(self.err(
                                    ctx,
                                    span,
                                    "Symbolic datatype construction is not supported.",
                                ))
                            }
                        }
                    }
                    Ok(SVal::Ground(Value::Data(ty.clone(), name.clone(), ground)))
                }
                Closure::Recognizer { ctor, .. } => match &args[0] {
                    SVal::Ground(Value::Data(_, c, _)) => {
                        Ok(SVal::Ground(Value::Bool(c == ctor)))
                    }
                    other => Err(self.err(
                        ctx,
                        span,
                        format!("Cannot apply recognizer to {:?}.", other),
                    )),
                },
                Closure::Accessor {
                    ctor, field_idx, ..
                } => match &args[0] {
                    SVal::Ground(Value::Data(_, c, fields)) if c == ctor => {
                        Ok(SVal::Ground(fields[*field_idx].clone()))
                    }
                    other => Err(self.err(
                        ctx,
                        span,
                        format!("Cannot apply accessor to {:?}.", other),
                    )),
                },
                Closure::RingOp { succ } => self.ring_op(ctx, *succ, &args[0], span),
                Closure::Table { index, elems } => {
                    let idx = if args.len() == 1 {
                        args.remove(0)
                    } else {
                        SVal::Tuple(args)
                    };
                    self.select_indexed(ctx, index, elems, &idx, span)
                }
                Closure::Builtin(name) => self.apply_builtin(ctx, name, args, span),
            },
            SVal::Array(it, elems) => {
                let idx = if args.len() == 1 {
                    args.remove(0)
                } else {
                    SVal::Tuple(args)
                };
                self.select_indexed(ctx, &it, &elems, &idx, span)
            }
            SVal::Ground(Value::Array(_)) => {
                Err(self.err(ctx, span, "Internal: ground array applied directly."))
            }
            SVal::Set(repr) => {
                let idx = if args.len() == 1 {
                    args.remove(0)
                } else {
                    SVal::Tuple(args)
                };
                self.set_member(ctx, &repr, &idx, span)
            }
            other => Err(self.err(
                ctx,
                span,
                format!("Function (array) type expected, found {:?}.", other),
            )),
        }
    }

    /// Membership test for a set value.
    pub fn set_member(
        &self,
        ctx: &EvalCtx,
        repr: &crate::sval::SetRepr,
        v: &SVal,
        span: Span,
    ) -> FResult<SVal> {
        use crate::sval::{BoundKind, SetRepr};
        match repr {
            SetRepr::Pred { ctx: pctx, var, pred } => {
                let c2 = pctx.bind1(var, v.clone());
                self.eval(&c2, pred)
            }
            SetRepr::List(vals) => {
                let mut ds = Vec::new();
                for w in vals {
                    ds.push(v.eq_sval(w).map_err(|m| self.err(ctx, span, m))?);
                }
                Ok(SVal::from_bool_expr(FExpr::or(ds)))
            }
            SetRepr::Bound { kind, bound } => {
                let (fv, _) = self.numeric_fexpr(ctx, v, span)?;
                let e = match kind {
                    BoundKind::UpTo => FExpr::Le(Rc::new(fv), Rc::new(bound.clone())),
                    BoundKind::Below => FExpr::Lt(Rc::new(fv), Rc::new(bound.clone())),
                    BoundKind::Above => FExpr::Lt(Rc::new(bound.clone()), Rc::new(fv)),
                };
                Ok(SVal::from_bool_expr(e))
            }
        }
    }

    fn ring_op(&self, ctx: &EvalCtx, succ: bool, v: &SVal, span: Span) -> FResult<SVal> {
        let shift = |tid: &TypeId, i: usize| -> FResult<usize> {
            let scalars = self.scalars.borrow();
            let (elems, is_ring) = scalars.get(tid).ok_or_else(|| {
                self.err(ctx, span, "rsucc/rpred applied to a non-ringset value.")
            })?;
            if !*is_ring {
                return Err(self.err(ctx, span, "rsucc/rpred applied to a non-ringset value."));
            }
            let n = elems.len();
            Ok(if succ { (i + 1) % n } else { (i + n - 1) % n })
        };
        match v {
            SVal::Ground(Value::Scalar(tid, i)) => Ok(SVal::Ground(Value::Scalar(
                tid.clone(),
                shift(tid, *i)?,
            ))),
            SVal::Sym(e, LeafType::Scalar(tid, elems)) => {
                // build ITE chain over the ring
                let n = elems.len();
                if n == 0 {
                    return Err(self.err(ctx, span, "rsucc/rpred on empty ringset."));
                }
                let mut result = FExpr::Const(Value::Scalar(tid.clone(), shift(tid, n - 1)?));
                for i in (0..n - 1).rev() {
                    let cond = FExpr::eq(e.clone(), FExpr::Const(Value::Scalar(tid.clone(), i)));
                    result = FExpr::ite(
                        cond,
                        FExpr::Const(Value::Scalar(tid.clone(), shift(tid, i)?)),
                        result,
                    );
                }
                Ok(SVal::Sym(result, LeafType::Scalar(tid.clone(), elems.clone())))
            }
            other => Err(self.err(
                ctx,
                span,
                format!("rsucc/rpred applied to {:?}.", other),
            )),
        }
    }

    /// Select from a decomposed array/function by (possibly symbolic) index.
    pub fn select_indexed(
        &self,
        ctx: &EvalCtx,
        index_ty: &CType,
        elems: &[SVal],
        idx: &SVal,
        span: Span,
    ) -> FResult<SVal> {
        match idx {
            SVal::Ground(v) => {
                let i = index_ty.index_of(v).ok_or_else(|| {
                    self.err(ctx, span, format!("Index {} out of bounds.", v))
                })?;
                if i >= elems.len() {
                    return Err(self.err(ctx, span, format!("Index {} out of bounds.", v)));
                }
                Ok(elems[i].clone())
            }
            _ => {
                // symbolic index: ITE chain over the domain
                let vals = index_ty.enumerate().ok_or_else(|| {
                    self.err(ctx, span, "Finite index type expected for symbolic selection.")
                })?;
                if elems.is_empty() {
                    return Err(self.err(ctx, span, "Selection from empty array."));
                }
                let mut result = elems[elems.len() - 1].clone();
                for i in (0..elems.len() - 1).rev() {
                    let cond = idx
                        .eq_sval(&SVal::Ground(vals[i].clone()))
                        .map_err(|m| self.err(ctx, span, m))?;
                    result = SVal::ite(&cond, &elems[i], &result)
                        .map_err(|m| self.err(ctx, span, m))?;
                }
                Ok(result)
            }
        }
    }

    pub fn select(&self, ctx: &EvalCtx, a: SVal, i: SVal, span: Span) -> FResult<SVal> {
        match a {
            SVal::Array(it, elems) => self.select_indexed(ctx, &it, &elems, &i, span),
            SVal::Fun(_) => self.apply(ctx, a, vec![i], span),
            SVal::Set(_) => self.apply(ctx, a, vec![i], span),
            SVal::Ground(Value::Array(_)) => Err(self.err(
                ctx,
                span,
                "Internal: ground array selected directly.",
            )),
            other => Err(self.err(
                ctx,
                span,
                format!("Function (array) type expected, found {:?}.", other),
            )),
        }
    }

    fn update(
        &self,
        ctx: &EvalCtx,
        target: SVal,
        accesses: &[Access],
        value: SVal,
        span: Span,
    ) -> FResult<SVal> {
        if accesses.is_empty() {
            return Ok(value);
        }
        let (first, rest) = accesses.split_first().unwrap();
        match (first, target) {
            (Access::Array(ie), SVal::Array(it, mut elems)) => {
                let iv = self.eval(ctx, ie)?;
                match &iv {
                    SVal::Ground(v) => {
                        let i = it.index_of(v).ok_or_else(|| {
                            self.err(ctx, span, format!("Index {} out of bounds.", v))
                        })?;
                        let inner = self.update(ctx, elems[i].clone(), rest, value, span)?;
                        elems[i] = inner;
                        Ok(SVal::Array(it, elems))
                    }
                    _ => {
                        // symbolic index: update every element under condition
                        let vals = it.enumerate().ok_or_else(|| {
                            self.err(ctx, span, "Finite index type expected.")
                        })?;
                        for (i, v) in vals.iter().enumerate() {
                            let cond = iv
                                .eq_sval(&SVal::Ground(v.clone()))
                                .map_err(|m| self.err(ctx, span, m))?;
                            let updated =
                                self.update(ctx, elems[i].clone(), rest, value.clone(), span)?;
                            elems[i] = SVal::ite(&cond, &updated, &elems[i])
                                .map_err(|m| self.err(ctx, span, m))?;
                        }
                        Ok(SVal::Array(it, elems))
                    }
                }
            }
            (Access::Args(ies), SVal::Array(it, elems)) => {
                let idx = if ies.len() == 1 {
                    self.eval(ctx, &ies[0])?
                } else {
                    SVal::Tuple(
                        ies.iter()
                            .map(|x| self.eval(ctx, x))
                            .collect::<FResult<_>>()?,
                    )
                };
                let acc = Access::Array(Expr {
                    kind: ExprKind::Unbounded,
                    span,
                    parens: 0,
                });
                // reuse array path by inlining: emulate with direct code
                let mut elems = elems;
                match &idx {
                    SVal::Ground(v) => {
                        let i = it.index_of(v).ok_or_else(|| {
                            self.err(ctx, span, format!("Index {} out of bounds.", v))
                        })?;
                        let inner = self.update(ctx, elems[i].clone(), rest, value, span)?;
                        elems[i] = inner;
                        Ok(SVal::Array(it, elems))
                    }
                    _ => {
                        let vals = it.enumerate().ok_or_else(|| {
                            self.err(ctx, span, "Finite index type expected.")
                        })?;
                        for (i, v) in vals.iter().enumerate() {
                            let cond = idx
                                .eq_sval(&SVal::Ground(v.clone()))
                                .map_err(|m| self.err(ctx, span, m))?;
                            let updated =
                                self.update(ctx, elems[i].clone(), rest, value.clone(), span)?;
                            elems[i] = SVal::ite(&cond, &updated, &elems[i])
                                .map_err(|m| self.err(ctx, span, m))?;
                        }
                        let _ = acc;
                        Ok(SVal::Array(it, elems))
                    }
                }
            }
            (Access::Record(f), SVal::Record(mut fs)) => {
                let pos = fs
                    .iter()
                    .position(|(n, _)| n == &f.name)
                    .ok_or_else(|| {
                        self.err(ctx, f.span, format!("Unknown record field \"{}\".", f.name))
                    })?;
                let inner = self.update(ctx, fs[pos].1.clone(), rest, value, span)?;
                fs[pos].1 = inner;
                Ok(SVal::Record(fs))
            }
            (Access::Tuple(i), SVal::Tuple(mut vs)) => {
                let idx = *i as usize;
                if idx < 1 || idx > vs.len() {
                    return Err(self.err(ctx, span, "Tuple index out of bounds."));
                }
                let inner = self.update(ctx, vs[idx - 1].clone(), rest, value, span)?;
                vs[idx - 1] = inner;
                Ok(SVal::Tuple(vs))
            }
            (_, SVal::Ground(gv)) => {
                // lift ground aggregate to structural form, then update
                let lifted = self.lift_ground(ctx, gv, span)?;
                self.update(ctx, lifted, accesses, value, span)
            }
            (_, other) => Err(self.err(
                ctx,
                span,
                format!("Invalid WITH update on {:?}.", other),
            )),
        }
    }

    /// Lift a ground aggregate value into structural SVal form.
    pub fn lift_ground(&self, ctx: &EvalCtx, v: Value, span: Span) -> FResult<SVal> {
        Ok(match v {
            Value::Tuple(vs) => SVal::Tuple(
                vs.into_iter()
                    .map(|x| self.lift_ground(ctx, x, span))
                    .collect::<FResult<_>>()?,
            ),
            Value::Record(fs) => SVal::Record(
                fs.into_iter()
                    .map(|(n, x)| Ok((n, self.lift_ground(ctx, x, span)?)))
                    .collect::<FResult<_>>()?,
            ),
            Value::Array(_) => {
                return Err(self.err(
                    ctx,
                    span,
                    "Internal: array value without index type.",
                ))
            }
            other => SVal::Ground(other),
        })
    }

    fn eval_quantifier(
        &self,
        ctx: &EvalCtx,
        q: Quantifier,
        decls: &[VarDecl],
        body: &Expr,
        span: Span,
    ) -> FResult<SVal> {
        // expand over the finite cartesian product of the bound domains
        let mut vars: Vec<(String, Vec<Value>)> = Vec::new();
        for d in decls {
            let ct = self.resolve_ctype(ctx, &d.ty)?;
            let vals = ct.enumerate().ok_or_else(|| {
                self.err(ctx, span, "Finite type expected in quantifier.")
            })?;
            for n in &d.names {
                vars.push((n.name.clone(), vals.clone()));
            }
        }
        let mut results: Vec<SVal> = Vec::new();
        let mut assignment = vec![0usize; vars.len()];
        'outer: loop {
            let mut m = HashMap::new();
            for (k, (name, vals)) in vars.iter().enumerate() {
                m.insert(name.clone(), SVal::Ground(vals[assignment[k]].clone()));
            }
            results.push(self.eval(&ctx.bind(m), body)?);
            // increment odometer
            for k in (0..vars.len()).rev() {
                assignment[k] += 1;
                if assignment[k] < vars[k].1.len() {
                    continue 'outer;
                }
                assignment[k] = 0;
            }
            break;
        }
        // combine
        if results.iter().any(|r| matches!(r, SVal::Formula(_))) {
            let mut acc: Option<TFormula> = None;
            for r in results {
                let f = self.to_formula(ctx, r, span)?;
                acc = Some(match acc {
                    None => f,
                    Some(a) => {
                        if q == Quantifier::Forall {
                            TFormula::and(a, f)
                        } else {
                            TFormula::or(a, f)
                        }
                    }
                });
            }
            return Ok(SVal::Formula(acc.unwrap_or(TFormula::Atom(FExpr::tt()))));
        }
        let mut es = Vec::new();
        for r in results {
            es.push(r.to_bool_fexpr().map_err(|m| self.err(ctx, span, m))?);
        }
        Ok(SVal::from_bool_expr(if q == Quantifier::Forall {
            FExpr::and(es)
        } else {
            FExpr::or(es)
        }))
    }

    // ------------------------------------------------------------------
    // Operators
    // ------------------------------------------------------------------

    fn eval_binary(
        &self,
        ctx: &EvalCtx,
        op: BinOp,
        a: &Expr,
        b: &Expr,
        span: Span,
    ) -> FResult<SVal> {
        use BinOp::*;
        let va = self.eval(ctx, a)?;
        let vb = self.eval(ctx, b)?;
        match op {
            And | Or | Xor | Implies | Iff => self.eval_bool_op(ctx, op, va, vb, span),
            Eq | Neq => {
                // set membership-style equality is still structural equality
                let eq = va.eq_sval(&vb).map_err(|m| self.err(ctx, span, m))?;
                Ok(SVal::from_bool_expr(if op == Neq {
                    FExpr::not(eq)
                } else {
                    eq
                }))
            }
            Lt | Le | Gt | Ge => {
                if let (SVal::Ground(Value::Num(x)), SVal::Ground(Value::Num(y))) = (&va, &vb) {
                    let r = match op {
                        Lt => x < y,
                        Le => x <= y,
                        Gt => x > y,
                        _ => x >= y,
                    };
                    return Ok(SVal::Ground(Value::Bool(r)));
                }
                let (fa, _) = self.numeric_fexpr(ctx, &va, a.span)?;
                let (fb, _) = self.numeric_fexpr(ctx, &vb, b.span)?;
                let e = match op {
                    Lt => FExpr::Lt(Rc::new(fa), Rc::new(fb)),
                    Le => FExpr::Le(Rc::new(fa), Rc::new(fb)),
                    Gt => FExpr::Lt(Rc::new(fb), Rc::new(fa)),
                    _ => FExpr::Le(Rc::new(fb), Rc::new(fa)),
                };
                Ok(SVal::from_bool_expr(e))
            }
            Plus | Minus | Mult | Div | IDiv | Mod => {
                if let (SVal::Ground(Value::Num(x)), SVal::Ground(Value::Num(y))) = (&va, &vb) {
                    let r = match op {
                        Plus => x + y,
                        Minus => x - y,
                        Mult => x * y,
                        Div => {
                            if y.is_zero() {
                                return Err(self.err(ctx, span, "Division by zero."));
                            }
                            x / y
                        }
                        IDiv | Mod => {
                            if !x.is_integer() || !y.is_integer() || y.is_zero() {
                                return Err(self.err(
                                    ctx,
                                    span,
                                    "DIV/MOD require integer operands and nonzero divisor.",
                                ));
                            }
                            let (xi, yi) = (x.to_integer(), y.to_integer());
                            let (q, r) = euclid(&xi, &yi);
                            BigRational::from_integer(if op == IDiv { q } else { r })
                        }
                        _ => unreachable!(),
                    };
                    return Ok(SVal::Ground(Value::Num(r)));
                }
                let (fa, ta) = self.numeric_fexpr(ctx, &va, a.span)?;
                let (fb, _) = self.numeric_fexpr(ctx, &vb, b.span)?;
                let e = match op {
                    Plus => FExpr::Add(vec![fa, fb]),
                    Minus => FExpr::Add(vec![fa, FExpr::Neg(Rc::new(fb))]),
                    Mult => FExpr::Mul(vec![fa, fb]),
                    Div => FExpr::Div(Rc::new(fa), Rc::new(fb)),
                    IDiv => FExpr::IDiv(Rc::new(fa), Rc::new(fb)),
                    _ => FExpr::Mod(Rc::new(fa), Rc::new(fb)),
                };
                Ok(SVal::Sym(e, ta))
            }
        }
    }

    fn eval_bool_op(
        &self,
        ctx: &EvalCtx,
        op: BinOp,
        va: SVal,
        vb: SVal,
        span: Span,
    ) -> FResult<SVal> {
        use BinOp::*;
        // formula lifting
        if matches!(va, SVal::Formula(_)) || matches!(vb, SVal::Formula(_)) {
            let fa = self.to_formula(ctx, va, span)?;
            let fb = self.to_formula(ctx, vb, span)?;
            let r = match op {
                And => TFormula::and(fa, fb),
                Or => TFormula::or(fa, fb),
                Implies => TFormula::or(TFormula::not(fa), fb),
                Xor => TFormula::or(
                    TFormula::and(fa.clone(), TFormula::not(fb.clone())),
                    TFormula::and(TFormula::not(fa), fb),
                ),
                Iff => TFormula::or(
                    TFormula::and(fa.clone(), fb.clone()),
                    TFormula::and(TFormula::not(fa), TFormula::not(fb)),
                ),
                _ => unreachable!(),
            };
            return Ok(SVal::Formula(r));
        }
        let fa = va.to_bool_fexpr().map_err(|m| self.err(ctx, span, m))?;
        let fb = vb.to_bool_fexpr().map_err(|m| self.err(ctx, span, m))?;
        let e = match op {
            And => FExpr::and(vec![fa, fb]),
            Or => FExpr::or(vec![fa, fb]),
            Implies => FExpr::or(vec![FExpr::not(fa), fb]),
            Xor => FExpr::not(FExpr::eq(fa, fb)),
            Iff => FExpr::eq(fa, fb),
            _ => unreachable!(),
        };
        Ok(SVal::from_bool_expr(e))
    }

    fn not_sval(&self, ctx: &EvalCtx, v: SVal, span: Span) -> FResult<SVal> {
        match v {
            SVal::Formula(f) => Ok(SVal::Formula(TFormula::not(f))),
            other => {
                let e = other.to_bool_fexpr().map_err(|m| self.err(ctx, span, m))?;
                Ok(SVal::from_bool_expr(FExpr::not(e)))
            }
        }
    }

    pub fn to_formula(&self, ctx: &EvalCtx, v: SVal, span: Span) -> FResult<TFormula> {
        match v {
            SVal::Formula(f) => Ok(f),
            other => {
                let e = other.to_bool_fexpr().map_err(|m| self.err(ctx, span, m))?;
                Ok(TFormula::Atom(e))
            }
        }
    }

    fn numeric_fexpr(
        &self,
        ctx: &EvalCtx,
        v: &SVal,
        span: Span,
    ) -> FResult<(FExpr, LeafType)> {
        match v {
            SVal::Ground(Value::Num(n)) => {
                Ok((FExpr::Const(Value::Num(n.clone())), LeafType::Int))
            }
            SVal::Sym(e, t)
                if matches!(
                    t,
                    LeafType::Int | LeafType::Real | LeafType::Range(..)
                ) =>
            {
                Ok((e.clone(), t.clone()))
            }
            other => Err(self.err(
                ctx,
                span,
                format!("Numeric expression expected, found {:?}.", other),
            )),
        }
    }

    fn apply_builtin(
        &self,
        ctx: &EvalCtx,
        name: &str,
        mut args: Vec<SVal>,
        span: Span,
    ) -> FResult<SVal> {
        // unpack single-tuple applications of binary builtins
        let bin_arity: Option<usize> = match name {
            "X" | "G" | "F" | "EX" | "AX" | "EG" | "AG" | "EF" | "AF" | "accepting" => Some(1),
            "U" | "W" | "R" | "M" | "EU" | "AU" | "ER" | "AR" | "min" | "max" | "exp"
            | "nor" | "nand" | "xnor" => Some(2),
            _ => None,
        };
        if let Some(k) = bin_arity {
            if args.len() == 1 && k == 2 {
                if let SVal::Tuple(vs) = args.remove(0) {
                    args = vs;
                } else {
                    return Err(self.err(ctx, span, "Wrong number of arguments."));
                }
            }
            if args.len() != k {
                return Err(self.err(ctx, span, "Wrong number of arguments."));
            }
        }
        macro_rules! f1 {
            ($ctor:ident) => {{
                let a = self.to_formula(ctx, args.remove(0), span)?;
                Ok(SVal::Formula(TFormula::$ctor(Rc::new(a))))
            }};
        }
        macro_rules! f2 {
            ($ctor:ident) => {{
                let b = self.to_formula(ctx, args.remove(1), span)?;
                let a = self.to_formula(ctx, args.remove(0), span)?;
                Ok(SVal::Formula(TFormula::$ctor(Rc::new(a), Rc::new(b))))
            }};
        }
        match name {
            "X" => f1!(X),
            "G" => f1!(G),
            "F" => f1!(F),
            "U" => f2!(U),
            "W" => f2!(W),
            "R" => f2!(R),
            "M" => f2!(M),
            "EX" => f1!(EX),
            "AX" => f1!(AX),
            "EG" => f1!(EG),
            "AG" => f1!(AG),
            "EF" => f1!(EF),
            "AF" => f1!(AF),
            "EU" => f2!(EU),
            "AU" => f2!(AU),
            "ER" => f2!(ER),
            "AR" => f2!(AR),
            "accepting" => {
                let a = self.to_formula(ctx, args.remove(0), span)?;
                Ok(SVal::Formula(a))
            }
            "min" | "max" => {
                let (a, b) = (args.remove(0), args.remove(0));
                if let (SVal::Ground(Value::Num(x)), SVal::Ground(Value::Num(y))) = (&a, &b) {
                    let r = if (name == "min") == (x < y) { x } else { y };
                    return Ok(SVal::Ground(Value::Num(r.clone())));
                }
                let (fa, ta) = self.numeric_fexpr(ctx, &a, span)?;
                let (fb, _) = self.numeric_fexpr(ctx, &b, span)?;
                let cond = if name == "min" {
                    FExpr::Lt(Rc::new(fa.clone()), Rc::new(fb.clone()))
                } else {
                    FExpr::Lt(Rc::new(fb.clone()), Rc::new(fa.clone()))
                };
                Ok(SVal::Sym(FExpr::ite(cond, fa, fb), ta))
            }
            "exp" => {
                let (a, b) = (args.remove(0), args.remove(0));
                match (&a, &b) {
                    (SVal::Ground(Value::Num(x)), SVal::Ground(Value::Num(y)))
                        if y.is_integer() && !y.is_negative() =>
                    {
                        let mut r = BigRational::from_integer(BigInt::from(1));
                        let mut k = y.to_integer();
                        while k > BigInt::zero() {
                            r *= x;
                            k -= 1;
                        }
                        Ok(SVal::Ground(Value::Num(r)))
                    }
                    _ => Err(self.err(ctx, span, "exp requires constant arguments.")),
                }
            }
            "nor" | "nand" | "xnor" => {
                let (a, b) = (args.remove(0), args.remove(0));
                let fa = a.to_bool_fexpr().map_err(|m| self.err(ctx, span, m))?;
                let fb = b.to_bool_fexpr().map_err(|m| self.err(ctx, span, m))?;
                let e = match name {
                    "nor" => FExpr::not(FExpr::or(vec![fa, fb])),
                    "nand" => FExpr::not(FExpr::and(vec![fa, fb])),
                    _ => FExpr::eq(fa, fb),
                };
                Ok(SVal::from_bool_expr(e))
            }
            "rsucc" => self.ring_op(ctx, true, &args[0], span),
            "rpred" => self.ring_op(ctx, false, &args[0], span),
            "dbg_print" | "dbg_expr" => Ok(args.remove(0)),
            "up_to" | "below" | "above" => {
                let bound = args.remove(0);
                let (fb, _) = self.numeric_fexpr(ctx, &bound, span)?;
                let kind = match name {
                    "up_to" => crate::sval::BoundKind::UpTo,
                    "below" => crate::sval::BoundKind::Below,
                    _ => crate::sval::BoundKind::Above,
                };
                Ok(SVal::Set(Rc::new(crate::sval::SetRepr::Bound {
                    kind,
                    bound: fb,
                })))
            }
            "real_pred?" | "int_pred?" | "nat_pred?" => {
                let v = args.remove(0);
                match &v {
                    SVal::Ground(Value::Num(n)) => Ok(SVal::Ground(Value::Bool(
                        match name {
                            "int_pred?" => n.is_integer(),
                            "nat_pred?" => n.is_integer() && !n.is_negative(),
                            _ => true,
                        },
                    ))),
                    _ => Ok(SVal::tt()),
                }
            }
            other => Err(self.err(
                ctx,
                span,
                format!("Builtin \"{}\" is not supported here.", other),
            )),
        }
    }
}

fn n_name(tid: &TypeId) -> String {
    tid.name.clone()
}

/// Euclidean division: quotient/remainder with 0 <= r < |b|.
fn euclid(a: &BigInt, b: &BigInt) -> (BigInt, BigInt) {
    let q = a / b;
    let r = a - &q * b;
    if r.is_negative() {
        if b.is_positive() {
            (q - 1, r + b)
        } else {
            (q + 1, r - b)
        }
    } else {
        (q, r)
    }
}

/// Prelude names that evaluate to builtin function values.
fn builtin(name: &str) -> Option<SVal> {
    const NAMES: &[&str] = &[
        "X", "G", "F", "U", "W", "R", "M", "EX", "AX", "EG", "AG", "EF", "AF", "EU", "AU",
        "ER", "AR", "accepting", "min", "max", "exp", "nor", "nand", "xnor", "rsucc", "rpred",
        "dbg_print", "dbg_expr", "up_to", "below", "above", "real_pred?", "int_pred?",
        "nat_pred?",
    ];
    if NAMES.contains(&name) {
        return Some(SVal::Fun(Rc::new(Closure::Builtin(name.to_string()))));
    }
    match name {
        "true" | "TRUE" => Some(SVal::Ground(Value::Bool(true))),
        "false" | "FALSE" => Some(SVal::Ground(Value::Bool(false))),
        _ => None,
    }
}
