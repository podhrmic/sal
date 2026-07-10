//! Pretty-printer for the SAL AST. The output re-parses to the same AST
//! (round-trip property tested over the whole corpus); it is not intended
//! to reproduce the original layout.

use crate::ast::*;

pub fn print_context(c: &SalContext) -> String {
    let mut p = Printer::new();
    p.context(c);
    p.out
}

pub fn print_expr(e: &Expr) -> String {
    let mut p = Printer::new();
    p.expr(e);
    p.out
}

pub fn print_module(m: &Module) -> String {
    let mut p = Printer::new();
    p.module(m);
    p.out
}

pub fn print_type(t: &Type) -> String {
    let mut p = Printer::new();
    p.ty(t);
    p.out
}

struct Printer {
    out: String,
    indent: usize,
}

impl Printer {
    fn new() -> Self {
        Printer {
            out: String::new(),
            indent: 0,
        }
    }

    fn push(&mut self, s: &str) {
        self.out.push_str(s);
    }

    fn nl(&mut self) {
        self.out.push('\n');
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
    }

    fn sep_by<T>(&mut self, items: &[T], sep: &str, mut f: impl FnMut(&mut Self, &T)) {
        for (i, it) in items.iter().enumerate() {
            if i > 0 {
                self.push(sep);
            }
            f(self, it);
        }
    }

    // -- names ---------------------------------------------------------------

    fn ctx_name(&mut self, c: &ContextName) {
        self.push(&c.name.name);
        if !c.actuals.is_empty() {
            self.push("{");
            let actuals = c.actuals.clone();
            self.sep_by(&actuals, ", ", |p, a| match a {
                Actual::Expr(e) => p.expr(e),
                Actual::Type(t) => p.ty(t),
            });
            self.push("}");
        }
    }

    fn name(&mut self, n: &Name) {
        if let Some(ctx) = &n.ctx {
            self.ctx_name(ctx);
            self.push("!");
        }
        self.push(&n.id.name);
    }

    // -- types ----------------------------------------------------------------

    fn ty(&mut self, t: &Type) {
        match &t.kind {
            TypeKind::Name(n) => self.name(n),
            TypeKind::Subrange(lo, hi) => {
                self.push("[");
                self.expr(lo);
                self.push(" .. ");
                self.expr(hi);
                self.push("]");
            }
            TypeKind::Subtype(sp) => self.set_pred(sp),
            TypeKind::Array(i, e) => {
                self.push("ARRAY ");
                self.ty(i);
                self.push(" OF ");
                self.ty(e);
            }
            TypeKind::Tuple(ts) => {
                self.push("[");
                self.sep_by(ts, ", ", |p, t| p.ty(t));
                self.push("]");
            }
            TypeKind::Function(d, r) => {
                self.push("[");
                self.ty(d);
                self.push(" -> ");
                self.ty(r);
                self.push("]");
            }
            TypeKind::Record(fs) => {
                self.push("[# ");
                self.sep_by(fs, ", ", |p, f| {
                    p.push(&f.name.name);
                    p.push(": ");
                    p.ty(&f.ty);
                });
                self.push(" #]");
            }
            TypeKind::State(m) => {
                self.push("STATE_TYPE(");
                self.module(m);
                self.push(")");
            }
        }
    }

    fn set_pred(&mut self, sp: &SetPred) {
        self.push("{");
        self.push(&sp.var.name);
        self.push(" : ");
        self.ty(&sp.ty);
        self.push(" | ");
        self.expr(&sp.pred);
        self.push("}");
    }

    fn var_decls(&mut self, ds: &[VarDecl]) {
        self.sep_by(ds, ", ", |p, d| {
            let names: Vec<&str> = d.names.iter().map(|i| i.name.as_str()).collect();
            p.push(&names.join(", "));
            p.push(" : ");
            p.ty(&d.ty);
        });
    }

    // -- expressions -----------------------------------------------------------

    fn expr(&mut self, e: &Expr) {
        for _ in 0..e.parens {
            self.push("(");
        }
        self.expr_kind(&e.kind);
        for _ in 0..e.parens {
            self.push(")");
        }
    }

    fn expr_kind(&mut self, k: &ExprKind) {
        match k {
            ExprKind::Name(n) => self.name(n),
            ExprKind::Next(id) => {
                self.push(&id.name);
                self.push("'");
            }
            ExprKind::Numeral(s) => self.push(s),
            ExprKind::Float { numer, denom } => {
                // reconstruct `n.d`: denom is 1 followed by d-length zeros
                let dlen = denom.len() - 1;
                let (int_part, frac) = numer.split_at(numer.len().saturating_sub(dlen));
                let int_part = if int_part.is_empty() { "0" } else { int_part };
                self.push(int_part);
                self.push(".");
                self.push(frac);
            }
            ExprKind::Str(s) => {
                self.push("\"");
                self.push(s);
                self.push("\"");
            }
            ExprKind::Binary(op, a, b) => {
                self.expr_prec(a, prec_of(*op), false);
                self.push(" ");
                self.push(op.name());
                self.push(" ");
                self.expr_prec(b, prec_of(*op), true);
            }
            ExprKind::Unary(op, a) => {
                match op {
                    UnOp::Not => {
                        self.push("NOT ");
                        // NOT operand binds at >= comparison level
                        self.expr_prec(a, 50, true);
                    }
                    UnOp::Minus => {
                        self.push("-");
                        self.expr_prec(a, 85, true);
                    }
                }
            }
            ExprKind::App(f, args) => {
                self.expr_prec(f, 100, false);
                self.push("(");
                self.sep_by(args, ", ", |p, a| p.expr(a));
                self.push(")");
            }
            ExprKind::ArraySelect(a, i) => {
                self.expr_prec(a, 100, false);
                self.push("[");
                self.expr(i);
                self.push("]");
            }
            ExprKind::RecordSelect(r, f) => {
                self.expr_prec(r, 100, false);
                self.push(".");
                self.push(&f.name);
            }
            ExprKind::TupleSelect(t, i) => {
                self.expr_prec(t, 100, false);
                self.push(".");
                self.push(&i.to_string());
            }
            ExprKind::Update {
                target,
                accesses,
                value,
            } => {
                self.expr_prec(target, 60, false);
                self.push(" WITH ");
                for a in accesses {
                    self.access(a);
                }
                self.push(" := ");
                self.expr_prec(value, 61, true);
            }
            ExprKind::Lambda(decls, body) => {
                self.push("LAMBDA (");
                self.var_decls(decls);
                self.push("): ");
                self.expr(body);
            }
            ExprKind::Quantified(q, decls, body) => {
                self.push(match q {
                    Quantifier::Forall => "FORALL (",
                    Quantifier::Exists => "EXISTS (",
                });
                self.var_decls(decls);
                self.push("): ");
                self.expr(body);
            }
            ExprKind::Let(decls, body) => {
                self.push("LET ");
                self.sep_by(decls, ", ", |p, d| {
                    p.push(&d.name.name);
                    p.push(" : ");
                    p.ty(&d.ty);
                    p.push(" = ");
                    p.expr(&d.value);
                });
                self.push(" IN ");
                self.expr(body);
            }
            ExprKind::SetPred(sp) => self.set_pred(sp),
            ExprKind::SetList(es) => {
                self.push("{");
                self.sep_by(es, ", ", |p, e| p.expr(e));
                self.push("}");
            }
            ExprKind::ArrayLit(d, body) => {
                self.push("[[");
                self.push(&d.names[0].name);
                self.push(" : ");
                self.ty(&d.ty);
                self.push("] ");
                self.expr(body);
                self.push("]");
            }
            ExprKind::RecordLit(entries) => {
                self.push("(# ");
                self.sep_by(entries, ", ", |p, (id, e)| {
                    p.push(&id.name);
                    p.push(" := ");
                    p.expr(e);
                });
                self.push(" #)");
            }
            ExprKind::TupleLit(es) => {
                self.push("(");
                self.sep_by(es, ", ", |p, e| p.expr(e));
                self.push(")");
            }
            ExprKind::Conditional {
                cond,
                then,
                els,
                is_elsif: _,
            } => {
                self.push("IF ");
                self.expr(cond);
                self.push(" THEN ");
                self.expr(then);
                self.cond_tail(els);
                self.push(" ENDIF");
            }
            ExprKind::ModInit(m) => {
                self.push("INIT_PRED(");
                self.module(m);
                self.push(")");
            }
            ExprKind::ModTrans(m) => {
                self.push("TRANS_PRED(");
                self.module(m);
                self.push(")");
            }
            ExprKind::Unbounded => self.push("_"),
        }
    }

    fn cond_tail(&mut self, els: &Expr) {
        if let ExprKind::Conditional {
            cond,
            then,
            els: inner,
            is_elsif: true,
        } = &els.kind
        {
            if els.parens == 0 {
                self.push(" ELSIF ");
                self.expr(cond);
                self.push(" THEN ");
                self.expr(then);
                self.cond_tail(inner);
                return;
            }
        }
        self.push(" ELSE ");
        self.expr(els);
    }

    /// Print a subexpression, adding parens when its top-level operator
    /// binds looser than the context requires. (Explicit source parens are
    /// preserved via `parens`; this adds the structurally necessary ones.)
    fn expr_prec(&mut self, e: &Expr, min: u8, is_rhs: bool) {
        let needs = e.parens == 0 && expr_binding(e).map_or(false, |(bp, right)| {
            bp < min || (bp == min && (right != is_rhs))
        });
        if needs {
            self.push("(");
        }
        self.expr(e);
        if needs {
            self.push(")");
        }
    }

    fn access(&mut self, a: &Access) {
        match a {
            Access::Array(e) => {
                self.push("[");
                self.expr(e);
                self.push("]");
            }
            Access::Record(id) => {
                self.push(".");
                self.push(&id.name);
            }
            Access::Tuple(i) => {
                self.push(".");
                self.push(&i.to_string());
            }
            Access::Args(es) => {
                self.push("(");
                self.sep_by(es, ", ", |p, e| p.expr(e));
                self.push(")");
            }
        }
    }

    // -- modules ----------------------------------------------------------------

    fn module(&mut self, m: &Module) {
        for _ in 0..m.parens {
            self.push("(");
        }
        match &m.kind {
            ModuleKind::Instance(n, actuals) => {
                self.name(n);
                if !actuals.is_empty() {
                    self.push("[");
                    self.sep_by(actuals, ", ", |p, e| p.expr(e));
                    self.push("]");
                }
            }
            ModuleKind::Sync(a, b) => {
                self.mod_prec(a, 2, false);
                self.push(" || ");
                self.mod_prec(b, 2, true);
            }
            ModuleKind::Async(a, b) => {
                self.mod_prec(a, 1, false);
                self.push(" [] ");
                self.mod_prec(b, 1, true);
            }
            ModuleKind::MultiSync(d, m) => {
                self.push("(|| (");
                self.push(&d.names[0].name);
                self.push(" : ");
                self.ty(&d.ty);
                self.push("): ");
                self.module(m);
                self.push(")");
            }
            ModuleKind::MultiAsync(d, m) => {
                self.push("([] (");
                self.push(&d.names[0].name);
                self.push(" : ");
                self.ty(&d.ty);
                self.push("): ");
                self.module(m);
                self.push(")");
            }
            ModuleKind::Hide(ids, m) => {
                self.push("LOCAL ");
                let names: Vec<&str> = ids.iter().map(|i| i.name.as_str()).collect();
                self.push(&names.join(", "));
                self.push(" IN ");
                self.module(m);
            }
            ModuleKind::NewOutput(ids, m) => {
                self.push("OUTPUT ");
                let names: Vec<&str> = ids.iter().map(|i| i.name.as_str()).collect();
                self.push(&names.join(", "));
                self.push(" IN ");
                self.module(m);
            }
            ModuleKind::Rename(renames, m) => {
                self.push("RENAME ");
                self.sep_by(renames, ", ", |p, (a, b)| {
                    p.lhs(a);
                    p.push(" TO ");
                    p.lhs(b);
                });
                self.push(" IN ");
                self.module(m);
            }
            ModuleKind::With(decls, m) => {
                self.push("WITH ");
                self.sep_by(decls, "; ", |p, d| {
                    p.push(match d.class {
                        VarClass::Input => "INPUT ",
                        VarClass::Output => "OUTPUT ",
                        VarClass::Global => "GLOBAL ",
                        VarClass::Local => "LOCAL ",
                    });
                    p.var_decls(&d.decls);
                });
                self.push(" ");
                self.module(m);
            }
            ModuleKind::Observe(a, b) => {
                self.push("OBSERVE ");
                self.mod_prec(a, 1, false);
                self.push(" WITH ");
                self.module(b);
            }
            ModuleKind::Base(b) => self.base_module(b),
        }
        for _ in 0..m.parens {
            self.push(")");
        }
    }

    /// Module precedence: prefix forms 0, [] is 1, || is 2, primary 3.
    fn mod_prec(&mut self, m: &Module, min: u8, is_rhs: bool) {
        let bp = match &m.kind {
            ModuleKind::Async(..) => Some(1),
            ModuleKind::Sync(..) => Some(2),
            ModuleKind::Hide(..)
            | ModuleKind::NewOutput(..)
            | ModuleKind::Rename(..)
            | ModuleKind::With(..)
            | ModuleKind::Observe(..) => Some(0),
            _ => None,
        };
        let needs = m.parens == 0 && bp.map_or(false, |bp| bp < min || (bp == min && is_rhs));
        if needs {
            self.push("(");
        }
        self.module(m);
        if needs {
            self.push(")");
        }
    }

    fn lhs(&mut self, l: &Lhs) {
        self.push(&l.base.name);
        if l.next {
            self.push("'");
        }
        let accesses = l.accesses.clone();
        for a in &accesses {
            self.access(a);
        }
    }

    fn base_module(&mut self, b: &BaseModule) {
        self.push("BEGIN");
        self.indent += 1;
        for d in &b.decls {
            self.nl();
            match d {
                BaseDecl::Vars(class, decls) => {
                    self.push(match class {
                        VarClass::Input => "INPUT ",
                        VarClass::Output => "OUTPUT ",
                        VarClass::Global => "GLOBAL ",
                        VarClass::Local => "LOCAL ",
                    });
                    self.var_decls(decls);
                }
                BaseDecl::Definition(defs) => {
                    self.push("DEFINITION");
                    self.indent += 1;
                    for (i, def) in defs.iter().enumerate() {
                        self.nl();
                        self.definition(def);
                        if i + 1 < defs.len() {
                            self.push(";");
                        }
                    }
                    self.indent -= 1;
                }
                BaseDecl::Initialization(items) => {
                    self.push("INITIALIZATION");
                    self.def_or_commands(items);
                }
                BaseDecl::Transition(items) => {
                    self.push("TRANSITION");
                    self.def_or_commands(items);
                }
            }
        }
        self.indent -= 1;
        self.nl();
        self.push("END");
    }

    fn def_or_commands(&mut self, items: &[DefOrCommand]) {
        self.indent += 1;
        for (i, it) in items.iter().enumerate() {
            self.nl();
            match it {
                DefOrCommand::Def(d) => self.definition(d),
                DefOrCommand::Commands(cmds, _) => {
                    self.push("[");
                    self.indent += 1;
                    for (j, c) in cmds.iter().enumerate() {
                        self.nl();
                        if j > 0 {
                            self.push("[] ");
                        }
                        self.some_command(c);
                    }
                    self.indent -= 1;
                    self.nl();
                    self.push("]");
                }
            }
            if i + 1 < items.len() {
                self.push(";");
            }
        }
        self.indent -= 1;
    }

    fn definition(&mut self, d: &Definition) {
        match d {
            Definition::Simple(s) => {
                self.lhs(&s.lhs);
                match &s.rhs {
                    Rhs::Expr(e) => {
                        self.push(" = ");
                        self.expr(e);
                    }
                    Rhs::Selection(e) => {
                        self.push(" IN ");
                        self.expr(e);
                    }
                }
            }
            Definition::Forall(decls, defs) => {
                self.push("(FORALL (");
                self.var_decls(decls);
                self.push("): ");
                let defs2 = defs.clone();
                self.sep_by(&defs2, "; ", |p, d| p.definition(d));
                self.push(")");
            }
        }
    }

    fn some_command(&mut self, c: &SomeCommand) {
        match c {
            SomeCommand::Guarded(g) => {
                if let Some(l) = &g.label {
                    self.push(&l.name);
                    self.push(": ");
                }
                match &g.guard {
                    Some(e) => self.expr(e),
                    None => self.push("ELSE"),
                }
                self.push(" -->");
                if !g.assignments.is_empty() {
                    self.push(" ");
                    let assigns = g.assignments.clone();
                    self.sep_by(&assigns, "; ", |p, d| p.definition(d));
                }
            }
            SomeCommand::Multi(decls, inner, _) => {
                self.push("([] (");
                self.var_decls(decls);
                self.push("): ");
                self.some_command(inner);
                self.push(")");
            }
        }
    }

    // -- declarations & contexts ---------------------------------------------

    fn context(&mut self, c: &SalContext) {
        self.push(&c.name.name);
        if !c.params.is_empty() {
            self.push("{");
            let params = c.params.clone();
            self.sep_by(&params, "; ", |p, param| match param {
                CtxParam::Types(ids) => {
                    let names: Vec<&str> = ids.iter().map(|i| i.name.as_str()).collect();
                    p.push(&names.join(", "));
                    p.push(" : TYPE");
                }
                CtxParam::Vars(ids, ty) => {
                    let names: Vec<&str> = ids.iter().map(|i| i.name.as_str()).collect();
                    p.push(&names.join(", "));
                    p.push(" : ");
                    p.ty(ty);
                }
            });
            self.push("}");
        }
        self.push(": CONTEXT =");
        self.nl();
        self.push("BEGIN");
        self.indent += 1;
        for d in &c.decls {
            self.nl();
            self.decl(d);
            self.push(";");
        }
        self.indent -= 1;
        self.nl();
        self.push("END");
        self.nl();
    }

    fn decl(&mut self, d: &Decl) {
        match d {
            Decl::Type { name, def } => {
                self.push(&name.name);
                self.push(" : TYPE");
                if let Some(def) = def {
                    self.push(" = ");
                    match def {
                        TypeDef::Type(t) => self.ty(t),
                        TypeDef::Scalar(ids) => {
                            self.push("{");
                            let names: Vec<&str> = ids.iter().map(|i| i.name.as_str()).collect();
                            self.push(&names.join(", "));
                            self.push("}");
                        }
                        TypeDef::Datatype(ctors) => {
                            self.push("DATATYPE ");
                            let cs = ctors.clone();
                            self.sep_by(&cs, ", ", |p, c| {
                                p.push(&c.name.name);
                                if !c.accessors.is_empty() {
                                    p.push("(");
                                    p.var_decls(&c.accessors);
                                    p.push(")");
                                }
                            });
                            self.push(" END");
                        }
                        TypeDef::Scalarset(e) => {
                            self.push("SCALARSET(");
                            self.expr(e);
                            self.push(")");
                        }
                        TypeDef::Ringset(e) => {
                            self.push("RINGSET(");
                            self.expr(e);
                            self.push(")");
                        }
                    }
                }
            }
            Decl::Constant {
                name,
                args,
                ty,
                value,
            } => {
                self.push(&name.name);
                if !args.is_empty() {
                    self.push("(");
                    self.var_decls(args);
                    self.push(")");
                }
                self.push(" : ");
                self.ty(ty);
                if let Some(v) = value {
                    self.push(" = ");
                    self.expr(v);
                }
            }
            Decl::Context { name, ctx } => {
                self.push(&name.name);
                self.push(" : CONTEXT = ");
                self.ctx_name(ctx);
            }
            Decl::Module { name, params, body } => {
                self.push(&name.name);
                if !params.is_empty() {
                    self.push("[");
                    self.var_decls(params);
                    self.push("]");
                }
                self.push(" : MODULE =");
                self.indent += 1;
                self.nl();
                self.module(body);
                self.indent -= 1;
            }
            Decl::Assertion { name, form, body } => {
                self.push(&name.name);
                self.push(match form {
                    AssertionForm::Obligation => " : OBLIGATION ",
                    AssertionForm::Claim => " : CLAIM ",
                    AssertionForm::Lemma => " : LEMMA ",
                    AssertionForm::Theorem => " : THEOREM ",
                });
                match body {
                    AssertionExpr::Models { module, formula } => {
                        self.module(module);
                        self.push(" |- ");
                        self.expr(formula);
                    }
                    AssertionExpr::Implements {
                        concrete,
                        abstract_,
                    } => {
                        self.module(concrete);
                        self.push(" IMPLEMENTS ");
                        self.module(abstract_);
                    }
                }
            }
            Decl::Import { ctx, renames } => {
                self.push("IMPORTING ");
                self.ctx_name(ctx);
                if !renames.is_empty() {
                    self.push(" WITH ");
                    let rs = renames.clone();
                    self.sep_by(&rs, ", ", |p, (a, b)| {
                        p.push(&a.name);
                        p.push(" TO ");
                        p.push(&b.name);
                    });
                }
            }
        }
    }
}

fn prec_of(op: BinOp) -> u8 {
    match op {
        BinOp::Mult | BinOp::Div | BinOp::IDiv | BinOp::Mod => 80,
        BinOp::Plus | BinOp::Minus => 70,
        BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 55,
        BinOp::And => 45,
        BinOp::Or => 40,
        BinOp::Xor => 35,
        BinOp::Implies => 30,
        BinOp::Iff => 25,
    }
}

/// Binding power of an expression's top-level operator, if it has one.
/// Returns (bp, right_assoc).
fn expr_binding(e: &Expr) -> Option<(u8, bool)> {
    match &e.kind {
        ExprKind::Binary(op, ..) => Some((prec_of(*op), matches!(op, BinOp::Implies))),
        ExprKind::Unary(UnOp::Not, _) => Some((50, false)),
        ExprKind::Unary(UnOp::Minus, _) => Some((85, false)),
        ExprKind::Update { .. } => Some((60, false)),
        // These extend maximally to the right; parenthesize when nested in
        // any operator context.
        ExprKind::Lambda(..)
        | ExprKind::Quantified(..)
        | ExprKind::Let(..) => Some((0, false)),
        ExprKind::Conditional { .. } => None, // delimited by IF/ENDIF
        _ => None,
    }
}
