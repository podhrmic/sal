//! SMT-based bounded model checking over infinite-state systems
//! (sal-inf-bmc): emits SMT-LIB2 and drives an external solver
//! (z3 / yices-smt2 / cvc5).

use std::collections::HashMap;
use std::fmt::Write as _;
use std::process::Command;

use num_traits::Signed;

use sal_flat::fexpr::{FExpr, LeafType};
use sal_flat::flatten::{FlatModule, TransNode};
use sal_flat::value::Value;

use crate::bounded::{BoolAlg, BoundedLtl};
use crate::explicit::EngineError;

type EResult<T> = Result<T, EngineError>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sort {
    B,
    I,
    R,
}

#[derive(Debug, Clone)]
struct Term(String, Sort);

pub struct SmtEnc<'m> {
    pub flat: &'m FlatModule,
    decls: Vec<String>,
    defs: Vec<String>,
    /// domain assertions per declared step
    declared_steps: std::collections::BTreeSet<usize>,
    aux: u32,
    cache: HashMap<(FExpr, usize, usize), Term>,
}

fn leaf_sort(t: &LeafType) -> Sort {
    match t {
        LeafType::Bool => Sort::B,
        LeafType::Real => Sort::R,
        _ => Sort::I,
    }
}

fn sym(l: usize, t: usize) -> String {
    format!("s{}_l{}", t, l)
}

impl<'m> SmtEnc<'m> {
    pub fn new(flat: &'m FlatModule) -> Self {
        SmtEnc {
            flat,
            decls: Vec::new(),
            defs: Vec::new(),
            declared_steps: Default::default(),
            aux: 0,
            cache: HashMap::new(),
        }
    }

    /// Ensure the state variables of step `t` are declared, with domain
    /// constraints; returns the conjunction of the domain assertions.
    pub fn declare_step(&mut self, t: usize) -> String {
        if self.declared_steps.contains(&t) {
            return "true".into();
        }
        self.declared_steps.insert(t);
        let mut dom = Vec::new();
        for (l, leaf) in self.flat.leaves.iter().enumerate() {
            let s = sym(l, t);
            let sort = match leaf_sort(&leaf.ty) {
                Sort::B => "Bool",
                Sort::I => "Int",
                Sort::R => "Real",
            };
            self.decls.push(format!("(declare-const {} {})", s, sort));
            match &leaf.ty {
                LeafType::Range(lo, hi) => {
                    dom.push(format!("(<= {} {})", lit_int(lo), s));
                    dom.push(format!("(<= {} {})", s, lit_int(hi)));
                }
                LeafType::Scalar(_, elems) => {
                    dom.push(format!("(<= 0 {})", s));
                    dom.push(format!("(< {} {})", s, elems.len()));
                }
                LeafType::Int { min, max } => {
                    if let Some(m) = min {
                        dom.push(format!("(<= {} {})", lit_int(m), s));
                    }
                    if let Some(m) = max {
                        dom.push(format!("(<= {} {})", s, lit_int(m)));
                    }
                }
                _ => {}
            }
        }
        if dom.is_empty() {
            "true".into()
        } else {
            format!("(and {})", dom.join(" "))
        }
    }

    fn fresh_bool(&mut self, def: String) -> Term {
        self.aux += 1;
        let name = format!("aux{}", self.aux);
        self.defs
            .push(format!("(define-fun {} () Bool {})", name, def));
        Term(name, Sort::B)
    }

    fn coerce_real(&self, t: &Term) -> String {
        match t.1 {
            Sort::I => format!("(to_real {})", t.0),
            _ => t.0.clone(),
        }
    }

    fn num_pair(&self, a: &Term, b: &Term) -> (String, String) {
        if a.1 == b.1 {
            (a.0.clone(), b.0.clone())
        } else {
            (self.coerce_real(a), self.coerce_real(b))
        }
    }

    fn enc(&mut self, e: &FExpr, cur: usize, next: usize) -> EResult<Term> {
        use FExpr::*;
        let key = (e.clone(), cur, next);
        if let Some(t) = self.cache.get(&key) {
            return Ok(t.clone());
        }
        let r = match e {
            Const(v) => value_term(v)?,
            Var(l, primed) => {
                let t = if *primed { next } else { cur };
                Term(
                    sym(*l as usize, t),
                    leaf_sort(&self.flat.leaves[*l as usize].ty),
                )
            }
            Not(a) => {
                let x = self.enc(a, cur, next)?;
                Term(format!("(not {})", x.0), Sort::B)
            }
            And(es) => {
                let mut parts = Vec::new();
                for x in es {
                    parts.push(self.enc(x, cur, next)?.0);
                }
                Term(format!("(and {})", parts.join(" ")), Sort::B)
            }
            Or(es) => {
                let mut parts = Vec::new();
                for x in es {
                    parts.push(self.enc(x, cur, next)?.0);
                }
                Term(format!("(or {})", parts.join(" ")), Sort::B)
            }
            Ite(c, t, f) => {
                let ec = self.enc(c, cur, next)?;
                let et = self.enc(t, cur, next)?;
                let ef = self.enc(f, cur, next)?;
                let (a, b) = self.num_pair(&et, &ef);
                let sort = if et.1 == ef.1 { et.1 } else { Sort::R };
                Term(format!("(ite {} {} {})", ec.0, a, b), sort)
            }
            Eq(a, b) => {
                let ea = self.enc(a, cur, next)?;
                let eb = self.enc(b, cur, next)?;
                let (x, y) = self.num_pair(&ea, &eb);
                Term(format!("(= {} {})", x, y), Sort::B)
            }
            Lt(a, b) | Le(a, b) => {
                let op = if matches!(e, Lt(..)) { "<" } else { "<=" };
                let ea = self.enc(a, cur, next)?;
                let eb = self.enc(b, cur, next)?;
                let (x, y) = self.num_pair(&ea, &eb);
                Term(format!("({} {} {})", op, x, y), Sort::B)
            }
            Add(es) => {
                let mut ts = Vec::new();
                for x in es {
                    ts.push(self.enc(x, cur, next)?);
                }
                let target = if ts.iter().any(|t| t.1 == Sort::R) {
                    Sort::R
                } else {
                    Sort::I
                };
                let parts: Vec<String> = ts
                    .iter()
                    .map(|t| {
                        if target == Sort::R {
                            self.coerce_real(t)
                        } else {
                            t.0.clone()
                        }
                    })
                    .collect();
                Term(format!("(+ {})", parts.join(" ")), target)
            }
            Mul(es) => {
                let mut ts = Vec::new();
                for x in es {
                    ts.push(self.enc(x, cur, next)?);
                }
                let target = if ts.iter().any(|t| t.1 == Sort::R) {
                    Sort::R
                } else {
                    Sort::I
                };
                let parts: Vec<String> = ts
                    .iter()
                    .map(|t| {
                        if target == Sort::R {
                            self.coerce_real(t)
                        } else {
                            t.0.clone()
                        }
                    })
                    .collect();
                Term(format!("(* {})", parts.join(" ")), target)
            }
            Neg(a) => {
                let x = self.enc(a, cur, next)?;
                Term(format!("(- {})", x.0), x.1)
            }
            Div(a, b) => {
                let ea = self.enc(a, cur, next)?;
                let eb = self.enc(b, cur, next)?;
                Term(
                    format!("(/ {} {})", self.coerce_real(&ea), self.coerce_real(&eb)),
                    Sort::R,
                )
            }
            IDiv(a, b) => {
                let ea = self.enc(a, cur, next)?;
                let eb = self.enc(b, cur, next)?;
                Term(format!("(div {} {})", ea.0, eb.0), Sort::I)
            }
            Mod(a, b) => {
                let ea = self.enc(a, cur, next)?;
                let eb = self.enc(b, cur, next)?;
                Term(format!("(mod {} {})", ea.0, eb.0), Sort::I)
            }
        };
        // name large boolean terms to keep the script small
        let r = if r.1 == Sort::B && r.0.len() > 400 {
            self.fresh_bool(r.0)
        } else {
            r
        };
        self.cache.insert(key, r.clone());
        Ok(r)
    }

    pub fn enc_bool(&mut self, e: &FExpr, cur: usize, next: usize) -> EResult<String> {
        let t = self.enc(e, cur, next)?;
        Ok(t.0)
    }

    pub fn init(&mut self) -> EResult<String> {
        let mut cs = vec![self.declare_step(0)];
        for i in &self.flat.invariants.clone() {
            cs.push(self.enc_bool(i, 0, 0)?);
        }
        for d in &self.flat.init_defs.clone() {
            cs.push(self.enc_bool(d, 0, 0)?);
        }
        for block in &self.flat.init_choices.clone() {
            let mut alts = Vec::new();
            for cmd in block {
                let g = self.enc_bool(&cmd.guard, 0, 0)?;
                let c = self.enc_bool(&cmd.constraint, 0, 0)?;
                alts.push(format!("(and {} {})", g, c));
            }
            cs.push(format!("(or {})", alts.join(" ")));
        }
        Ok(format!("(and {})", cs.join(" ")))
    }

    pub fn trans(&mut self, cur: usize, next: usize) -> EResult<String> {
        let d1 = self.declare_step(cur);
        let d2 = self.declare_step(next);
        let node = self.flat.trans.clone();
        let mut cs = vec![d1, d2, self.enc_trans_node(&node, cur, next)?];
        for d in &self.flat.trans_defs.clone() {
            cs.push(self.enc_bool(d, cur, next)?);
        }
        for i in &self.flat.invariants.clone() {
            cs.push(self.enc_bool(i, next, next)?);
        }
        Ok(format!("(and {})", cs.join(" ")))
    }

    fn enc_trans_node(&mut self, node: &TransNode, cur: usize, next: usize) -> EResult<String> {
        Ok(match node {
            TransNode::True => "true".into(),
            TransNode::Cmds(cmds) => {
                let mut alts = Vec::new();
                for cmd in cmds {
                    let g = self.enc_bool(&cmd.guard, cur, next)?;
                    let c = self.enc_bool(&cmd.constraint, cur, next)?;
                    alts.push(format!("(and {} {})", g, c));
                }
                format!("(or {})", alts.join(" "))
            }
            TransNode::All(nodes) => {
                let mut cs = Vec::new();
                for n in nodes {
                    cs.push(self.enc_trans_node(n, cur, next)?);
                }
                format!("(and {})", cs.join(" "))
            }
            TransNode::Interleave(branches) => {
                let mut alts = Vec::new();
                for (n, frame) in branches {
                    let e = self.enc_trans_node(n, cur, next)?;
                    let f = self.enc_bool(frame, cur, next)?;
                    alts.push(format!("(and {} {})", e, f));
                }
                format!("(or {})", alts.join(" "))
            }
        })
    }

    pub fn state_eq(&mut self, s: usize, t: usize) -> String {
        let d1 = self.declare_step(s);
        let d2 = self.declare_step(t);
        let mut cs = vec![d1, d2];
        for l in 0..self.flat.leaves.len() {
            cs.push(format!("(= {} {})", sym(l, s), sym(l, t)));
        }
        format!("(and {})", cs.join(" "))
    }

    /// Build the final script.
    pub fn script(&self, assertion: &str) -> String {
        let mut s = String::new();
        let _ = writeln!(s, "(set-logic ALL)");
        for d in &self.decls {
            let _ = writeln!(s, "{}", d);
        }
        for d in &self.defs {
            let _ = writeln!(s, "{}", d);
        }
        let _ = writeln!(s, "(assert {})", assertion);
        let _ = writeln!(s, "(check-sat)");
        s
    }

    pub fn value_query(&self, steps: usize) -> String {
        let mut names = Vec::new();
        for t in 0..=steps {
            for l in 0..self.flat.leaves.len() {
                names.push(sym(l, t));
            }
        }
        format!("(get-value ({}))", names.join(" "))
    }
}

fn lit_int(i: &num_bigint::BigInt) -> String {
    if i.is_negative() {
        format!("(- {})", i.magnitude())
    } else {
        i.to_string()
    }
}

fn value_term(v: &Value) -> EResult<Term> {
    Ok(match v {
        Value::Bool(b) => Term(b.to_string(), Sort::B),
        Value::Num(n) => {
            if n.is_integer() {
                Term(lit_int(&n.to_integer()), Sort::I)
            } else {
                let num = n.numer();
                let den = n.denom();
                Term(
                    format!("(/ {} {})", lit_int(num), lit_int(den)),
                    Sort::R,
                )
            }
        }
        Value::Scalar(_, i) => Term(i.to_string(), Sort::I),
        other => {
            return Err(EngineError::Eval(format!(
                "cannot encode value {} for SMT",
                other
            )))
        }
    })
}

/// Adapter for the shared bounded-LTL expansion.
pub struct SmtAlg<'a, 'm> {
    pub enc: &'a mut SmtEnc<'m>,
}

impl<'a, 'm> BoolAlg for SmtAlg<'a, 'm> {
    type B = String;

    fn tt(&mut self) -> String {
        "true".into()
    }

    fn ff(&mut self) -> String {
        "false".into()
    }

    fn and(&mut self, xs: Vec<String>) -> String {
        match xs.len() {
            0 => "true".into(),
            1 => xs.into_iter().next().unwrap(),
            _ => format!("(and {})", xs.join(" ")),
        }
    }

    fn or(&mut self, xs: Vec<String>) -> String {
        match xs.len() {
            0 => "false".into(),
            1 => xs.into_iter().next().unwrap(),
            _ => format!("(or {})", xs.join(" ")),
        }
    }

    fn not(&mut self, x: String) -> String {
        format!("(not {})", x)
    }

    fn atom(&mut self, e: &FExpr, t: usize) -> String {
        let _ = self.enc.declare_step(t);
        self.enc.enc_bool(e, t, t).expect("atom encoding failed")
    }
}

/// Run a solver on a script; returns Some(model-output) if sat.
pub fn run_solver(script: &str, query: &str) -> EResult<Option<String>> {
    let solvers: [(&str, &[&str]); 3] = [
        ("yices-smt2", &[]),
        ("z3", &["-in", "-smt2"]),
        ("cvc5", &["--lang", "smt2"]),
    ];
    for (bin, args) in solvers {
        let full = format!("{}\n{}\n", script, query);
        let result = Command::new(bin)
            .args(args)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .spawn()
            .and_then(|mut child| {
                use std::io::Write;
                child
                    .stdin
                    .as_mut()
                    .unwrap()
                    .write_all(full.as_bytes())?;
                child.wait_with_output()
            });
        match result {
            Ok(out) => {
                let text = String::from_utf8_lossy(&out.stdout).to_string();
                if text.starts_with("unsat") {
                    return Ok(None);
                }
                if text.starts_with("sat") {
                    return Ok(Some(text));
                }
                // solver choked; try the next one
                continue;
            }
            Err(_) => continue,
        }
    }
    Err(EngineError::Eval(
        "no working SMT solver found (tried yices-smt2, z3, cvc5)".into(),
    ))
}

pub enum SmtResult {
    NoCe(usize),
    Counterexample(Vec<Vec<Value>>),
    Proved,
    InductionFailed,
}

/// BMC search over the SMT backend.
pub fn smt_bmc_search(
    flat: &FlatModule,
    formula: &sal_flat::formula::TFormula,
    depth: usize,
    lemmas: &[FExpr],
) -> EResult<SmtResult> {
    let neg = crate::ltl::to_nnf(formula, true).map_err(EngineError::Eval)?;
    let neg = std::rc::Rc::new(neg);
    for k in 0..=depth {
        let mut enc = SmtEnc::new(flat);
        let mut cs = vec![enc.init()?];
        for t in 0..k {
            cs.push(enc.trans(t, t + 1)?);
        }
        for t in 0..=k {
            for lemma in lemmas {
                let d = enc.declare_step(t);
                cs.push(d);
                cs.push(enc.enc_bool(lemma, t, t)?);
            }
        }
        let mut alts = Vec::new();
        {
            let mut alg = SmtAlg { enc: &mut enc };
            let mut bltl = BoundedLtl::new(&mut alg, k);
            alts.push(bltl.no_loop(&neg, 0));
        }
        for l in 0..=k {
            let wl = {
                let mut alg = SmtAlg { enc: &mut enc };
                let mut bltl = BoundedLtl::new(&mut alg, k);
                bltl.with_loop(&neg, 0, l)
            };
            let tk = enc.trans(k, k + 1)?;
            let eq = enc.state_eq(k + 1, l);
            alts.push(format!("(and {} {} {})", tk, eq, wl));
        }
        cs.push(format!("(or {})", alts.join(" ")));
        let script = enc.script(&format!("(and {})", cs.join(" ")));
        if let Some(model) = run_solver(&script, &enc.value_query(k))? {
            let states = decode_model(flat, &model, k);
            return Ok(SmtResult::Counterexample(states));
        }
    }
    Ok(SmtResult::NoCe(depth))
}

/// k-induction over the SMT backend.
pub fn smt_k_induction(
    flat: &FlatModule,
    prop: &FExpr,
    k: usize,
    lemmas: &[FExpr],
) -> EResult<SmtResult> {
    // base
    {
        let mut enc = SmtEnc::new(flat);
        let mut cs = vec![enc.init()?];
        for t in 0..k {
            cs.push(enc.trans(t, t + 1)?);
        }
        let mut bad = Vec::new();
        for t in 0..=k {
            let d = enc.declare_step(t);
            cs.push(d);
            let p = enc.enc_bool(prop, t, t)?;
            bad.push(format!("(not {})", p));
            for lemma in lemmas {
                cs.push(enc.enc_bool(lemma, t, t)?);
            }
        }
        cs.push(format!("(or {})", bad.join(" ")));
        let script = enc.script(&format!("(and {})", cs.join(" ")));
        if let Some(model) = run_solver(&script, &enc.value_query(k))? {
            let states = decode_model(flat, &model, k);
            return Ok(SmtResult::Counterexample(states));
        }
    }
    // step
    {
        let mut enc = SmtEnc::new(flat);
        let mut cs = vec![enc.declare_step(0)];
        for i in &flat.invariants.clone() {
            cs.push(enc.enc_bool(i, 0, 0)?);
        }
        for t in 0..=k {
            cs.push(enc.trans(t, t + 1)?);
        }
        for t in 0..=k {
            let p = enc.enc_bool(prop, t, t)?;
            cs.push(p);
            for lemma in lemmas {
                cs.push(enc.enc_bool(lemma, t, t)?);
            }
        }
        for lemma in lemmas {
            let l = enc.enc_bool(lemma, k + 1, k + 1)?;
            cs.push(l);
        }
        let p = enc.enc_bool(prop, k + 1, k + 1)?;
        cs.push(format!("(not {})", p));
        let script = enc.script(&format!("(and {})", cs.join(" ")));
        if run_solver(&script, "")?.is_some() {
            return Ok(SmtResult::InductionFailed);
        }
    }
    Ok(SmtResult::Proved)
}

/// Parse a (get-value ...) response into per-step states.
fn decode_model(flat: &FlatModule, output: &str, steps: usize) -> Vec<Vec<Value>> {
    // build map name -> value string via a light s-expr scan
    let mut map: HashMap<String, String> = HashMap::new();
    let body = output.trim_start_matches("sat").trim();
    let toks = tokenize_sexp(body);
    let mut i = 0;
    // structure: ( (name val) (name val) ... )
    while i < toks.len() {
        if toks[i] == "(" && i + 1 < toks.len() && toks[i + 1].starts_with('s') {
            let name = toks[i + 1].clone();
            // value: till matching close
            let mut depth = 0;
            let mut j = i + 2;
            let mut val = String::new();
            while j < toks.len() {
                match toks[j].as_str() {
                    "(" => {
                        depth += 1;
                        val.push('(');
                        val.push(' ');
                    }
                    ")" => {
                        if depth == 0 {
                            break;
                        }
                        depth -= 1;
                        val.push(')');
                        val.push(' ');
                    }
                    t => {
                        val.push_str(t);
                        val.push(' ');
                    }
                }
                j += 1;
            }
            map.insert(name, val.trim().to_string());
            i = j + 1;
        } else {
            i += 1;
        }
    }
    let mut out = Vec::new();
    for t in 0..=steps {
        let mut state = Vec::new();
        for (l, leaf) in flat.leaves.iter().enumerate() {
            let raw = map.get(&sym(l, t)).cloned().unwrap_or_default();
            state.push(parse_value(&raw, &leaf.ty));
        }
        out.push(state);
    }
    out
}

fn tokenize_sexp(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '(' | ')' => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                out.push(c.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn parse_value(raw: &str, ty: &LeafType) -> Value {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    let raw = raw.trim();
    if raw == "true" {
        return Value::Bool(true);
    }
    if raw == "false" {
        return Value::Bool(false);
    }
    // (- 3), (/ 1 2), (- (/ 1 2)), plain numerals (possibly decimal "1.5")
    let toks = tokenize_sexp(raw);
    let n = parse_num(&toks, &mut 0).unwrap_or_else(|| BigRational::from_integer(0.into()));
    match ty {
        LeafType::Scalar(id, _) => {
            let idx: usize = n
                .to_integer()
                .try_into()
                .unwrap_or(0usize);
            Value::Scalar(id.clone(), idx)
        }
        _ => Value::Num(n),
    }
    .clone()
}

fn parse_num(
    toks: &[String],
    pos: &mut usize,
) -> Option<num_rational::BigRational> {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    if *pos >= toks.len() {
        return None;
    }
    let t = &toks[*pos];
    if t == "(" {
        *pos += 1;
        let op = toks.get(*pos)?.clone();
        *pos += 1;
        let r = match op.as_str() {
            "-" => {
                let a = parse_num(toks, pos)?;
                match parse_num(toks, pos) {
                    Some(b) => a - b,
                    None => -a,
                }
            }
            "/" => {
                let a = parse_num(toks, pos)?;
                let b = parse_num(toks, pos)?;
                a / b
            }
            _ => return None,
        };
        // consume until close
        while *pos < toks.len() && toks[*pos] != ")" {
            *pos += 1;
        }
        *pos += 1;
        Some(r)
    } else {
        *pos += 1;
        if let Some(dot) = t.find('.') {
            let int_part = &t[..dot];
            let frac = &t[dot + 1..];
            let denom = BigInt::from(10u32).pow(frac.len() as u32);
            let numer: BigInt =
                format!("{}{}", int_part, frac).parse().ok()?;
            Some(BigRational::new(numer, denom))
        } else {
            let i: BigInt = t.parse().ok()?;
            Some(BigRational::from_integer(i))
        }
    }
}
