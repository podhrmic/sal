//! Flattener/engine semantics tests on inline models.
//!
//! Each test pins down a behavior that was discovered by probing the
//! SAL 3.3 oracle (see docs/ARCHITECTURE.md, "Semantics that are easy to
//! get wrong"). The models are written to a temp dir because context
//! names must match file names.

use std::rc::Rc;

use sal_core::wfc::Checker;
use sal_core::SalEnv;
use sal_engine::explicit::Explicit;
use sal_engine::symbolic::Symbolic;
use sal_flat::flatten::FlatModule;
use sal_flat::sval::EvalCtx;
use sal_flat::{FExpr, Flattener};
use sal_syntax::ast::{Module, ModuleKind, Name};
use sal_syntax::span::Span;

/// Parse an inline context (named `ctx`) and flatten `module`.
fn flatten(src: &str, ctx_name: &str, module: &str) -> FlatModule {
    let dir = std::env::temp_dir().join(format!("sal-rs-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}.sal", ctx_name));
    std::fs::write(&path, src).unwrap();

    let env = SalEnv::new();
    let def = env.parse_file(&path).expect("parse");
    let inst = env.plain_instance(def);
    Checker::new(&env).check_instance(&inst).expect("typecheck");

    let flattener = Flattener::new(&env);
    let module_ast = Module {
        kind: ModuleKind::Instance(
            Name {
                ctx: None,
                id: sal_syntax::ast::Ident {
                    name: module.into(),
                    span: Span::dummy(),
                },
                span: Span::dummy(),
            },
            vec![],
        ),
        span: Span::dummy(),
        parens: 0,
    };
    flattener
        .flatten_module(&EvalCtx::new(Rc::clone(&inst)), &module_ast)
        .expect("flatten")
}

/// Boolean state predicate `leaf-name = value-display`.
fn atom(flat: &FlatModule, name: &str, value: &str) -> FExpr {
    let (i, leaf) = flat
        .leaves
        .iter()
        .enumerate()
        .find(|(_, l)| l.name == name)
        .unwrap_or_else(|| panic!("no leaf named {}", name));
    let vals = leaf.ty.values().expect("finite leaf");
    for (k, v) in vals.iter().enumerate() {
        let display = match (&v, &leaf.ty) {
            (sal_flat::Value::Scalar(_, idx), sal_flat::fexpr::LeafType::Scalar(_, es)) => {
                es[*idx].clone()
            }
            (v, _) => format!("{}", v),
        };
        if display == value {
            return FExpr::eq(FExpr::Var(i as u32, false), FExpr::Const(vals[k].clone()));
        }
    }
    panic!("no value {} for leaf {}", value, name);
}

/// `G prop` verdict from both engines; they must agree.
fn invariant_both(flat: &FlatModule, prop: &FExpr) -> bool {
    let explicit = Explicit::new(flat).expect("explicit");
    let e = matches!(
        explicit.check_invariant(prop).expect("explicit run"),
        sal_engine::explicit::CheckResult::Proved
    );
    let mut symbolic = Symbolic::new(flat).expect("symbolic");
    let s = symbolic.check_invariant(prop).expect("symbolic run").is_none();
    assert_eq!(e, s, "explicit and symbolic engines disagree");
    s
}

#[test]
fn else_is_negated_guard_disjunction() {
    // g1 is always enabled, so ELSE never fires: x = 2 is unreachable
    let flat = flatten(
        "elseneg: CONTEXT = BEGIN
           m: MODULE = BEGIN OUTPUT x: [0..3]
             INITIALIZATION x = 0
             TRANSITION [ x <= 1 --> x' = 1 [] ELSE --> x' = 2 ] END;
         END",
        "elseneg",
        "m",
    );
    let bad = atom(&flat, "x", "2");
    assert!(invariant_both(&flat, &FExpr::not(bad)));
}

#[test]
fn else_fires_when_guards_false() {
    // from x = 1 the guard is false, so ELSE reaches x = 2
    let flat = flatten(
        "elseon: CONTEXT = BEGIN
           m: MODULE = BEGIN OUTPUT x: [0..3]
             INITIALIZATION x = 0
             TRANSITION [ x = 0 --> x' = 1 [] ELSE --> x' = 2 ] END;
         END",
        "elseon",
        "m",
    );
    let bad = atom(&flat, "x", "2");
    assert!(!invariant_both(&flat, &FExpr::not(bad)));
}

#[test]
fn missing_transition_section_stutters() {
    // initmod has no TRANSITION: its step freezes x, so after the worker
    // moves x to 1 it stays 1 (x = 0 never recurs; x never exceeds 1)
    let flat = flatten(
        "stutter: CONTEXT = BEGIN
           worker: MODULE = BEGIN GLOBAL x: [0..2]
             TRANSITION [ x = 0 --> x' = 1 ] END;
           initmod: MODULE = BEGIN GLOBAL x: [0..2]
             INITIALIZATION x = 0 END;
           system: MODULE = worker [] initmod;
         END",
        "stutter",
        "system",
    );
    let two = atom(&flat, "x", "2");
    assert!(invariant_both(&flat, &FExpr::not(two)));
}

#[test]
fn shared_locals_pair_into_tuples() {
    let flat = flatten(
        "tup: CONTEXT = BEGIN
           m: MODULE = BEGIN LOCAL pc: [0..1]
             INITIALIZATION pc = 0 TRANSITION pc' = pc END;
           system: MODULE = m [] m;
         END",
        "tup",
        "system",
    );
    let names: Vec<&str> = flat.leaves.iter().map(|l| l.name.as_str()).collect();
    assert!(names.contains(&"pc.1"), "leaves: {:?}", names);
    assert!(names.contains(&"pc.2"), "leaves: {:?}", names);
}

#[test]
fn multicomposition_arrays_locals() {
    let flat = flatten(
        "arr: CONTEXT = BEGIN
           m [i: [1..3]]: MODULE = BEGIN LOCAL pc: [0..1]
             INITIALIZATION pc = 0 TRANSITION pc' = pc END;
           system: MODULE = ([] (i: [1..3]): m[i]);
         END",
        "arr",
        "system",
    );
    let names: Vec<&str> = flat.leaves.iter().map(|l| l.name.as_str()).collect();
    for want in ["pc[1]", "pc[2]", "pc[3]"] {
        assert!(names.contains(&want), "leaves: {:?}", names);
    }
}

#[test]
fn unassigned_controlled_vars_are_framed() {
    // the command only assigns x; y must stay at its initial value
    let flat = flatten(
        "frame: CONTEXT = BEGIN
           m: MODULE = BEGIN OUTPUT x: [0..1], y: [0..1]
             INITIALIZATION x = 0; y = 0
             TRANSITION [ TRUE --> x' = 1 ] END;
         END",
        "frame",
        "m",
    );
    let y1 = atom(&flat, "y", "1");
    assert!(invariant_both(&flat, &FExpr::not(y1)));
}

#[test]
fn definitions_are_invariants() {
    // DEFINITION couples d to x in every state, including after steps
    let flat = flatten(
        "defs: CONTEXT = BEGIN
           m: MODULE = BEGIN OUTPUT x: [0..1] OUTPUT d: BOOLEAN
             DEFINITION d = (x = 1)
             INITIALIZATION x = 0
             TRANSITION [ TRUE --> x' = 1 - x ] END;
         END",
        "defs",
        "m",
    );
    // d <=> (x = 1): never (d AND x = 0)
    let d = atom(&flat, "d", "true");
    let x0 = atom(&flat, "x", "0");
    let bad = FExpr::and(vec![d, x0]);
    assert!(invariant_both(&flat, &FExpr::not(bad)));
}

#[test]
fn in_selection_constrains_membership() {
    // x' IN {1, 2}: x = 3 unreachable, x = 2 reachable
    let flat = flatten(
        "sel: CONTEXT = BEGIN
           m: MODULE = BEGIN OUTPUT x: [0..3]
             INITIALIZATION x = 0
             TRANSITION [ TRUE --> x' IN {1, 2} ] END;
         END",
        "sel",
        "m",
    );
    let three = atom(&flat, "x", "3");
    assert!(invariant_both(&flat, &FExpr::not(three)));
    let two = atom(&flat, "x", "2");
    assert!(!invariant_both(&flat, &FExpr::not(two)));
}

#[test]
fn symbolic_lhs_index_has_update_semantics() {
    // a'[i] = 1 with a state-dependent i: the other element is unchanged
    let flat = flatten(
        "symidx: CONTEXT = BEGIN
           m: MODULE = BEGIN
             INPUT i: [0..1]
             OUTPUT a: ARRAY [0..1] OF [0..2]
             INITIALIZATION a = [[j: [0..1]] 0]
             TRANSITION [ TRUE --> a'[i] = 1 ] END;
         END",
        "symidx",
        "m",
    );
    // 2 is never assigned anywhere
    let bad = FExpr::or(vec![atom(&flat, "a[0]", "2"), atom(&flat, "a[1]", "2")]);
    assert!(invariant_both(&flat, &FExpr::not(bad)));
    // both elements can become 1 (via different inputs)
    let a0 = atom(&flat, "a[0]", "1");
    assert!(!invariant_both(&flat, &FExpr::not(a0)));
}

#[test]
fn ltl_liveness_and_bounded_bmc_agree() {
    // a free-running bit: GF(x = 1) is violated by the stutter loop
    let flat = flatten(
        "live: CONTEXT = BEGIN
           m: MODULE = BEGIN OUTPUT x: [0..1]
             INITIALIZATION x = 0
             TRANSITION [ TRUE --> x' = 1 [] TRUE --> x' = 0 ] END;
         END",
        "live",
        "m",
    );
    use sal_flat::formula::TFormula;
    let gf = TFormula::G(Rc::new(TFormula::F(Rc::new(TFormula::Atom(atom(
        &flat, "x", "1",
    ))))));
    // symbolic LTL: counterexample exists (loop forever on x = 0)
    let mut sym = Symbolic::new(&flat).expect("symbolic");
    assert!(sym.check_ltl(&gf).expect("ltl").is_some());
    // bounded LTL (SAT) finds the same lasso within depth 4
    let r = sal_engine::bmc::bmc_search(&flat, &gf, 4, &[], true).expect("bmc");
    assert!(matches!(
        r,
        sal_engine::bmc::BmcResult::Counterexample(_)
    ));
}

#[test]
fn reordering_preserves_verdicts() {
    // same model, reordering forced on vs off: identical verdict
    let flat = flatten(
        "reo: CONTEXT = BEGIN
           m: MODULE = BEGIN OUTPUT x: [0..7], y: [0..7]
             INITIALIZATION x = 0; y = 0
             TRANSITION [ x < 7 --> x' = x + 1; y' = 7 - x
                       [] ELSE --> x' = 0 ] END;
         END",
        "reo",
        "m",
    );
    let bad = atom(&flat, "y", "1");
    let mut plain = Symbolic::new(&flat).unwrap();
    let mut reord = Symbolic::new(&flat).unwrap();
    reord.mgr.set_reorder(true);
    let a = plain.check_invariant(&FExpr::not(bad.clone())).unwrap().is_none();
    let b = reord.check_invariant(&FExpr::not(bad)).unwrap().is_none();
    assert_eq!(a, b);
}
