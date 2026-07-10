//! SAL Symbolic Model Checker (Rust reimplementation).
//!
//! Currently backed by the explicit-state engine for invariant (G p)
//! properties; LTL with fairness and the BDD engine are in progress.

use std::process::ExitCode;

use sal_cli::common::{parse_args, print_states, resolve_context, resolve_qualified};
use sal_core::wfc::Checker;
use sal_core::SalEnv;
use sal_engine::symbolic::Symbolic;
use sal_flat::formula::TFormula;
use sal_flat::Flattener;

fn main() -> ExitCode {
    let args = parse_args(&["assertion"]);
    let env = SalEnv::new();
    let checker = Checker::new(&env);

    let target = if let Some(a) = args.opt("assertion") {
        resolve_qualified(&env, &checker, a)
    } else if args.positional.len() == 2 {
        resolve_context(&env, &checker, &args.positional[0])
            .map(|inst| (inst, args.positional[1].clone()))
    } else {
        eprintln!("Usage: sal-smc [options] <context-name> <assertion-name>");
        eprintln!("   or  sal-smc [options] --assertion='<ctx>{{<params>}}!<assertion>'");
        return ExitCode::from(255);
    };
    let (inst, assertion) = match target {
        Ok(t) => t,
        Err(e) => {
            eprintln!("{}", e);
            return ExitCode::from(255);
        }
    };

    let flattener = Flattener::new(&env);
    let result = flattener.flatten_assertion(&inst, &assertion);
    let (flat, formula) = match result {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Error: Processing the assertion `{}!{}'. Reason:", inst.key, assertion);
            eprintln!("{}", e);
            return ExitCode::from(255);
        }
    };

    let mut engine = match Symbolic::new(&flat) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("Error: {}", e);
            return ExitCode::from(255);
        }
    };

    // dispatch: propositional / invariant properties use plain
    // reachability (shortest counterexamples); CTL uses fixpoints; LTL
    // uses the Büchi product.
    enum Kind {
        Initial(sal_flat::FExpr),
        Invariant(sal_flat::FExpr),
        Ctl,
        Ltl,
    }
    let kind = match &formula {
        TFormula::Atom(e) => Kind::Initial(e.clone()),
        TFormula::G(inner) | TFormula::AG(inner) if inner.as_atom().is_some() => {
            Kind::Invariant(inner.as_atom().unwrap().clone())
        }
        f if f.is_ctl() && f.has_ltl() => {
            eprintln!("Error: formula mixes CTL and LTL operators.");
            return ExitCode::from(255);
        }
        f if f.is_ctl() => Kind::Ctl,
        _ => Kind::Ltl,
    };

    let outcome = match kind {
        Kind::Initial(p) => engine.check_initial(&p),
        Kind::Invariant(p) => engine.check_invariant(&p),
        Kind::Ctl => engine.check_ctl(&formula),
        Kind::Ltl => engine.check_ltl(&formula),
    };

    match outcome {
        Ok(None) => {
            println!("proved.");
            ExitCode::SUCCESS
        }
        Ok(Some(path)) => {
            print_states(&flat, &path, "Counterexample:");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("Error: {}", e);
            ExitCode::from(255)
        }
    }
}
