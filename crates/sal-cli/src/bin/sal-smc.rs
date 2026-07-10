//! SAL Symbolic Model Checker (Rust reimplementation).
//!
//! Currently backed by the explicit-state engine for invariant (G p)
//! properties; LTL with fairness and the BDD engine are in progress.

use std::process::ExitCode;
use std::rc::Rc;

use sal_cli::common::{parse_args, print_path, resolve_context, resolve_qualified};
use sal_core::wfc::Checker;
use sal_core::SalEnv;
use sal_engine::explicit::{CheckResult, Explicit};
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

    let engine = match Explicit::new(&flat) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("Error: {}", e);
            return ExitCode::from(255);
        }
    };

    // supported: pure-propositional and G/AG invariants
    let prop = match &formula {
        TFormula::Atom(e) => Some((e.clone(), true)),
        TFormula::G(inner) | TFormula::AG(inner) => {
            inner.as_atom().map(|e| (e.clone(), false))
        }
        _ => None,
    };
    let Some((prop, init_only)) = prop else {
        eprintln!(
            "Error: this LTL/CTL formula is not yet supported by the Rust sal-smc \
             (invariant properties only)."
        );
        return ExitCode::from(255);
    };

    let outcome = if init_only {
        // property must hold in the initial states
        (|| {
            for s in engine.initial_states()? {
                if !engine.holds(&prop, &s)? {
                    return Ok(CheckResult::Counterexample(
                        sal_engine::explicit::Path {
                            steps: vec![(Rc::clone(&s), None)],
                        },
                    ));
                }
            }
            Ok(CheckResult::Proved)
        })()
    } else {
        engine.check_invariant(&prop)
    };

    match outcome {
        Ok(CheckResult::Proved) => {
            println!("proved.");
            ExitCode::SUCCESS
        }
        Ok(CheckResult::Counterexample(path)) => {
            print_path(&flat, &path, "Counterexample:");
            ExitCode::SUCCESS
        }
        Ok(_) => unreachable!(),
        Err(e) => {
            eprintln!("Error: {}", e);
            ExitCode::from(255)
        }
    }
}
