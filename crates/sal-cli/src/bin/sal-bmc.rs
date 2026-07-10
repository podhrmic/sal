//! SAL Bounded Model Checker (Rust reimplementation, SAT-based).

use std::process::ExitCode;

use sal_cli::common::{parse_args, print_states, resolve_context, resolve_qualified};
use sal_core::env::Entry;
use sal_core::wfc::Checker;
use sal_core::SalEnv;
use sal_engine::bmc::{bmc_search, k_induction, BmcResult};
use sal_flat::fexpr::FExpr;
use sal_flat::formula::TFormula;
use sal_flat::Flattener;

fn main() -> ExitCode {
    let args = parse_args(&["assertion", "depth"]);
    let env = SalEnv::new();
    let checker = Checker::new(&env);

    let target = if let Some(a) = args.opt("assertion") {
        resolve_qualified(&env, &checker, a)
    } else if args.positional.len() == 2 {
        resolve_context(&env, &checker, &args.positional[0])
            .map(|inst| (inst, args.positional[1].clone()))
    } else {
        eprintln!("Usage: sal-bmc [options] <context-name> <assertion-name>");
        return ExitCode::from(255);
    };
    let (inst, assertion) = match target {
        Ok(t) => t,
        Err(e) => {
            eprintln!("{}", e);
            return ExitCode::from(255);
        }
    };

    let depth: usize = args
        .opt("depth")
        .or_else(|| args.opt("d"))
        .and_then(|d| d.parse().ok())
        .unwrap_or(10);
    let induction = args.flag("i") || args.flag("induction");

    let flattener = Flattener::new(&env);
    let (flat, formula) = match flattener.flatten_assertion(&inst, &assertion) {
        Ok(r) => r,
        Err(e) => {
            eprintln!(
                "Error: Processing the assertion `{}!{}'. Reason:",
                inst.key, assertion
            );
            eprintln!("{}", e);
            return ExitCode::from(255);
        }
    };

    // lemmas (-l name): invariant bodies of other assertions
    let mut lemmas: Vec<FExpr> = Vec::new();
    for (k, v) in &args.options {
        if k == "l" || k == "lemma" {
            let Some(name) = v else { continue };
            match flattener.lower_assertion_in(&inst, name, &flat) {
                Ok(lf) => {
                    let atom = match &lf {
                        TFormula::G(inner) | TFormula::AG(inner) => inner.as_atom().cloned(),
                        TFormula::Atom(e) => Some(e.clone()),
                        _ => None,
                    };
                    match atom {
                        Some(a) => lemmas.push(a),
                        None => {
                            eprintln!(
                                "Error: lemma \"{}\" is not an invariant property.",
                                name
                            );
                            return ExitCode::from(255);
                        }
                    }
                }
                Err(e) => {
                    eprintln!("{}", e);
                    return ExitCode::from(255);
                }
            }
        }
    }
    let _ = inst.symbols.borrow().get(&assertion).map(|e| {
        matches!(e, Entry::Assertion { .. })
    });

    let result = if induction {
        let atom = match &formula {
            TFormula::G(inner) | TFormula::AG(inner) => inner.as_atom().cloned(),
            TFormula::Atom(e) => Some(e.clone()),
            _ => None,
        };
        let Some(prop) = atom else {
            eprintln!("Error: induction is only supported for invariant properties.");
            return ExitCode::from(255);
        };
        k_induction(&flat, &prop, depth, &lemmas)
    } else {
        bmc_search(&flat, &formula, depth, &lemmas)
    };

    match result {
        Ok(BmcResult::Proved) => {
            println!("proved.");
            ExitCode::SUCCESS
        }
        Ok(BmcResult::InductionFailed) => {
            println!("k-induction rule failed, please try to increase the depth.");
            ExitCode::SUCCESS
        }
        Ok(BmcResult::NoCe(k)) => {
            println!("no counterexample between depths: [0, {}].", k);
            ExitCode::SUCCESS
        }
        Ok(BmcResult::Counterexample(states)) => {
            print_states(&flat, &states, "Counterexample:");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("Error: {}", e);
            ExitCode::from(255)
        }
    }
}
