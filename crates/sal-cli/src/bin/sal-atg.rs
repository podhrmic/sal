//! SAL Automated Test Generator (Rust reimplementation).
//!
//! Given a SAL module instrumented with boolean trap variables and a
//! Scheme goals file `(define goal-list '("g1" "g2" ...))`, generates a
//! set of tests (input sequences) driving the traps to TRUE: an initial
//! segment from the initial states, repeatedly extended toward further
//! undischarged goals; when no extension is possible a new test is
//! started. Segments are found with BDD reachability (shortest
//! segments, like `--smcinit`/`--incremental` in the original).

use std::process::ExitCode;

use sal_cli::common::{display_leaf, parse_args, resolve_context, resolve_qualified};
use sal_core::env::Entry;
use sal_core::wfc::Checker;
use sal_core::SalEnv;
use sal_engine::bdd::{NodeId, F};
use sal_engine::symbolic::Symbolic;
use sal_flat::fexpr::{FExpr, LeafType};
use sal_flat::sval::EvalCtx;
use sal_flat::value::Value;
use sal_flat::Flattener;
use sal_syntax::ast::{Module, ModuleKind, Name, VarClass};
use sal_syntax::span::Span;

/// Parse `(define goal-list '("a" "b" ...))` with `;` comments.
fn parse_goals(src: &str) -> Result<Vec<String>, String> {
    let mut clean = String::new();
    for line in src.lines() {
        let line = match line.find(';') {
            Some(i) => &line[..i],
            None => line,
        };
        clean.push_str(line);
        clean.push('\n');
    }
    let mut goals = Vec::new();
    let mut rest = clean.as_str();
    if !rest.contains("goal-list") {
        return Err("goals file does not define goal-list".into());
    }
    while let Some(i) = rest.find('"') {
        rest = &rest[i + 1..];
        let Some(j) = rest.find('"') else {
            return Err("unterminated string in goals file".into());
        };
        goals.push(rest[..j].to_string());
        rest = &rest[j + 1..];
    }
    if goals.is_empty() {
        return Err("no goals found in goals file".into());
    }
    Ok(goals)
}

fn main() -> ExitCode {
    let args = parse_args(&["assertion", "module", "depth"]);
    let env = SalEnv::new();
    let checker = Checker::new(&env);

    if args.positional.len() != 3 {
        eprintln!("Usage: sal-atg [options] <context-name> <module-name> <goals-file>");
        return ExitCode::from(255);
    }
    let goals_src = match std::fs::read_to_string(&args.positional[2]) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error: cannot read goals file \"{}\": {}", args.positional[2], e);
            return ExitCode::from(255);
        }
    };
    let goals = match parse_goals(&goals_src) {
        Ok(g) => g,
        Err(m) => {
            eprintln!("Error: {}", m);
            return ExitCode::from(255);
        }
    };

    let ctx_ref = &args.positional[0];
    let module_name = args.positional[1].clone();
    let inst = match if ctx_ref.contains('{') {
        resolve_qualified(&env, &checker, &format!("{}!__x", ctx_ref)).map(|(i, _)| i)
    } else {
        resolve_context(&env, &checker, ctx_ref)
    } {
        Ok(i) => i,
        Err(e) => {
            eprintln!("{}", e);
            return ExitCode::from(255);
        }
    };
    if !matches!(
        inst.symbols.borrow().get(&module_name),
        Some(Entry::Module { .. })
    ) {
        eprintln!(
            "Error: Module \"{}\" was not found in context \"{}\".",
            module_name, inst.name
        );
        return ExitCode::from(255);
    }

    // options
    let id: usize = args.opt("id").and_then(|v| v.parse().ok()).unwrap_or(8);
    let ed: usize = args.opt("ed").and_then(|v| v.parse().ok()).unwrap_or(8);
    let md: usize = args.opt("md").and_then(|v| v.parse().ok()).unwrap_or(0);
    let smcinit = args.flag("smcinit");
    let branch = args.flag("branch");
    let noprune = args.flag("noprune");
    let fullpath = args.flag("fullpath");
    // --latching / --incremental / --noslice / --innerslice are accepted;
    // BDD search always yields shortest segments and scans whole segments.

    let flattener = Flattener::new(&env);
    let module_ast = Module {
        kind: ModuleKind::Instance(
            Name {
                ctx: None,
                id: sal_syntax::ast::Ident {
                    name: module_name.clone(),
                    span: Span::dummy(),
                },
                span: Span::dummy(),
            },
            vec![],
        ),
        span: Span::dummy(),
        parens: 0,
    };
    let ectx = EvalCtx::new(inst.clone());
    let flat = match flattener.flatten_module(&ectx, &module_ast) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("{}", e);
            return ExitCode::from(255);
        }
    };

    // map goal names to boolean leaves
    let mut goal_leaves: Vec<(String, u32)> = Vec::new();
    for g in &goals {
        match flat
            .leaves
            .iter()
            .position(|l| l.name == *g && matches!(l.ty, LeafType::Bool))
        {
            Some(i) => goal_leaves.push((g.clone(), i as u32)),
            None => {
                eprintln!(
                    "Error: trap variable \"{}\" is not a boolean variable of module \"{}\".",
                    g, module_name
                );
                return ExitCode::from(255);
            }
        }
    }

    let mut engine = match sal_cli::common::build_symbolic(&flat, &args) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("Error: {}", e);
            return ExitCode::from(255);
        }
    };

    // trap BDDs
    let trap_bdd: Vec<NodeId> = goal_leaves
        .iter()
        .map(|(_, l)| {
            engine
                .enc_bool(&FExpr::Var(*l, false))
                .expect("trap encoding")
        })
        .collect();

    let mut remaining: Vec<usize> = (0..goal_leaves.len()).collect();
    let mut tests: Vec<Vec<Vec<Value>>> = Vec::new();

    let target_of = |eng: &mut Symbolic, rem: &[usize]| -> NodeId {
        let mut t = F;
        for &i in rem {
            t = eng.mgr.or(t, trap_bdd[i]);
        }
        t
    };
    // discharge goals satisfied along a segment; prune all (default) or
    // just one (--noprune)
    let discharge = |rem: &mut Vec<usize>, seg: &[Vec<Value>], noprune: bool| {
        let mut hit: Vec<usize> = Vec::new();
        for &i in rem.iter() {
            let leaf = goal_leaves[i].1 as usize;
            if seg.iter().any(|s| s[leaf] == Value::Bool(true)) {
                hit.push(i);
            }
        }
        if noprune && hit.len() > 1 {
            hit.truncate(1);
        }
        rem.retain(|i| !hit.contains(i));
        !hit.is_empty()
    };

    let init_bound = if smcinit && id == 0 { None } else { Some(id) };
    while !remaining.is_empty() {
        // initial segment
        let target = target_of(&mut engine, &remaining);
        let init = engine.init;
        let Some(mut path) = engine.find_path(init, target, 0, init_bound) else {
            break;
        };
        discharge(&mut remaining, &path, noprune);
        let init_seg_end = path.len() - 1;
        // extensions
        if ed > 0 {
            loop {
                if remaining.is_empty() {
                    break;
                }
                let target = target_of(&mut engine, &remaining);
                let last = engine.state_bdd(path.last().unwrap());
                match engine.find_path(last, target, md.max(1), Some(ed)) {
                    Some(seg) => {
                        path.extend(seg.into_iter().skip(1));
                        discharge(&mut remaining, &path, noprune);
                    }
                    None => {
                        if branch {
                            // try extending from the end of the initial
                            // segment instead
                            let anchor = engine.state_bdd(&path[init_seg_end]);
                            let target = target_of(&mut engine, &remaining);
                            if let Some(seg) =
                                engine.find_path(anchor, target, md.max(1), Some(ed))
                            {
                                path.extend(seg.into_iter().skip(1));
                                discharge(&mut remaining, &path, noprune);
                                continue;
                            }
                        }
                        break;
                    }
                }
            }
        }
        tests.push(path);
    }

    // report
    let total: usize = tests.iter().map(|t| t.len().saturating_sub(1)).sum();
    println!("{} tests generated; total length {}", tests.len(), total);
    if remaining.is_empty() {
        println!("All test goals discharged.");
    } else {
        let names: Vec<&str> = remaining
            .iter()
            .map(|&i| goal_leaves[i].0.as_str())
            .collect();
        println!(
            "{} undischarged test goals:({})",
            remaining.len(),
            names.join(" ")
        );
    }
    for t in &tests {
        println!("========================");
        println!("Path");
        println!("========================");
        for (i, state) in t.iter().enumerate() {
            println!("Step {}:", i);
            println!("--- Input Variables (assignments) ---");
            for (li, v) in state.iter().enumerate() {
                if flat.leaves[li].class == VarClass::Input {
                    println!("{} = {}", flat.leaves[li].name, display_leaf(&flat.leaves[li], v));
                }
            }
            if fullpath {
                println!("--- System Variables (assignments) ---");
                for (li, v) in state.iter().enumerate() {
                    if flat.leaves[li].class != VarClass::Input {
                        println!(
                            "{} = {}",
                            flat.leaves[li].name,
                            display_leaf(&flat.leaves[li], v)
                        );
                    }
                }
            }
            println!("------------------------");
        }
    }
    ExitCode::SUCCESS
}
