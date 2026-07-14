//! SAL Path Finder (Rust reimplementation): generates an execution path
//! of the given depth.

use std::process::ExitCode;

use sal_cli::common::{parse_args, print_states, resolve_context, resolve_qualified};
use sal_core::env::Entry;
use sal_core::wfc::Checker;
use sal_core::SalEnv;
use sal_flat::sval::EvalCtx;
use sal_flat::Flattener;
use sal_syntax::ast::{Module, ModuleKind, Name};
use sal_syntax::span::Span;

fn main() -> ExitCode {
    let args = parse_args(&["module", "depth"]);
    let env = SalEnv::new();
    let checker = Checker::new(&env);

    let target = if let Some(m) = args.opt("module") {
        resolve_qualified(&env, &checker, m)
    } else if args.positional.len() == 2 {
        resolve_context(&env, &checker, &args.positional[0])
            .map(|inst| (inst, args.positional[1].clone()))
    } else {
        eprintln!("Usage: sal-path-finder [options] <context-name> <module-name>");
        eprintln!("   or  sal-path-finder [options] <file-name> <module-name>");
        eprintln!("   or  sal-path-finder [options] --module='<ctx>!<module>'");
        return ExitCode::from(255);
    };
    let (inst, module_name) = match target {
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

    if let Err(e) = checker.check_instance(&inst) {
        eprintln!("{}", e);
        return ExitCode::from(255);
    }
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
    let ctx = EvalCtx::new(inst.clone());
    let flat = match flattener.flatten_module(&ctx, &module_ast) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("{}", e);
            return ExitCode::from(255);
        }
    };
    let mut engine = match sal_cli::common::build_symbolic(&flat, &args) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("Error: {}", e);
            return ExitCode::from(255);
        }
    };
    match engine.random_path(depth) {
        Ok(states) => {
            print_states(&flat, &states, "Path:");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("Error: {}", e);
            ExitCode::from(255)
        }
    }
}
