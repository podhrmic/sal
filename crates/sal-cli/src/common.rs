//! Shared plumbing for the CLI tools: argument handling, context/assertion
//! resolution, and counterexample printing.

use std::path::Path;
use std::rc::Rc;

use sal_core::env::Instance;
use sal_core::wfc::Checker;
use sal_core::{SalEnv, SalError};
use sal_engine::explicit::Path as CePath;
use sal_flat::fexpr::LeafType;
use sal_flat::flatten::FlatModule;
use sal_flat::value::Value;
use sal_syntax::ast::{ExprKind, Name};

/// Minimal option scanner: collects positional args and recognized
/// `--opt=value` / `--opt value` options, ignoring verbosity.
pub struct Args {
    pub positional: Vec<String>,
    pub options: Vec<(String, Option<String>)>,
}

/// Long options accepted (and ignored where semantics-neutral) by every
/// tool; unknown options are rejected like the oracle does.
const COMMON_FLAGS: &[&str] = &[
    "assertion", "module", "depth", "verbose", "backward", "forward",
    "iterative", "induction", "delta-path", "acyclic", "complete-path",
    "disable-traceability", "enable-ate", "disable-ate",
    "uppercase-keywords", "help", "version", "enable-dynamic-reorder",
    "disable-dynamic-reorder", "enable-slicer", "disable-slicer",
    "solver", "lemma", "monolithic", "smcinit", "branch", "noprune",
    "fullpath", "latching", "incremental", "incrinit", "incrext", "noslice",
    "innerslice", "testpurpose", "id", "ed", "md", "static-order",
];

pub fn parse_args(value_opts: &[&str]) -> Args {
    let mut positional = Vec::new();
    let mut options = Vec::new();
    let mut args = std::env::args().skip(1).peekable();
    while let Some(a) = args.next() {
        if a == "-v" || a == "--verbose" {
            let _ = args.next();
        } else if let Some(rest) = a.strip_prefix("--") {
            if let Some((k, v)) = rest.split_once('=') {
                if !COMMON_FLAGS.contains(&k) && !value_opts.contains(&k) {
                    reject_option(&a);
                }
                options.push((k.to_string(), Some(v.to_string())));
            } else if value_opts.contains(&rest) {
                options.push((rest.to_string(), args.next()));
            } else {
                if !COMMON_FLAGS.contains(&rest) {
                    reject_option(&a);
                }
                options.push((rest.to_string(), None));
            }
        } else if let Some(rest) = a.strip_prefix('-') {
            // short options with a value (-d 10, -l lemma, -s solver,
            // -io orderfile)
            if ["d", "l", "s", "io", "id", "ed", "md"].contains(&rest) {
                options.push((rest.to_string(), args.next()));
            } else if ["i", "ei", "ea", "ice"].contains(&rest) {
                options.push((rest.to_string(), None));
            } else {
                reject_option(&a);
            }
        } else {
            positional.push(a);
        }
    }
    Args {
        positional,
        options,
    }
}

fn reject_option(opt: &str) -> ! {
    eprintln!("Illegal option `{}'. Try `--help' for more information.", opt);
    std::process::exit(255)
}

impl Args {
    pub fn opt(&self, name: &str) -> Option<&str> {
        self.options
            .iter()
            .rev()
            .find(|(k, _)| k == name)
            .and_then(|(_, v)| v.as_deref())
    }

    pub fn flag(&self, name: &str) -> bool {
        self.options.iter().any(|(k, _)| k == name)
    }
}

/// Resolve `ctx` / `ctx.sal` / `ctx{actuals}` (as a parsed Name) into an
/// instance.
pub fn resolve_context(
    env: &SalEnv,
    checker: &Checker,
    name: &str,
) -> Result<Rc<Instance>, SalError> {
    if name.contains('/') || name.ends_with(".sal") {
        let def = env.parse_file(Path::new(name))?;
        let inst = env.plain_instance(def);
        checker.check_instance(&inst)?;
        return Ok(inst);
    }
    // possibly parameterized: parse as an expression fragment
    if name.contains('{') {
        let e = sal_syntax::parse_expr(&format!("{}!__x", name)).map_err(|pe| {
            SalError::global(format!("Invalid context reference \"{}\": {}", name, pe))
        })?;
        if let ExprKind::Name(Name { ctx: Some(cn), .. }) = &e.kind {
            return checker.resolve_context_name_pub(&env.prelude, cn);
        }
        return Err(SalError::global(format!(
            "Invalid context reference \"{}\".",
            name
        )));
    }
    let def = env.load_context(name)?;
    let inst = env.plain_instance(def);
    checker.check_instance(&inst)?;
    Ok(inst)
}

/// Resolve an assertion reference: either `name` within `default_ctx`, or a
/// qualified `ctx{...}!name`.
pub fn resolve_qualified(
    env: &SalEnv,
    checker: &Checker,
    reference: &str,
) -> Result<(Rc<Instance>, String), SalError> {
    let e = sal_syntax::parse_expr(reference).map_err(|pe| {
        SalError::global(format!("Invalid reference \"{}\": {}", reference, pe))
    })?;
    let ExprKind::Name(n) = &e.kind else {
        return Err(SalError::global(format!(
            "Invalid reference \"{}\".",
            reference
        )));
    };
    match &n.ctx {
        Some(cn) => {
            let inst = checker.resolve_context_name_pub(&env.prelude, cn)?;
            Ok((inst, n.id.name.clone()))
        }
        None => Err(SalError::global(format!(
            "Reference \"{}\" must be qualified with a context.",
            reference
        ))),
    }
}

/// Print a path of decoded states (from the symbolic engine).
pub fn print_states(flat: &FlatModule, states: &[Vec<Value>], header: &str) {
    println!("{}", header);
    println!("========================");
    println!("Path");
    println!("========================");
    for (i, state) in states.iter().enumerate() {
        println!("Step {}:", i);
        println!("--- System Variables (assignments) ---");
        for (li, v) in state.iter().enumerate() {
            let leaf = &flat.leaves[li];
            println!("{} = {}", leaf.name, display_leaf(leaf, v));
        }
        println!("------------------------");
    }
}

/// Print a counterexample path in the oracle's general shape.
pub fn print_path(flat: &FlatModule, path: &CePath, header: &str) {
    println!("{}", header);
    println!("========================");
    println!("Path");
    println!("========================");
    for (i, (state, prov)) in path.steps.iter().enumerate() {
        println!("Step {}:", i);
        println!("--- System Variables (assignments) ---");
        for (li, v) in state.iter().enumerate() {
            let leaf = &flat.leaves[li];
            println!("{} = {}", leaf.name, display_leaf(leaf, v));
        }
        println!("------------------------");
        if let Some(p) = prov {
            if !p.is_empty() {
                println!("Transition Information: ");
                println!("(label {})", p);
                println!("------------------------");
            }
        }
    }
}

pub fn display_leaf(leaf: &sal_flat::fexpr::LeafInfo, v: &Value) -> String {
    match (v, &leaf.ty) {
        (Value::Scalar(_, i), LeafType::Scalar(_, elems)) if *i < elems.len() => {
            elems[*i].clone()
        }
        (Value::Bool(b), _) => b.to_string(),
        (Value::Num(n), _) => {
            if n.is_integer() {
                n.to_integer().to_string()
            } else {
                format!("{}/{}", n.numer(), n.denom())
            }
        }
        (other, _) => format!("{}", other),
    }
}

/// Build the symbolic engine honoring --static-order=<name> and
/// -io <order-file>.
pub fn build_symbolic<'m>(
    flat: &'m sal_flat::flatten::FlatModule,
    args: &Args,
) -> Result<sal_engine::symbolic::Symbolic<'m>, String> {
    use sal_engine::ordering;
    let order = if let Some(path) = args.opt("io") {
        let text = std::fs::read_to_string(path)
            .map_err(|e| format!("cannot read order file \"{}\": {}", path, e))?;
        ordering::order_from_file(flat, &text)?
    } else {
        let strategy = match args.opt("static-order") {
            Some(name) => ordering::StaticOrder::parse(name)
                .ok_or_else(|| format!("unknown static order strategy \"{}\"", name))?,
            None => ordering::StaticOrder::MinSupp,
        };
        ordering::compute_order(flat, strategy)
    };
    let mut engine =
        sal_engine::symbolic::Symbolic::with_order(flat, &order).map_err(|e| e.to_string())?;
    // dynamic variable reordering (group sifting): opt-in via
    // --enable-dynamic-reorder, matching the oracle's default. The
    // min-supp static order is usually better than what budgeted sifting
    // finds; reordering pays on models where the static heuristics fail.
    let enable = args.flag("enable-dynamic-reorder") && !args.flag("disable-dynamic-reorder");
    engine.mgr.set_reorder(enable);
    Ok(engine)
}
