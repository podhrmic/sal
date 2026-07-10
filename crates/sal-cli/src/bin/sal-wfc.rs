//! SAL Well-Formedness Checker (Rust reimplementation).
//!
//! Usage: sal-wfc [options] [context-name]
//!    or  sal-wfc [options] [file-name]
//!
//! Prints "Ok." and exits 0 on success; prints "Error: ..." and exits -1
//! (255) on failure, matching the oracle.

use std::path::Path;
use std::process::ExitCode;

use sal_core::wfc::Checker;
use sal_core::SalEnv;

fn main() -> ExitCode {
    let mut main_arg: Option<String> = None;
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "-v" | "--verbose" => {
                let _ = args.next();
            }
            "-h" | "--help" => {
                print_help();
                return ExitCode::SUCCESS;
            }
            _ if a.starts_with("--verbosity") => {}
            _ => {
                if main_arg.is_some() {
                    eprintln!("Illegal argument `{}'.", a);
                    return ExitCode::from(255);
                }
                main_arg = Some(a);
            }
        }
    }
    let Some(target) = main_arg else {
        print_help();
        return ExitCode::from(255);
    };

    let env = SalEnv::new();
    let checker = Checker::new(&env);
    let result = (|| {
        let def = if target.contains('/') || target.ends_with(".sal") {
            env.parse_file(Path::new(&target))?
        } else {
            env.load_context(&target)?
        };
        let inst = env.plain_instance(def);
        checker.check_instance(&inst)
    })();

    match result {
        Ok(()) => {
            println!("Ok.");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("{}", e);
            ExitCode::from(255)
        }
    }
}

fn print_help() {
    println!("SAL Well-Formedness Checker");
    println!("Usage: sal-wfc [options] [context-name]");
    println!("   or  sal-wfc [options] [file-name]");
}
