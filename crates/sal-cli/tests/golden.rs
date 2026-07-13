//! Fast golden-verdict regression tests: a curated subset of the oracle
//! manifest that runs in seconds. The full sweep is
//! `tools/check-parity.py`.

use std::path::PathBuf;
use std::process::Command;

fn corpus(dir: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/corpus").join(dir)
}

fn run(bin: &str, dir: &str, args: &[&str]) -> (i32, String) {
    let exe = match bin {
        "sal-atg" => env!("CARGO_BIN_EXE_sal-atg"),
        "sal-smc" => env!("CARGO_BIN_EXE_sal-smc"),
        "sal-bmc" => env!("CARGO_BIN_EXE_sal-bmc"),
        "sal-inf-bmc" => env!("CARGO_BIN_EXE_sal-inf-bmc"),
        "sal-wfc" => env!("CARGO_BIN_EXE_sal-wfc"),
        "sal-deadlock-checker" => env!("CARGO_BIN_EXE_sal-deadlock-checker"),
        _ => panic!("unknown bin"),
    };
    let out = Command::new(exe)
        .args(args)
        .current_dir(corpus(dir))
        .output()
        .expect("spawn");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.code().unwrap_or(-1), text)
}

fn expect(bin: &str, dir: &str, args: &[&str], needle: &str) {
    let (_, text) = run(bin, dir, args);
    assert!(
        text.contains(needle),
        "{} {:?} in {}: expected {:?}, got:\n{}",
        bin,
        args,
        dir,
        needle,
        text
    );
}

#[test]
fn peterson_suite() {
    expect("sal-smc", "dist/peterson", &["peterson", "mutex"], "proved.");
    expect("sal-smc", "dist/peterson", &["peterson", "invalid"], "Counterexample:");
    expect("sal-smc", "dist/peterson", &["peterson", "mutex_ctl"], "proved.");
    expect("sal-smc", "dist/peterson", &["peterson", "livenessbug1"], "Counterexample:");
    expect("sal-smc", "dist/peterson", &["peterson", "liveness1"], "proved.");
    expect("sal-bmc", "dist/peterson", &["-d", "10", "peterson", "invalid"], "Counterexample:");
    expect("sal-bmc", "dist/peterson", &["-i", "-d", "3", "peterson", "mutex"], "proved.");
    expect(
        "sal-deadlock-checker",
        "dist/peterson",
        &["peterson", "system"],
        "does NOT contain deadlock",
    );
}

#[test]
fn wfc_suite() {
    expect("sal-wfc", "dist/peterson", &["peterson.sal"], "Ok.");
    expect("sal-wfc", "dist/bakery", &["bakery.sal"], "Ok.");
    expect("sal-wfc", "dist/fischer", &["fischer.sal"], "Ok.");
}

#[test]
fn bakery_mutex() {
    expect(
        "sal-smc",
        "dist/bakery",
        &["--assertion=bakery{5,15}!mutex"],
        "proved.",
    );
}

#[test]
fn phil_stutter_and_ringset() {
    expect(
        "sal-smc",
        "dist/phil",
        &["--assertion=phil{4}!th1"],
        "proved.",
    );
}

#[test]
fn inf_bakery_smt() {
    expect(
        "sal-inf-bmc",
        "dist/inf-bakery",
        &["-d", "3", "inf_bakery", "mutex"],
        "no counterexample",
    );
    expect(
        "sal-inf-bmc",
        "dist/inf-bakery",
        &["-i", "-d", "1", "inf_bakery", "aux1"],
        "proved.",
    );
}

#[test]
fn else_negation_semantics() {
    // ELSE = ¬(∨ guards): pcp scheduler must be deadlock-free
    expect(
        "sal-smc",
        "web/pcp-sal",
        &["tst_pcp_generic", "deadlock_free"],
        "proved.",
    );
}

#[test]
fn infinite_state_rejected_by_smc() {
    let (_, text) = run("sal-smc", "dist/inf-bakery", &["inf_bakery", "mutex"]);
    assert!(text.contains("Error"), "expected finite-type error, got:\n{}", text);
}

#[test]
fn atg_examples() {
    // counts and undischarged sets must match the oracle goldens in
    // tests/golden/atg/
    let (_, out) = run(
        "sal-atg",
        "../atg",
        &["traffic", "controller", "traffic_goals.scm", "-ed", "8", "-id", "8"],
    );
    assert!(out.contains("1 tests generated"), "{}", out);
    assert!(
        out.contains("1 undischarged test goals:(g_unreachable)"),
        "{}",
        out
    );

    let (_, out) = run(
        "sal-atg",
        "../atg",
        &["gear", "scheduler", "gear_goals.scm", "-ed", "8", "-id", "8"],
    );
    assert!(out.contains("1 tests generated"), "{}", out);
    assert!(out.contains("All test goals discharged."), "{}", out);

    let (_, out) = run(
        "sal-atg",
        "../atg",
        &["gear", "scheduler", "gear_goals.scm", "-ed", "0", "-id", "8"],
    );
    assert!(out.contains("6 tests generated"), "{}", out);

    let (_, out) = run(
        "sal-atg",
        "../atg",
        &["boundary", "acc", "boundary_goals.scm", "-ed", "8", "-id", "20"],
    );
    assert!(out.contains("All test goals discharged."), "{}", out);
}
