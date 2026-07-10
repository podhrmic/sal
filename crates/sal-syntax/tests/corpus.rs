//! Parse every .sal file in the corpus and check the print/re-parse
//! round-trip: parse(src) -> print -> parse must succeed and print
//! identically the second time.
//!
//! Files the oracle itself rejects (golden sal-wfc verdict `error` with a
//! parse error) are expected to fail.

use std::path::{Path, PathBuf};

fn corpus_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/corpus")
        .canonicalize()
        .unwrap()
}

/// Files rejected by the oracle's own parser (from the golden manifest).
const ORACLE_REJECTS: &[&str] = &[
    "dist/BSubSpor/BSubSpor78.sal",              // uses INVARIANT extension
    "dist/tta-startup/faulty-hub/startup-faulty-guardian.sal", // m4 template
    "dist/tta-startup/faulty-node/startup-skel.sal",           // m4 template
    "web/arbiter-sal/arbiter.sal",               // uses `Array` as identifier
    "web/qlock/qlock2.sal",
];

#[test]
fn corpus_round_trip() {
    let root = corpus_root();
    let mut files: Vec<PathBuf> = walk(&root);
    files.sort();
    assert!(files.len() > 80, "corpus missing? found {}", files.len());

    let mut failures = Vec::new();
    let mut parsed = 0usize;
    for f in &files {
        let rel = f.strip_prefix(&root).unwrap().to_string_lossy().to_string();
        let src = std::fs::read_to_string(f).unwrap();
        let expect_reject = ORACLE_REJECTS.iter().any(|r| rel == *r);
        match sal_syntax::parse_context(&src) {
            Ok(ast) => {
                if expect_reject {
                    failures.push(format!("{rel}: parsed but oracle rejects it"));
                    continue;
                }
                parsed += 1;
                let printed = sal_syntax::printer::print_context(&ast);
                match sal_syntax::parse_context(&printed) {
                    Ok(ast2) => {
                        let printed2 = sal_syntax::printer::print_context(&ast2);
                        if printed != printed2 {
                            failures.push(format!("{rel}: round-trip print mismatch"));
                        }
                    }
                    Err(e) => {
                        failures.push(format!("{rel}: printed form fails to re-parse: {e}"))
                    }
                }
            }
            Err(e) => {
                if !expect_reject {
                    failures.push(format!("{rel}: {e}"));
                }
            }
        }
    }
    eprintln!("parsed {parsed} corpus files");
    assert!(
        failures.is_empty(),
        "{} corpus failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

fn walk(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for entry in std::fs::read_dir(dir).unwrap() {
        let p = entry.unwrap().path();
        if p.is_dir() {
            out.extend(walk(&p));
        } else if p.extension().map_or(false, |e| e == "sal") {
            out.push(p);
        }
    }
    out
}
