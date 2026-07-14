# sal-rs — SAL (Symbolic Analysis Laboratory) in Rust

A reimplementation of SRI's SAL 3.3 model-checking suite in Rust, developed
against the official binary distribution as a differential-testing oracle.

**Start with [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)** — it maps the
pipeline, the crates, the two central data structures, and the semantics
gotchas. `PLAN.md` has the full project plan and `docs/grammar-notes.md` the
concrete-syntax facts extracted from the original implementation.

## Tools

| Tool | Backend | Status |
|------|---------|--------|
| `sal-wfc` | name resolution + type checker | 91/91 golden verdicts; 150 mutants: 0 divergences |
| `sal-smc` | BDD engine: invariants (shortest CEs), CTL fixpoints, LTL via Büchi product + Emerson-Lei | golden parity except perf timeouts |
| `sal-deadlock-checker` | BDD reachability | golden parity except perf timeouts |
| `sal-bmc` | SAT (varisat), bounded LTL lasso semantics, k-induction with `-l` lemmas | golden parity |
| `sal-inf-bmc` | SMT-LIB2 → yices-smt2 / z3 / cvc5, same bounded semantics | golden parity except `--enable-ate` |
| `sal-path-finder` | BDD image walk | golden parity |
| `sal-atg` | BDD segment search over trap variables (tests/atg examples + oracle goldens) | matches oracle test counts & goal sets; shorter tests (shortest-segment search) |
| `sal-sim`, `sal-wmc`, `sal-emc`, lsal front-end | — | not implemented (P1/P2 in PLAN.md) |

**Overall: 696/735 (94.7%) of the golden verdict manifest matches** (lsal-syntax
cases excluded as out of scope). The 39 remaining mismatches:

- 12 — `sync_peterson` livenessbug1–6 (×2 engines): a genuine **oracle bug**;
  SAL 3.3 mis-substitutes module parameters inside ELSE guards, producing
  spurious counterexamples. Our verdicts follow the language semantics and
  the oracle's own else-flattening code (`ELSE = ¬(∨ guards)`, verified with
  probe models).
- ~17 — BDD performance timeouts on the largest models (needham, ultralog,
  sats, BSubSpor class): the bottleneck is datatype partition merges in the
  encoder, not variable order. Static ordering (`--static-order`, on by
  default, ported from the oracle's `ordering.scm`) and opt-in dynamic
  reordering (`--enable-dynamic-reorder`, Rudell group sifting) already
  cover the order-bound cases (arbiter{20}, phil{8}, s_qlock).
- ~10 — out of scope: `.lsal` (Lisp syntax) inputs (dme, ring, util) and
  `--enable-ate` abstraction for infinite-index arrays (stack, queue,
  pipeline).

## Layout

```
crates/sal-syntax    lexer, parser, AST, pretty-printer (round-trips the corpus)
crates/sal-core      context env, prelude, name resolution, type checker
crates/sal-flat      flattener: module algebra -> leaf-variable transition systems
crates/sal-engine    engines: BDD (own manager), explicit, SAT BMC, SMT BMC, LTL->Büchi
crates/sal-cli       flag-compatible binaries
lib/ltllib.sal       LTL pattern library (port of ltllib.lsal)
tests/corpus         .sal examples from the SAL 3.3 distribution + website
tests/golden         oracle verdict manifest (committed; 800 cases)
tools/               get-oracle.sh, gen-golden.py, check-parity.py, differential-wfc.py
```

## Testing

```sh
cargo test                                  # unit + corpus round-trip tests
tools/get-oracle.sh                         # install the SAL 3.3 oracle into .oracle/
python3 tools/gen-golden.py                 # (re)generate golden verdicts
cargo build --release
SAL_RS_PROFILE=release python3 tools/check-parity.py   # compare all tools vs golden
python3 tools/differential-wfc.py           # mutation-based differential testing
```

The golden manifest records the oracle's verdict for every assertion in the
corpus across all tools (proved / counterexample+length / no_ce /
induction_failed / deadlock / error / timeout). `check-parity.py` runs the
Rust binaries on the same cases and compares verdicts (counterexample
lengths are compared softly, since trace selection may legitimately
differ).

## Notable semantics ported from the original

- Case-insensitive keywords; operator identifiers must start with `$&@^~`.
- Same-named local variables become nested tuples under binary composition
  (`pc.1`, `pc.2`) and arrays under multi-composition (`pc[i]`).
- Definitions act as invariants (conjoined to every step); transition-
  section definitions hold across asynchronous interleaving; unassigned
  controlled variables are framed per command; ELSE guards are the negated
  disjunction of the sibling guards.
- `sal-smc` requires finite state ("Finite type expected" otherwise);
  `sal-inf-bmc` supports NATURAL/INTEGER/REAL leaves natively.
- The `{;;}` actual-parameter syntax, `ctx{...}!name` qualified names, and
  context-name = file-name rules follow the oracle.

## License

GPL-2.0 (the reimplementation was developed with the GPL source of SAL 3.3
as an algorithm reference).
