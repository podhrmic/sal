# Rewriting SAL (Symbolic Analysis Laboratory) in Rust — Project Plan

## 1. What we are rewriting

SAL 3.3 (SRI, 2013) is a framework for specifying and analyzing transition
systems. It consists of:

- **The SAL language** (defined in *The SAL Language Manual*, SRI-CSL-01-02
  Rev. 2): contexts containing type, constant, module, and assertion
  declarations. Modules are transition systems (INPUT/OUTPUT/GLOBAL/LOCAL
  variables, DEFINITION/INITIALIZATION/TRANSITION sections with definitions
  and guarded commands) composed synchronously (`||`), asynchronously (`[]`),
  and via multi-composition, RENAME, LOCAL/OUTPUT hiding, WITH, and OBSERVE.
  The type system is PVS-like: booleans, (unbounded) integers/naturals/reals,
  subranges, predicate subtypes, scalars (enumerations), recursive DATATYPEs,
  arrays, tuples, records, higher-order function types, dependent types.
  Assertions are `module |- temporal-formula` with LTL (`G`, `F`, `X`, `U`,
  `W`, …) and CTL (`AG`, `AF`, `EG`, …) operators supplied by prelude
  contexts.

- **The tool suite** (Scheme, ~256 source files, compiled with Bigloo; C glue
  for CUDD BDDs, GMP, SAT solvers; bundled Yices 1.0.38):

  | Tool | Function | Priority |
  |------|----------|----------|
  | `sal-wfc` | well-formedness/type checker | P0 |
  | `sal-smc` | BDD-based symbolic model checker (LTL + CTL fragment), counterexamples | P0 |
  | `sal-deadlock-checker` | BDD-based deadlock detection | P0 |
  | `sal-bmc` | SAT-based bounded model checking + k-induction (finite state) | P0 |
  | `sal-inf-bmc` | SMT-based BMC + k-induction (infinite state, via Yices) | P0 |
  | `sal-sim` | interactive/scripted simulator | P1 |
  | `sal-path-finder` / `sal-path-explorer` | random/guided path generation | P1 |
  | `sal-atg`, `sal-atg2` | automated test generation | P2 |
  | `sal-emc`, `sal-wmc` | explicit-state / witness model checkers | P2 |
  | `sal2bool`, `sal-sld`, `sal-sc`, `lsal2xml`, `ltl2buchi`, `salenv` (Scheme REPL) | translators & environment | P2 |

  P0 = must pass full differential suite; P1 = functional parity on examples;
  P2 = best effort / out of initial scope (documented gaps). The `salenv`
  Scheme REPL API is explicitly **out of scope**; we provide equivalent CLI
  flags instead.

## 2. Ground truth and references (already acquired)

- Source: `https://sri-fm.github.io/sal/opendownload/sal-3.3-src.tar.gz`
  (kept unpacked for algorithm reference — flattening, slicing, LTL→Büchi,
  BMC encodings live in `src/sal-*.scm`).
- **Oracle**: the official x86_64 Linux binary distribution
  (`sal-3.3-bin-x86_64-unknown-linux-gnu.tar.gz`) runs on this machine
  (verified: `sal-smc` proves `peterson.sal mutex`, produces counterexamples,
  `sal-bmc`/`sal-inf-bmc` work with the *bundled* Yices 1.0.38 first on
  PATH). `tools/get-oracle.sh` reproduces the installation into `.oracle/`.
- Docs: language report + tutorials in `reference/` (fetched from
  sri-fm.github.io).
- Examples: 65 `.sal` files in the source tarball `examples/` + the website
  example set (arbiter, bakery, fischer, inf-bakery, pcp, peterson, qlock,
  short, simpson, skdmxa, stack, ultralog, needham…). Vendored under
  `tests/corpus/`.

- Licensing note: SAL is GPL/dual-licensed and this rewrite is developed with
  the GPL source open as a reference, so the Rust code is **GPLv2** unless a
  separate license is negotiated with SRI (fm-licensing@csl.sri.com).

## 3. Architecture of the Rust implementation

Cargo workspace `sal-rs`:

```
crates/
  sal-syntax     lexer, parser, concrete AST, source positions, pretty-printer
  sal-ast        resolved AST, symbol tables, context instantiation
  sal-typecheck  type checker + well-formedness (TCC generation points)
  sal-flat       module algebra → FlatModule: state vars + Expr-level
                 init/trans/definition/invariant, composition, slicing (cone
                 of influence), LTL/CTL formula extraction from assertions
  sal-enum       concrete value domains, expression evaluator (explicit
                 engine: simulator, random path, explicit deadlock check)
  sal-bdd        boolean encoding of finite types + BDD engine
  sal-smc        CTL fixpoint checking; LTL via Büchi/tableau product with
                 fairness; witness/counterexample reconstruction
  sal-bmc        CNF unrolling, SAT interface, k-induction
  sal-smt        SMT-LIB2 emission, external solver driver (Yices2/Z3),
                 infinite-state BMC + k-induction
  sal-cli        one binary per tool (sal-wfc, sal-smc, sal-bmc,
                 sal-inf-bmc, sal-deadlock-checker, sal-sim, …) with
                 flag-compatible CLIs
```

Key design decisions:

1. **Pipeline mirrors the original**: parse → typecheck → instantiate
   assertion's module → flatten (compose) → slice w.r.t. property → encode
   (BDD / CNF / SMT) → check → decode counterexample back through the
   flattening map so traces print in terms of original variable names and
   transition labels (the oracle prints module-instance/label provenance —
   we must preserve that mapping).
2. **BDD engine**: start with `biodivine-lib-bdd` (pure Rust, mature);
   abstract behind a trait so a bespoke engine (with dynamic reordering à la
   CUDD) can replace it if performance on the larger examples (dme, md80,
   tta-startup) demands it. Variable ordering: interleave current/next bits,
   respect `--var-order` files (`.ord` files exist in the corpus).
3. **SAT**: pure-Rust CDCL via `rustsat` + `batsat`/`splr` (no C deps);
   DIMACS dump option for debugging parity with the oracle's
   `yices --dimacs` path.
4. **SMT**: emit SMT-LIB2 and drive an external `yices-smt2` or `z3`
   process — same architecture as the original (which shells out to Yices 1).
   Solver choice via `--solver`, auto-detected.
5. **LTL→Büchi**: implement the standard tableau (GPVW/LTL2BA-style)
   translation in-tree; the original ships a `ltl2buchi` helper which we also
   expose as a binary for differential testing of just that stage.
6. **Semantics of guarded commands** (manual §4–5): guards may reference
   next-state variables; chosen command's assignments conjoined with all
   DEFINITION section constraints; unassigned components framed
   (`x'[i].f = …` ⇒ rest of `x` unchanged); ELSE = negation of other guards;
   async composition eliminates definitions into commands; initialization
   combination per §5.4. These subtleties are where divergence bugs will
   live — each gets targeted unit tests derived from the manual's examples.
7. **Numerics**: unbounded integers/rationals (`num-bigint`/`num-rational`)
   — SAL REALs are mathematical reals; finite subranges detected for
   boolean encoding exactly as the oracle does.

## 4. Test strategy (built FIRST, before any Rust code)

### 4.1 Corpus

`tests/corpus/` = all `.sal` files from the tarball examples + website
examples (with READMEs recording provenance and the commands each README
suggests). `.ord` variable-order files kept alongside.

### 4.2 Golden verdict manifest

`tools/gen-golden.sh` enumerates every assertion (THEOREM/LEMMA/CLAIM/
OBLIGATION) in every corpus context and runs the **oracle**:

- `sal-wfc <file>` → `ok | error(message)`
- `sal-smc <file> <assertion>` → `proved | counterexample(k states) | error`
- `sal-deadlock-checker <file> <module>` → `ok | deadlock`
- `sal-bmc --depth=10 <file> <assertion>` → `no-ce-up-to-depth | counterexample(k)`
- `sal-bmc -i --depth=10` (k-induction) where README suggests it
- `sal-inf-bmc -d 10 [-i]` for the infinite-state examples (inf-bakery,
  inf-skdmxa, fischer, …)

Each run bounded by a timeout (default 120 s; big models tagged `slow` and
given 20 min in a nightly lane, `timeout` recorded as a legitimate golden
outcome otherwise). Results in `tests/golden/manifest.toml`:
`{file, tool, args, assertion, verdict, ce_depth?, wall_time}`.
The manifest is committed — tests run without the oracle installed.

### 4.3 Test layers

1. **Unit tests** per crate (lexer/parser round-trip: `parse ∘ print ∘ parse`
   idempotent on all corpus files; typechecker accept/reject cases; guarded
   command semantics micro-models with hand-computed reachable sets).
2. **Golden tests** (`cargo test --test golden`): run *our* binaries over the
   manifest; compare **verdicts**, not raw text: proved/counterexample
   status, counterexample length, deadlock yes/no. Counterexample traces are
   validated *semantically*: replay the trace through our evaluator and check
   init/trans/¬property — this avoids depending on the oracle's
   nondeterministic choice of trace.
3. **Differential tests** (`tools/differential.sh`, requires `.oracle/`):
   re-runs oracle and Rust side by side on (a) the corpus, (b) **generated
   models** from a small random SAL model generator (finite scalar/subrange
   state spaces small enough for both engines), comparing verdicts and CE
   lengths. Any divergence is minimized and archived under
   `tests/regressions/`.
4. **Error-path tests**: corpus files mutated (undeclared identifiers, type
   errors, non-finite state for sal-smc) must be *rejected by both* — checks
   our sal-wfc parity.

### 4.4 Acceptance criteria ("passes all tests and examples")

- 100% of golden manifest entries for P0 tools match (excluding entries whose
  golden verdict is `timeout`, where we require "no wrong verdict").
- Round-trip parse of 100% of corpus files.
- Differential campaign: ≥10k generated models, zero verdict divergences.

## 5. Milestones & order of work

| # | Milestone | Exit criterion |
|---|-----------|----------------|
| M0 | Repo scaffold, oracle script, corpus vendored | `tools/get-oracle.sh && tools/gen-golden.sh` produce committed manifest |
| M1 | Golden manifest generated | manifest.toml covers every corpus assertion × P0 tool |
| M2 | sal-syntax | round-trip on 100% corpus; parse-error parity spot-checks |
| M3 | sal-typecheck + `sal-wfc` | wfc verdict parity on corpus + mutated corpus |
| M4 | sal-flat + sal-enum + `sal-deadlock-checker` (explicit) + `sal-sim` (batch) | deadlock verdicts parity on small/medium models |
| M5 | sal-bdd + `sal-smc` (G-safety first, then full LTL via Büchi, CTL) + BDD deadlock | sal-smc golden parity |
| M6 | sal-bmc (SAT, k-induction) | sal-bmc golden parity |
| M7 | sal-smt + `sal-inf-bmc` | inf-bmc golden parity |
| M8 | Differential fuzz campaign, perf pass on slow examples, docs | acceptance criteria §4.4 |

Rationale for order: each engine reuses the previous layer, and the explicit
evaluator (M4) doubles as the semantic validator for counterexample traces
from every later engine.

## 6. Known risks / hard parts

- **Dependent & predicate subtypes** in full generality (sal-wfc checks more
  than it proves; we match its *observable* behavior, not full TCC proving —
  the oracle defers TCCs too).
- **Guard-references-next-state + ELSE semantics** under async composition:
  subtle; covered by targeted micro-model differential tests.
- **LTL with fairness in sal-smc** (livenessN theorems in peterson/bakery
  use `G(F …) => …` patterns): needs correct Büchi product + fair-cycle
  detection (Emerson-Lei).
- **Performance** on dme/md80/tta-startup: pure-Rust BDD without dynamic
  reordering may lag CUDD; mitigation: static ordering heuristics from the
  original (`ordering.scm`), optional `cudd-sys` backend behind a feature.
- **Oracle quirks**: the concrete grammar accepted by the oracle is more
  liberal than the manual (e.g. Opchar identifiers, `RING` display); when
  manual and oracle disagree, **the oracle wins** (differential tests define
  the spec).
- **Yices 1.x** counterexample formats differ from Yices2/Z3; we only match
  *verdicts and CE length*, and revalidate traces with our own evaluator.

## 7. Deliverables

- `sal-rs` workspace with flag-compatible binaries for all P0/P1 tools.
- Committed golden manifest + corpus + regression corpus.
- `tools/` scripts: get-oracle, gen-golden, differential, fuzz.
- README with usage, parity matrix, and documented gaps (P2 tools).
