# Architecture

How a SAL specification becomes a verdict, and where to look when
something goes wrong. Read this before diving into any crate.

## The pipeline

Every tool runs the same front half and picks an engine for the back half:

```
                    .sal file
                        │
   sal-syntax     parse ▼  (lexer.rs → parser.rs → ast.rs)
                    SalContext (concrete AST)
                        │
   sal-core    resolve+ ▼  (env.rs: instances, prelude.rs, wfc.rs: checker)
               typecheck
                    Instance (symbol tables, parameter bindings)
                        │
   sal-flat     flatten ▼  (flatten.rs: module algebra, eval.rs: evaluator)
                    FlatModule = leaf variables + init/trans constraints
                    TFormula   = LTL/CTL formula over FExpr atoms
                        │
   sal-engine   check   ▼
        ┌───────────┬───────────┬───────────┬──────────────┐
   symbolic.rs   bmc.rs      smt.rs     explicit.rs
   (BDD: smc,   (SAT: bmc)  (SMT:       (reference
   deadlock,                 inf-bmc)    implementation,
   path, atg)                            used in tests)
                        │
   sal-cli      print   ▼  (one binary per tool; common.rs = shared CLI)
                verdict + trace in the oracle's output format
```

The **golden test suite** (`tests/golden/manifest.jsonl`, 800 verdicts
produced by the original SAL 3.3 binaries in `.oracle/`) defines
correctness: when the language manual and the oracle disagree, the oracle
wins. `tools/check-parity.py` runs the whole suite; `cargo test` runs a
fast curated subset plus unit tests.

## Crate map

| Crate | Contents | Start reading at |
|---|---|---|
| `sal-syntax` | lexer, recursive-descent parser (mirrors the oracle's LALR grammar, see `docs/grammar-notes.md`), AST, round-trip printer | `ast.rs` |
| `sal-core` | context loading/instantiation (`env.rs`), builtin prelude, name resolution + type checker (`wfc.rs`), semantic types (`types.rs`) | `env.rs` |
| `sal-flat` | the flattener: module composition → transition system over *leaf* variables | `flatten.rs` top comment |
| `sal-engine` | the four checking engines + BDD manager + LTL→Büchi + variable ordering | `symbolic.rs` |
| `sal-cli` | flag-compatible binaries; `common.rs` has arg parsing, context resolution, trace printing | `common.rs` |

## The two central data structures

**`FlatModule`** (`sal-flat/src/flatten.rs`) — everything the engines
consume. State is a vector of *leaves*: scalar variables of type bool,
bounded integer range, unbounded int/real, or enumeration. Aggregates
(tuples, records, finite arrays/functions, finite datatypes) were
decomposed structurally by the flattener; quantifiers over finite domains
were expanded; constants were evaluated away.

- `invariants` — DEFINITION-section equations + subtype predicates; hold
  in *every* state (engines conjoin them to init and, primed, to every
  transition).
- `init_defs` + `init_choices` — initial-state constraints; unassigned
  variables are unconstrained.
- `trans_defs` + `trans: TransNode` — the transition relation, with the
  composition shape preserved (`Cmds` = guarded-command choice, `All` =
  synchronous conjunction, `Interleave` = asynchronous choice with frame
  conditions). Engines lower this shape natively (e.g. the BDD engine
  keeps it as a disjunctive partition).
- `components` — the base-module instances of the composition, used only
  by the static variable-ordering heuristics.

**`FExpr`** (`sal-flat/src/fexpr.rs`) — expressions over leaves:
`Var(leaf, primed)` plus boolean/arithmetic operators. `TFormula` wraps
FExpr atoms with LTL/CTL operators.

## Semantics that are easy to get wrong

These were all discovered by probing the oracle (probe models live in the
git history; the parity suite guards them):

- **ELSE guards** are `¬(∨ sibling guards)` — but note the oracle itself
  has a bug substituting module parameters inside else-guards
  (sync_peterson divergence, see README).
- **Missing TRANSITION section** = stutter: the module's step keeps its
  controlled variables unchanged (except definition-bound ones).
- **Shared local variables**: same-named locals become nested *tuples*
  under binary composition (`pc.1`, `pc.2`) and *arrays* under
  multi-composition (`pc[i]`). Implemented in `merge_binary`/`merge_multi`.
- **Frames**: a guarded command implicitly holds its module's unassigned
  controlled leaves constant; async interleaving frames the other side's
  controlled leaves; `trans_defs`-bound leaves are never framed.
- **Declaration-order visibility**: a name declared *later* in a context
  must not shadow the prelude inside *earlier* bodies (`EvalCtx::visible`).
- **Context decls shadow prelude builtins**: a scalar element named `X`
  beats the LTL operator `X`.
- **sal-bmc default** checks one path of length exactly `--depth`
  (`--iterative` restores incremental search).

## The BDD engine (`sal-engine/src/bdd.rs` + `symbolic.rs`)

The manager is hash-consed with three non-obvious properties:

1. **Variable identity ≠ level.** `level_of`/`var_at` hold the current
   order; operations pick top variables by level. Current-state bits are
   *even* variables, next-state *odd*, and each `(2k, 2k+1)` pair sits on
   adjacent levels (cur above next) — that makes priming a structural map
   (`shift(±1)`) and is preserved by reordering, which sifts pairs as
   groups.
2. **Reordering is in-place**: `NodeId`s survive a reorder and keep
   denoting the same function. Nodes that collide during a swap become
   *forwards*; everything resolves them (`resolve`/`repair`), and fixpoint
   loops must compare with `Mgr::same`, never `==`, on stored ids.
3. **GC needs complete roots.** `reorder_if_needed(roots)` may only be
   called at *safe points* where the caller enumerates every BDD it still
   holds (see `Symbolic::reorder_point` and the pending-roots stack in
   `enc_trans_parts`). Handing incomplete roots corrupts the manager —
   the randomized test in `bdd.rs` exists precisely because this happened.

Encoding: boolean leaves are one BDD variable; other finite leaves are
binary-encoded with a domain constraint. Non-boolean expressions are
encoded as *partitions* — `Vec<(Value, condition-BDD)>` — with bitwise
fast paths for `Var = Var` / `Var = Const`. The transition relation is a
**disjunctive partition** (one BDD per interleaving branch/command);
`image`/`preimage` iterate the parts.

Static variable order (`ordering.rs`) is a port of the oracle's
`ordering.scm`: min-supp greedy component permutation + weight-sorted
layout. Dynamic reordering is opt-in (`--enable-dynamic-reorder`) because
the static order usually wins on this corpus.

## Testing layers

1. `cargo test` — unit tests (lexer, BDD incl. randomized reorder
   equivalence, flattener semantics, engine differential) + corpus
   round-trip + fast golden subset (`sal-cli/tests/golden.rs`).
2. `tools/check-parity.py` — full 735-case golden sweep vs the manifest
   (`SAL_RS_PROFILE=release`, ~20 min).
3. `tools/differential-wfc.py` — mutation-based differential testing.
4. `tools/benchmark.py` — oracle-vs-Rust wall-time comparison.

## Known gaps

`.lsal` (Lisp syntax) inputs; `--enable-ate` (infinite-index arrays);
`sal-sim`/`sal-wmc`/`sal-emc`; needham-class performance (datatype
partition merges — an encoder problem, not an ordering problem);
`--backward` accepted but runs forward reachability.
