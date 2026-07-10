# SAL 3.3 concrete syntax — facts extracted from the oracle's parser
(`sal-parser.scm` in the 3.3 source; these override the language manual)

## Lexer
- Keywords are **case-insensitive** (`begin`, `BEGIN`, `Begin` all keywords)
  unless `--uppercase-keywords`. Keyword set: type array of with lambda forall
  exists let in if then else elsif endif begin end rename to context module
  input output global local initialization definition transition theorem
  lemma claim obligation observe implements datatype state_type init_pred
  trans_pred scalarset ringset importing suffix prefix.
- `AND OR NOT XOR DIV MOD div mod and or not xor` are operators recognized in
  **exact lower or exact upper case only** (`And` is an identifier).
- Identifiers: `[A-Za-z_][A-Za-z0-9?_]*`, or an opchar-identifier that must
  **start** with one of `$ & @ ^ ~` followed by opchars (opchar = anything
  not alnum, `()[]{}%,.:;#\!?_|`, or whitespace). A bare `_` is the
  UNBOUNDED token.
- Numerals: decimal, hex `0x…`, binary `0b…` (normalized to decimal).
  Floats: `NUMERAL . NUMERAL` parsed in the grammar as application
  `/(nd, 10^len(d))` (a rational).
- Strings: `"…"` with backslash escapes.
- Fixed tokens: `(# #) [# #]` (record literal/type), `:= .. = => / /= || []
  + -> --> - * < <= <=> > >= |- | ' . , : ; ! ( ) [ ] { } %`(comment to EOL).
- Fragment entry points via invisible tokens `@BTE@`(expr) `@BTT@`(type)
  `@BTM@`(module) `@BTA@`(assertion name) `@BTI@`(import) — used to parse
  CLI arguments like `--assertion='ctx{10}!name'`.

## Precedence (highest → lowest, from the lalr declarations)
application/`[idx]` > `.` > unary `-` > `* / DIV MOD` > `+ -` >
`WITH` > `= /= < > <= >=` > `NOT` > `AND` > `OR` > `XOR` >
`=>` (right-assoc) > `<=>` > `||` (module sync) > `[]` (module async) >
module-`WITH` > `:` > `IN`. All left-assoc unless noted.
Note: **XOR is looser than OR** (manual said equal); comparisons are
left-assoc in the impl (manual said non-assoc).

## Grammar deviations from the manual
- Function types are **unary only**: `[T1, T2 -> T]` rejected with an error
  suggesting a tuple domain.
- `IMPORTING ctxref` declaration exists (with `WITH a TO b, …` renames).
- Type defs additionally: `SCALARSET(expr)`, `RINGSET(expr)`.
- State-type syntax is `STATE_TYPE(module)`, `INIT_PRED(module)`,
  `TRANS_PRED(module)` (not `M.STATE`/`M.INIT`/`M.TRANS`).
- Context actuals `{…}` are a uniform list of exprs/types separated by
  `,` or `;` with optional leading/trailing `;` — arity/kind is resolved
  against the referenced context's parameter list.
- Assertion bodies are only `module |- expr` or `module IMPLEMENTS module`.
- LET declarations require a type: `LET x : T = e IN e`.
- Update expr: `e WITH access+ := e`, where access includes `(args)`
  (function update) besides `[i]`, `.field`, `.num`.
- LHS: `IDENT ['] access*` (quote immediately after the identifier).
- Guarded commands inside `[ … ]` are separated by `[]`; ELSE must be last;
  labels only on guarded/else commands (not on multi-commands);
  multi-command: `([] (v: T): cmd)`, no nested ELSE.
- Base module sections may repeat and appear in any order; a trailing `;`
  after each section's item list is allowed.
- Declarations in a context body are each terminated by `;` (required).
- Empty context body is a parse error ("Invalid empty context.").
- Uninterpreted: `x: T`, `f(x: T): T`, `t: TYPE` (no `=`) all legal
  declarations.
- Module instance actuals use square brackets: `name[e1, e2]`.
- Parenthesized exprs/modules record a PARENS count (printer fidelity).
