# KatLang Agent Instructions

## Project Overview

- These instructions are for Codex and other AI coding agents working in this repository.
- `AGENTS.md` is the canonical shared agent-instructions file for this repo.
- KatLang's authoritative language model is `lean/KatLang.lean`.
- The C# implementation in `src/KatLang/` must stay semantically aligned with Lean.
- If Lean and C# are both wrong for the same bug, fix both together when feasible.
- Keep this file operational and concise.

## Core Architecture

- `lean/KatLang.lean`: source of truth for AST shape, evaluation rules, and invariants.
- `lean/CoreTests.lean`, `lean/AstDemo.lean`: Lean-side regression and AST compatibility checks.
- `lean/CoreArityAlgebra.lean`, `lean/CoreArityAlgebraProofs.lean`, `lean/CoreArityAlgebra.md`: isolated paper-facing extraction of KatLang's arity algebra; it must stay faithful to `lean/KatLang.lean` but is not authoritative semantics.
- `src/KatLang/`: C# AST, parser, front-end elaboration, evaluator, diagnostics, and public API.
- `src/KatLang/Semantics/`: editor-facing semantic tooling only; it is not the evaluator and not the normative semantics layer.
- `tests/KatLang.Tests/`: parser, evaluator, elaboration, semantics, and integration regression coverage.
- `tutorial.md`, `KatLang.ebnf`, and generator prompt/agent files must stay aligned with real language behavior.

## Language Semantics And Design Rules

- Lean 4 wins over implementation convenience, performance, or stylistic preference.
- `lean/CoreArityAlgebra.lean` defines the algebra. `lean/CoreArityAlgebraProofs.lean` proves the small laws and executable checks. If either diverges from `lean/KatLang.lean`, fix the artifact or explicitly change the authoritative model first.
- If Lean is ambiguous for a requested behavior change, stop and clarify before implementing.
- Do not invent syntax or semantics that are not in Lean unless the task explicitly includes the Lean change.
- Do not add new operators, convenience syntax, implicit coercions, hidden fallbacks, or AST simplifications that erase Lean distinctions.
- Preserve structural distinctions in the AST and runtime model. In particular, `.dotCall`, `open`, and `Output = expr` are language-level constructs, not incidental parser sugar.
- `Expr.SequenceConstruct` / `.sequenceConstruct` is an INTERNAL sequence-join node, not the AST representation of written parenthesized sequence values (those parse to zero-parameter blocks; `()` to the empty-sequence node). Its evaluation drops `()` leaves, so routing surface syntax through it would violate visible-empty semantics — the parser must never produce it (guarded by `SequenceConstructContainmentTests`, CoreTests internal-node guards, and the semantic explorer's internal-node cases; see `docs/design/sequence-boundary-audit-2026-07.md` §7).
- `Output = expr` is reserved result syntax. `Algo.Output` and `Algo.Output(...)` are invalid.
- Ownership-first lookup is fundamental. Keep lookup behavior aligned across evaluator, parser/front-end elaboration, parameter detection, and semantic tooling.
- `open Name` may target a lexically visible private head, but `open` only exposes public members.
- `open` is a declaration/import directive, not an output expression: it takes ONE comma-separated target list (`open A, B, C`; string targets use single quotes — `open 'url', A`), parsed by a dedicated comma-list parser into individual targets (resolve, argumentless dot-call path, block, or string-load sugar). Each algorithm allows at most one `open` declaration. The first target must begin on the same physical line as `open` (`open` newline `A` is a missing-target error and `A` stays a separate row). Comma keeps its normal explicit line-continuation behavior — `open A,` newline `B` and `open A` newline `, B` both continue the list — and a leading `.` continues a dotted target (`open A` newline `.B` is `open A.B`), but a plain newline never continues `open`: `open Math` newline `Math.Pi` is an open plus a report row. `;` and same-line adjacency are NOT open-target separators (`open A ; B` and `open A B` report a missing-comma diagnostic, never two targets). Spread `...` is not open-target syntax for any atom kind, including string targets: `open A...`, `open A...B`, `open A, B...`, and `open 'url'...` are targeted parse errors, never list-like opens.
- `open 'url'` is front-end sugar for load elaboration, not a core AST construct.
- Dot-call uses structural lookup first and lexical fallback second. Structural lookup, receiver injection, fallback order, and diagnostics must stay consistent across Lean and C#.
- Ordinary lexical dot-call passes the receiver as one leading argument boundary. `A.B(C, D)` means `B(A, C, D)`, not a call where `A`'s top-level values are spread before `C` and `D`.
- Only sequence/variadic builtin dot-call paths may opt into receiver top-level expansion, and that expansion must remain explicit in builtin metadata/evaluator handling.

## Lean/C# Consistency Requirements

- `Parser.Parse(...)` and `ParseResult` are elaborated front-end outputs, not raw syntax trees.
- The raw syntax boundary is `Parser.ParseSyntax(...)`.
- `FrontEndPipeline.Process(...)` is the explicit C# front-end path for elaboration passes such as load elaboration, parameter detection, implicit argument resolution, and property exposure resolution.
- Default parse/run entry points reject unresolved `load`; only elaboration-enabled paths may consume it.
- When semantics change, update all affected layers together: Lean, C# parser/elaboration/evaluator, `src/KatLang/Semantics/`, tests, and user-facing docs.
- Avoid duplicating semantic rules across parser, evaluator, parameter detection, and semantic model code. Reuse the owning logic when possible.
- Most C# cache-like runtime machinery is implementation-only and should not be mirrored in Lean merely for performance parity. The zero-parameter property cache is the explicit exception: property-style access `A` may use the per-run cache, while explicit call `A()` bypasses that property’s cache entry. This `A` vs `A()` distinction is core KatLang semantics and is modeled in Lean.
- Lean core numeric semantics use `Int`; the current C# runtime uses `decimal`. Do not silently widen or reinterpret numeric behavior without checking Lean first.

## Builtins And Spread Conventions

- `arity` means the structural count of top-level output slots.
- `count` means the number of evaluated top-level values after sequence values are opened by the consuming operation.
- Do not treat `arity` and `count` as interchangeable.
- A property/call/builtin RESULT boundary is a value boundary: it always returns ONE value, with emitted count `Result.valueCount` (0 for the empty sequence value, otherwise 1 — a list value always counts 1, including `[]`). A multi-output body/collection is observed by the caller as one sequence value; only explicit caller-site postfix `...` re-opens it into the surrounding item supply (spread reads the value via `spreadItems` — the spread view that also opens one list boundary — not the emitted count; `toItems` is the non-spread item view and keeps lists opaque). Redundant unary sequence structure is canonicalized during ordinary value construction, including `(())` and `((()))` to `()`. The shared helper is `reCountValueBoundary` (Lean) / `ReCountValueBoundary` (C#); it re-counts the value boundary without rebuilding the value and is applied at user/conditional calls (`evalUserCallCounted`, `evalConditionalCallCounted`) and structural dot zero-arg access (`evalDotCallCounted`). Collection-producing builtins (`order`, `orderDesc`, `distinct`, `take`, `skip`, `filter`, `map`, `range`, `atoms`) materialize ONE exact list value with count 1 via `makeCollectionListResult` / `MakeCollectionListResult` and need no re-count. Rest/variadic bindings likewise store one exact list value with count 1 (`collectRest` / `CollectRest`) and need no re-count or raw-supply storage. Lexical zero-arg property access and `if` already re-counted this way; the reduce initial accumulator is likewise reified as one written accumulator slot (`reCountValueBoundary`) before reduction, so an empty reduction returns it as ONE value. NOT value boundaries (must keep their multi-item counts): root/body output accumulation (`evalAlgOutputCountedCore`), `while`/`repeat` multi-slot loop state, and the strict single-value `map`/`reduce` callback contract. Scalar/reduction builtins already return one value and are unchanged.
- Comma is the explicit expression-list separator, and same-line adjacency is an implicit comma where an expression-list context is active, so `1, 2, 3` and `1 2 3` both produce three slots there. A newline is a separate mechanism — a body/statement/output boundary, not a global implicit comma: at root output or inside an explicitly open context it may separate slots (so `1`/`2`/`3` on three lines are three output slots), but a simple one-line property body ends at the newline. Root output consumes a bare expression list as output slots; call syntax consumes it as argument slots; parentheses materialize it as one sequence value. Parsing must not depend on callable arity, runtime values, inferred types, or any other semantic information.
- Semicolon `;` is not supported as expression syntax. It is not an alternative separator or sequence constructor. The parser reports: "Semicolon is not supported as an expression separator. Use comma or adjacency for separate expressions, or parentheses for one sequence value." Use comma/adjacency for separate slots and parentheses for one sequence-valued slot, e.g. `sum((10, 20, 30))`, `take((1, 2, 3), 2)`, and row-like values as `Reports = (row1), (row2)`.
- Postfix continuations win over adjacency on the same physical line only. A `(` or `{` after a callable target on the same physical line is a call delimiter even across whitespace, while a physical newline never continues a closed expression into a call. For multiline calls, open the delimiter before the newline. Indexing `:`, postfix grace `~`, binary operators, and postfix `...` are also same-physical-line only. A leading `.` is the supported method-chain continuation. Definition bodies, explicit `Output = ...` bodies, and open target lists are line-bounded: a newline ends the body, so an expression on a following line — at any indentation — is a separate output row parsed by the surrounding output/algorithm context, never a body continuation. (Same-line adjacency, an already-open delimiter, a same-line binary operator, and a leading `.` still continue the body's single expression. Root output and algorithm/brace bodies, by contrast, keep the expression list open across newlines, so a newline there separates output slots.)
- Ellipsis `...` has two roles distinguished by ORIENTATION, matching the semantic direction (`collect : Supply -> ListValue` vs `open : Value -> Supply`). PREFIX `...name` is the canonical rest/collect BINDING marker and is valid only in binding positions — explicit parameter lists (`F(...items)`, `F(first, ...middle, last)`), nested sequence-value parameter patterns (`F((x, ...y, z))`), and assignment deconstruction, including the single-target form `...items = RHS`. The rest target must be an identifier on the SAME physical line as the marker (same-line whitespace is allowed); prefix `...` anywhere in expression position is a targeted parse error, never a spread. POSTFIX `expr...` is the spread operator described in this bullet and is unchanged. Legacy POSTFIX rest binding (`F(items...) = body`, `x, middle..., y = RHS`) still parses with identical runtime semantics but reports a `DiagnosticSeverity.Warning` naming the canonical `...name` replacement — migration compatibility only; never write it in new source, tests, docs, or generated examples. The warning is carried by `ParseResult.Diagnostics` / `FrontEndPipeline`, not by `KatLangEngine.Run` results.
- `expr...` opens ONE item-producing boundary of the evaluated value and contributes the opened items to the surrounding item supply — it does not create or emit a sequence value by itself. Sequence values and exact list values supply their contained items; other values follow the total item-view rule (an atom or string supplies itself as one item). It never consumes a right operand: `A...B`, `A...C`, `A... B`, and `A...` newline `B` all parse as expression lists beginning with `A...`. `A... ; B` is invalid semicolon syntax.
- Call argument-slot assembly is SHARED by every callable shape — flat fixed, flat/mixed variadic, patterned (repeated-name / sequence-value patterns), and multi-clause conditional (`BuildCallArgumentInputs` in C#, `collectVariadicCallItems` in Lean): each written slot is evaluated, every non-spread slot is reified as exactly ONE argument value, and every explicit spread slot is expanded by exactly one value boundary into ordinary argument slots BEFORE any arity checking, clause selection, or pattern binding. Caller-side spread therefore has identical meaning for every callee representation: `F(A...)` supplies A's opened items as slots whether `F` is flat, patterned, or a clause family (clause selection happens after expansion, so a literal clause such as `F(0, 0)` can win on a spread `(0, 0)` and a one-argument catch-all can never absorb a spread pair). WRITTEN-SLOT REIFICATION is the same rule at every syntax form whose grammar defines one value per written slot — list-literal elements, written sequence-value pattern argument items (`evalExplicitSequenceValueExprSlots` / `EvalExplicitSequenceValueExprSlots`), and the reduce initial accumulator (reified via `reCountValueBoundary` before reduction): a non-spread expression whose counted supply emitted several items (an index projection, a loop result, a counted callback parameter) still contributes ONE value (`S = ((1, 2), (3, 4))` makes `[S:0, 5]` the list `[(1, 2), 5]`; only `[S:0..., 5]` splices). Root/body output rows and loop step outputs are NOT written value slots — they keep their multi-item emission semantics (with one documented receiver-specific exception: a sequence-value-PATTERNED loop step's output keeps a top-level spread expression as ONE packed next-state slot, preserving structured state boundaries in both directions — see the loop-step notes in `tutorial.md` and `docs/design/sequence-boundary-audit-2026-07.md`).
- Square brackets construct EXACT immutable list values (`Result.listValue` / `Expr.ListLiteral`), a second collection kind beside sequence values: no singleton/empty canonicalization ever applies to list structure (`[7] != 7`, `[] != ()`), while parentheses around a list stay redundant sequence grouping (`([1, 2]) == [1, 2]`). `[` always begins a NEW expression (never a call/indexing delimiter; `A[1]` is adjacency `A, [1]`), and bracket content is a pure expression list (spread elements insert their item supply; declarations are illegal inside brackets). Spread uses `Result.spreadItems` / `SpreadItems` (opens one sequence OR list boundary). Indexing `:` opens its TARGET through the projection view `Result.projectionItems` / `ProjectionItems` (`[1, 2, 3]:0` is 1 under the same zero-based index rules as sequence selection), while a selected list ELEMENT is returned exactly as stored — one opaque list (`[[1, 2], [3, 4]]:0` is `[1, 2]`; chaining selects one level at a time). Every other NON-spread consumer keeps lists opaque via `toItems` (a list is one item for value boundaries and call binding — calls never open lists implicitly). Deconstruction's `Result.structureItems?` / `StructureItems` opens a lone sequence OR lone list (`x, y, z = [1, 2, 3]`); rest bindings collect exact lists (see the rest-collection rule below). The post-binding builtin collection view opens a BOUND list exactly like a bound sequence value (`count([1, 2, 3])` is 3, `A.take(1)` works on a list property; the opening is never recursive — a nested list stays one opaque item; spread supplies ordinary argument slots, so `count([1, 2, 3]...)` is an arity error under the fixed `count(collection)` signature). The `atoms` builtin recursively collects numeric atoms through BOTH sequence and list boundaries (depth-first, left to right; strings contribute none) via its own dedicated collector `Result.languageAtoms` / `LanguageAtoms` and materializes them as ONE exact list through `makeCollectionListResult` (`atoms(7)` is `[7]`, `atoms([1, [2]])` is `[1, 2]`, `atoms('text')` is `[]` — the result kind never depends on the input). Truth testing is deliberately SEPARATE: `truthValue?`/`TruthValue` reads the sequence-only `Result.atoms`/`ToAtoms` view, so lists still have no truth value (`if([1], a, b)` stays invalid) and the atoms traversal can never leak into `if`. Multi-clause conditional sequence-value patterns still match sequence values only (list patterns are deferred, so a list argument takes the fallback clause — except a SINGLETON pattern `(x)`, which matches any one argument whole via the scalar one-item rule, binding `x` to the entire list). Host-boundary flattening (`runFlat` / `Result.hostAtoms`, C# `RunFlat`/`EvaluateToAtoms` via `ToHostAtoms`) opens list boundaries; the truth-testing `Result.atoms`/`toItems` views stay list-opaque. Receiver theorems: `receivers_agree_outside_lone_structure` / `receivers_never_same_on_lone_structure` (unified over both structure kinds via the `loneStructure` predicate, with per-kind corollaries `receivers_never_agree_on_lone_seq` / `receivers_never_agree_on_lone_list` and the concrete `lone_rest_disagrees_on_lone_list`) in `lean/CoreArityAlgebraProofs.lean`; list-side receiver behavior over the real model is proven by the list bridge laws in `lean/KatLangArityLaws.lean` (e.g. `deconstruct_fixed_single_list_opens`, `lone_rest_list_call_and_deconstruct_differ`). The CoreArityAlgebra paper artifact now models `Val.list` and `collect` (the pre-list sequence-only extraction is preserved at the pinned paper tag).
- Postfix `...` binds to its immediate operand before expression-list handling. `X(a b...)` and `X(a` newline `b...)` parse as `X(a, b...)`. To spread a value plus another argument as separate slots, use comma or adjacency: `f(A..., B)` and `f(A...B)` are both two-argument forms. To make one sequence-value argument containing a spread plus another value, write `f((A..., B))`.
- Rest binding COLLECTS an exact immutable list. The three item-supply operations are distinguished by receiver purpose: `capture : Supply -> Value` (ordinary value/output capture — the canonicalizing `Result.normalize` boundary), `collect : Supply -> ListValue` (rest/variadic binding — `collectRest` in Lean, `CollectRest` in C#), and `open : Value -> Supply` (postfix spread — `spreadItems`). Every rest binding — rest-only variadic, mixed prefix/rest/suffix, and deconstruction rest — materializes exactly the assigned item slots as ONE exact list with emitted count 1: zero slots form `[]`, one slot forms `[item]` (NEVER erased, so one remaining structured row stays distinguishable from the row's elements), many form `[a, b, ...]`. Ordinary capture is unchanged (`x = 1, 2, 3` is `(1, 2, 3)`).
- A user-defined top-level variadic parameter collects the argument slots that were actually supplied to the call. `Name(...values) = body` binds `values` to the collected list; a plain `Name(A)` supplies one argument (`values = [A]`), while `Name(A...)` explicitly opens `A` first (`values = [A's items...]`). The old rest-only grouped/spread display coincidence is intentionally GONE: `F(A)` and `F(A...)` are observably different for every sequence-valued, list-valued, and empty argument (`F(())` collects `[()]` vs `F(()...)` collecting `[]`). For a scalar atom or string argument the two calls coincide — spread is total, so `7...` supplies `7` itself. `Name()` collects `[]`. A lone rest-only `...values` is the degenerate single-rest case of this model. Forwarding is ordinary list spread — `Forward(...items) = Target(items...)` re-supplies exactly the collected items (`open(collect(xs)) = xs`), and passing the rest unspread passes one list argument; there is no hidden raw-supply metadata, no `variadicSupplyEnv`/`VariadicStreamEnv`, and no provenance tracking. The front-end implicit-argument resolver synthesizes variadic forwarding as explicit spread arguments for the same reason.
- A parameter list with two or more captures that contains one rest binds the supplied function-call argument stream: fixed captures bind from the front and back, and the single movable rest collects the remaining middle arguments (possibly zero) as one exact list; a plain function call does not implicitly open a single sequence or list argument. Assignment deconstruction, by contrast, is an unpacking receiver (Python-style): `x, ...y, z = RHS` opens one lone sequence- or list-valued shared right-hand-side value and matches its items element-by-element, so `x, y, z = A` splits a stored sequence value or exact list value `A`. A written spread RHS is first captured into that shared value; it usually presents the same immediate items, but a singleton list whose lone element is itself a sequence or list can open one level further after singleton capture (for example, bare `x, y = [(1, 2)]` fails while `x, y = [(1, 2)]...` succeeds). The rest target then collects its middle items into an exact list by the same rule (`x, ...rest = [1, 2, 3]` binds `rest = [2, 3]`; `x, ...rest = 1` binds `rest = []`). This unpacking is deconstruction-specific and does NOT change function calls — `F(A)` still passes `A` as one argument and needs `F(A...)` to open it. The shared front/rest/back matcher is `bindParameterPatternList` (Lean) / `BindParameterPatternList` in C#); every rest materialization funnels through `collectRest` (Lean) / `CollectRest` (C#) — the plain and counted pattern binders plus the flat-variadic loop path all call it, always producing one exact list with emitted count 1. Item-supply call routing is `Algorithm.usesItemSupplyBinding` / `IsDeconstructionUserCallShape`. Assignment deconstruction is parser-elaborated so the right-hand side is evaluated once into a shared property and each target binds through an inline sequence-value parameter pattern (`SequenceValueParameterPattern`) that opens that single shared value. The same `(x, ...y, z)` sequence-value parameter pattern opens one received value for parameter/callback-position destructuring. Flat callbacks with a top-level rest bind through the shared binder too (`bindCountedCallbackParameterPatternList` / `BindCountedCallbackParameterPatternList`): a rest-only callback keeps each iterated element as ONE collected slot (`[7].map(Collect)` binds `items = [7]`; `[(1, 2)].map(Collect)` binds `items = [(1, 2)]`), while a multi-parameter flat callee first opens a lone SEQUENCE-valued element into row slots (the flat-callback row convention; exact-LIST elements stay opaque and arity-error in flat binding — the nested `F((x, ...y, z))` pattern form is the tool that opens BOTH kinds) and then allocates prefix/rest/suffix (`Rows.map(F)` with `F(x, ...y, z)` on sequence row `(1, 2, 3, 4)` binds `y = [2, 3]`, agreeing with the nested form on sequence rows only). Only the sequence-value pattern's scalar-element fallback stays strict (callback deconstruction for scalar elements deferred). The front-end implicit-argument resolver synthesizes forwarding spread only when BOTH the destination capture is variadic AND the source binding of that name is a rest: `Use(items) = Target` with variadic `Target(...items)` elaborates to `Target(items)` (one argument; `Use([1, 2])` is `[[1, 2]]`), a caller rest `Use(...items) = Target` (variadic `Target`) elaborates to `Target(items...)`, and a rest-collected source forwarded into a FIXED destination parameter passes the collected list as one argument (fixed parameters are never reopened).
- Ordinary lexical dot-call passes the receiver as one leading argument boundary. `A.B(C, D)` means `B(A, C, D)`, not a call where `A`'s top-level values are spread before `C` and `D`. For collection builtins the receiver therefore fills the fixed `collection` parameter (`A.take(2)` is `take(A, 2)`, `A.count` is `count(A)`), with no builtin-specific receiver placement.
- Collection builtins are ordinary FIXED-ARITY callables that receive exactly ONE fixed `collection` parameter followed by fixed control parameters: `count(collection)`, `sum(collection)`, `first/last/min/max/avg/order/orderDesc/distinct(collection)`, `take/skip(collection, count)`, `contains(collection, item)`, `map(collection, mapper)`, `filter(collection, predicate)`, `reduce(collection, reducer, initial)`. An unspread sequence or list value is ONE argument at this call boundary like at every other call boundary, and NOTHING is opened before binding — `count(1, 2, 3)`, `count()`, `sum(A..., B...)`, `take((1, 2, 3))` (missing count), `take([1, 2, 3]..., 2)`, and `distinct((), ())` are ordinary arity errors (spread only supplies ordinary argument slots that obey the same fixed arity; re-group to pass spread items as one collection: `sum((A..., B...))`). The bound collection value is interpreted through the POST-BINDING one-level collection view (`builtinCollectionItems` / `BuiltinCollectionItems`): a lone sequence OR exact list opens one outer boundary and any other value is a one-element collection — `count((1, 2, 3))`, `count([1, 2, 3])`, and `Values.count` are 3, `count(7)` is 1, `count(())`/`count([])` are 0, and opening is never recursive (`count((1, [2], 3))` is 3, `count(([], []))` is 2). Item shape/empty policies apply to the viewed items (`sum` numeric constraint, `first` non-empty). Collection-producing builtins (`filter`, `map`, `order`, `orderDesc`, `distinct`, `take`, `skip`, `range`) materialize their kept/projected items as ONE exact immutable list via `makeCollectionListResult` / `MakeCollectionListResult`: zero items form `[]`, a single kept item forms `[item]` (never erased, so `take(((1, 2), (3, 4)), 1)` is `[(1, 2)]` and `distinct(((), ()))` is `[()]`), and nested sequence/list elements stay exact — the result kind never depends on the input kind, and only explicit `...` re-opens the list into the arity layer. Canonical arity capture (`combineOutputSlots`, ordinary construction) and spread are UNCHANGED by this model, and rest binding produces the SAME exact-list kind (`collectRest`) — variadic parameters remain a general arity mechanism for user functions, and passing a collected variadic to a builtin unspread passes it as the one collection argument (`Qmean(...args) = args.sum / args.count` works because the post-binding collection view opens the bound list; `map(values..., f)` inside a body is an arity error — write `map(values, f)`). Callback/builtin execution stays a separate runtime-owned phase after binding.
- Sequence builtins and spread behavior must stay consistent across Lean and C#.
- Changes to builtins, preludes, intrinsic metadata, or sequence syntax require synchronized updates in evaluator, front-end assumptions, semantics, tests, tutorial, EBNF, and generator guidance.

## Editor Semantics
- `src/KatLang/Semantics/` derives editor-facing meaning from parsed and elaborated ASTs.
- Build semantic models from `Parser.Parse(...)` / `ParseResult`, not from raw syntax.
- Only source-backed identifiers may produce semantic sites, resolutions, declarations, or spans.
- Synthetic constructs must not invent source spans.
- If editor-visible behavior changes, update `src/KatLang/Semantics/` and `tests/KatLang.Tests/SemanticModelTests.cs` together.
- Preserve exact source-span invariants for hover, references, go-to-definition, classification, and callable-property metadata.

## Testing Expectations

- Prefer minimal, semantics-preserving, reviewable changes.
- Add or update focused tests near the changed layer.
- Include negative coverage when failure modes are meaningful.
- When changing language behavior, update Lean tests and C# tests together.
- If a change crosses parser, evaluator, semantics, or docs boundaries, cover the affected layers in the same task when feasible.

## Documentation Expectations

- Update `KatLang.ebnf` when lexer/parser grammar changes.
- Update `tutorial.md` when user-facing behavior changes.
- Update generator-facing files when syntax, builtins, `Output`, `open`/`load`, or recommended code-generation idioms change.
- In this repo that usually includes `.github/agents/katlang-generator.agent.md` and any related generator prompt assets.
- When generator guidance changes, explicitly check both `.github/agents/katlang-generator.agent.md` and `experimental/prompts/katlang-generator.txt`.

## Coding Guidance

- Prefer small changes that fix the root semantic issue without widening scope unnecessarily.
- Do not introduce new AST shapes unless strongly justified by Lean or an existing architectural boundary.
- Preserve the current parser/evaluator/tooling boundaries instead of re-encoding the same rule in multiple places.
- Keep diagnostics structured, source-positioned, user-friendly, and phrased in KatLang terms.
- If a change is implementation-only optimization, say so explicitly.

## Validation

Run the full validation script from repo root:

```powershell
pwsh .\scripts\validate-all.ps1
```

This runs the C# test suite, `git diff --check`, and Lean targets:

```powershell
lake build CoreTests
lake build KatLangArityLaws
lake build AstDemo
lake build CoreArityAlgebra
lake build CoreArityAlgebraProofs
lake build SemanticExplorerCases
lake build LanguageSpecCases
```

Manual fallback:

```powershell
dotnet test .\KatLang.slnx -p:UseSharedCompilation=false
git diff --check
Push-Location .\lean
lake build CoreTests
lake build KatLangArityLaws
lake build AstDemo
lake build CoreArityAlgebra
lake build CoreArityAlgebraProofs
lake build SemanticExplorerCases
lake build LanguageSpecCases
Pop-Location
```

Lean CoreTests now use `#guard` for semantic assertions, so a failing assertion fails `lake build CoreTests`. Remaining `#eval` lines are demo/inspection output only.

`lean/SemanticExplorerCases.lean` is a GENERATED Lean/C# differential corpus — do not edit it by hand. A failing `#guard` there is a Lean/C# divergence (or a Lean-internal plain/counted evaluator mismatch) on that case. After an intentional semantics change, regenerate it with `$env:KATLANG_REGENERATE_SEMANTIC_EXPLORER = "1"; dotnet test .\KatLang.slnx --filter SemanticExplorerLeanArtifact`, review the diff, and rebuild the Lean target. See `docs/design/sequence-boundary-audit-2026-07.md`.

## Executable Language Specification

- `tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs` is the canonical executable specification: named cases with stable IDs and HAND-WRITTEN canonical expectations. Never regenerate its expectations from observed behavior — a failing `LanguageSpec*` test means either fix the implementation or edit the canonical case in a reviewed diff.
- GENERATED from it (do not edit by hand): `lean/LanguageSpecCases.lean` and the `=== BEGIN GENERATED: katlang-spec-examples ===` block in `.github/agents/katlang-generator.agent.md` and `experimental/prompts/katlang-generator.txt`. Regenerate all three with `$env:KATLANG_REGENERATE_LANGUAGE_SPEC = "1"; dotnet test .\KatLang.slnx --filter LanguageSpecArtifacts`, review the diff, then `lake build LanguageSpecCases`.
- Tutorial examples marked `<!-- spec:case-id -->` are verified against the corpus (source and expected output) by `TutorialSpecTests`; when changing a linked example, update the canonical case and the tutorial together.
- When language behavior intentionally changes, update the affected canonical cases in the same task as the Lean/C#/tutorial/generator changes.
- Maintainer guide: `docs/design/executable-language-spec.md` (partitions, counts, how to add cases, worked example).

## Lean/C# Semantic Alignment

Before editing, classify the change using `src/KatLang/SEMANTIC-ALIGNMENT.md`.

- Observable semantics require Lean consideration and usually Lean updates/parity tests.
- C# implementation/tooling-only changes require C# tests; Lean updates are not required.
- Optimization-only changes do not change Lean, but require equivalence tests against the generic path.
- Diagnostic wording-only changes do not require Lean if the structured error kind/payload is unchanged.
- Grammar or AST changes usually require Lean review.

If in doubt, the manifest's "Lean update required?" column is authoritative. If Lean is silent or ambiguous, stop and ask.

## Do Not

- Do not silently change language semantics.
- Do not let Lean and C# diverge.
- Do not treat `AGENTS.md` as a long design essay.
- Do not let multiple agent-instruction files drift into conflicting guidance.
- Do not add convenience syntax, hidden fallbacks, or duplicated semantic logic just to make a local change easier.
