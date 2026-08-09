# Sequence-Boundary Audit and Semantic Explorer (July 2026)

> **Syntax note (2026-07-29):** the collection/spreading surface syntax was later redesigned: prefix `*name` is now the collect marker (collecting binding / collecting parameter), postfix `value*` is the spread marker, and the former spellings `name...`, `spread(x)`, and `x.spread` are no longer KatLang syntax (`spread` is an ordinary identifier). Spellings in the historical text below are the spellings of their time; the semantics they describe are unchanged.

Status: completed audit + durable validator. This document is the Phase-1
receiver/boundary review deliverable for the small-state arity-semantics
validator, and the reference for the invariants that validator enforces.

> **Update (2026-07-17, builtin-list follow-up).** Collection-producing
> builtins (`filter`, `map`, `order`, `orderDesc`, `distinct`, `take`, `skip`,
> `range`) now materialize ONE exact immutable list value via
> `makeCollectionListResult` / `MakeCollectionListResult`;
> `combineCollectionResult` / `CombineCollectionResult` no longer exists:
> zero kept items form `[]`, one kept item forms `[item]`, and builtin
> the builtin collection view opens a lone bound LIST like a lone sequence value.
> Canonical arity capture and output-slot combination remain sequence-centered.
> Variadic/collecting binding now uses exact immutable list collection instead. The semantic descriptions below have been updated;
> the corpus/accounting history remains the July 2026 audit record. See
> AGENTS.md and `src/KatLang/CALLABLES.md` for the operational rules.

The validator itself lives in:

- `tests/KatLang.Tests/SemanticExplorerCorpus.cs` — bounded value space x receiver templates (shared corpus),
- `tests/KatLang.Tests/SemanticExplorerHarness.cs` — neutral observation format (raw structure, emitted count, error category),
- `tests/KatLang.Tests/SemanticExplorerTests.cs` — C#-side structural invariants + machine-readable report,
- `tests/KatLang.Tests/SemanticExplorerLeanArtifactTests.cs` — generator/pin for the differential artifact,
- `lean/SemanticExplorerCases.lean` — generated Lean AST corpus with `#guard`s pinned to C#-observed results (`lake build SemanticExplorerCases` fails on any Lean/C# divergence).

## 1. The current boundary model (as implemented)

One rule with four explicitly documented non-boundary exceptions, confirmed by
executable evidence on the surface corpus (current accounting in §5.1).

**Counts.** Every evaluation step carries `CountedResult = (value, emittedCount)`.
`Result.valueCount` is 0 for `()` and 1 for everything else.

**Value boundaries** (result re-counted to `valueCount` via
`reCountValueBoundary` / inline equivalent — the value itself is never
rebuilt): user calls, conditional calls, lexical zero-arg property access `A`,
explicit call `A()`, structural dot access `A.B` / `A.B()`, `if`, and the
collection-producing builtins (`order`, `orderDesc`, `distinct`, `take`,
`skip`, `filter`, `map`, `range`, `atoms`).

**Non-boundaries** (multi-item counts flow through):

1. Root/body output accumulation: a spread slot contributes its spread item
   count (possibly 0); a **non-spread slot contributes `max(1, emitted)`** —
   so `()` stays one visible row, and a supply-emitting expression such as
   `x:0` emits several rows at root.
2. `while`/`repeat` multi-slot loop state.
3. The strict single-value `map`/`reduce` callback contract (multi-output or
   `()`-valued callback results are errors, not grouped values).

*(Superseded, July 2026 collecting-binding change: raw variadic parameter
storage — `variadicSupplyEnv` / `VariadicStreamEnv` with raw item counts —
was removed. Collecting bindings now collect ONE exact immutable list with emitted
count 1 (`collectSegment` / `CollectSegment`), and forwarding is ordinary list
spread: `sum(a)` passes the bound list as the one collection argument, and
`a.spread` re-spreads exactly the collected items.)*

**Construction.** Parenthesized lists parse to zero-parameter blocks whose
output slots keep `()` items visible; slots are combined with the shallow
`CombineOutputSlots` (1 slot -> the slot itself, else one sequence value).
Written singleton parens are transparent (`(1)` = `1`, `(())` = `()`,
`(((1,2)))` = `(1,2)`). Deep `Result.Normalize` is applied only at
construction/capture sites whose inputs are already canonical, so it never
flattens meaningful nested multi-item structure.

**Collection builtin returns.** `filter`, `map`, `order`, `orderDesc`,
`distinct`, `take`, `skip`, and `range` materialize one exact immutable list:
0 items -> `[]`, 1 item -> `[item]`, and 2+ items -> `[item, ...]`, preserving
all sibling boundaries including `()` items. This exact materialization is not
canonical arity capture. `atoms` joined this family in the issue #136
follow-up: it recursively collects numeric atoms through both sequence and
list boundaries via the dedicated `languageAtoms` collector and materializes
them as one exact list, while truth testing keeps reading the sequence-only
`Result.atoms` view (lists still have no truth value).

**Spread.** `expr.spread` opens exactly one layer via `spreadItems`: `().spread` and
`[].spread` contribute zero items, an atom spreads to itself, a sequence or list
supplies its immediate items, and nested values stay intact.

**Indexing.** `x:i` selects one top-level item and projects its content one
level, emitting `(projectedValue, itemCount)` — a *supply*, not a value. The
supply is observable only at root/body output rows (with the `max(1, n)`
non-spread bump); every other receiver (argument slot, sequence literal,
capture) re-materializes it as one value.

**Equality.** `==`/`!=` compare evaluated raw structure (`BEq` / 
`Result.ValueComparer`), no normalization at comparison time, mixed kinds
compare unequal. `()` is transparent for every *non*-comparison binary
operator (`() > 1` = `1`, `() + ()` = `()`) and for unary operators, but is a
first-class operand for `==`/`!=`.

**count / .count.** Both paths supply exactly one fixed `collection` argument.
Only after fixed binding, the builtin collection view opens one outer sequence
or exact-list boundary; sibling groups remain items. `count(V)` and `V.count`
therefore agree. `count(V.spread)` has ordinary spread-call meaning instead: it is
valid only when the spread supplies exactly one argument, and otherwise is an
ordinary arity error for `count(collection)`.

**Cache.** `A` vs `A()` changes only the per-run zero-arg property cache
usage; the cached raw count is re-counted at every observable boundary, so
caching cannot change observable counts or structure (validated).

## 2. Receiver/boundary matrix

Neutral encoding: `S[...]` = sequence value (raw structure), `n` = emitted
count at the observed boundary, `E:x` = typed error. Full per-cell data for
all 1,559 surface cases is in the machine-readable report
(`SemanticExplorerReport.json`, written next to the test assembly on every
run) and pinned per-case in `lean/SemanticExplorerCases.lean`. The matrix
below is the required-values digest; Lean/C# agreement is per the generated
artifact (see §5).

Written value V (canonical raw after capture / survives?):

| V (source) | raw structure | `(1)`-style distinction survives? |
|---|---|---|
| `()` | `S[]` | — |
| `1` | `1` | — |
| `(1)` | `1` | no (transparent grouping, documented) |
| `(1, 2)` | `S[1, 2]` | yes |
| `((), ())` | `S[S[], S[]]` | yes |
| `((), 1)` | `S[S[], 1]` | yes |
| `((1, 2), 3)` | `S[S[1, 2], 3]` | yes |
| `((1, 2), (3, 4))` | `S[S[1, 2], S[3, 4]]` | yes |
| `(())` | `S[]` | no (canonicalizes, documented) |
| `((1))` | `1` | no |
| `(((1, 2)))` | `S[1, 2]` | no (written slot still counts one argument at call sites) |

Receiver rows (columns: input `V`; supplied arity seen internally; output raw;
observable count at root; notes):

| Receiver / operation | internal supplied arity | output raw | n | notes |
|---|---|---|---|---|
| root output `V` | 1 slot | canonical V | 1 | non-spread slot ≥ 1 row, incl. `()` |
| root `V.spread` | `items(V)` | canonical V | `items(V).count` | `().spread` -> 0 rows, display `""` |
| root `(), 99` | 2 slots | `S[S[], 99]` | 2 | `()` stays a visible row |
| capture `x = V` | 1 | canonical V | 1 | identical for `x`, `x()`, `A.X`, `A.X()` |
| fixed param `F(V)` | 1 arg | V | 1 | call never opens a grouped arg |
| fixed `F(V.spread)` | `items(V)` args | item / `E:arity` | 1 | succeeds iff exactly 1 item |
| variadic `F(V)` / `F(V.spread)` | 1 arg / items | `L[V]` / `L[items(V).spread]` | 1 | the variadic parameter COLLECTS an exact list; grouped and spread calls always differ (July 2026 supersession of the old single-variadic coincidence) |
| mixed `F(h, t...)(V.spread)` | items | front/back split; the variadic parameter collects the middle as `L[...]` | 1 | a 1-item collected segment stays `[item]` (no collapse; July 2026 supersession of the old capture law) |
| deconstruction `x, y = V` | `items(V)` | element-wise match | 1 | `= V` ≡ `= V.spread` (unpacking receiver) |
| explicit seq `(V, 99)` | 2 slots | `S[V, 99]` | 1 | `()` survives as item; nesting intact |
| spread in seq `(V.spread, 99)` | items+1 | shallow combine | 1 | `(().spread, 99)` = `99` (singleton collapse) |
| `count(V)` / `V.count` | 1 fixed collection arg | `items(V).count` | 1 | collection view opens one bound sequence/list boundary |
| `count(V.spread)` | `items(V).count` ordinary args | count or `E:arity` | 1 / — | succeeds only when spread supplies exactly one argument |
| `x:0` (item = pair) | — | projected item content | `max(1, k)` | supply at root; 1 value everywhere else |
| `x:0` (item = `()`) | — | `S[]` | 1 | projection count 0, root bump to 1 row |
| `x:9` / `x:-1` | — | `E:index` / parse error | — | negative selector rejected at parse (C#) |
| `==` / `!=` | 2 values | `1`/`0` | 1 | structural, reflexive, path-independent |
| re-entry `I(x)`, `P = R` | 1 | unchanged | 1 | validated across double re-entry |
| `take/skip/filter/distinct/order/map` | items | exact list of survivors/results | 1 | zero -> `[]`; one -> `[item]`; never singleton-erased |
| `range` | — | exact integer list | 1 | inclusive ascending/descending span |
| `atoms` | — | exact list of collected atoms | 1 | recursive flattener through sequence AND list boundaries; truth testing stays list-opaque |

## 3. Answers to the architectural questions

1. **Should collection-producing builtins return a captured sequence-value
   boundary?** No. They return one exact immutable list value. Empty and
   singleton list boundaries remain visible (`[]`, `[item]`); canonical
   sequence capture remains reserved for arity storage and combination.
2. **Should lexical zero-arg access and structural dot access re-count
   identically?** They already do (validated: `capture`/`captureCall`/
   `dotAccess`/`dotAccessCall` agree on every corpus value).
3. **Which operations may preserve an internal item supply?** Exactly the four
   documented non-boundaries (§1) plus `:` projection *between* evaluation and
   the next boundary. No others were found in the sweep.
4. **Which must expose a captured value?** Every property/call/builtin result,
   argument slot, sequence-literal item, and stored binding.
5. **Where is capture/normalization applied?** Deep `normalize` at written
   sequence construction and ordinary value capture (inputs canonical); shallow
   combine at output slots. Collecting binding and collection-producing builtins
   instead construct exact lists and never renormalize item internals.
6. **Where may a value be re-spread?** Any expression-list context (root/body
   slots, call args, sequence literals, builtin supplies) — exactly one layer.
7. **Can any operation construct a literal-unwritable value?** No. 0 orphan
   singleton nodes across all generated cases (enforced as `UnexpectedWrapper`).
8. **Is every displayed value reconstructable?** Yes for numeric/sequence
   values including all counts (enforced as `DisplayNotReconstructable`),
   with two documented exceptions: string display drops quotes (explicit
   non-goal), and a zero-item output displays as no text, which is not a
   parseable program (`().spread` at root).
9. **Can two values display identically but behave differently?** No collision
   found across the corpus (enforced as `DisplayCollision`).
10. **Can one raw value observe differently by construction path?** No.
    Equality/count/indexing agree across literal, capture, call-return,
    builtin-return, deconstruction, and cache/no-cache paths (validated).
11. **Can a collection builtin erase a one-survivor boundary?** No. The exact
    result is `[survivor]`, so `count(take(V, 1))` is 1 whenever `V` supplies an
    item, including when that item is a sequence value or `()`. Explicit
    `take(V, 1).spread` re-spreads the list and supplies the survivor itself.
12. **Can a non-spread `()` disappear from an item position?** Not from any
    parser-reachable position (root rows, property bodies, sequence literals,
    argument slots, builtin supplies all preserve it — validated as
    `DroppedVisibleEmpty`). The one code path that *would* drop it —
    `Expr.SequenceConstruct` evaluation (`EvalSequenceConstructCounted`,
    which skips `valueCount = 0` leaves) — is not produced by the C# parser
    for any surface syntax; it exists as an evaluator-internal reshaping node
    (strict-variadic suffix splitting) and in Lean-side test constructions.
    See §6 (residual risks).
13. **Can singleton erasure flatten meaningful nested structure?** No. Deep
    sequence-normalize sites receive canonical inputs; arity combine sites are
    shallow; exact list materialization applies no singleton erasure.
    Validated by `UnexpectedFlattening` on nested values incl. `((), (1, 2))`,
    `(((), 1), 2)`, and exact nested list elements.
14. **Are root output, property access, function return, builtin return one
    rule?** One rule + the four *documented* exceptions of §1. The only
    subtle interaction is `:` projection emitting a supply that root rows
    display opened while every other receiver re-materializes — this is the
    documented "selection projects content" rule meeting the documented
    "root output is not a value boundary" rule, not a special case of either.

## 4. Findings classification

**Confirmed bug (found by the differential corpus, fixed):** Lean's plain
`evalAlgOutputCore` kept a non-empty spread output slot as **one un-expanded
slot**, while Lean's own counted core (`evalAlgOutputCountedCore`) and the C#
evaluator splice the spread items. Observable divergence on the surface
program `(A.spread, 99)` with a multi-item `A` — Lean produced `((1, 2), 99)`
where C# and the tutorial (`(Values.spread, 8)` = `(1, 2, 3, 8)`) produce
`(1, 2, 99)` — through every plain-evaluation path: value-position sequence
literals, binary-operand evaluation (so `(P.spread, 99) == (1, 2, 99)` was `0` in
Lean), spread operands of written blocks, the `eval .param` thunk fallback,
and Lean's own `runResult` root. Lean was also internally inconsistent: its
plain and counted evaluators disagreed on the same AST. 11 of the 905 initial
differential cases failed (`spreadInSeq` x every multi-item value); all other
894 cells agreed. Fix: `evalAlgOutputCore` is now the value projection of
`evalAlgOutputCountedCore`, exactly mirroring C#'s `EvalAlgOutputCore`
(`Evaluator.cs:4715`). Loop-step state, which legitimately keeps spread
boundaries structured, was never on this path (it uses `evalAlgOutputSlots`
with its explicit preserve flag).

One pre-existing CoreTests guard had pinned the divergent grouped behavior
(`sequenceValueVariadicLoopStepPreservesSequenceValueHistorySlot`), citing a
C# regression name that does not exist; the actual C# regression
(`Eval_LoopStep_SequenceValueCommaHistorySlotUsesExplicitSpreadAcrossRepeat`)
asserts the flat result. The guard was corrected to the C#-verified flat
behavior and renamed `sequenceValueVariadicLoopStepSpreadGrowsHistoryFlat`;
four new CoreTests guards pin the splicing rule at the value-position,
root-row, written-`()`-slot, and equality-operand layers.

(The corpus also reproduces the historical bug classes as regression pins:
#133 one-survivor wrappers, #132 property-call boundary, #128 `()`
visibility, orphan construction, empty-item preservation in builtin
supplies.)

**Likely design inconsistencies:** none that survive contact with the
documented rules. Candidates examined and resolved as rule-consistent:

- `count(take(V, 1)) != 1` (see §3.11) — consequence of two documented rules.
- `x:0` emitting several root rows while `G(x:0)` passes one argument —
  documented projection/supply semantics vs written-slot argument rule.
- `x:0` on a `()` item shows one `()` row (projection count 0, root bump) —
  same rule that keeps a non-spread `()` visible.

**Intentional behavior (documented):** singleton-paren transparency;
`()` operator transparency for non-comparison operators; call-vs-
deconstruction opening asymmetry; strict single-value map/reduce callback
result contract; string display non-roundtrip.

*(Superseded, July 2026 collecting-binding change: the single-variadic coincidence
`F(V)` ≡ `F(V.spread)` and its theorem `agree_on_lone_seq_iff_lone_rest` are
GONE — collecting bindings collect exact immutable lists, so `F(V)` and `F(V.spread)`
always differ, and the receiver contrast is now proven by
`receivers_never_agree_on_lone_seq` / `lone_collecting_disagrees_on_lone_list` in
`CoreArityAlgebraProofs.lean` plus the collect bridge laws in
`KatLangArityLaws.lean`. The correction pass additionally routed flat
callbacks with a top-level variadic parameter through the shared prefix/collecting/suffix binder,
so `[7].map(Collect)` collects `items = [7]`.)*

**Unresolved design choices (pre-existing, unchanged):** sequence-value
callback deconstruction on scalar elements (still strict; deferred per
BINDING-ARCHITECTURE.md Phase 26 — flat top-level variadic callbacks now bind
through the shared binder, but the nested-pattern scalar fallback stays
singleton-only); zero-item root output displaying as empty text (not
reconstructable as a program).

## 5. Lean/C# differential results

The generated artifact pins every Lean-representable corpus case
(**1,528 surface cases** as of this update — the surface corpus minus its 31
parse-level cases such as `(3,)`, `x:-1`, `A.spread == A.spread`, and `1 ; 2`, which
are C#-only typed outcomes since Lean has no surface parser — plus **14**
direct internal-node cases; see §5.1 for the full accounting). Encoding
notes:

- Parenthesized lists are emitted as zero-parameter blocks (`.block (alg [] [] [] [...])`),
  mirroring the C# parser. They are **not** emitted as `.sequenceConstruct`
  chains: `sequenceConstruct` is an internal/test form on both sides (its
  evaluation drops `()` leaves, and the C# parser never produces it for
  written parentheses). Note for Lean test authors: the two encodings are
  interchangeable only for non-empty, non-spread leaves.
- Assignment deconstruction is emitted in its parser-elaborated form (shared
  RHS property + `sequenceValue` parameter pattern helper).
- The root emitted count is observed through a generated `runCountedM`
  (same wiring as `runResultM`, keeping `evalAlgOutputCounted`'s count),
  matching C# `Evaluator.RunCounted`.
- The artifact's `obs` additionally cross-checks Lean's plain (`runResult`)
  and counted evaluators on every case; any disagreement between Lean's own
  two paths surfaces as an `internalMismatch` observation and fails the
  guard. This is the check that would have caught the §4 bug directly.
- `SemanticExplorerHarness.Observe` applies the SAME cross-check on the C#
  side (`Evaluator.Run` against `Evaluator.RunCounted`, throwing on any
  value/error-category disagreement), so both implementations' plain and
  counted evaluators are compared on every surface case. Before the August
  2026 coverage census the C# surface path observed only `RunCounted`, so a
  plain-evaluator regression could not fail any generated guard;
  `ObserveAst` already cross-checked the internal-node cases.

First run: 11 of the 905 initially generated surface cases failed
(`spreadInSeq` on every multi-item value), identifying the §4 divergence.
(Earlier prose reported 906/912-style figures; those counted a header comment
that mentions `#guard` — the generated footer totals are authoritative.)
After the one-definition Lean fix and adding divergence-class specials:
**`lake build SemanticExplorerCases` passes — all differential cases agree**
(values x receivers, spread, deconstruction, indexing, equality,
`()`-transparency, collection builtins, re-entry, error categories),
including the plain/counted internal consistency check on every case.

### 5.1 Corpus and guard accounting

Counts below are as of this audit. Every total is computed by the tooling —
the JSON report's `partition` object, the generated artifact's footer, and
the test runner — never maintained by hand; the partition identity
(surface = Lean-representable + parse-level, exclusions exactly the
parse-level set) is enforced by
`CorpusPartition_LeanExclusionsAreExactlyTheParseLevelCases`.

| Suite / artifact | Exact count | Included | Excluded | Source of truth |
|---|---:|---|---|---|
| Surface corpus (= C# semantic report surface section) | 1,559 | 1,404 template cases (54 receiver templates x 26 values) + 155 specials; outcomes 1,343 ok / 185 err / 31 parse-error | internal-node cases; anchor pins | `SemanticExplorerCorpus.AllCases()`; report `partition.surfaceCases` |
| Lean-representable surface differential | 1,528 | the 1,559 above minus the 31 parse-level cases (26 `indexNeg__*` + five deliberate parse-error specials) | parse-level cases (Lean has no surface parser) | report `partition.leanRepresentable`; artifact header/footer |
| Internal `SequenceConstruct` corpus | 14 | direct-AST `internal__sc_*` cases | everything source-driven | `SemanticExplorerCorpus.InternalNodeCases()`; report `partition.internalNodeCases` |
| Generated Lean case guards | 1,542 | 1,528 surface + 14 internal-node (one `#guard` per case), plus two partition-count guards | nothing (header states the split) | `SemanticExplorerCases.lean` header/footer |
| C# semantic report internal-node section | 14 | id, relation, internal + surface observations per case | — | report `internalNodeCases` |
| Parser/elaboration reachability sweep | 1,559 attempted, 1,528 scanned | every corpus source that parses (post-`FrontEndPipeline` ASTs) | the 31 deliberate parse-error cases (skipped) | `EntireSemanticExplorerCorpus_ParsesWithoutSequenceConstruct` |
| Containment test invocations | 42 | parser theories, corpus sweep, AST-family pins, visitor-preservation facts, direct-node pins, difference facts, and the call-function `NotAnAlgorithm` payload pin | explorer/anchor tests (counted separately) | `dotnet test --filter FullyQualifiedName~SequenceConstructContainmentTests` |
| Explorer-related test invocations | 44 | 37 explorer/anchor pins + four artifact freshness/comparability/partition/accounting facts + three cross-harness/containment/formatting guards matched by the filter | — | `dotnet test --filter FullyQualifiedName~SemanticExplorer` |
| Full .NET solution | 6,338 (6,330 main-suite + 8 formatting public-API invocations, as of this audit; the suite grows — the live run is authoritative) | everything incl. all of the above | — | `dotnet test .\KatLang.slnx -p:UseSharedCompilation=false` |

Historical accounting note: the original audit's **931 vs 912** and
**925 vs 924** discrepancies came from counting a header comment that mentioned
`#guard`. The corpus has since expanded (the three stacked `value**` templates
`spreadRootStacked` / `collectingStacked` / `captureStacked` added by the
arity-differential campaign, July 2026; then the four direct no-output-block
spread specials and the call-function internal-node case added by the Track 4
output-composition fixes, August 2026 — the previously uncovered direct
`.block` spread-operand arm; then the 39 specials added by the Track 9
coverage census, August 2026 — 37 for `min`/`max`/`first`/`last`/`orderDesc`/
`while`/`contains`, the six builtins that had Lean guards and C# tests but no
SHARED differential case, plus two `dotAccessPublicMember` specials covering
the public spelling of structural dot access; then the 19 `open`/visibility
specials added by the Track 10 name-resolution audit, August 2026 — the family
covering public/private/local-only exposure through `open`, provider ambiguity,
open-target dedup, inline blocks, dotted paths, ownership-first shadowing,
nested-scope leakage, builtin collision, and structural dot access to a private
member, none of which had ANY case in either generated artifact before); the
generated header, partition guards, JSON report, and table above now agree on
1,557 surface cases, 31 parse-level exclusions, 1,526 Lean-representable
surface cases, and 14 internal-node cases.

Corpus fidelity note (Track 10): the `open`/visibility family's Lean programs
are not hand-transcribed. `LeanAstEncoder` prints the Lean constructor form of
the source's real ELABORATED AST, and `OpenVisibilityCorpusFidelityTests` pins
every declared program against it. That matters twice over for this family:
exposure metadata (`publicProp` / `privateProp` /
`publicLocalProp .localCapturedAncestorParams`) IS the semantics under test, and
the front end additionally rewrites names that no provider supplies into
implicit parameters — so the honest Lean encoding of `open Lib` over a private
`X` is `alg ["X"] [.resolve "Lib"] [] [.param "X"]`, not the naive shape of the
written source. The encoder is fail-loud on node kinds it does not model, so it
cannot silently approximate a program the way the Track 9 defect below did.

Corpus fidelity note (Track 9): the `dotAccess` / `dotAccessCall` templates
and the `multiPropDot` special write `A = { X = ... }`, which the C# parser
elaborates as a PRIVATE property, but their Lean encoding used
`publicProp "X"` — so 109 differential cases were comparing structurally
different programs. The encoding now uses `privateProp`, which both restores
fidelity and makes those cases pin the documented rule that structural dot
access sees private members (`open` filters to public members,
`Algorithm.lookupProp` does not). No pinned observation changed.

## 6. Recommended rule and residual risks

**Recommended coherent rule (already the implemented one — recommendation is
to keep it and enforce it):**

> Every property/call/builtin result, argument slot, sequence-literal item,
> and stored binding is a *value* boundary: one value, count `valueCount`.
> Item supplies exist only inside root/body output accumulation and loop
> state; only a written `spread(value)` / `value.spread` intrinsic (or the documented openers: deconstruction RHS
> and `:` projection) may open one layer of a value into a surrounding
> supply. Collection builtins first bind one ordinary fixed `collection`
> value, then apply their separate post-binding one-level view.
> Sequence-centered arity construction erases exactly the unwritable
> boundaries (singleton wrap, redundant empty nesting) and nothing else;
> collection-producing builtins construct exact writable list boundaries.

*(July 2026 collecting-binding update: the original recommendation listed "raw
variadic storage" as a third item-supply site. That storage no longer exists —
collecting bindings collect ONE exact immutable list (`collectSegment`), a value
boundary like every other stored binding, and forwarding re-spreads it only
through a written named spread intrinsic.)*

The smallest implementation change needed to enforce it: **none** — the rule
holds today; the change delivered is the validator that keeps it holding.

**Residual risks tracked by the validator:**

1. `Expr.SequenceConstruct`'s `()`-dropping evaluation is intentional
   internal-join semantics, contained and guarded — see §7.
2. New builtins that return collections must use
   `MakeCollectionListResult` / `makeCollectionListResult`; adding one to the
   corpus is one template entry.
3. Numeric divergence (Lean `Int` vs C# `decimal`) is out of scope for the
   integer-only corpus; extending values to decimals would surface it
   deliberately.

## 7. `Expr.SequenceConstruct` containment (July 2026 follow-up)

**Role (provenance-audited).** `Expr.SequenceConstruct` / Lean
`Expr.sequenceConstruct` is an internal sequence-JOIN node retained for
semantic AST compatibility with the Lean model; surface spreading is the
named `spread` intrinsic (`Expr.SequenceSpread`) and never builds it. It is
**not** the AST representation of
written parenthesized sequence values — those parse to zero-parameter
`Expr.Block`s (and `()` to `Expr.EmptySequence`).

**Provenance (origin vs rebuild).** Precise terminology matters here: an
*origin site* can introduce the node into an AST that did not already contain
it; a *rebuild site* reconstructs one only because its input already contains
it. The parser and all current production transformations have **zero origin
sites** for `Expr.SequenceConstruct`: the parser never constructs it
(directly, via desugaring, or in error recovery — and `Parser.Parse` runs the
full `FrontEndPipeline`, so the containment sweep scans post-elaboration
ASTs); no evaluator or reification path creates one (`resultToExpr` emits
blocks). **Nine production visitor branches** (`ModuleLoader`,
`ParameterDetector` x4, `ImplicitArgumentResolver` x3,
`PropertyExposureResolver`) may **rebuild** an existing node while mapping
its children — preservation is pinned by
`ProductionVisitor_PreservesExternallyOriginatedNode` — but none can
introduce one. After this audit removed C#'s last production origin site
(the legacy reshape, below), the remaining origin mechanisms are
**intentional and external**: the public C# AST API
(`new Expr.SequenceConstruct(...)` + public `Evaluator.Run(Expr)`), Lean's
exported `sequenceConstruct` helper, and the test suites. The node is
therefore unreachable from valid KatLang surface syntax, but deliberately
reachable through public semantic-AST construction.

**Why its evaluation drops `()`.** The node has join semantics: an empty
contribution adds no items
(`evalSequenceConstructCounted` skips `valueCount = 0` leaves, splices spread
leaves, normalizes). This is intentional for the internal role, pinned by
CoreTests (`spreadEmptyJoinContributesNoItems`,
`internalSequenceConstruct*` guards), and exactly why the node must stay
surface-unreachable: written parentheses always keep a non-spread `()`
visible. Canonical counterexample: internal `sequenceConstruct((), 1)`
evaluates to `1`; written `((), 1)` is `S[S[], 1]`.

**Divergence found and fixed — compatibility note for semantic-AST
consumers (authoritative statement; other documents cross-reference this
paragraph).** C# previously applied an undocumented, C#-only strict-variadic
suffix reshape (`SplitStrictVariadicSuffixArgument` +
`ConstructSequenceExpr`) when a builtin call's argument algorithm was exactly
one `Expr.SequenceConstruct`. Current KatLang parsing never produced that
shape, so **no KatLang source program is affected** — the path was reachable
only through manually authored or externally supplied semantic ASTs built
with the public AST API. The reshape had no Lean counterpart, was exercised
by zero tests, and could produce results different from Lean; it was
inconsistent with the then-current boundary model, which treated a lone
grouped source as one collection value rather than structurally redistributing
written slots across the control-argument boundary. It was **removed** before
the fixed-collection migration. Under the current model, an externally
constructed `SequenceConstruct` used as the collection argument value-evaluates
once, binds as the one fixed `collection` value, and is opened only by the
post-binding collection view on both implementations. This is a
**compatibility-affecting bug fix for public semantic-AST consumers**, even
though it is not a surface-language change. Verified outcomes (pinned in
`SequenceConstructContainmentTests` and the `internal__sc_*` differential
cases):

| Current hand-built AST input | Current aligned result |
|---|---|
| `take(SC[1, (2, 5)], 2)` | `[1, (2, 5)]` on both; the nested pair stays one item |
| `take(SC[1, 2, 5], 2)` | `[1, 2]` on both |
| `take(SC[(), 1, 2], 2)` | `[1, 2]` on both; the internal join drops the `()` leaf |
| `sum(SC[1, 2])` | `3` on both |

**Containment guarantees and their enforcing tests:**

| Guarantee | Enforced by |
|---|---|
| Surface syntax never parses or elaborates to the node (zero origin sites) | `SequenceConstructContainmentTests.SurfaceSequenceSyntax_NeverParsesToSequenceConstruct` + `EntireSemanticExplorerCorpus_ParsesWithoutSequenceConstruct` (all corpus programs attempted, the deliberate parse-error cases skipped; see §5.1) + pre-existing `ParserTests` absence assertions |
| Surface forms keep their intended AST family | `ParenthesizedSequenceSyntax_UsesExpectedNodes` |
| Production visitors rebuild, never drop or originate | `ProductionVisitor_PreservesExternallyOriginatedNode` |
| Node semantics pinned (incl. `()`-drop, spread splice) | `DirectSequenceConstruct_DropsEmptyLeavesAndSplicesSpreads` (C#), `internalSequenceConstruct*` guards (Lean CoreTests) |
| Lean/C# agreement on the node | 13 `internal__sc_*` cases in the generated `SemanticExplorerCases.lean` (pinned to C#-observed results) |
| Lean plain/counted agreement | plain eval is the counted projection on both sides + the artifact's per-case internal cross-check |
| Accidental surface exposure detected at the observation level | `InternalNodeSurfaceHazard` findings in `SemanticExplorerTests` (internal vs surface-counterpart relations, visible in `SemanticExplorerReport.json` under `internalNodeCases`) + `DirectSequenceConstruct_IsIntentionallyDifferentFromWrittenParentheses` |
| Purpose documented at definition/eval sites | doc comments on `Ast.cs` `SequenceConstruct`, `EvalSequenceConstructCounted`, Lean `Expr.sequenceConstruct`, `evalSequenceConstructCounted` |

**Guidance for future syntax work:** do not reuse this node for written
sequence syntax; parenthesized lists are blocks. If a new internal join is
ever needed, prefer extending the explorer's internal-node corpus in the
same change.

## 8. Running the validator

- C# invariants + JSON report: `dotnet test .\KatLang.slnx --filter SemanticExplorer`
  (also runs in the full suite; report at
  `tests/KatLang.Tests/bin/<cfg>/net10.0/SemanticExplorerReport.json`).
- Lean differential: `lake build SemanticExplorerCases` (wired into
  `scripts/validate-all.ps1`).
- Regenerate after intentional semantics changes:
  `$env:KATLANG_REGENERATE_SEMANTIC_EXPLORER = "1"; dotnet test .\KatLang.slnx --filter SemanticExplorerLeanArtifact`,
  review the artifact diff, then rebuild the Lean target.
