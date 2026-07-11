# Sequence-Boundary Audit and Semantic Explorer (July 2026)

Status: completed audit + durable validator. This document is the Phase-1
receiver/boundary review deliverable for the small-state arity-semantics
validator, and the reference for the invariants that validator enforces.

The validator itself lives in:

- `tests/KatLang.Tests/SemanticExplorerCorpus.cs` — bounded value space x receiver templates (shared corpus),
- `tests/KatLang.Tests/SemanticExplorerHarness.cs` — neutral observation format (raw structure, emitted count, error category),
- `tests/KatLang.Tests/SemanticExplorerTests.cs` — C#-side structural invariants + machine-readable report,
- `tests/KatLang.Tests/SemanticExplorerLeanArtifactTests.cs` — generator/pin for the differential artifact,
- `lean/SemanticExplorerCases.lean` — generated Lean AST corpus with `#guard`s pinned to C#-observed results (`lake build SemanticExplorerCases` fails on any Lean/C# divergence).

## 1. The current boundary model (as implemented)

One rule with four explicitly documented non-boundary exceptions, confirmed by
executable evidence on the 931-case surface corpus (accounting in §5.1).

**Counts.** Every evaluation step carries `CountedResult = (value, emittedCount)`.
`Result.valueCount` is 0 for `()` and 1 for everything else.

**Value boundaries** (result re-counted to `valueCount` via
`reCountValueBoundary` / inline equivalent — the value itself is never
rebuilt): user calls, conditional calls, lexical zero-arg property access `A`,
explicit call `A()`, structural dot access `A.B` / `A.B()`, `if`, and the
collection-producing builtins (`order`, `orderDesc`, `distinct`, `take`,
`skip`, `filter`, `map`, `range`, `atoms`).

**Non-boundaries** (multi-item counts flow through):

1. Root/body output accumulation: a spread slot contributes its opened item
   count (possibly 0); a **non-spread slot contributes `max(1, emitted)`** —
   so `()` stays one visible row, and a supply-emitting expression such as
   `x:0` or a variadic parameter reference emits several rows at root.
2. Raw variadic parameter storage (`countedParamEnv` / `VariadicStreamEnv`):
   the captured value keeps its raw item count, which is what makes
   internal forwarding (`sum(a)`, `a...`) work.
3. `while`/`repeat` multi-slot loop state.
4. The strict single-value `map`/`reduce` callback contract (multi-output or
   `()`-valued callback results are errors, not grouped values).

**Construction.** Parenthesized lists parse to zero-parameter blocks whose
output slots keep `()` items visible; slots are combined with the shallow
`CombineOutputSlots` (1 slot -> the slot itself, else one sequence value).
Written singleton parens are transparent (`(1)` = `1`, `(())` = `()`,
`(((1,2)))` = `(1,2)`). Deep `Result.Normalize` is applied only at
construction/capture sites whose inputs are already canonical, so it never
flattens meaningful nested multi-item structure.

**Collection builtin returns.** Kept items recombine with the shallow
singleton-erasing `CombineCollectionResult`: 0 items -> `()`, 1 kept item IS
the result (no orphan wrapper), 2+ items -> one sequence value preserving all
sibling boundaries including `()` items.

**Spread.** `expr...` opens exactly one layer via `toItems`: `()...`
contributes zero items, an atom spreads to itself, nested sequence items stay
intact.

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

**count / .count.** Both paths reach the same item-supply binding: one grouped
argument is opened one level (singleton-boundary normalization), sibling
groups are preserved. `count`, `.count`, `count(V...)`, and spread-supply
counts all observe the same layer.

**Cache.** `A` vs `A()` changes only the per-run zero-arg property cache
usage; the cached raw count is re-counted at every observable boundary, so
caching cannot change observable counts or structure (validated).

## 2. Receiver/boundary matrix

Neutral encoding: `S[...]` = sequence value (raw structure), `n` = emitted
count at the observed boundary, `E:x` = typed error. Full per-cell data for
all 931 surface cases is in the machine-readable report
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
| root `V...` | `items(V)` | canonical V | `items(V).count` | `()...` -> 0 rows, display `""` |
| root `(), 99` | 2 slots | `S[S[], 99]` | 2 | `()` stays a visible row |
| capture `x = V` | 1 | canonical V | 1 | identical for `x`, `x()`, `A.X`, `A.X()` |
| fixed param `F(V)` | 1 arg | V | 1 | call never opens a grouped arg |
| fixed `F(V...)` | `items(V)` args | item / `E:arity` | 1 | succeeds iff exactly 1 item |
| variadic `F(V)` / `F(V...)` | 1 arg / items | V (rest-only coincidence) | 1 | mixed shapes distinguish the two |
| mixed `F(h, t...)(V...)` | items | front/back split; rest groups middle | 1 | rest of 1 item collapses (capture law) |
| deconstruction `x, y = V` | `items(V)` | element-wise match | 1 | `= V` ≡ `= V...` (unpacking receiver) |
| explicit seq `(V, 99)` | 2 slots | `S[V, 99]` | 1 | `()` survives as item; nesting intact |
| spread in seq `(V..., 99)` | items+1 | shallow combine | 1 | `(()..., 99)` = `99` (singleton collapse) |
| `count(V)` / `V.count` / `count(V...)` | items | `items(V).count` | 1 | same layer for all four forms |
| `x:0` (item = pair) | — | projected item content | `max(1, k)` | supply at root; 1 value everywhere else |
| `x:0` (item = `()`) | — | `S[]` | 1 | projection count 0, root bump to 1 row |
| `x:9` / `x:-1` | — | `E:index` / parse error | — | negative selector rejected at parse (C#) |
| `==` / `!=` | 2 values | `1`/`0` | 1 | structural, reflexive, path-independent |
| re-entry `I(x)`, `P = R` | 1 | unchanged | 1 | validated across double re-entry |
| `take/skip/filter/distinct/order/map` | items | shallow-combined survivors | 1 | 1 survivor IS the result (no wrapper) |
| `range`, `atoms` | — | flat atom sequence | 1 | `atoms` is the recursive flattener |

## 3. Answers to the architectural questions

1. **Should collection builtins always return one captured sequence-value
   boundary?** They return one *value* whose boundary erases a single
   survivor (documented #133 rule). This is coherent with capture/`combineOutputSlots`
   and is what keeps display/count/equality/indexing agreeing on one canonical
   value. Keep.
2. **Should lexical zero-arg access and structural dot access re-count
   identically?** They already do (validated: `capture`/`captureCall`/
   `dotAccess`/`dotAccessCall` agree on every corpus value).
3. **Which operations may preserve an internal item supply?** Exactly the four
   documented non-boundaries (§1) plus `:` projection *between* evaluation and
   the next boundary. No others were found in the sweep.
4. **Which must expose a captured value?** Every property/call/builtin result,
   argument slot, sequence-literal item, and stored binding.
5. **Where is capture/normalization applied?** Deep `normalize` at written
   construction and variadic capture (inputs canonical); shallow combine at
   output slots and collection returns. The two agree because item internals
   are never renormalized.
6. **Where may spread reopen a value?** Any expression-list context (root/body
   slots, call args, sequence literals, builtin supplies) — exactly one layer.
7. **Can any operation construct a literal-unwritable value?** No. 0 orphan
   singleton nodes across all generated cases (enforced as `UnexpectedWrapper`).
8. **Is every displayed value reconstructable?** Yes for numeric/sequence
   values including all counts (enforced as `DisplayNotReconstructable`),
   with two documented exceptions: string display drops quotes (explicit
   non-goal), and a zero-item output displays as no text, which is not a
   parseable program (`()...` at root).
9. **Can two values display identically but behave differently?** No collision
   found across the corpus (enforced as `DisplayCollision`).
10. **Can one raw value observe differently by construction path?** No.
    Equality/count/indexing agree across literal, capture, call-return,
    builtin-return, deconstruction, and cache/no-cache paths (validated).
11. **Can a builtin one-survivor reduction leave a hidden wrapper?** No — the
    survivor IS the result. Consequence worth knowing: `count(take(V, 1))` is
    the *survivor's* item count (e.g. 2 for `take(((1,2),3),1)`, 0 for a kept
    `()`), not 1. That follows from the same two documented rules
    (single-survivor erasure + count's singleton opening) and is pinned by the
    validator.
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
    normalize sites receive canonical inputs; combine sites are shallow.
    Validated by `UnexpectedFlattening` on nested values incl. `((), (1, 2))`,
    `(((), 1), 2)`.
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
program `(A..., 99)` with a multi-item `A` — Lean produced `((1, 2), 99)`
where C# and the tutorial (`(Values..., 8)` = `(1, 2, 3, 8)`) produce
`(1, 2, 99)` — through every plain-evaluation path: value-position sequence
literals, binary-operand evaluation (so `(P..., 99) == (1, 2, 99)` was `0` in
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
deconstruction opening asymmetry (proven in `CoreArityAlgebraProofs`:
`agree_on_lone_seq_iff_lone_rest`); rest-only coincidence `F(V)` ≡ `F(V...)`;
strict map/reduce callback contract; string display non-roundtrip.

**Unresolved design choices (pre-existing, unchanged):** callback
deconstruction (deferred per BINDING-ARCHITECTURE.md Phase 26); zero-item
root output displaying as empty text (not reconstructable as a program).

## 5. Lean/C# differential results

The generated artifact pins every Lean-representable corpus case
(**911 surface cases** as of this audit — the surface corpus minus its 20
parse-level cases such as `(3,)`, `x:-1`, `A... == A...`, and `1 ; 2`, which
are C#-only typed outcomes since Lean has no surface parser — plus **13**
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
| Surface corpus (= C# semantic report surface section) | 931 | 867 template cases (51 receiver templates x 17 values) + 64 specials; outcomes 816 ok / 95 err / 20 parse-error | internal-node cases; anchor pins | `SemanticExplorerCorpus.AllCases()`; report `partition.surfaceCases` |
| Lean-representable surface differential | 911 | the 931 above minus the 20 parse-level cases (17 `indexNeg__*` + `trailingComma`, `spreadAsBinaryOperand`, `semicolonSeparator`) | parse-level cases (Lean has no surface parser) | report `partition.leanRepresentable`; artifact footer |
| Internal `SequenceConstruct` corpus | 13 | direct-AST `internal__sc_*` cases | everything source-driven | `SemanticExplorerCorpus.InternalNodeCases()`; report `partition.internalNodeCases` |
| Generated Lean guards | 924 | 911 surface + 13 internal-node (one `#guard` per case) | nothing (footer states the split) | `SemanticExplorerCases.lean` footer: `-- Total: 924 guards (911 surface + 13 internal-node).` |
| C# semantic report internal-node section | 13 | id, relation, internal + surface observations per case | — | report `internalNodeCases` |
| Parser/elaboration reachability sweep | 931 attempted, 911 scanned | every corpus source that parses (post-`FrontEndPipeline` ASTs) | the 20 deliberate parse-error cases (skipped) | `EntireSemanticExplorerCorpus_ParsesWithoutSequenceConstruct` |
| Containment test invocations | 32 | 18-form parser theory, corpus sweep, AST-family pins, visitor-preservation fact, 8 direct-node pins, difference fact, 2 lone-argument facts | explorer/anchor tests (counted separately) | `dotnet test --filter SequenceConstructContainment` |
| Explorer test invocations | 30 | anchor pins, invariant sweep, artifact freshness + comparable-observations + partition facts | — | `dotnet test --filter SemanticExplorer` |
| Full .NET suite | 2348 | everything incl. all of the above | — | `dotnet test .\KatLang.slnx` |

The previously reported pairs reconcile as: **931 vs 912** — 931 is the full
surface corpus; the Lean artifact excludes exactly the 20 parse-level cases,
giving 911 (the old "912" additionally counted the artifact's header comment
that mentions `#guard`). **925 guards** similarly overcounted 924 by that
same header line. **"~970" sweep programs** was an estimate; the sweep
attempts all 931 corpus sources and scans the 911 that parse.

## 6. Recommended rule and residual risks

**Recommended coherent rule (already the implemented one — recommendation is
to keep it and enforce it):**

> Every property/call/builtin result, argument slot, sequence-literal item,
> and stored binding is a *value* boundary: one value, count `valueCount`.
> Item supplies exist only inside root/body output accumulation, raw variadic
> storage, loop state, and builtin collection binding; only written `...`
> (or the documented openers: deconstruction RHS, builtin singleton-boundary
> normalization, `:` projection) may open one layer of a value into a supply.
> All construction paths erase exactly the unwritable boundaries (singleton
> wrap, redundant empty nesting) and nothing else.

The smallest implementation change needed to enforce it: **none** — the rule
holds today; the change delivered is the validator that keeps it holding.

**Residual risks tracked by the validator:**

1. `Expr.SequenceConstruct`'s `()`-dropping evaluation is intentional
   internal-join semantics, contained and guarded — see §7.
2. New builtins that return collections must use `CombineCollectionResult` +
   `ReCountValueBoundary`; adding one to the corpus is one template entry.
3. Numeric divergence (Lean `Int` vs C# `decimal`) is out of scope for the
   integer-only corpus; extending values to decimals would surface it
   deliberately.

## 7. `Expr.SequenceConstruct` containment (July 2026 follow-up)

**Role (provenance-audited).** `Expr.SequenceConstruct` / Lean
`Expr.sequenceConstruct` is an internal sequence-JOIN node: the retained
encoding of the removed binary spread-join (`A...B` before it became the
expression-list slots `A..., B`). It is **not** the AST representation of
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

**Why its evaluation drops `()`.** Join semantics inherited from the old
two-operand spread form: an empty contribution adds no items
(`evalSequenceConstructCounted` skips `valueCount = 0` leaves, splices spread
leaves, normalizes). This is intentional for the internal role, pinned by
CoreTests (`postfixSpreadEmptyJoinContributesNoItems`,
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
inconsistent with the ordinary boundary model, which treats a lone grouped
argument as one value opened once by singleton-boundary normalization rather
than structurally redistributing written slots across the suffix boundary.
It has been **removed**: an externally constructed lone `SequenceConstruct`
argument now value-evaluates to one grouped value and follows the ordinary
grouped-argument path on both implementations. This is a
**compatibility-affecting bug fix for public semantic-AST consumers**, even
though it is not a surface-language change. Verified outcomes (pinned in
`SequenceConstructContainmentTests` and the `internal__sc_*` differential
cases):

| Hand-built AST input | Former C# (reshape) | Lean | Current aligned |
|---|---|---|---|
| `take(SC[1, (2, 5)])` | `(1, 2)` | `err arity` (take count must be one whole number) | `err arity` on both |
| `take(SC[1, 2, 5])` | `(1, 2)` | `(1, 2)` | `(1, 2)` (unchanged) |
| `take(SC[(), 1, 2])` | `1` | `1` | `1` (unchanged) |
| `sum(SC[1, 2])` | `3` | `3` | `3` (unchanged) |

**Containment guarantees and their enforcing tests:**

| Guarantee | Enforced by |
|---|---|
| Surface syntax never parses or elaborates to the node (zero origin sites) | `SequenceConstructContainmentTests.SurfaceSequenceSyntax_NeverParsesToSequenceConstruct` (18 forms) + `EntireSemanticExplorerCorpus_ParsesWithoutSequenceConstruct` (931 corpus programs attempted, 911 scanned post-elaboration; see §5.1) + pre-existing `ParserTests` absence assertions |
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
