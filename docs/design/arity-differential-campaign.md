# Arity-Differential Campaign (July 2026)

A generated semantic differential test campaign comparing the production
KatLang implementation against an independent executable mirror of the
list-aware Core Arity Algebra, across the meaningful combinations of value
shape × receiver × binding form × spread multiplicity.

Everything lives in `tests/KatLang.Tests/ArityDifferential/`:

| File | Role |
|---|---|
| `AlgebraOracle.cs` | Test-only executable oracle: `OracleVal` (atom/seq/list) plus `items`, `normalize`, `capture`, `collect`, `structureItems?`, `openLoneStructure`, the origin-tagged call supply (`OracleSlot` / `OracleOrigin`, `written` / `final` / `values`), `loneWrittenSeq?` / `collectorSupply` / `fuseCollectorSegment` (the collector supply-boundary law), `bindPats`/`bindArgs`/`bindDeconstruct`, the repeated-spread composition, `valueCount`, and the root-row rule. Each member's doc comment names its Lean anchor. References nothing from `src/KatLang`. |
| `ArityDifferentialModel.cs` | The dimensions (`ReceiverKind`, `BindingForm`, `SpreadMultiplicity`), the `ReceiverLaw` taxonomy with Lean references, and the case records. |
| `ArityDifferentialMatrix.cs` | The deterministic generator: value-shape catalog, receiver templates, relational families, diagnostic matrix, and the exclusion ledger that accounts for every theoretical cell. |
| `ArityDifferentialTests.cs` | The xunit runner: per-case theories, relational checks, diagnostics, receiver-once budget probes, oracle self-checks, determinism check, coverage accounting, and the `ArityDifferentialReport.json` side-car. |

## What the campaign asserts

1. **Matrix cases** — each generated program runs through the production
   front end and evaluator (`SemanticExplorerHarness.Observe`, which itself
   cross-checks `Evaluator.RunCounted` against `KatLangEngine.Run`) and must
   produce exactly the neutral observation (`ok raw=… n=…` / `err category`)
   computed by the algebra oracle. Every case names ONE primary receiver law;
   the oracle's intermediate steps are recorded as an algebra trace and
   printed on failure together with the Lean reference.
2. **Relational families** — pairs of programs the formal model says must
   agree (direct/dotted, stacked/grouped repeated spread, spread/literal
   items, deconstruction item-view, forwarding round trip) or must stay
   observably different (capture vs collect, the repeated-spread fixed-point
   characterization in both directions, the grouped-receiver exception
   boundary). Both sides are also pinned absolutely against the oracle, so a
   relation can never pass because both sides drifted together.
3. **Diagnostic matrix** — invalid collect-marker structure, misplaced
   spreads, and arity-after-spread programs with stable rejection identities
   (parse-diagnostic fragments or the shared error-category taxonomy).
4. **Accounting** — the theoretical space is `receivers × forms × shapes ×
   multiplicities` (6 × 3 × 14 × 3 = 756 cells). The generator throws if any
   cell is neither covered by a case nor matched by a documented exclusion
   rule, and `Coverage_EveryTheoreticalCellIsCoveredOrExcludedWithAReason`
   pins the identity `covered + excluded = theoretical`. Exclusions carry
   their reasons into `ArityDifferentialReport.json`.
5. **Determinism** — `Generation_IsDeterministicAcrossCleanRegenerations`
   regenerates everything from scratch twice and fingerprints ids, sources,
   expectations, traces, and exclusions.

## Oracle correspondence

| Oracle member | Lean anchor |
|---|---|
| `OracleVal` Atom/Seq/List | `CoreArityAlgebra.Val` (`atom`/`seq`/`list`) |
| `Items` | `CoreArityAlgebra.items` = full-model `Result.spreadItems` |
| `Normalize` | `CoreArityAlgebra.normalize` = `Result.normalize` |
| `Capture` | `CoreArityAlgebra.capture` = `Result.normalize ∘ Result.sequenceValue` (`captureForArityLaw`) |
| `Collect` | `CoreArityAlgebra.collect` = `collectSegment` / `Result.listValue` |
| `StructureItems` | `CoreArityAlgebra.structureItems?` = `Result.structureItems?` |
| `OpenLoneStructure` | `CoreArityAlgebra.openLoneStructure` |
| `IsLoneStructure` | `CoreArityAlgebra.loneStructure` |
| `OracleOrigin` / `Written` / `Final` / `Values` | `CoreArityAlgebra.Origin` / `written` / `final` / `values` (full model: `SupplyOrigin` on `ParameterPatternInput`, marked by `collectVariadicCallItems`) |
| `LoneWrittenSeq` / `CollectorSupply` / `FuseCollectorSegment` | `CoreArityAlgebra.loneWrittenSeq?` / `collectorSupply` / `fuseCollectorSegment` (full model: `KatLang.lean collectorSupply` inside the pattern binders) |
| `BindPats` / `BindArgs` / `BindDeconstruct` | `CoreArityAlgebra.bindPats` / `bindArgs = bindPats ∘ fuseCollectorSegment` / `bindDeconstruct = bindPats ∘ openLoneStructure` (`bindPats_collect_exact` allocation) |
| `SpreadSupply(v, stars)` | first star `items`, each further star `items ∘ capture` — `repeated_spread_cardinality`; evaluator: `evalSequenceSpreadCounted` |
| `ValueCount` | `Result.valueCount` (`valueCount_le_one`, `valueCount_empty_list`) |
| `RootNonSpreadRow` | `evalAlgOutputCountedCore`'s non-spread slot rule (a non-spread row is one visible slot even when empty) |

The oracle deliberately models ONLY this fragment — no expressions, no
environments, no builtins — so it cannot become a second interpreter, and it
is compared with the runtime only through the neutral encoding shared with
the generated Lean guards (`LeanObsTemplate.SharedDefinitions`).

## Receiver-law taxonomy

`ReceiverLaw` in `ArityDifferentialModel.cs` is the closed list; each law maps
to its Lean definition/theorem via `ReceiverLaws.LeanReference`, and the
coverage test asserts every declared law is exercised by at least one
generated case. Three behaviors surfaced by the campaign deserve explicit
mention because they are receiver-specific exceptions rather than instances
of the plain algebra:

1. **`GROUPED_SPREAD_RECEIVER_FEEDS_LEADING_COLLECTING`** — `(A*).F` is the
   capture receiver for every callee EXCEPT one whose binding plan has a
   leading flat collecting parameter, where the parenthesized spread feeds
   its items exactly like the fluent `A*.F` (Lean
   `parenthesizedSequenceSpreadReceiver?` + `hasLeadingFlatCollectingParameter`,
   C# `Evaluator.BuildLexicalReceiverCallArgs`, pinned by
   `StarSyntaxTests.SpreadInsideAGroup_IsACaptureReceiver_NotAFluentSupply`
   and CoreTests `dotCallParityCases` C–G). The relational family
   `grouped-receiver-exception` pins the boundary from four sides: fluent
   coincidence, written-argument difference, stored-capture difference (the
   rule is syntactic on the receiver expression), and the non-leading
   collecting case (`Mid3`) where the exception does NOT apply.

   > **Superseded (August 2026, compositional dot-call collecting receiver
   > binding).** The spelling- and callee-dependent exception above was
   > REPLACED by a general "segment" rule (`COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY`):
   > every lexical dot-call receiver was one leading segment carrying its raw
   > counted supply, consumed by a flat top-level collecting parameter, so a
   > written group receiver fed a collector its rows (`(1, 2, 3).Mean` averaged
   > the items) and a named `()` receiver supplied zero items.
   >
   > **Superseded again (September 2026, dot-call passes a value).** The
   > segment rule is GONE with its carrier (`CollectingSegmentEmittedCount` /
   > `collectingSegmentCount?`), its Lean laws (`dot_receiver_segment_*`), and
   > the oracle's `StoredReceiverSegmentSupply`. The receiver of an
   > extension dot-call is the ORDINARY leading argument of the written call
   > (`R.F(args)` ≡ `F(R, args)`; law **`DOTTED_CALL_EQUALS_DIRECT_REWRITE`**),
   > so it is ONE collected item whatever it is (`(1, 2, 3).Mean` binds
   > `[(1, 2, 3)]`; `().Gather` collects `[()]` exactly like `Gather(())`),
   > and only the spread marker supplies items (`R*.F` ≡ `F(R*)`, law
   > **`FLUENT_SPREAD_RECEIVER_IS_LEXICAL_CALL`**; the capture `(R*).F` ≡
   > `F((R*))` is **`GROUPED_SPREAD_RECEIVER_CAPTURES`** for every callee,
   > collectors included). The relational family is now
   > `grouped-receiver-capture` (grouped vs fluent DIFFER except on
   > singleton supplies; grouped vs written argument and grouped vs stored
   > capture always AGREE; the non-leading `Mid3` case agrees), the
   > `direct-vs-dotted` family always agrees, and the written-receiver
   > templates are `dot-inline-collect` / `dot-nested-collect` /
   > `dot-list-literal-collect` / `dot-written-fixed-prefix` /
   > `dot-written-suffix-whole` / `dot-written-suffix-collected` /
   > `dot-empty-collect`. See `SEMANTIC-ALIGNMENT.md` "Dot-call passes a
   > value" and the `KatLangArityLaws` `dot_receiver_*` bridge laws.
   >
   > **Refined (September 2026, the collector supply-boundary law).** The
   > dotted equivalence is untouched, but what a COLLECTING callee binds for
   > its lone written sequence slot changed: the oracle's call supply now
   > carries slot provenance (`OracleSlot` = value × `OracleOrigin`;
   > `Written` for a non-spread written slot, `Final` for an explicit-spread
   > item), and `BindArgs` is `BindPats ∘ FuseCollectorSegment` — the
   > segment allocated to the collector after fixed prefix/suffix allocation
   > opens exactly one level when it is ONE written sequence value
   > (`CollectorSupply`), and is otherwise collected exactly (laws
   > **`COLLECTOR_LONE_WRITTEN_SEQUENCE_OPENS_ONE_LEVEL`** and
   > **`COLLECTOR_EXPLICIT_SPREAD_ITEM_IS_FINAL`**;
   > `CALLBACK_COLLECTING_COLLECTS_ONE_SLOT` became
   > **`CALLBACK_ITEM_IS_A_WRITTEN_SLOT`**, since a whole callback item is a
   > written slot). Consequences in the matrix: `Gather(V)` / `V.Gather` /
   > `(V, 9).Gather` / `().Gather` / `[V].map(GatherCb)` open a lone written
   > sequence value one level (`().Gather` is `[]` like `Gather(())`; lists
   > stay `[V]`), `Mid3(0, V, 9)` and `Suffix2((V, 9), 5)` open the lone
   > sequence left after fixed allocation, `(V*).Gather` is the written
   > capture `Gather((V*))` and now COINCIDES with the fluent `V*.Gather`
   > for every shape except the lone structured item `[(1, 2)]` (whose
   > singleton capture exposes a pair that opens, while the final spread
   > item stays exact), and `spread-vs-literal-items` agrees except when the
   > item view is exactly one sequence value (the literal slot is written,
   > the spread item final). Loop init and state slots are unchanged (final
   > items: `Snap.repeat(1, V)` still collects `[V]`).
2. **Loop init arity floor** — `repeat`/`while` require at least one initial
   state slot, so a zero-item spread in init position (`Snap.repeat(1, ()*)`)
   is an ordinary arity rejection after spreading.
3. **Counted callback scalar strictness — RESOLVED (September 2026, S3).**
   The callback pattern matcher's scalar fallback used to be
   singleton-pattern-only (`bindCountedParameterPattern`: `if items.length ==
   1`), so `[7].map(NestedCb)` with `NestedCb((x, *y))` was an arity
   rejection while the ordinary call `NestedCb(7)` bound `x = 7, y = []`.
   Both binders now open a nested pattern's value through the ONE rule
   `Result.sequenceValuePatternItems` / `SequenceValuePatternItems`, so the
   matrix row `cb-map-nested-pattern` binds a scalar element through the
   ordinary one-item fallback (`[[7, []]]`) exactly as the direct call does.

## Relationship to the other corpora

- The **semantic explorer** (`SemanticExplorerCorpus`) is the Lean/C#
  differential: it re-pins *observed* behavior as generated Lean guards. This
  campaign added the three stacked-spread templates `spreadRootStacked`,
  `collectingStacked`, `captureStacked` there (26 values each), so the
  repeated-spread chain is now Lean/C#-differentially guarded and not only
  hand-pinned by the `stackedSpread*` CoreTests guards.
- The **language spec** (`LanguageSpecCorpus`) is hand-written canonical
  expectations. This campaign complements it: expectations here are computed
  by the algebra oracle, and a failure means the runtime disagrees with the
  algebra (or the oracle misstates a documented receiver law — the failure
  report prints both the algebra trace and the Lean reference to arbitrate).
- The Lean-side laws corresponding to the oracle live in
  `lean/CoreArityAlgebra.lean` / `CoreArityAlgebraProofs.lean` (extraction)
  and `lean/KatLangArityLaws.lean` (bridge over the real model).

## How to extend

**Add a value shape.** Append to `ArityDifferentialMatrix.Shapes` with a
stable kebab id, the KatLang literal, the oracle value, and a description of
what the shape distinguishes. Every template picks it up automatically; the
coverage identity forces you to either generate cases or add an exclusion
rule for any cell the templates cannot express. Update the pinned counts in
`Coverage_PinnedPartitionCounts` deliberately. Do not add shapes that differ
only in numeric literals.

**Add a receiver template.** Add an `Add…Cases` builder (or extend one) in
`ArityDifferentialMatrix.Generate`. Compute the expectation exclusively
through `AlgebraOracle` operations, record the algebra trace, and assign the
primary law per multiplicity. If the template fills previously excluded
cells, delete or narrow the exclusion rule — the accounting test fails on
rules that silently stop matching reality only when a cell would go
unaccounted, so review the exclusion list whenever coverage moves.

**Add a receiver law.** Extend `ReceiverLaw`, add the Lean anchor to
`ReceiverLaws.LeanReference`, and use it as some case's primary law — the
coverage test fails on laws that are declared but never exercised, and on
laws without a Lean reference. If a new behavior cannot be assigned ONE
existing law and needs a new one, first check whether it is genuinely a
documented receiver-specific rule (like the three above); do not invent a law
named after a test to make a mismatch pass.

**Regeneration/validation.** The matrix is generated in memory — there is no
checked-in artifact to refresh. Run:

```powershell
dotnet test .\KatLang.slnx -p:UseSharedCompilation=false --filter FullyQualifiedName~ArityDifferential
```

After changing the semantic explorer corpus (the stacked templates live
there), regenerate and rebuild the Lean artifact:

```powershell
$env:KATLANG_REGENERATE_SEMANTIC_EXPLORER = "1"
dotnet test .\KatLang.slnx --filter SemanticExplorerLeanArtifact
Push-Location .\lean; lake build SemanticExplorerCases; Pop-Location
```

and reconcile the counts in `docs/design/sequence-boundary-audit-2026-07.md`
(the accounting test tells you the expected row verbatim).
