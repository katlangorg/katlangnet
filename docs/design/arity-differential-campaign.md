# Arity-Differential Campaign (July 2026)

A generated semantic differential test campaign comparing the production
KatLang implementation against an independent executable mirror of the
list-aware Core Arity Algebra, across the meaningful combinations of value
shape × receiver × binding form × spread multiplicity.

Everything lives in `tests/KatLang.Tests/ArityDifferential/`:

| File | Role |
|---|---|
| `AlgebraOracle.cs` | Test-only executable oracle: `OracleVal` (atom/seq/list) plus `items`, `normalize`, `capture`, `collect`, `structureItems?`, `openLoneStructure`, `bindPats`/`bindArgs`/`bindDeconstruct`, the repeated-spread composition, `valueCount`, and the root-row rule. Each member's doc comment names its Lean anchor. References nothing from `src/KatLang`. |
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
| `BindPats` / `BindArgs` / `BindDeconstruct` | `CoreArityAlgebra.bindPats` / `bindArgs` / `bindDeconstruct` (`bindPats_collect_exact` allocation) |
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
2. **Loop init arity floor** — `repeat`/`while` require at least one initial
   state slot, so a zero-item spread in init position (`Snap.repeat(1, ()*)`)
   is an ordinary arity rejection after spreading.
3. **Counted callback scalar strictness** — the callback pattern matcher's
   scalar fallback is singleton-pattern-only (`bindCountedParameterPattern`:
   `if items.length == 1`), so `[7].map(NestedCb)` with `NestedCb((x, *y))`
   is an arity rejection; callback deconstruction for scalar elements is
   intentionally deferred.

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
