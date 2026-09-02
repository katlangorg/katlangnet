# The Executable Language Specification

This document is the maintainer guide for KatLang's canonical executable
specification: a single corpus of named semantic cases that four layers
consume and verify — the Lean model, the C# implementation, `tutorial.md`,
and the katlang-generator prompt files. It complements (and does not replace)
the semantic explorer described in
[sequence-boundary-audit-2026-07.md](sequence-boundary-audit-2026-07.md).

## 1. Where the canonical cases live

`tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs` is the single
authoritative source. Each `SpecCase` (schema:
`tests/KatLang.Tests/LanguageSpec/SpecCase.cs`) carries a stable kebab-case
`Id`, a `Category`, the KatLang `Source`, an expected `Outcome`
(Evaluates / EvalError / ParseError), and **hand-written canonical
expectations**: exact engine display, emitted count, raw value shape in the
neutral `S[...]` encoding, stable error category, optional probes
(equality / `count` / `.count` / indexing observations), an optional Lean AST
construction, and a reader-facing explanation.

The governance rule that makes this corpus canonical: **expectations are
never regenerated from observed behavior.** If a test in this system fails,
either the implementation drifted (fix the implementation) or the language
intentionally changed (edit the canonical case in a reviewed diff, then
regenerate the derived artifacts).

Contrast with `SemanticExplorerCorpus` (same test project): the explorer is a
generated cross-product corpus whose Lean artifact pins *observed* C#
behavior for bounded differential validation. The explorer answers "do Lean
and C# agree everywhere in this bounded space?"; the language spec answers
"do Lean, C#, the tutorial, and the generator all match what we *decided* the
language does?". Both corpora are kept disjoint (enforced by
`Schema_IdsDoNotCollideWithExplorerCorpus`), and their counts are never
summed into one total.

## 2. How each layer consumes the corpus

| Layer | Consumer | Drift signal |
|---|---|---|
| C# engine | `LanguageSpecRunnerTests` runs every case + probe through `Parser.Parse` / `Evaluator.RunCounted` / `KatLangEngine.Run` (via `SemanticExplorerHarness`) | test failure |
| Lean model | generated `lean/LanguageSpecCases.lean`: one `#guard obs case_x == "<canonical neutral>"` per Lean-guarded case | `lake build LanguageSpecCases` failure |
| tutorial.md (linked) | `<!-- spec:case-id -->` markers before fences; `TutorialSpecTests` verifies source + expected output against the case | test failure |
| tutorial.md (all result claims) | `TutorialResultSweepTests` executes every fence followed by a `**Result(s):**` claim through `KatLangEngine.Run` and display-matches the claim (section 6a) | test failure |
| generator prompts | marker-delimited generated block in `.github/agents/katlang-generator.agent.md` AND `experimental/prompts/katlang-generator.txt`, rendered from cases flagged `IncludeInGeneratorPrompt` | staleness test failure |

The Lean/C# trust boundary: the two implementations are never executed in one
process. Both are checked against the SAME canonical neutral observation
string — C# at `dotnet test` time, Lean at `lake build` time, coordinated by
the committed generated artifact. A representable case on which they disagree
cannot pass both stages.

## 3. Partitions and counts

Every case is in exactly one of three partitions (identity enforced by
`Partition_CountsReconcile`):

- **Lean-guarded** — `LeanProgram` is set; the case is emitted into
  `lean/LanguageSpecCases.lean`.
- **parse-level** — `Outcome == ParseError`; C#-only because the Lean model
  has no surface parser.
- **C#-only** — evaluates/errs but has no Lean program; requires an explicit
  `LeanExclusionReason` naming the reviewed model divergence (the
  Decimal128-vs-Lean-Int numeric family, or the unmodeled Math-native
  surface; the numeric boundary itself is defined by the "Core numeric
  semantics" row in `src/KatLang/SEMANTIC-ALIGNMENT.md`). An integer-looking
  source is not automatically Lean-comparable: Decimal128 precision/range can
  diverge from unbounded `Int` before the result is observed.

Probes are C#-only auxiliary observations by design and are counted
separately. Internal-node (`Expr.SequenceConstruct`) cases are owned by the
semantic-explorer corpus, not this one.

Counts are never maintained by hand. The generated Lean artifacts embed an id
list plus `#guard <list>.length == N` where the list is built by the emission
loop and `N` is computed independently from the corpus partition — so a
generation bug fails `lake build`, not a comment. Machine-readable partition
summaries are written to `LanguageSpecReport.json` (and the explorer's
`SemanticExplorerReport.json`) in the test output directory.

## 4. What is generated (never edit by hand)

- `lean/LanguageSpecCases.lean` — regenerate with
  `$env:KATLANG_REGENERATE_LANGUAGE_SPEC = "1"; dotnet test .\KatLang.slnx --filter LanguageSpecArtifacts`
- `lean/SemanticExplorerCases.lean` — regenerate with
  `$env:KATLANG_REGENERATE_SEMANTIC_EXPLORER = "1"; dotnet test .\KatLang.slnx --filter SemanticExplorerLeanArtifact`
- the `=== BEGIN GENERATED: katlang-spec-examples ... ===` block inside both
  generator prompt files — regenerated by the same `LanguageSpecArtifacts`
  filter run as the spec Lean artifact.

Both Lean artifacts embed the same observation machinery (`neutral`,
`errCategory`, `runCountedM`, `obs`), emitted from the single C# constant
`LeanObsTemplate.SharedDefinitions` — extend `errCategory` there AND
`SemanticExplorerHarness.ErrorCategory` together when adding an `EvalError`
kind, then regenerate both artifacts.

A regeneration run WRITES the artifact and then FAILS BY DESIGN (also when the
content did not change): it is a regeneration, not a verification, and its
result must never read as green. `scripts/validate-all.ps1` removes every
`KATLANG_REGENERATE_*` variable from its process before it builds, so it never
regenerates anything. The shared contract and the flag registry are
`tests/KatLang.Tests/Infrastructure/ArtifactRegeneration.cs`; the same
discipline governs the public API baseline
(`tests/KatLang.Formatting.PublicApi.Tests/PublicApiBaseline.txt`,
`KATLANG_REGENERATE_PUBLIC_API`).

After any regeneration: review the diff, clear the flag, rerun the normal
verification, then run the corresponding `lake build` target.

## 5. How to add a new case

1. Add a `SpecCase` to `LanguageSpecCorpus.AllCases()` under the right
   category (`LanguageSpecCorpus.Categories`). Write the expectations from
   the *language rules* (AGENTS.md, the audit doc, the tutorial) — then let
   the runner tell you if the implementation disagrees. Do not paste observed
   output without checking it against the documented rules first.
2. Decide the partition. The ordinary path needs NOTHING beyond the source:
   the corpus derives `LeanProgram` from the source's real elaborated AST
   through `LeanAstEncoder` (M11), so a same-program differential case cannot
   be authored with two unrelated program definitions. Only two explicit
   deviations exist, both schema-enforced and count-ratcheted
   (`FidelityRatchet_LeanGuardedCoverageCannotSilentlyShrink`):
   - `LeanExclusionReason` — the case is C#-only (an intentional model
     divergence, e.g. decimal semantics outside the Lean Int core or the
     unmodeled Math-native surface);
   - `LeanProgramOverride` + `LeanOverrideReason` — an exceptional,
     deliberately hand-authored Lean construction (not same-program-verified;
     currently unused).
   If the encoder refuses a shape, corpus construction fails naming the case:
   either extend `LeanAstEncoder` deliberately (with reviewed goldens in
   `LeanAstEncoderTests`) or exclude the case with a reviewed reason.
   Exclusion IDs are pinned exactly in both corpora, and blank exclusion or
   override reasons are schema errors; a case cannot move out of derivation by
   merely toggling a boolean or incrementing a permissive count.
3. `dotnet test --filter LanguageSpec` — the runner verifies the C# side.
4. Regenerate the spec artifacts (section 4), review the diff, and
   `lake build LanguageSpecCases` — the guard verifies the Lean side.
5. Optionally link it in the tutorial (section 6) or flag it for the
   generator prompts (`IncludeInGeneratorPrompt = true`, then regenerate).

## 6. How tutorial examples reference cases

Put an HTML comment marker on its own line immediately before the example's
opening fence:

```markdown
<!-- spec:take-single-survivor -->
```

`TutorialSpecTests` then enforces: the marker resolves to an existing case id
(renames fail), each id is linked at most once, the fence text equals the
canonical `Source` byte-for-byte, and the expected output matches the
canonical display through whichever convention follows the fence —
`**Result:** `value``, `**Result:** error — ...`, or a `**Results:**` fence
(blank lines inside a results fence are presentation-only grouping and are
ignored for comparison). Fences whose expectations live in trailing
`# value` comments are covered by the comment-claims lint when the
value-literal claims line up one-to-one with display rows.

Keep prose free: only the marked source and its stated outputs are pinned.
Markers are invisible in rendered Markdown.

## 6a. The tutorial result-claim sweep (M13)

Independently of markers, **every** tutorial fence whose next non-blank line
is a result claim is executable documentation. `TutorialResultSweepTests`
executes the fence source through the public runtime (`KatLangEngine.Run`,
default options and normal resource limits) and compares the canonical
display (`RunResult.ToDisplayString()`, line endings normalized to `"\n"`)
against the claim. No marker is required — writing

````markdown
```
1 + 2
```

**Result:** `3`
````

automatically enters the sweep. The recognized claim forms (shared grammar in
`TutorialCorpus`, exercised on synthetic markdown by
`TutorialCorpusParserTests`):

- `**Result:** `value`` — one display row, matched exactly (Decimal128
  quantum, signed zero, `NaN`/`Infinity` and sequence/list delimiters
  included). A longer matching backtick run may delimit a value that itself
  contains a shorter backtick run;
- `**Results:**` (or `**Result:**`) followed by a bare fenced output block —
  one display row per non-blank line (blank rows are presentation-only
  grouping);
- `**Result:** error — ...` — the source must parse cleanly and fail
  evaluation (`EvalFailure`/`NoProgramOutput`; a parse failure or a
  successful evaluation fails the sweep). A generic error label promises only
  that classification. The tutorial's current three labels also name a
  specific failure family, so their complete source/prose inventory is pinned
  and checked through public `KatLangErrorCode` values (never rendered-message
  substrings) by
  `DetailedErrorClaims_MatchTheirReviewedStructuredErrors`.

The deliberately narrow fence contract is a column-zero, untagged, exactly
three-backtick fence; tagged, indented/list/blockquote, longer, and trailing-
space fence forms are not KatLang source fences. If any such unsupported form
is paired with a label-like Result line, parsing fails conspicuously. The label
lint is likewise fail-loud for plain `Result:`, changed emphasis/casing,
indentation, list/blockquote/heading placement, a claim not directly following
a source fence, an unterminated fence, or a Results label without an output
block. Whitespace-only separator lines count as blank. A formatting near-miss
therefore cannot silently drop a result claim out of verification. Accounting
is a pinned partition identity:
result-bearing fences = engine-verified + explicitly skipped, with the exact
skip inventory pinned in `SkipInventory_IsExactlyTheReviewedSet`.
Result-bearing coverage is additionally **monotonic**
(`CoverageRatchet_ResultBearingClaimsCannotSilentlyShrink`): new claims are
automatically accepted and tested with no pin to update, while removing an
existing claim requires deliberately lowering the pinned baseline in the same
reviewed diff.

The escape hatch for a genuinely non-standalone example is an explicit
reviewed skip on the marker line before the fence:

```markdown
<!-- spec:skip module loading needs a host-configured network downloader -->
```

The reason is mandatory and non-blank (a blank reason fails parsing), a skip
on a claim-less fence fails, and adding or removing a skip must update the
pinned inventory in the same diff. That inventory pins the complete section,
source, claim kind/display, and reason while deliberately ignoring line
numbers, so moving an unchanged example within its section is stable but
source/result/reason drift is reviewed. Use a skip only for structural reasons
(needs a downloader/host setup, intentionally illustrative); a stale result,
an inconvenient harness, or a real bug is never a skip reason. Examples with
nondeterministic output (e.g. `Math.Random`) must not carry an exact
`**Result:**` claim — describe the range in prose instead.

Blank lines inside a fenced Results block remain presentation-only grouping
and are removed before comparison, matching the pre-M13 marker convention.
Consequently that form cannot encode an empty-string row among other output
rows; no current claim needs that shape. KatLang string literals cannot span
physical lines, so multiline string values are not another ambiguity. If a
future tutorial example needs to distinguish an empty row or zero emitted rows
structurally, give it a marker-linked canonical case (raw value + emitted-count
pin) instead of relying on the display-only fenced form.

## 7. Running all validation

`pwsh .\scripts\validate-all.ps1` runs everything: the C# suite (spec runner,
tutorial checks, generator-block freshness, artifact freshness, partition
identities), `git diff --check`, and all Lean targets including
`LanguageSpecCases`.

## 8. Verification levels (use these words)

- **Theorem-level**: general laws proved over total functions of the real
  model (`lean/KatLangArityLaws.lean`: `normalize_idempotent`,
  `orphanFree_normalize`, capture canonicity, the spread/capture round-trip)
  and over the paper algebra (`lean/CoreArityAlgebraProofs.lean`). These
  cover the normalization/binding fragment only — the evaluator itself is
  `partial` and is NOT covered by theorems.
- **Bounded differential validation**: the generated `#guard` corpora
  (explorer + language spec). Say "generated guards over the representable
  partition", never "formally verified evaluator".
- **Parser-level cases**: C#-only; Lean has no surface parser.
- **Implementation-only regressions**: C#-only cases with an explicit
  exclusion reason (e.g. decimal display).

## 9. Worked example: one case through all four layers

Case `take-single-survivor` (`LanguageSpecCorpus.cs`):
source `take(((1, 2), (3, 4)), 1)`, canonical display `[(1, 2)]`, canonical
neutral `ok raw=L[S[1, 2]] n=1`, probes for `count(...)` = 1, non-equality
with `(1, 2)`, and re-spreading the result (`take(...)*` is the kept pair).

1. **C#**: `LanguageSpecRunnerTests.Case_MatchesCanonicalExpectations`
   parses and evaluates the source, asserting the neutral observation and
   display; the probes run the same way.
2. **Lean**: the generated `lean/LanguageSpecCases.lean` contains
   `def case_take_single_survivor` (the equivalent AST: a `take` call on a
   block-of-blocks) and
   `#guard obs case_take_single_survivor == "ok raw=L[S[1, 2]] n=1"`. The
   related general law — collection results are exact lists whose one-item
   boundary is never erased — is the theorem side: the
   `makeCollectionListResult` pins in CoreTests plus
   `makeCollectionListResult_exact` in `KatLangArityLaws`.
3. **Tutorial**: the `take` section's example fence is marked
   `<!-- spec:take-family-tutorial -->` (the composite tutorial fence that
   contains this program); editing the fence or its Results block without
   updating the corpus fails `TutorialSpecTests`.
4. **Generator**: the case is flagged `IncludeInGeneratorPrompt`, so both
   prompt files' generated block teaches
   `take(((1, 2), (3, 4)), 1)` → `[(1, 2)]` with the exact-list
   explanation, and goes stale (test failure) if the canonical case changes.

## 10. Known limitations

- Parse-level cases pin the structured `DiagnosticCode` family of the
  expected diagnostic (schema-required since the structured-code work) plus,
  sparingly, a message fragment for deliberately worded diagnostics; Lean
  still verifies nothing at parse level.
- Probes and display expectations are C#-only (Lean has no display layer).
- The generator harness (`experimental/prompts/katlang-generator-harness.ps1`)
  and its test-case JSON are untracked and outside this system; only the two
  tracked prompt files participate. Prompt examples outside the generated
  block remain hand-maintained.
- Every tutorial fence with a `**Result(s):**` claim is engine-verified by
  the sweep (section 6a) or carries an explicit reviewed `spec:skip` reason;
  only claim-less fences (syntax fragments, style demos, and the indented
  Pitfalls illustrations with inline `# error:` comments) remain outside
  mechanical output verification. Marker linkage (section 6) stays the
  stronger pin — it additionally ties an example to canonical raw structure,
  emitted count, and structured error identity.
