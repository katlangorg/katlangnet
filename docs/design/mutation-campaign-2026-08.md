# Mutation-testing campaign — semantic core (2026-08-22)

Tool: Stryker.NET 4.16.0 (pinned in `dotnet-tools.json`). Config: `stryker-config.json`.
Reports (gitignored): `artifacts/stryker/{calibration,core,evalcore}/reports/`.

## 1. Why

The Aug 9 2026 `mutation-adequacy-map` was a HAND-ESTIMATED ~40-mutant sketch. This campaign
replaces it with a measured one: every surviving mutant triaged, and the genuine gaps closed
with tests that were each VERIFIED to fail on their mutant.

A 10,953-test suite with a 2.6:1 test-to-source line ratio looks authoritative, but coverage
cannot show whether assertions actually constrain behaviour. Track 12 already found 41
`EvaluatorTests` running on illegal source. Mutation testing is the systematic form of that check.

## 2. Result

| Run | Scope | Tested | Killed | Survived | Timeout | NoCov | Score |
|---|---|---|---|---|---|---|---|
| calibration | `ElaboratedScopeLookup.cs` | 68 | 63 | 5 | 0 | 2 | **90.0%** |
| core | `Result`, `ParameterDetector`, `ImplicitArgumentResolver`, `NameSuggestions`, `CallableBindingPlan` | 683 | 583 | 67 | 40 | 82 | **80.5%** |
| evalcore | `Evaluator.cs` (bind-parameters, pattern-matching, eval/call/dot-call), `PropertyExposureResolver`, `PropertyDependencyGraph` | 815 | 698 | 100 | 17 | 61 | **81.6%** |

Per file (tested mutants only):

| File | Tested | Score |
|---|---|---|
| PropertyExposureResolver.cs | 58 | 94.8% |
| NameSuggestions.cs | 123 | 88.6% |
| CallableBindingPlan.cs | 79 | 83.5% (about 100% for reachable code, see section 5) |
| Result.cs | 199 | 82.4% (about 98% discounting provable equivalents, see section 5) |
| Evaluator.cs | 695 | 82.2% |
| ImplicitArgumentResolver.cs | 155 | 79.4% |
| ParameterDetector.cs | 206 | 73.3% |
| PropertyDependencyGraph.cs | 123 | 72.4% |

**Headline: the semantic core is strongly constrained.** In the binding/arity spans of the
evaluator the first 352 consecutive mutants were killed without a single survivor. Where the
suite is weak, it is weak in ONE identifiable dimension — source spans.

## 3. THE dominant finding: source-span propagation is untested

Across both runs, span handling accounts for the single largest survivor cluster.

**Front-end rewriting drops spans undetected** (34 survived + about 15 no-coverage). Every
`Object initializer mutation` survivor deletes the span initializer from a node rebuilt by
`ParameterDetector.RewriteParams` / `RewriteBinderRefs` / `ProcessExpr`, or by
`ImplicitArgumentResolver.RewriteImplicitCalls` / `ProcessExprNested` — covering `Expr.Call`,
`Index`, `Unary`, `Binary`, `SequenceConstruct`, `SequenceSpread`, `ListLiteral`, `Capture`
and `AlgorithmExpr`.

**Evaluator diagnostic span attachment is unpinned** (about 15 of 35 survivors in the
eval/call/dot-call region): the span-fallback chains at 7113, 7252, 7257 and 2243/2279/2285;
the "attach a span if the error has none" conditionals at 7130 and 7280; and the error
constructions carrying spans at 7068, 7172, 7889, 7921.

These spans ARE consumed: `expr.Span` is read 61 times in `Evaluator.cs` (diagnostic attachment
via `AtSpanIfMissing`) and by `SemanticModelBuilder`. AGENTS.md requires exact source-span
invariants for hover, references, go-to-definition and classification — this is the layer that
carries them, and almost none of it is observed by a test.

The initial campaign closed one representative front-end slice with
`ImplicitParameterRewrite_PreservesRewrittenNodeSpan`. The 2026-08-27 follow-up expands this to
composite nodes in both rewriting passes and adds exact evaluator diagnostic-span contracts for
plain and counted evaluation. See section 9.

## 4. Other confirmed gaps

| # | Finding | Status |
|---|---|---|
| G9 | `TryCollectVisibleLexicalNames` candidate budget and duplicate-name skip (Stryker 978/991/1009). The pre-existing budget test uses a BARE name, where the candidate set is empty and both branches agree; they diverge only with a dot-member receiver, whose structural candidates are collected BEFORE the lexical sweep. | **FIXED**, 3 tests, all verified to kill |
| G5 | `Result.cs:444` bounded atoms cap, `>=` weakened to `>` on the SCALAR-root arm | **FIXED**, verified to kill |
| G1 | Rewritten-node spans (section 3) | **IMPLEMENTED**; expanded front-end and evaluator span suites; consolidated rerun pending |
| G2 | Grace weight accumulation across MULTIPLE occurrences (`ParameterDetector:689`, `+=` to `-=`). That branch runs only on a SECOND graced occurrence of a name, so no test grace-marks one name twice. | **FIXED**, verified against the arithmetic mutant |
| G4 | Collecting-parameter forwarding with a second callee capture (`ImplicitArgumentResolver:450`): weakening the conjunction renames EVERY callee capture, not just the forwarded one. | **RECLASSIFIED: equivalent** under the single-capture forwarding invariant; expression simplified |
| G12 | Two suffix parameters after a collecting parameter. The suffix arithmetic is degenerate with ONE suffix (its index term is always 0) and survives in BOTH `Evaluator.BindCallableArguments` (1504/1505) and the COUNTED patterned binder `BindCountedParameterPatternList` (3315). | **FIXED**; all four arithmetic mutants verified to fail — the flat pair by the new loop-step parity test, the counted patterned pair by the DEDICATED `CountedFamily_MapCallbackCollectingWithTwoSuffixes_BindsBothSuffixesByPosition` test (each mutant fails it independently; `MixedCollecting` remains additional cross-mode coverage — see section 9) |
| G13 | Eager-parameter resource-limit retention (`Evaluator:1739`, 4 mutants). AGENTS.md documents this rule as load-bearing for budget conservation. | **IMPLEMENTED**, shared sync/async policy helper and direct contract test; consolidated rerun pending |
| G14 | `ReCountValueBoundary` versus dot-receiver segment at the prepared-argument boundary (`Evaluator:2247`; both directions survive) | **IMPLEMENTED**, shared sync/async boundary helper plus source-level and direct tests; consolidated rerun pending |
| G15 | Decimal128 numeric edges from the Aug 20 migration: exponent clamp at 6176, `quantumExponent >= 6111`, range-bound finiteness checks (7403/7407/7421), random-sampling internals | **IMPLEMENTED**; boundary contracts added, representative mutants verified, equivalent quantum guard removed; consolidated rerun pending |
| G10 | `FindResolveSpan` null-coalescing chains (1117/1127) — a FALLBACK used only when the detector's `RecordFirstOccurrence` recorder did not run | **FIXED**, exact binary/call provenance spans verified against ordering mutants |

## 5. Findings that are NOT gaps

Reporting these accurately matters as much as the defects.

- **`CallableBindingPlan.cs` 13 no-coverage mutants are fail-loud invariant guards**
  (`throw new InvalidOperationException(...)`). Surface-unreachable by construction — exactly the
  class AGENTS.md says to pin from a prebuilt AST, if at all. Its real score for reachable code
  is about 100%.
- **Most `Result.cs` survivors are provably equivalent.** Of 16: the copy loop bound weakened to
  `<=` copies one extra slot that the next statement immediately overwrites (and is in bounds);
  removing `continue` after popping a suspended frame is a no-op because frames are suspended
  only when items remain; dropping the `ReferenceEquals` fast path costs work, not correctness;
  hash-component removals change hash VALUES, not equality, and forcing the leaf-hash probe to
  `false` is consistent for all values so the equals/hashCode contract still holds. Only line 444
  is a real gap.
- **`Result.cs:1194` `ReferencePair.Equals`** needs a hash collision to be observed, because
  `GetHashCode` combines BOTH references. Equivalent in practice; the conjunction remains
  load-bearing under collision. Hardening note, not a test gap.

## 6. The timeouts are genuine detection, not score inflation

A timeout scores as killed, so it can silently inflate a score. Inspected: nearly all mutate
loop guards where non-termination is the EXPECTED consequence — the `Result.cs` explicit-stack
traversals (weakening the continuation guard pushes a frame with nothing left to visit, so
pop/re-descend loops forever), `ImplicitArgumentResolver` traversal flags, the `NameSuggestions`
edit-distance bound, and the `ParameterDetector` Grace weight loop. Two object-initializer
timeouts (ParameterDetector 274, 948) have no obvious mechanism and are recorded UNVERIFIED.

## 7. Operational findings (reusable — these cost real time to learn)

1. **About 61 min fixed overhead per invocation, INDEPENDENT of `mutate` scope.** Stryker
   instruments the WHOLE project into one assembly and runs coverage capture over it BEFORE
   applying the mutate filter. MANY SMALL SEGMENTS ARE A TRAP (5 segments equals 5 hours of pure
   overhead). Prefer one run at the broadest scope that fits the window.
2. **`mutate` spans are CHARACTER OFFSETS, not line numbers.** This silently cost run 1 its
   entire evaluator scope: the intended bind-parameters range selected lines 24-48 instead.
   Compute offsets from the file, and VERIFY afterwards from the tested mutants' line
   distribution (run 2: 695 mutants, 100 percent inside the three intended regions).
3. **`mutate` globs ARE honoured in solution mode.** "N mutants created" is the INSTRUMENTED
   count, not the tested count; the filter appears later as "Removed by mutate filter".
4. **About 22.6 percent of created mutants fail to compile** and are dropped by Safe Mode, which
   removes ALL mutants in the affected method.
5. **Measure throughput over a WHOLE run, never a window.** A 91-second sample read 11.4
   mutants/min; the full run was 6.0. Survivors dominate the tail, because a survivor runs its
   ENTIRE covering-test set while a killed mutant bails on the first failure.
6. **`coveredBy` in the JSON report is NOT a coverage oracle.** 34 of 63 demonstrably-killed
   mutants carry no `coveredBy` array. Only the `NoCoverage` STATUS is trustworthy. Deriving a
   project-wide untested-code map from `coveredBy` produced a plausible but WRONG "46 percent
   uncovered" figure. (Root cause found 2026-08-28 — see finding 11: the coverage-capture run had
   died partway; with the stack-probe filter in place, `coveredBy` is complete and the
   `NoCoverage` status is meaningful again.)
7. **You cannot build or run `dotnet test` while Stryker is running** — its testhost locks the
   test assembly in `bin`. Schedule verification BETWEEN runs.
8. **Oversubscription is a correctness risk, not just a speed one.** xunit defaults to parallel
   collections here, so 14 sessions times 16 threads can slow mutants enough to convert genuine
   survivors into false timeouts, which count as KILLED. `additional-timeout` was raised to 30s.
9. **Do NOT scope the TEST side to save time.** Excluding the slow matrix suites (CountedMatrix,
   ArityDifferential, StructuralFuzz, LifetimeDifferential) would speed runs materially, but they
   are the differential oracles designed to catch semantic drift. Scoping MUTANTS preserves
   validity; scoping TESTS does not.
10. **Always verify a killing test by applying its mutant.** Of 7 tests written against specific
    mutants, 4 passed on the mutant at first attempt. Two were fixed by routing to the real code
    path (a scalar-root cap arm; a callback binder); two were kept as ordinary regression tests
    with corrected comments once their intended sites proved to be on unreached paths.
11. **Stack-calibration probe tests can kill the sequential coverage-capture run.** Stryker
    instruments EVERY method with `MutantControl` guards, inflating stack frames severalfold, so
    tests probing calibrated stack budgets are invalid BY PREMISE on an instrumented assembly.
    The full suite still passes Stryker's PARALLEL initial run, but coverage capture is a
    separate SEQUENTIAL run with different thread conditions: there the probes start failing
    (the module-loader per-level backstop fired mid-capture) and one killed the testhost
    outright. Every test after the death point silently loses its per-test coverage; Stryker
    then treats those tests as covering NOTHING — the 2026-08-28 first attempt "completed" in 20
    minutes with 681 NoCoverage, a meaningless 31.17 % score, and manually-PROVEN-killed mutants
    reported as NoCoverage (preserved at `artifacts/stryker/closure-2026-08-28-invalid-capture`).
    This retroactively explains finding 6: the 2026-08-22 capture run also died, just late
    enough in the assembly-dependent xunit order to leave usable coverage. Fix: the
    `test-case-filter` key in `stryker-config.json` (honored by Stryker 4.16 though absent from
    `--help`) excludes the nine dedicated stack/depth-calibration suites (187 tests) from all
    Stryker test runs. A filtered NameSuggestions probe reproduced the 2026-08-22 measurement
    exactly (NoCoverage 5, score 88.62 % vs 88.6 %) with the capture run lasting the full suite
    duration (`artifacts/stryker/probe-capture` and `probe-filter` hold the diagnostic pair).
    Residual: mutants killable ONLY by the excluded calibration suites can now surface as
    NoCoverage or survivors — triage such survivors against that exclusion list before
    classifying them, and never weaken the filter to whole differential-oracle suites (finding 9
    still applies; the calibration suites are excluded for validity, not speed).

## 8. Tests added

| Test | File | Kills |
|---|---|---|
| `CandidateBudgetExceeded_SuppressesEvenAnAvailableStructuralSuggestion` | ImplicitParameterDiagnosticsTests | Stryker 991 (verified) |
| `CandidateBudgetExceededThroughOpen_SuppressesEvenAnAvailableStructuralSuggestion` | ImplicitParameterDiagnosticsTests | Stryker 1009 (verified) |
| `NameVisibleAtTwoScopeLevels_StillYieldsSuggestion` | ImplicitParameterDiagnosticsTests | Stryker 978 (verified) |
| `ImplicitParameterProvenance_TakesFirstOccurrenceAcrossBinaryOperands` | ImplicitParameterDiagnosticsTests | regression only (see G10) |
| `ImplicitParameterProvenance_TakesCalleeOccurrenceBeforeArgument` | ImplicitParameterDiagnosticsTests | regression only (see G10) |
| `ImplicitParameterRewrite_PreservesRewrittenNodeSpan` (Theory, 5 cases) | ParameterDetectorTests | span-drop cluster (verified) |
| `BoundedLanguageAtoms_CapBoundaryIsExact` | WideValueRobustnessTests | `Result.cs:444` (verified) |
| `MixedCollecting_WithTwoSuffixParameters_BindsEachSuffixByPosition` | CollectingBindingTests | BOTH counted patterned-binder suffix mutants (3315 site; verified 2026-08-27 — the initial "regression only" triage was wrong: its counted-mode callback rows are the suite's only reach of that site) |

At the time of the measured 2026-08-22 campaign, no production code was changed. The closure
follow-up in section 9 includes behavior-preserving internal refactoring to make the policies
independently testable and to remove equivalent mutation sites.

## 9. Gap-closure follow-up (2026-08-27/28)

The four closure lanes are implemented. This is an implementation and targeted-verification
result, not a replacement mutation score. The `Evaluator.cs` character offsets have been
recomputed (section 10) and the consolidated rerun was attempted on 2026-08-28; the measurement
is BLOCKED by a test-platform coverage-channel defect (see the attempts subsection below), so
the 2026-08-22 numbers in section 2 remain the last valid measurement.

| Lane | Gaps | Closure evidence |
|---|---|---|
| Spans | G1, G10 | Composite-span preservation now covers both front-end rewriting passes, including host ASTs and synthesized implicit calls. Evaluator tests exercise the exact plain/counted error-construction branches and pin expression-first fallback, callee context, and attach-only-if-missing behavior. Representative span-drop and ordering mutants were applied manually and failed the new tests. |
| Binding | G2, G4, G12 | Repeated Grace occurrences pin additive accumulation, and a mixed-sign pair pins cross-occurrence cancellation. All four G12 suffix mutants fail, with attribution re-verified by injection during the 2026-08-27 review: the flat `BindCallableArguments` pair dies to the new flat loop-step parity test; the counted patterned pair (3315, `BindCountedParameterPatternList`) dies ONLY to the 2026-08-22 `MixedCollecting` two-suffix test, whose counted-mode callback rows are the suite's sole reach of that site — NOT to the new patterned loop-step test, which instead pins the plain `BindParameterPatternList` used by patterned loop steps (a fifth injected mutant there fails all four two-suffix tests). G4 was proved unreachable as stated because forwarding accepts exactly one callee capture, and the redundant discriminator was removed. |
| Budgets | G13, G14 | Resource-limit retention and prepared-argument boundary counting are named shared policies, used by both sync and async evaluation. Direct policy tests distinguish resource from ordinary errors and dot receivers from ordinary argument segments; source-level tests exercise patterned dot receivers. |
| Decimal128 | G15 | Tests pin round-digit clamping before narrowing, finite bounds independently, overflowed differences, exact `-10^34` integer bounds, half-open range scaling, unit-fraction component limits, upper-endpoint wrapping, and production `UInt128` draws. The `quantumExponent >= 6111` survivor was confirmed equivalent — `ScaleB` clamps the target quantum at the 6111 ceiling, so `Quantize` returns the same value at the same quantum and the `HaveSameQuantum` exit fires (verified for the trailing-zero coefficient case, where coarsening is value-exact and only the ceiling stops it, and for the reachable `Pow(10, 6112)` climb) — and the redundant guard was removed; the clamp premise is pinned by a trailing-zero boundary test. |

Targeted mutant injection was used while writing the tests, including G2, G10 ordering, all four
G12 suffix mutations, and the G15 finiteness/range/boundary/component mutations. The complete
repository gate then passed: solution build, **11,203 C# tests with 0 failures**, diff check, all
Lean targets, and the Lean/C# differential corpus via `pwsh .\scripts\validate-all.ps1`.

A same-day review pass re-verified the kills by fresh injection (G2; all four G12 mutants — with
a full-suite run under the counted pattern-index mutant proving `MixedCollecting` was then its
only killer — plus a fifth mutant in the plain patterned binder) and corrected one evidence
attribution: the counted patterned binder (3315) is reached by counted-mode callback rows, not by
the new patterned loop-step parity test (see the Binding lane row above). The review also aligned the async `Resolve` twin
with the sync `AtSpanIfMissing` refactor, moved the displaced `Lean: eval` doc comment off the
new test seams back onto `Eval`, restored the mixed-sign Grace cancellation pin that the rewritten
accumulation test had replaced, and added the coarsest-quantum trailing-zero termination test
pinning the `ScaleB` clamp premise behind the G15 equivalence verdict.

On 2026-08-28 a DEDICATED counted-family pin was added —
`CountedFamily_MapCallbackCollectingWithTwoSuffixes_BindsBothSuffixesByPosition` invokes
`Evaluator.RunCounted` directly on a flat map callee with a collecting parameter and two suffix
parameters, so the counted route (`BindCountedCallbackParameterPatternList` →
`BindCountedParameterPatternList`) no longer depends on `EvaluateAllModes` retaining its counted
mode. Both counted suffix-arithmetic mutants were re-injected one at a time and each failed this
one test independently. It is now the PRIMARY evidence for the counted patterned pair;
`MixedCollecting` remains additional cross-mode coverage.

Semantic-alignment verdict: the production edits factor existing host policies and remove
equivalent branches; they do not change observable KatLang semantics. Sync and async evaluator
paths use the same helpers, so no Lean specification change is required.

### Consolidated remeasurement attempts (2026-08-28) — BLOCKED by the coverage channel

The consolidated rerun was attempted with the recomputed offsets. The SCOPE is verified correct,
independent of coverage quality: 12,779 mutants instrumented; the mutate filter passes exactly
the union scope (in-scope non-compile-error population 1,940, matching the 2026-08-22 union of
1,638 once the "block already covered" bucket — 320 mutants that the old per-run reports carried
as plain Ignored — is added back); every `Evaluator.cs` in-scope mutant falls inside the three
recomputed regions (650 total: 241 bind-parameters, 145 pattern-matching, 264 eval/call/dot-call,
ZERO outside). The removed-equivalent claims are confirmed structurally from the report: the G4
conjunction and the `quantumExponent >= 6111` guard no longer produce mutants at all.

The MEASUREMENT itself is not trustworthy, and no score from these runs supersedes section 2.
Evidence chain:

- Attempt 1 (`artifacts/stryker/closure-2026-08-28-invalid-capture`): the coverage-capture host
  was killed by a stack-calibration probe (finding 11); only 116 of 10,913 tests ever reported
  coverage; 939 tested / 681 NoCoverage / "31.17 %" in 20 minutes; mutants PROVEN killed by
  manual injection (G2 at 689; all four G12 sites) were reported as NoCoverage.
- The `test-case-filter` fix (finding 11) removes that crash mode and is KEPT: a filtered
  NameSuggestions probe (`probe-filter`) reproduced the 2026-08-22 per-file numbers exactly
  (NoCoverage 5; 88.62 % vs 88.6 %).
- Attempt 2 (`artifacts/stryker/closure-2026-08-28`): capture completed without a crash, but
  per-test attribution collapsed in the VSTest result channel (`TestRunCache: No test found
  corresponding to testResult`, `InProgressTests is null` in the testhost logs): only 1,295 of
  10,726 tests appear in any `coveredBy` set; 1,323 mutants "tested" in 11 minutes; "55.31 %";
  proven-killed mutants reported Survived (1509, 1510) and NoCoverage (689, 3328). Attribution
  completeness varies run to run with identical configuration (116 → 2,695 → 1,295 tests).
- Runner experiments: `--test-runner mtp` discovers 0 tests (xunit v2 exposes no
  Microsoft.Testing.Platform entry point), and pinning `xunit.runner.visualstudio` 2.8.2
  (`probe-v2runner`) let the capture run full-length yet still attributed only 5,324 of 10,726
  tests while producing 30 timeouts among 102 tested mutants — a different distortion, so the
  pin was reverted.
- The environment (SDK 11.0.100-preview.7 installed 2026-08-19, identical pinned packages,
  pinned Stryker 4.16.0, same config) matches the 2026-08-22 campaign on paper. Finding 6 —
  missing `coveredBy` for 54 % of sampled killed mutants back then — now reads as an earlier,
  milder form of the same channel loss that happened to leave enough attribution to measure.

Consequence: the per-gap closure evidence remains the MANUAL one-at-a-time mutant injections
documented above — complete for G1/G2/G10/G12/G13/G14/G15 and independent of the coverage
channel. Survivors reported by the distorted runs were NOT triaged into classifications:
classifying them would launder measurement noise into evidence. The consolidated remeasurement
stays PENDING until the coverage channel is trustworthy; candidate paths are a test-platform /
SDK servicing update, a Stryker release with a more robust coverage transport, or migrating the
suite to xunit v3 + Microsoft.Testing.Platform (an infrastructure decision beyond this
campaign). Rerun readiness is otherwise complete — recomputed offsets
(`scripts/compute-stryker-offsets.ps1 -Update`), the capture-protecting `test-case-filter`, and
the union scope — and the acceptance bar for a future run is: the report must show coverage
attributed for roughly 10,000+ of the suite's tests (distinct `coveredBy` ids) before its
statuses may be read as measurement.

## 10. Reproducing

`stryker-config.json` holds the union scope used here. Run:

```
dotnet tool restore
dotnet stryker --skip-version-check --output artifacts/stryker/<name>
```

The `Evaluator.cs` ranges in that config are CHARACTER OFFSETS (not line numbers; UTF-16 code
units with CRLF counted as 2). They are DERIVED from the file's stable region banners by
`scripts/compute-stryker-offsets.ps1` — run it with `-Update` to rewrite the config **whenever
`Evaluator.cs` changes**; it also asserts that the known campaign sites (G12-G15) are inside the
ranges and that the config stays valid JSON. Each range runs from the start of its opening banner
line to the start of its closing banner line: bind-parameters = `// ── Bind parameters` ..
`// ── Result helpers`; pattern-matching = `// ── Pattern matching` ..
`// ── Collection materialization budget`; eval/call/dot-call = `// ── Main eval` ..
`// ── Entry points`. As of 2026-08-28 the derived ranges are `{53560..113305}` (lines
1197..2479), `{130744..168018}` (lines 2839..3707) and `{319630..412667}` (lines 7028..9015).
Calibration: the banner rule reproduces the 2026-08-22 offsets EXACTLY for the first two regions;
the old third region deviated slightly from its own banners (it started ~5 lines before
`// ── Main eval`, inside the spine-machine epilogue, and ended ~6 lines short, cutting the last
dot-call helper's argument list), so the banner-exact region shifts a handful of edge mutants.
Verify after each run that the tested mutants' line numbers fall inside the intended regions.
The config's `test-case-filter` MUST stay in place: it excludes the stack/depth-calibration
suites whose premise is invalid on an instrumented assembly and which otherwise kill the
sequential coverage-capture run (finding 11). Budget roughly 30 minutes of scope-independent
setup per invocation (build, instrumented initial run, full-suite coverage capture), then about
4-6 mutants/minute.
