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

Closed here (verified): `ImplicitParameterRewrite_PreservesRewrittenNodeSpan` in
`ParameterDetectorTests` pins span survival for five rewritten node shapes.
Left open: evaluator-side diagnostic span attachment. A focused suite asserting error spans for
each `EvalError` construction site is the natural follow-up.

## 4. Other confirmed gaps

| # | Finding | Status |
|---|---|---|
| G9 | `TryCollectVisibleLexicalNames` candidate budget and duplicate-name skip (Stryker 978/991/1009). The pre-existing budget test uses a BARE name, where the candidate set is empty and both branches agree; they diverge only with a dot-member receiver, whose structural candidates are collected BEFORE the lexical sweep. | **FIXED**, 3 tests, all verified to kill |
| G5 | `Result.cs:444` bounded atoms cap, `>=` weakened to `>` on the SCALAR-root arm | **FIXED**, verified to kill |
| G1 | Rewritten-node spans (section 3) | **PARTLY FIXED**, verified for 5 node shapes |
| G2 | Grace weight accumulation across MULTIPLE occurrences (`ParameterDetector:689`, `+=` to `-=`). That branch runs only on a SECOND graced occurrence of a name, so no test grace-marks one name twice. | Open |
| G4 | Collecting-parameter forwarding with a second callee capture (`ImplicitArgumentResolver:450`): weakening the conjunction renames EVERY callee capture, not just the forwarded one. | Open |
| G12 | Two suffix parameters after a collecting parameter. The suffix arithmetic is degenerate with ONE suffix (its index term is always 0) and survives in BOTH `Evaluator.BindCallableArguments` (1504/1505) and the patterned binder (3315). A regression test for the shape was added but does NOT reach either site. | Open; shape test added |
| G13 | Eager-parameter resource-limit retention (`Evaluator:1739`, 4 mutants). AGENTS.md documents this rule as load-bearing for budget conservation. | Open |
| G14 | `ReCountValueBoundary` versus dot-receiver segment at the prepared-argument boundary (`Evaluator:2247`; both directions survive) | Open |
| G15 | Decimal128 numeric edges from the Aug 20 migration: exponent clamp at 6176, `quantumExponent >= 6111`, range-bound finiteness checks (7403/7407/7421), random-sampling internals | Open |
| G10 | `FindResolveSpan` null-coalescing chains (1117/1127) — a FALLBACK used only when the detector's `RecordFirstOccurrence` recorder did not run | Open |

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
   uncovered" figure.
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
| `MixedCollecting_WithTwoSuffixParameters_BindsEachSuffixByPosition` | CollectingBindingTests | regression only (see G12) |

No production code was changed. This campaign is test-and-analysis only.

## 9. Reproducing

`stryker-config.json` holds the union scope used here. Run:

```
dotnet tool restore
dotnet stryker --skip-version-check --output artifacts/stryker/<name>
```

The `Evaluator.cs` ranges in that config are CHARACTER OFFSETS (not line numbers) for
bind-parameters (lines 1192-2465), pattern-matching (2826-3693) and eval/call/dot-call
(7013-8988). **Recompute them whenever `Evaluator.cs` changes**, and verify afterwards that the
tested mutants' line numbers fall inside the intended regions. Budget about 61 minutes of
scope-independent setup per invocation, then roughly 8 mutants/minute.
