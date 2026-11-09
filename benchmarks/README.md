# KatLang C# Benchmarks

This folder holds KatLang C# performance scenarios for evaluator cache and optimizer comparisons. The benchmark set is intentionally small and deterministic so later evaluator changes can be compared without changing language semantics.

## Run

```powershell
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj
```

Useful filters:

```powershell
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj -- --filter *ParseAndEvaluate*
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj -- --filter *PreparedEvaluation*
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj -- --filter *GcdWhileLoop*
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj -- --filter *LoopStage2*
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj -- --filter *SequencePipelineStage2*
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj -- --filter *SequencePipelineDispatch*
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj -- --filter *PerSitePlanRetention*
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj -- --loop-stats
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj -- --sequence-stats
```

BenchmarkDotNet writes summaries under `BenchmarkDotNet.Artifacts/results/`.

## What Is Measured

- `ParseAndEvaluateBenchmarks` measures `KatLangEngine.EvaluateToAtoms(source)`, so parse, front-end elaboration, and evaluation are all included.
- `PreparedEvaluationBenchmarks` parses and elaborates each checked-in scenario once outside the timed benchmark and then measures `Evaluator.RunFlat(new Expr.AlgorithmExpr(root))`.
- The baseline method in each class is `RepeatedZeroArgPropertyReuse`, so BenchmarkDotNet's ratio columns compare the other scenarios against that same repeated zero-arg property reuse scenario for each benchmark mode.
- `LoopMode=Generic` disables the internal optimized loop path; `LoopMode=Optimized` enables it. This makes loop-heavy scenarios compare before/after behavior without changing KatLang source semantics.
- `SequencePipelineMode=Generic` disables sequence filter-count fusion; `SequencePipelineMode=Optimized` enables Stage S2 direct range iteration while keeping loop optimization enabled in the sequence pipeline benchmarks.
- `SequencePipelineDispatchBenchmarks` measures the sequence-pipeline PROBE cost on calls and dot-calls that are never candidates (M15): `Optimized` is the fusion-enabled recognition-miss path, `Generic` is the fusion-disabled bail path, and the generic loop strategy is pinned so every iteration crosses the expression dispatch that hosts the probe. Allocated bytes/op is the primary metric.
- `PerSitePlanRetentionBenchmarks` measures J7 per-site plan retention (2026-11-09) on prepared roots with both optimizations enabled: the S1 workload `Id(count(filter(range(1, 20000), IsEven)))` in a loop-only program (an added `Unused(s) = s.while`) against the same program without the loop (the loop-free control, which never retains plans), and the P1 loop `S(x) = Id(Id(Id(x + 1))), x < 1000` / `S(0).while` against a loop-free control making the same nested calls once per item of a 1000-item `map`. Before per-site retention the S1 loop program planned the supplied pipeline and ran it generically, and the P1 loop formed 2001 plans; now the first fuses like its control and the second forms one plan. Time and allocated bytes/op are the metrics; compare each workload with its control. Filter: `--filter *PerSitePlanRetention*`.
- `EvaluatorIdentityStateBenchmarks` measures the evaluator's declaration / activation / scope-owner bookkeeping (invalid-state audit §3.1, September 2026) on twelve prepared shapes — a parameterized call, three nested calls, an exported property cache hit, a local-only property read, `M.A`, a captured-ancestor read from a nested call, recursion to depth 40, a clause-family call, a recursive clause family (`Fib(15)`, the run-local family-preparation memo's hot path), a two-parameter call (`Add(a, b) = a + b`, the binder's flat unique-name path), a user call whose body is one builtin call (`Abs(x) = if(x < 0, -x, x)`, the builtin argument supply), and a callback shape (`range(1, 201).map(Inc)`, one callback invocation per item) — with per-run time, allocated bytes, and Gen0 pressure; divide by `UnitsPerRun` for per-operation numbers (201 normally, including the two-parameter, builtin-call and callback shapes; 804 calls for the nested shape, 41 calls for recursion, 1,973 family calls for the recursive family). Sources live in `EvaluatorIdentityStateScenarios` (the same class a paired Stopwatch harness can compile in). Filter: `--filter *EvaluatorIdentityState*`. `ParameterActivationCaptureBenchmarks` separately checks narrow-to-wide signature scaling (`--filter *ParameterActivationCapture*`); the wide path must deduplicate in linear time.

## Scenario Set

| Scenario | File | Intent | Origin |
| --- | --- | --- | --- |
| Repeated zero-arg property reuse | `benchmarks/KatLang.Benchmarks/Scenarios/repeated-zero-arg-property-reuse.kat` | Repeated access to the same zero-arg property to expose recomputation cost. | `EvaluatorTests.Eval_RepeatedEligiblePropertyWithinSingleRun` |
| Scalar helper sum calls | `benchmarks/KatLang.Benchmarks/Scenarios/scalar-helper-sum-calls.kat` | A parameterized helper closes over a shared zero-arg sequence sum and is called with distinct scalar arguments. | User-provided benchmark case |
| Nested property chains | `benchmarks/KatLang.Benchmarks/Scenarios/nested-property-chains.kat` | Repeated one-hop receiver property lookup across nested algorithm contexts; the scenario deliberately stays one hop, although dot chains of any depth are legal KatLang. | `EvaluatorTests.Eval_Distinguishes_HigherOrderAlgorithmContexts` |
| Sequence-heavy builtins | `benchmarks/KatLang.Benchmarks/Scenarios/sequence-heavy-builtins.kat` | `range -> filter -> map -> reduce` callback and traversal workload. | `tutorial.md` builtin examples |
| Property-rich shared subcomputations | `benchmarks/KatLang.Benchmarks/Scenarios/property-rich-shared-subcomputations.kat` | Several dependent properties repeatedly reuse the same intermediate totals. | Derived from existing property reuse tests and tutorial patterns |
| Realistic while calculation | `benchmarks/KatLang.Benchmarks/Scenarios/realistic-while-calculation.kat` | Larger calculation-style loop using `while`, `if`, dot-call, and selection. | `EvaluatorTests.Eval_While_DotCall_SumMultiplesOf3Or5` |
| GCD while loop | `benchmarks/KatLang.Benchmarks/Scenarios/gcd-while-loop.kat` | Compact Euclidean GCD `while` loop with two state values and a continuation flag. | `EvaluatorTests.Eval_While_GcdDotCall_ProjectsFinalState` |
| Repeat many iterations | `benchmarks/KatLang.Benchmarks/Scenarios/repeat-many-iterations.kat` | Minimal high-iteration `repeat` loop to isolate loop-frame overhead. | Stage 1 loop optimization benchmark case |
| Nested captured parent loop | `benchmarks/KatLang.Benchmarks/Scenarios/nested-captured-parent-loop.kat` | Nested step mutates one loop state value while reading parent parameters and a sibling property. | `EvaluatorTests.Eval_While_NestedStepUsesMutableStateAndCapturedParentValues` |
| Minimal repeat loop | `benchmarks/KatLang.Benchmarks/Scenarios/minimal-repeat-loop.kat` | Exact two-line `Step = k + 1` / `Step(2).repeat(1000000)[0]` Stage 2 loop microbenchmark. | Stage 2 loop optimization benchmark case |
| Minimal while loop | `benchmarks/KatLang.Benchmarks/Scenarios/minimal-while-loop.kat` | Exact two-line `Step = k + 1, k <= 1000000` / `Step(2).while[0]` Stage 2 loop microbenchmark. | Stage 2 loop optimization benchmark case |
| Arithmetic while loop | `benchmarks/KatLang.Benchmarks/Scenarios/arithmetic-while-loop.kat` | Exact two-line `Step = k + 1, k * k <= 1000000` / `Step(2).while[0]` Stage 2 loop microbenchmark. | Stage 2 loop optimization benchmark case |
| Captured parent loop | `benchmarks/KatLang.Benchmarks/Scenarios/captured-parent-loop.kat` | Exact parent-captured limit loop shape for Stage 2 planning. | Stage 2 loop optimization benchmark case |
| Nested repeated call loop | `benchmarks/KatLang.Benchmarks/Scenarios/nested-repeated-call-loop.kat` | Exact outer repeat plus inner while call shape for Stage 2 planning. | Stage 2 loop optimization benchmark case |
| Square-free count inline loop | `benchmarks/KatLang.Benchmarks/Scenarios/square-free-count-inline-loop.kat` | Square-free counting with the inner loop expression written inline. | Stage 3A loop optimization benchmark case |
| Square-free count local temp loop 1000 | `benchmarks/KatLang.Benchmarks/Scenarios/square-free-count-local-temp-loop-1000.kat` | Manual repeat square-free counting with a local `K2` property at N=1000. | Stage S2 sequence pipeline comparison benchmark case |
| Square-free count local temp loop | `benchmarks/KatLang.Benchmarks/Scenarios/square-free-count-local-temp-loop.kat` | Square-free counting with the inner loop using a local `K2` property. | Stage 3B loop optimization benchmark case |
| Sequence filter count over range | `benchmarks/KatLang.Benchmarks/Scenarios/sequence-filter-count-even-range.kat` | Stage S2 `range(...).filter(IsEven).count` benchmark at N=10000. | Stage S2 sequence pipeline optimization benchmark case |
| Sequence square-free filter count 1000 | `benchmarks/KatLang.Benchmarks/Scenarios/sequence-square-free-filter-count-1000.kat` | Square-free count through direct range filter-count at N=1000. | Stage S2 sequence pipeline optimization benchmark case |
| Sequence square-free filter count 10000 | `benchmarks/KatLang.Benchmarks/Scenarios/sequence-square-free-filter-count-10000.kat` | Square-free count through direct range filter-count at N=10000. | Stage S2 sequence pipeline optimization benchmark case |
| Dispatch non-candidate calls | `benchmarks/KatLang.Benchmarks/Scenarios/dispatch-non-candidate-calls.kat` | 100000 ordinary plain calls that are never pipeline candidates, isolating per-call sequence-pipeline probe cost. | M15 sequence pipeline dispatch benchmark case |
| Dispatch non-candidate dot-calls | `benchmarks/KatLang.Benchmarks/Scenarios/dispatch-non-candidate-dot-calls.kat` | 100000 ordinary dot-calls that are never pipeline candidates, isolating per-dot-call sequence-pipeline probe cost. | M15 sequence pipeline dispatch benchmark case |
| Per-site supplied pipeline in a loop program | `benchmarks/KatLang.Benchmarks/Scenarios/persite-supplied-pipeline-loop-program.kat` | S1 workload: a supplied `count(filter(range(...), IsEven))` beside an unused loop; the run is loop-only, so J7 per-site retention decides whether the supplied call is a plan. | S1 (2026-10-17), J7 per-site retention |
| Per-site supplied pipeline control | `benchmarks/KatLang.Benchmarks/Scenarios/persite-supplied-pipeline-control.kat` | Loop-free control of the S1 workload (a META-free program never retains plans). | S1 (2026-10-17), J7 per-site retention |
| Per-site nested Id loop 1000 | `benchmarks/KatLang.Benchmarks/Scenarios/persite-nested-id-loop-1000.kat` | P1 workload: two supplied nested `Id` calls per loop transition, 1000 transitions. | P1 (2026-10-20), J7 per-site retention |
| Per-site nested Id control 1000 | `benchmarks/KatLang.Benchmarks/Scenarios/persite-nested-id-control-1000.kat` | Loop-free control of the P1 workload: the same nested `Id` calls once per item of a 1000-item `map`. | P1 (2026-10-20), J7 per-site retention |

## Cache-Sensitive Notes

- The most cache-sensitive scenarios are `RepeatedZeroArgPropertyReuse`, `ScalarHelperSumCalls`, and `PropertyRichSharedSubcomputations` because they intentionally re-read the same zero-arg properties or call through helpers that close over them.
- `NestedPropertyChains` intentionally measures one-hop dot access. Multi-hop dot chains (`Lib.Sub.Q`, navigated structurally at every level) are legal KatLang; to measure them, add a new scenario instead of mutating this baseline.
- `SequenceHeavyBuiltins` is a useful control case: if it changes a lot without the property-heavy scenarios moving, the hotspot is more likely callback dispatch or sequence traversal than property reuse.
- `RealisticWhileCalculation` is the end-to-end sanity check. It mixes multiple evaluator features and is the best quick regression scan after any future performance work.
