# KatLang C# Benchmarks

This folder holds the uncached KatLang C# performance baseline. The benchmark set is intentionally small and deterministic so later evaluator changes can be compared against it without changing language semantics.

## Run

```powershell
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj
```

Useful filters:

```powershell
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj -- --filter *ParseAndEvaluate*
dotnet run -c Release --project benchmarks/KatLang.Benchmarks/KatLang.Benchmarks.csproj -- --filter *PreparedEvaluation*
```

BenchmarkDotNet writes summaries under `BenchmarkDotNet.Artifacts/results/`.

## What Is Measured

- `ParseAndEvaluateBenchmarks` measures `KatLangEngine.EvaluateToAtoms(source)`, so parse, front-end elaboration, and evaluation are all included.
- `PreparedEvaluationBenchmarks` parses and elaborates each checked-in scenario once outside the timed benchmark and then measures `Evaluator.RunFlat(new Expr.Block(root))`.
- The baseline method in each class is `RepeatedZeroArgPropertyReuse`, so BenchmarkDotNet's ratio columns compare the other scenarios against that same uncached reuse case.

## Scenario Set

| Scenario | File | Intent | Origin |
| --- | --- | --- | --- |
| Repeated zero-arg property reuse | `benchmarks/KatLang.Benchmarks/Scenarios/repeated-zero-arg-property-reuse.kat` | Repeated access to the same zero-arg property to expose recomputation cost. | `EvaluatorTests.Eval_RepeatedEligiblePropertyWithinSingleRun` |
| Scalar helper sum calls | `benchmarks/KatLang.Benchmarks/Scenarios/scalar-helper-sum-calls.kat` | A parameterized helper closes over a shared zero-arg sequence sum and is called with distinct scalar arguments. | User-provided benchmark case |
| Nested property chains | `benchmarks/KatLang.Benchmarks/Scenarios/nested-property-chains.kat` | Repeated one-hop exported receiver lookup across nested algorithm contexts; KatLang does not currently expose arbitrary multi-hop user-defined dot chains. | `EvaluatorTests.Eval_Distinguishes_HigherOrderAlgorithmContexts` |
| Sequence-heavy builtins | `benchmarks/KatLang.Benchmarks/Scenarios/sequence-heavy-builtins.kat` | `range -> filter -> map -> reduce` callback and traversal workload. | `tutorial.md` builtin examples |
| Property-rich shared subcomputations | `benchmarks/KatLang.Benchmarks/Scenarios/property-rich-shared-subcomputations.kat` | Several dependent properties repeatedly reuse the same intermediate totals. | Derived from existing property reuse tests and tutorial patterns |
| Realistic while calculation | `benchmarks/KatLang.Benchmarks/Scenarios/realistic-while-calculation.kat` | Larger calculation-style loop using `while`, `if`, dot-call, and selection. | `EvaluatorTests.Eval_While_DotCall_SumMultiplesOf3Or5` |

## Notes For Later Caching Work

- The most cache-sensitive scenarios are `RepeatedZeroArgPropertyReuse`, `ScalarHelperSumCalls`, and `PropertyRichSharedSubcomputations` because they intentionally re-read the same zero-arg properties or call through helpers that close over them.
- `NestedPropertyChains` is intentionally limited to the legal one-hop exported dot-access surface. If multi-hop user-defined chains become part of KatLang semantics later, add a new scenario instead of mutating this baseline.
- `SequenceHeavyBuiltins` is a useful control case: if it changes a lot without the property-heavy scenarios moving, the hotspot is more likely callback dispatch or sequence traversal than property reuse.
- `RealisticWhileCalculation` is the end-to-end sanity check. It mixes multiple evaluator features and is the best quick regression scan after any future performance work.