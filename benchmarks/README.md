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

The run is unambiguous from the main checkout even when git-ignored copies of `KatLang.Benchmarks.csproj` exist (under `artifacts/`, `.claude/worktrees/`, or a scratch export). BenchmarkDotNet 0.14.0 would otherwise search the whole repository for a project of that name and report every benchmark as `NA` ("Found more than one matching project file"). The build records its own project path in the assembly, and `PinnedProjectToolchain` makes every job — `[SimpleJob]` attributes and command-line jobs such as `--job dry` alike — build exactly that project; the summary's job names show `Toolchain=CsProj (pinned project)`. Do not delete other people's scratch copies or worktrees to work around a benchmark run. The pinned toolchain targets `net11.0` only, so `--runtimes` is not supported.

Compare timings only against a same-build control — a control workload or mode measured in the same build and run (for example each `PerSitePlanRetention` workload against its loop-free control); across a code change compare those same-build ratios, never raw timings: timings can move 7–15% between builds with byte-identical allocation (JIT/layout effects).

BenchmarkDotNet writes summaries under `BenchmarkDotNet.Artifacts/results/`.

## Exit Code

BenchmarkDotNet never fails the process itself: a benchmark whose build fails or that throws becomes an `NA` row, and a rejected configuration returns no summary at all. The host sets the exit code instead, and prints one line `KatLang.Benchmarks: <reason> Exit code <n>.` whenever it has something to report (on the error stream when the code is nonzero).

| Exit code | Meaning |
| --- | --- |
| `0` | At least one benchmark case produced a successful report, or nothing was asked to run: `--help`, `--version`, `--info`, `--list`, and the diagnostic runners (`--cache-stats`, `--loop-stats`, `--sequence-stats`, `--async-stack-capacity`). |
| `1` | Benchmarks were selected but none produced a successful report (every row is `NA`, for example after a build failure or when every benchmark throws), or BenchmarkDotNet reported a critical validation error. |
| `2` | A run was requested and nothing ran: the filter matched nothing, nothing was selected at the interactive prompt (for example no `--filter` and no console input), or BenchmarkDotNet rejected the arguments. |

A successful report is a case whose build and every launch succeeded and that holds a result measurement. Exit code 0 means "at least one result", not "every result": when only some cases fail, the host still exits 0 and prints `warning: N of M benchmark case(s) produced no successful report (NA).`, so read the summary before citing a number. Never treat an `NA` row as data. Read the exit code of the benchmark process itself (`$LASTEXITCODE` after `dotnet run` in PowerShell, `$?` or `PIPESTATUS` in bash), not that of a pipeline it feeds. The decision is the pure function `BenchmarkHostExit.Decide`, pinned by `BenchmarkHostExitTests` in `tests/KatLang.Tests`.

Informational requests in BenchmarkDotNet response files (`@path/to/options.rsp`) follow the same exit-code rules as direct arguments, including `--help` and `--version`. A missing response file or rejected arguments still exit 2.

Any other exit code is a crash, not a result: an exception that escapes BenchmarkDotNet ends the process with the runtime's unhandled-exception code (`0xE0434352` on Windows, which Git Bash reports as 127). One case is known in BenchmarkDotNet 0.14.0: adding `--job dry` to a run of `PerSitePlanRetentionBenchmarks` throws `ArgumentException: values can't be empty` from the rank column while the summary table is built, after the benchmarks themselves ran. The other six classes with `[RankColumn]` were not tried and are expected to fail the same way. Run such a class with its own job (omit `--job`).

## What Is Measured

- `ParseAndEvaluateBenchmarks` measures `KatLangEngine.EvaluateToAtoms(source)`, so parse, front-end elaboration, and evaluation are all included.
- `PreparedEvaluationBenchmarks` parses and elaborates each checked-in scenario once outside the timed benchmark and then measures `Evaluator.RunFlat(new Expr.AlgorithmExpr(root))`.
- The baseline method in each class is `RepeatedZeroArgPropertyReuse`, so BenchmarkDotNet's ratio columns compare the other scenarios against that same repeated zero-arg property reuse scenario for each benchmark mode.
- `LoopMode=Generic` disables the internal optimized loop path; `LoopMode=Optimized` enables it. This makes loop-heavy scenarios compare before/after behavior without changing KatLang source semantics.
- `SequencePipelineMode=Generic` disables sequence filter-count fusion; `SequencePipelineMode=Optimized` enables Stage S2 direct range iteration while keeping loop optimization enabled in the sequence pipeline benchmarks.
- `SequencePipelineDispatchBenchmarks` measures the sequence-pipeline PROBE cost on calls and dot-calls that are never candidates (M15): `Optimized` is the fusion-enabled recognition-miss path, `Generic` is the fusion-disabled bail path, and the generic loop strategy is pinned so every iteration crosses the expression dispatch that hosts the probe. Allocated bytes/op is the primary metric.
- `PerSitePlanRetentionBenchmarks` measures J7 per-site plan retention (2026-11-09) on prepared roots with both optimizations enabled: the S1 workload `Id(count(filter(range(1, 20000), IsEven)))` in a loop-only program (an added `Unused(s) = s.while`) against the same program without the loop (the loop-free control, which never retains plans), and the P1 loop `S(x) = Id(Id(Id(x + 1))), x < 1000` / `S(0).while` against a loop-free control making the same nested calls once per item of a 1000-item `map`. Before per-site retention the S1 loop program planned the supplied pipeline and ran it generically, and the P1 loop formed 2001 plans; now the first fuses like its control and the second forms one plan. Time and allocated bytes/op are the metrics; compare each workload with its control. Filter: `--filter *PerSitePlanRetention*`.
- The same class measures builtin-aware transport (0eed993a, 2026-11-10) with two more pairs. `IfCalleeLoop1000` calls `F(x) = if(x > 0, x, 0)` with the supplied `G(n)` once per transition of a 1000-transition loop, and `CountCalleeLoop1000` calls `F(xs) = count(xs)` with the supplied `range(1, 3)`. The callee hands its parameter only to a value-only builtin, so the supplied call is not a plan and the run forms one plan, the loop step. Each stands beside a planned baseline, `IfCalleePlannedBaseline1000` / `CountCalleePlannedBaseline1000`: the same program plus an unread local property `Keep = Pass(x)` in `F`. That property transports the parameter to a user callable, so the supplied call stays a plan (1001 plans per run), and because it is never read, the evaluation steps and checkpoints are identical. Compare each workload with its planned baseline, not with a loop-free control: the difference is the cost of the retained plans. A baseline that reaches the builtin through an alias (`Choose = if`) also keeps the plan but allocates about 400 B more per call for reasons unrelated to plan retention, so it is not used. Measured once at dbd2e8fd (2026-11-11, the class's own short job): 4.90 MB against 5.12 MB per run for `if` (230,592 B, 232 B per retained plan) and 4.80 MB against 4.91 MB for `count` (119,880 B, 120 B per retained plan). The mean times of each pair differed by 2–3% in the baseline's favour, inside the build-to-build noise described above, so that run shows the gain in allocation only.
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
| Per-site if callee loop 1000 | `benchmarks/KatLang.Benchmarks/Scenarios/persite-if-callee-loop-1000.kat` | Builtin-aware transport workload: `F(x) = if(x > 0, x, 0)` receives the supplied `G(n)` once per loop transition and hands it only to the value-only builtin `if`, so the supplied call is not a plan. | Builtin-aware per-site transport (0eed993a, 2026-11-10) |
| Per-site if callee planned baseline 1000 | `benchmarks/KatLang.Benchmarks/Scenarios/persite-if-callee-planned-baseline-1000.kat` | Non-eligible twin of the `if` callee loop: an unread local property `Keep = Pass(x)` transports the parameter to a user callable, so the supplied call stays a plan while the executed work is the same. | Builtin-aware per-site transport (0eed993a, 2026-11-10) |
| Per-site count callee loop 1000 | `benchmarks/KatLang.Benchmarks/Scenarios/persite-count-callee-loop-1000.kat` | Builtin-aware transport workload: `F(xs) = count(xs)` receives the supplied `range(1, 3)` once per loop transition and hands it only to the value-only builtin `count`, so the supplied call is not a plan. | Builtin-aware per-site transport (0eed993a, 2026-11-10) |
| Per-site count callee planned baseline 1000 | `benchmarks/KatLang.Benchmarks/Scenarios/persite-count-callee-planned-baseline-1000.kat` | Non-eligible twin of the `count` callee loop: an unread local property `Keep = Pass(xs)` transports the parameter to a user callable, so the supplied call stays a plan while the executed work is the same. | Builtin-aware per-site transport (0eed993a, 2026-11-10) |

## Cache-Sensitive Notes

- The most cache-sensitive scenarios are `RepeatedZeroArgPropertyReuse`, `ScalarHelperSumCalls`, and `PropertyRichSharedSubcomputations` because they intentionally re-read the same zero-arg properties or call through helpers that close over them.
- `NestedPropertyChains` intentionally measures one-hop dot access. Multi-hop dot chains (`Lib.Sub.Q`, navigated structurally at every level) are legal KatLang; to measure them, add a new scenario instead of mutating this baseline.
- `SequenceHeavyBuiltins` is a useful control case: if it changes a lot without the property-heavy scenarios moving, the hotspot is more likely callback dispatch or sequence traversal than property reuse.
- `RealisticWhileCalculation` is the end-to-end sanity check. It mixes multiple evaluator features and is the best quick regression scan after any future performance work.
