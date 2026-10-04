using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

public class Q09IndependentHostileReviewTests
{
    private sealed record Seen(string Outcome, long Steps, long Raw, int Depth, long Items, long Strings,
        string Effects, long Planned, long Fused)
    {
        public string Semantic => $"{Outcome}\n{Steps}/{Raw}/{Depth}/{Items}/{Strings}\n{Effects}";
    }

    private sealed class WatchingCache : IZeroArgPropertyResultCache
    {
        private readonly RunScopedZeroArgPropertyResultCache _inner = new();
        public EvaluationBudget? Budget { get; private set; }
        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Budget = (EvaluationBudget)execution.RunIdentity;
            return _inner.GetOrEvaluate(execution, evaluate);
        }
    }

    private static async Task<Seen> Run(string source, int route, EvaluationLimits? limits = null,
        int cancelAt = 0, bool suspend = false)
    {
        using var cancellation = new CancellationTokenSource();
        var effects = new List<string>();
        Result Trace(Result value)
        {
            effects.Add(SemanticExplorerHarness.Neutral(value));
            if (cancelAt > 0 && effects.Count == cancelAt) cancellation.Cancel();
            return value;
        }
        var operations = HostOperations.Create(HostOperation.Create("trace", (args, _) => Trace(args[0]), "v"));
        if (suspend)
            operations = HostOperations.Create(HostOperation.CreateAsync("trace", async (args, _) =>
            {
                await Task.Yield();
                return Trace(args[0]);
            }, "v"));
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, $"Illegal fixture:\n{source}\n{string.Join("\n", parsed.Diagnostics)}");
        var program = new Expr.AlgorithmExpr(parsed.Root);
        var loops = new LoopOptimizationDiagnostics();
        var pipelines = new SequencePipelineDiagnostics();
        var syncCache = new WatchingCache();
        var asyncCache = new PassThroughAsyncZeroArgPropertyResultCache();
        EvaluationBudget budget;
        string outcome;
        try
        {
            var observed = route == 2 || suspend
                ? await Evaluator.RunCountedObservedAsync(program, limits,
                    zeroArgPropertyResultCache: asyncCache,
                    loopDiagnostics: loops, sequenceDiagnostics: pipelines, hostOperations: operations,
                    randomSeed: 739, cancellationToken: cancellation.Token)
                : Evaluator.RunCountedObserved(program, limits, enableOptimizations: route == 1,
                    zeroArgPropertyResultCache: syncCache,
                    loopDiagnostics: loops, sequenceDiagnostics: pipelines, hostOperations: operations,
                    randomSeed: 739, cancellationToken: cancellation.Token);
            var result = observed.Result;
            budget = observed.Budget;
            outcome = result.IsError ? DescribeErrorTree(result.Error)
                : $"{SemanticExplorerHarness.Neutral(result.Value.Value)}; count={result.Value.EmittedCount}";
        }
        catch (OperationCanceledException error)
        {
            Assert.Equal(cancellation.Token, error.CancellationToken);
            budget = (route == 2 || suspend ? asyncCache.ObservedBudget : syncCache.Budget)!;
            Assert.NotNull(budget);
            outcome = "cancelled";
        }
        Assert.Equal(0, budget.CurrentDepth);
        return new(outcome,
            budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
            budget.MaterializedItems, budget.MaterializedStringChars, string.Join("|", effects),
            loops.OptimizedLoopHits, pipelines.FilterCountFusionHits);
    }

    [Theory]
    [InlineData("Step(s) = if(true, s, 0)\nrepeat(Step, 1, { 1 / 0 })")]
    [InlineData("Step(s) = if(s, 1, 0)\nrepeat(Step, 1, { 1 / 0 })")]
    [InlineData("Step(s) = if(true, s, 0)\nF(v) = repeat(Step, 1, v)\nF({ 1 / 0 })")]
    [InlineData("Step(s) = if(true, s, 0)\nrepeat(Step, 1, { })")]
    public async Task TransportedIfStateDemand_KeepsTheGenericErrorTree(string source)
    {
        var generic = await Run(source, 0);
        var planned = await Run(source, 1);
        Assert.Equal(1, planned.Planned);
        Assert.Equal(generic.Semantic, planned.Semantic);
        Assert.Equal(generic.Semantic, (await Run(source, 2)).Semantic);
    }

    private static IEnumerable<string> GeneratedSources()
    {
        // A grammar-product corpus, independent of the implementation review's templates.
        // Each leaf is nested in several different immediate-consumer contexts.
        string[] leaves = ["s", "2", "-s", "if(true, s, 4)", "if(s > 3, 7, s)", "T", "T()", "F(s)"];
        for (var seed = 0; seed < 256; seed++)
        {
            var e = leaves[seed % leaves.Length];
            for (var level = 0; level < seed % 5 + 1; level++)
                e = ((seed >> level) % 5) switch
                {
                    0 => $"-({e})",
                    1 => $"(({e}) + s) mod 97",
                    2 => $"if(0 <= s < 200, ({e}), s)",
                    3 => $"if(({e}) != s, s + 1, ({e}))",
                    _ => $"(({e}) * 1) ^ 1",
                };
            var n = seed % 13 + 1;
            var initial = seed % 4 == 0 ? "{ trace(randomInt(0, 8)) }" : "2";
            yield return $"Step(s) = {{\nT = s + 2\nF(s) = s + 3\n{e}\n}}\nrepeat(Step, {n}, {initial})";
        }
        for (var n = 0; n < 20; n++)
        {
            yield return $"range(trace({n + 1}), trace(1)).filter({{ trace(randomInt(0, 8)) > 3 }}).count";
            yield return $"P(v) = {{ A = v + 0\ntrace(A) mod 3 == 0 }}\nAlias = P\nrange(0, {n}).map({{ x + 1 }}).filter(Alias).count";
            yield return $"F(v) = range(1, {n + 1}).filter({{ trace(v) > x }}).count\nF({{ trace(8) }})";
            yield return $"Step(s, t) = s + 1, if(s > {n}, 'abcdef', 'xy')\nrepeat(Step, {n + 2}, 0, {{ trace('z') }})";
        }
        string[] shapes =
        [
            "Step(s) = if(s == 2, (), s + 1)\nrepeat(Step, 7, 0)",
            "Step(s) = if(s == 2, (s, 8), s + 1)\nrepeat(Step, 7, 0)",
            "Step(s) = if(s == 2, (), s + 1), s < 7\nwhile(Step, 0)",
            "Step(s) = { T = s + 1\n T(), T < 8 }\nwhile(Step, 0)",
            "Step(s) = 1 / (s - 3)\nrepeat(Step, 5, 3)",
            "Step(s, t) = s + 1, 1 / (s - 3)\nrepeat(Step, 6, 0, 1)",
            "Ignore(a, b) = b\nStep(s) = Ignore({ 1 / 0 }, s + 1)\nrepeat(Step, 4, 0)",
            "Ignore(a, b) = b\nStep(s) = Ignore(trace(randomInt(0, 99)), s + 1)\nrepeat(Step, 4, 0)",
            "Step(s) = if(true, s, s)\nrepeat(Step, 2, { trace(7) })",
            "Step(s) = if(s, 2, 3)\nrepeat(Step, 1, { true })",
            "Step(s) = s:0\nrepeat(Step, 1, [trace(7)])",
            "Id(v) = v\nStep(s) = Id(s)\nrepeat(Step, 1, { trace(7) })",
            "Z = trace(randomInt(0, 99))\nA = Z\nStep(s) = s + A - Z\nrepeat(Step, 3, 0)",
            "Step(s) = range(1, 8).filter({ x < 5 }).count + s\nrepeat(Step, 2, 0)",
            "range(1, 8).filter({ repeat({ x + 1 }, 2, x) > 5 }).count",
            "range(1, 8).filter({ trace(x) > 3 }).filter({ trace(x) < 7 }).count",
            "range(1, 8).filter({ trace(x) > 3 }).map({ trace(x) + 1 })",
            "range(1, 8).filter({ 1 / (x - 4) > 0 }).count",
            "range(1, 8).filter({ trace('ab') == 'ab' }).count",
            "Step(s) = if(true, s, 1 / 0)\nrepeat(Step, 0, { trace(7) })",
        ];
        foreach (var source in shapes) yield return source;
    }

    [Fact]
    public async Task IndependentGrammarProduct_ExactBudgetsEffectsAndMixedLimits_OnThreeRoutes()
    {
        var programs = 0;
        var runs = 0;
        foreach (var source in GeneratedSources())
        {
            programs++;
            var unlimited = await Run(source, 0);
            var limits = new List<EvaluationLimits?> { null, new(), new() { MaxSteps = long.MaxValue },
                new() { MaxMaterializedItems = long.MaxValue },
                new() { MaxStringLength = EvaluationLimits.MaxSupportedStringLength },
                new() { MaxMaterializedStringChars = long.MaxValue } };
            foreach (var s in Enumerable.Range(-3, 6).Select(d => unlimited.Steps + d).Where(s => s > 0).Distinct())
            {
                limits.Add(new() { MaxSteps = s });
                limits.Add(new() { MaxSteps = s, MaxMaterializedItems = Math.Max(1, unlimited.Items - 1) });
                limits.Add(new() { MaxSteps = s, MaxMaterializedStringChars = Math.Max(0, unlimited.Strings - 1), MaxStringLength = 3 });
            }
            limits.Add(new() { MaxMaterializedItems = Math.Max(1, unlimited.Items - 1) });
            limits.Add(new() { MaxMaterializedItems = Math.Max(1, unlimited.Items), MaxCollectionItems = 3 });
            foreach (var configuration in limits)
            {
                var generic = await Run(source, 0, configuration);
                var planned = await Run(source, 1, configuration);
                var twin = await Run(source, 2, configuration);
                runs += 3;
                Assert.True(generic.Semantic == planned.Semantic,
                    $"{source}\n{configuration}\ngeneric: {generic.Semantic}\nplanned: {planned.Semantic}");
                Assert.True(generic.Semantic == twin.Semantic,
                    $"{source}\n{configuration}\ngeneric: {generic.Semantic}\ntwin: {twin.Semantic}");
                if (unlimited.Steps > 0 && configuration == new EvaluationLimits { MaxSteps = unlimited.Steps })
                    Assert.Equal(unlimited.Semantic, generic.Semantic);
                if (unlimited.Outcome.Contains("; count=", StringComparison.Ordinal)
                    && unlimited.Steps > 1
                    && configuration == new EvaluationLimits { MaxSteps = unlimited.Steps - 1 })
                    Assert.Contains("EvaluationStepLimitExceeded", generic.Outcome);
                if (configuration is null || configuration == new EvaluationLimits()
                    || configuration.MaxSteps == long.MaxValue || configuration.MaxMaterializedItems == long.MaxValue
                    || configuration.MaxMaterializedStringChars == long.MaxValue
                    || configuration.MaxStringLength == EvaluationLimits.MaxSupportedStringLength)
                    Assert.Equal(unlimited.Semantic, generic.Semantic);
            }
        }
        Console.WriteLine($"Independent corpus: programs={programs}; runs={runs}; mismatches=0");
    }

    [Fact]
    public async Task ExactRawTargets_AndEveryTransitionNearBulkBoundary_OnThreeRoutes()
    {
        string[] sources = [
            "Step(s) = -(-(s + 1))\nrepeat(Step, 7, { trace(2) })",
            "Step(s) = if(0 < s < 8 != false, s + 1, s)\nrepeat(Step, 7, { trace(2) })",
            "Step(s) = { T = s + 1\n T() + if(true, T, s) }\nrepeat(Step, 7, { trace(2) })",
            "range(trace(1), trace(5)).filter({ trace(x) mod 2 == 0 }).count",
            "Step(s) = if(true, s, 0)\nrepeat(Step, 1, { trace(7) })",
            // Q-26 changes planner coverage here; move checkpoint blocks through the inner
            // invocation and the subsequent row as well as through a spread handover.
            "Fib(a, b) = b, a + b\nStep(p, n) = repeat(Fib, 2, trace(n), n), n + 1\nrepeat(Step, 3, 0, 0)",
            "Fib(a, b) = b, a + b\nStep(a, b) = { repeat(Fib, 2, trace(a), b)* }\nrepeat(Step, 3, 0, 1)",
        ];
        var runs = 0;
        foreach (var body in sources)
        {
            var baseline = await Run(body, 0);
            foreach (var target in new long[] { 4095, 4096, 4097, 8191, 8192, 8193, 12287, 12288, 12289, 16403, 32768 })
            {
                var padded = string.Concat(Enumerable.Repeat("0\n", checked((int)(target - baseline.Raw)))) + body;
                var expected = await Run(padded, 0);
                Assert.Equal(target, expected.Raw);
                foreach (var s in Enumerable.Range(-3, 6).Select(d => expected.Steps + d).Append(long.MaxValue).Where(s => s > 0))
                {
                    var limits = new EvaluationLimits { MaxSteps = s };
                    var generic = await Run(padded, 0, limits);
                    Assert.Equal(generic.Semantic, (await Run(padded, 1, limits)).Semantic);
                    Assert.Equal(generic.Semantic, (await Run(padded, 2, limits)).Semantic);
                    runs += 3;
                }
            }
            // Slide the batch-end checkpoint over every logical point of the operation,
            // rather than only measuring the completed total on either side of a block.
            for (var prefix = 4096 - baseline.Raw - 2; prefix <= 4096; prefix++)
            {
                var padded = string.Concat(Enumerable.Repeat("0\n", checked((int)prefix))) + body;
                foreach (var s in new[] { 1L, 2L, 3L, 5L, 8L })
                {
                    var limits = new EvaluationLimits { MaxSteps = s };
                    var generic = await Run(padded, 0, limits);
                    Assert.Equal(generic.Semantic, (await Run(padded, 1, limits)).Semantic);
                    Assert.Equal(generic.Semantic, (await Run(padded, 2, limits)).Semantic);
                    runs += 3;
                }
            }
        }
        Console.WriteLine($"Exact raw targets and moving-boundary runs={runs}; mismatches=0");
    }

    [Theory]
    [InlineData("Step(s, t) = s + 1, trace(s)\nrepeat(Step, 8, 0, 0)")]
    [InlineData("range(trace(1), trace(7)).filter({ trace(x) > 3 }).count")]
    [InlineData("Step(s) = s + 1\nrepeat(Step, trace(7), { trace(0) })")]
    [InlineData("Step(s) = if(true, s, 0)\nrepeat(Step, 1, { trace(7) })")]
    [InlineData("Reject(x) = trace(false)\nrange(1, 1).filter(Reject).count")]
    // Q-26: a nested loop step row is one value, so this outer loop now stays planned through it.
    [InlineData("Fib(x, y) = y, x + y\nStepT(p, n) = repeat(Fib, 1, trace(n), n), n + 1\nrepeat(StepT, 6, 0, 0)")]
    [InlineData("Fib(a, b) = trace(b), trace(a + b)\nStep(a, b) = { repeat(Fib, 2, a, b)* }\nrepeat(Step, 3, 0, 1)")]
    [InlineData("Inner(n) = trace(n + 1), trace(n < 3)\nOuter(p, n) = while(Inner, n), trace(n + 1)\nrepeat(Outer, 3, 0, 0)")]
    [InlineData("Fib(a, b) = trace(b), trace(a + b)\nmap([1, 2], { repeat(Fib, 2, x, 1) })")]
    public async Task CancellationAtEveryEffect_KeepsCountersAndEffects_OnThreeRoutes(string body)
    {
        var source = "Probe = 0\nProbe\n" + body;
        var full = await Run(source, 0);
        Assert.NotEmpty(full.Effects);
        var effectCount = full.Effects.Split('|').Length;
        foreach (var cancelAt in Enumerable.Range(1, effectCount))
            foreach (var limits in new EvaluationLimits?[] { null, new() { MaxSteps = long.MaxValue },
                new() { MaxMaterializedItems = long.MaxValue, MaxMaterializedStringChars = long.MaxValue } })
            {
                var generic = await Run(source, 0, limits, cancelAt);
                Assert.Equal("cancelled", generic.Outcome);
                Assert.Equal(generic.Semantic, (await Run(source, 1, limits, cancelAt)).Semantic);
                Assert.Equal(generic.Semantic, (await Run(source, 2, limits, cancelAt)).Semantic);
                // A successful suspending run does not cover cancellation during suspension.
                Assert.Equal(generic.Semantic, (await Run(source, 2, limits, cancelAt, suspend: true)).Semantic);
            }
        Assert.Equal(full.Semantic, (await Run(source, 2, suspend: true)).Semantic);
    }

    [Fact]
    public async Task AsyncObservedEntry_KeepsStrategyUnderEquivalentConfigurations()
    {
        var parsed = Parser.Parse("A = 2\nStep(s) = s + 1\nrepeat(Step, 3, 0) + range(1, 5).filter({ x > 2 }).count + A");
        Assert.False(parsed.HasErrors);
        var program = new Expr.AlgorithmExpr(parsed.Root);
        string? expected = null;
        foreach (var limits in new EvaluationLimits?[] { null, new(), new() { MaxSteps = long.MaxValue },
            new() { MaxMaterializedItems = long.MaxValue }, new() { MaxStringLength = EvaluationLimits.MaxSupportedStringLength },
            new() { MaxMaterializedStringChars = long.MaxValue } })
        {
            var loops = new LoopOptimizationDiagnostics();
            var pipelines = new SequencePipelineDiagnostics();
            var (result, budget) = await Evaluator.RunCountedObservedAsync(program, limits,
                zeroArgPropertyResultCache: new WatchingCache(), loopDiagnostics: loops, sequenceDiagnostics: pipelines);
            Assert.False(result.IsError);
            Assert.Equal(1, loops.OptimizedLoopHits);
            Assert.Equal(1, pipelines.FilterCountFusionHits);
            var outcome = $"{SemanticExplorerHarness.Neutral(result.Value.Value)};{result.Value.EmittedCount};"
                + $"{budget.ConsumedSteps}/{budget.ConsumedExpressionCheckpoints}/{budget.PeakDepth}/{budget.MaterializedItems}/{budget.MaterializedStringChars}";
            expected ??= outcome;
            Assert.Equal(expected, outcome);
        }
    }

    [Fact]
    public void RejectedBulkCheckpoint_IsNonMutatingAndRetainsTheTerminalFailure()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 });
        for (var i = 0; i < 8191; i++) Assert.Null(budget.TryChargeExpressionNodeWork());
        Assert.Equal(8191, budget.ConsumedExpressionCheckpoints);
        Assert.Equal(1, budget.ConsumedSteps);
        var error = Assert.IsType<EvalError.EvaluationStepLimitExceeded>(budget.TryChargeExpressionNodeWork());
        Assert.Same(error, budget.TryChargeExpressionNodeWork());
        Assert.Same(error, budget.TryReserveCollection(0));
        Assert.Same(error, budget.TryReserveString(0));
        Assert.Equal(8191, budget.ConsumedExpressionCheckpoints);
        Assert.Equal(1, budget.ConsumedSteps);

        using var cancelled = new CancellationTokenSource();
        var other = EvaluationBudget.Create(null, cancellationToken: cancelled.Token);
        for (var i = 0; i < 4095; i++) Assert.Null(other.TryChargeExpressionNodeWork());
        cancelled.Cancel();
        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => other.TryChargeExpressionNodeWork());
        Assert.Equal(cancelled.Token, thrown.CancellationToken);
        Assert.Equal(4095, other.ConsumedExpressionCheckpoints);
        Assert.Equal(0, other.ConsumedSteps);
    }

    [Fact]
    public void PreparedHostCells_AndHostOnlyTempSignatures_KeepGenericAccounting()
    {
        for (var shape = 0; shape < 8; shape++)
            foreach (var maxSteps in new long[] { 1, 2, 3, 4, 5, 8, 20, long.MaxValue })
            {
                string Observe(bool optimize)
                {
                    var limits = new EvaluationLimits { MaxSteps = maxSteps };
                    var budget = EvaluationBudget.Create(limits);
                    var effects = new List<string>();
                    var loops = new LoopOptimizationDiagnostics();
                    var ctx = Evaluator.EvalCtx.Empty with
                    {
                        CallStack = [BuiltinRegistry.CreateRuntimePreludeAlgorithm()],
                        Budget = budget,
                        EnableLoopOptimization = optimize,
                        LoopDiagnostics = loops,
                    };
                    var supplied = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [new Expr.Num(7)]));
                    EvalResult<Evaluator.CountedResult> Demand()
                    {
                        effects.Add("demand");
                        return shape == 5 ? new EvalError.DivByZero() : Evaluator.EvalCounted(new Expr.Num(7), ctx, []);
                    }
                    var cell = shape == 6
                        ? NeedCell.Ready(new Evaluator.CountedResult(new Result.Atom(7), 1))
                        : new NeedCell(Demand, () => new(Demand()), () => EvalResult<Algorithm?>.Ok(null), source: supplied, budget: budget);
                    ctx = ctx.WithNeedEnv([("c", cell)]);
                    IReadOnlyList<ParameterPattern> patterns = shape switch
                    {
                        1 => [new CaptureParameterPattern("c", Kind: ParameterKind.Collecting)],
                        2 => [new CaptureParameterPattern("c"), new CaptureParameterPattern("c")],
                        3 => [new SequenceValueParameterPattern([new CaptureParameterPattern("c"), new CaptureParameterPattern("z")])],
                        _ => [new CaptureParameterPattern("c")],
                    };
                    Expr tempBody = shape == 4
                        ? new Expr.Comparison(new Expr.Param("c"), [])
                        : new Expr.Param("c");
                    var temp = new Algorithm.User(null, patterns, [], [], [tempBody]);
                    var arguments = shape == 2
                        ? new OutputBundle([new Expr.Param("c"), new Expr.Param("c")])
                        : new OutputBundle([new Expr.Param("c")]);
                    Expr output = new Expr.Call(new Expr.Resolve("T"), arguments);
                    if (shape == 7)
                        output = new Expr.Call(new Expr.Resolve("if"), new OutputBundle([new Expr.BoolLiteral(true), output, new Expr.Param("s")]));
                    var step = new Algorithm.User(null, [new CaptureParameterPattern("s")], [], [new Property("T", temp)], [output]);
                    var call = new Expr.Call(new Expr.Resolve("repeat"), new OutputBundle([new Expr.AlgorithmExpr(step), new Expr.Num(2), new Expr.Num(0)]));
                    var result = Evaluator.EvalCounted(call, ctx, []);
                    Assert.Equal(0, budget.CurrentDepth);
                    if (maxSteps == long.MaxValue)
                        Assert.Equal(optimize ? 1 : 0, loops.OptimizedLoopHits);
                    return (result.IsError ? DescribeErrorTree(result.Error) : SemanticExplorerHarness.Neutral(result.Value.Value))
                        + $"\n{budget.ConsumedSteps}/{budget.ConsumedExpressionCheckpoints}/{budget.PeakDepth}/{budget.MaterializedItems}/{budget.MaterializedStringChars}\n{string.Join(',', effects)}";
                }
                Assert.Equal(Observe(false), Observe(true));
            }
    }

    [Fact]
    public void ZeroKeptReservation_ObservesCancellationBeforeTheSingleOutputReturns()
    {
        foreach (var limits in new EvaluationLimits?[] { null, new() { MaxSteps = long.MaxValue },
            new() { MaxMaterializedItems = long.MaxValue } })
        {
            string Observe(bool optimize)
            {
                using var cancellation = new CancellationTokenSource();
                var calls = 0;
                var operations = HostOperations.Create(HostOperation.Create("reject", (_, _) =>
                {
                    calls++;
                    cancellation.Cancel();
                    return new Result.Bool(false);
                }, "x"));
                var parsed = Parser.Parse("range(1, 1).filter(reject).count", new RunOptions { HostOperations = operations });
                Assert.False(parsed.HasErrors);
                var budget = EvaluationBudget.Create(limits, cancellationToken: cancellation.Token, hostOperations: operations);
                var diagnostics = new SequencePipelineDiagnostics();
                var ctx = Evaluator.EvalCtx.Empty with
                {
                    Budget = budget,
                    CallStack = [operations.RuntimePreludeAlgorithm],
                    EnableSequencePipelineOptimization = optimize,
                    SequenceDiagnostics = diagnostics,
                };
                // Enter the internal expression evaluator directly: the top-level completion
                // cancellation check would mask a missing empty-list reservation.
                var error = Assert.ThrowsAny<OperationCanceledException>(() =>
                    Evaluator.EvalCounted(new Expr.AlgorithmExpr(parsed.Root), ctx, []));
                Assert.Equal(cancellation.Token, error.CancellationToken);
                Assert.Equal(1, calls);
                Assert.Equal(0, budget.CurrentDepth);
                Assert.Equal(optimize ? 1 : 0, diagnostics.FilterCountFusionHits);
                return $"{budget.ConsumedSteps}/{budget.ConsumedExpressionCheckpoints}/{budget.PeakDepth}/{budget.MaterializedItems}/{budget.MaterializedStringChars}";
            }
            Assert.Equal(Observe(false), Observe(true));
        }
    }

    [Theory]
    [InlineData("Step(s) = if(s == 2, (trace(s), trace(8)), trace(s + 1))\nrepeat(Step, 3, 0)")]
    [InlineData("Step(s) = if(s == 2, (), trace(s + 1))\nrepeat(Step, 3, 0)")]
    [InlineData("Step(s) = [(1, 2)]:0\nrepeat(Step, 3, 0)")]
    public async Task FinalIterationHandover_DoesNotStartAnotherGenericIteration(string source)
    {
        var baseline = await Run(source, 0);
        Assert.Equal(1, (await Run(source, 1)).Planned);
        foreach (var steps in Enumerable.Range(1, checked((int)baseline.Steps + 1)).Select(n => (long)n).Append(long.MaxValue))
        {
            var limits = new EvaluationLimits { MaxSteps = steps };
            var generic = await Run(source, 0, limits);
            Assert.Equal(generic.Semantic, (await Run(source, 1, limits)).Semantic);
            Assert.Equal(generic.Semantic, (await Run(source, 2, limits)).Semantic);
        }
    }

    [Fact]
    public void CurrentAccountingDescriptions_DoNotRetainTheOldSelectorsOrStackCalibration()
    {
        var root = RepoRoot.Find();
        var materialization = File.ReadAllText(Path.Combine(root, "tests/KatLang.Tests/CollectionMaterializationLimitsTests.cs"));
        Assert.DoesNotContain("ConfiguredCumulativeBudget_ForcesGenericPaths", materialization);
        Assert.DoesNotContain("now forces the generic sequence paths", materialization);
        Assert.DoesNotContain("A configured MaxMaterializedItems forces", materialization);
        Assert.DoesNotContain("a configured cumulative string budget forces", materialization);
        var cancellation = File.ReadAllText(Path.Combine(root, "tests/KatLang.Tests/EvaluationCancellationTests.cs"));
        Assert.DoesNotContain("this path never runs under a step budget", cancellation);
        var alignment = File.ReadAllText(Path.Combine(root, "src/KatLang/SEMANTIC-ALIGNMENT.md"));
        Assert.DoesNotContain("is what calibrates `MaxSupportedDepth` against the backstop", alignment);
        var asyncDesign = File.ReadAllText(Path.Combine(root, "docs/design/async-evaluation-2026-08.md"));
        Assert.DoesNotContain("the same generic mode configured step/string/", asyncDesign);
        var asyncStack = File.ReadAllText(Path.Combine(root, "tests/KatLang.Tests/AsyncEvaluation/AsyncStackDepthTests.cs"));
        Assert.DoesNotContain("SYNCHRONOUS evaluator's calibrated", asyncStack);
        Assert.DoesNotContain("recursion equal the synchronous verdicts exactly", asyncStack);
        var registry = File.ReadAllText(Path.Combine(root, "fuzz/KatLang.ParserFuzz/Metamorphic/MetamorphicFamilyRegistry.cs"));
        Assert.DoesNotContain("budget disables the sequence-pipeline optimizer", registry);
        var metamorphic = File.ReadAllText(Path.Combine(root, "tests/KatLang.Tests/MetamorphicPhase3FamilyTests.cs"));
        Assert.DoesNotContain("A configured cumulative item budget forces", metamorphic);
    }
}
