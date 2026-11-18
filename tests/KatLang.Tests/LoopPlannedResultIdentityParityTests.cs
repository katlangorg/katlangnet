using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// CLR identity of the results a PLANNED loop hands on, as a host operation observes it (KL-01,
/// November 2026; C#-only host contract, no Lean counterpart).
///
/// <para>The host rule (<c>docs/design/language-rules/evaluator-and-hosting.md</c> § Zero-argument
/// property cache): rereading or forwarding an existing <see cref="Result"/> preserves its CLR object
/// identity, while equal values computed independently may share an object or use distinct objects.
/// A cached local entry is ONE result for all its consumers — every read of <c>T</c> and the fresh
/// <c>T()</c> that first establishes the entry — so a host that compares the two positions of
/// <c>T, T</c> or <c>T(), T</c> by reference sees one object on every route. The planned loop used to
/// keep a local temp's numeric value unboxed in its per-iteration memo and box it again at every
/// output read, which turned <c>if(SamePair(...), 9, 1 / 0)</c> into a division by zero on the
/// optimized route only.</para>
///
/// <para><c>SamePair(pair)</c> is an ordinary host operation, configured for parsing and for every
/// evaluation (asynchronous on the twin routes, which pins the generic loop strategy). Every fixture
/// parses cleanly, the optimized route must have run the loop wholly planned (one optimized loop,
/// no planned-expression fallback, nothing generic inside it), and the routes agree on outcome,
/// structured error, emitted count, host calls and every budget counter.</para>
/// </summary>
public class LoopPlannedResultIdentityParityTests
{
    // ── Fixtures ─────────────────────────────────────────────────────────────────────────────

    /// <summary>The one-iteration repeat whose only arithmetic is <c>T = a + 1</c>.</summary>
    private static string RepeatStep(string rows) => "Step(a, b) = {\n  T = a + 1\n  " + rows + "\n}\n";

    private static string RepeatObserver(string rows) => RepeatStep(rows) + "SamePair(repeat(Step(0, 0), 1))";

    private const string BranchWitness = "Step(a, b) = {\n  T = a + 1\n  T, T\n}\nif(SamePair(repeat(Step(0, 0), 1)), 9, 1 / 0)";

    /// <summary>
    /// A plan-eligible <c>while</c> returning its FINAL INCOMING state: round one's flag holds and
    /// its rows form the state <c>(T, T)</c>; round two's flag fails first, so that state is the result.
    /// </summary>
    private const string WhileObserver = "Step(a, b) = {\n  T = a + 1\n  T, T, a < 1\n}\nSamePair(while(Step(0, 0)))";

    /// <summary>
    /// Rows of the one-iteration repeat: the planned additions each executes and whether both
    /// positions must be ONE object (<c>null</c>: independent evaluations, either verdict is valid).
    /// </summary>
    public static TheoryData<string, int, bool?> RepeatRows => new()
    {
        // Two reads of one established local entry.
        { "T, T", 1, true },
        // The fresh call that first owns the empty entry establishes it; the read reuses that result.
        { "T(), T", 1, true },
        // One bound argument forwarded twice.
        { "a, a", 0, true },
        // The second call is a fresh invocation of an established entry: an independent evaluation.
        { "T(), T()", 2, null },
        // The read establishes the entry; the later call is fresh.
        { "T, T()", 2, null },
    };

    /// <summary>Distinct executions of one literal site: either verdict is valid, Boolean literals included.</summary>
    public static TheoryData<string> IndependentLiteralSources => new()
    {
        "Step(a, b) = b, 7\nSamePair(repeat(Step(0, 0), 2))",
        "Step(a, b) = b, true\nSamePair(repeat(Step(0, 0), 2))",
    };

    /// <summary>Fixtures that must fail with one structured error on every route.</summary>
    public static TheoryData<string, KatLangErrorCode, int> FailingSources => new()
    {
        // The branch witness inverted: the shared result selects the failing branch everywhere.
        { "Step(a, b) = {\n  T = a + 1\n  T, T\n}\nif(SamePair(repeat(Step(0, 0), 1)), 1 / 0, 9)", KatLangErrorCode.DivisionByZero, 1 },
        { "Step(a, b) = {\n  T = a + 1\n  T(), T\n}\nif(SamePair(repeat(Step(0, 0), 1)), 1 / 0, 9)", KatLangErrorCode.DivisionByZero, 1 },
        // The temp itself fails inside the planned loop: the host is never reached.
        { "Step(a, b) = {\n  T = a / b\n  T, T\n}\nSamePair(repeat(Step(1, 0), 1))", KatLangErrorCode.DivisionByZero, 0 },
        { "Step(a, b) = {\n  T = a / b\n  T(), T\n}\nSamePair(repeat(Step(1, 0), 1))", KatLangErrorCode.DivisionByZero, 0 },
    };

    /// <summary>
    /// Other paths that hand one result on: exported temps, served from the run cache, and a planned
    /// iteration that hands over to the generic loop (its third row emits no value), with the
    /// optimized-loop fallbacks each records.
    /// </summary>
    public static TheoryData<string, int> HandOnSources => new()
    {
        { "Step(a, b) = {\n  E = 6 * 7\n  E, E\n}\nSamePair(repeat(Step(0, 0), 1))", 0 },
        { "Step(a, b) = {\n  E = 6 * 7\n  E(), E\n}\nSamePair(repeat(Step(0, 0), 1))", 0 },
        { "Step(a, b, c) = {\n  T = a + 1\n  T, T, c\n}\nSamePair(repeat(Step(0, 0, ()), 1))", 1 },
        { "Step(a, b, c) = {\n  T = a + 1\n  T(), T, c\n}\nSamePair(repeat(Step(0, 0, ()), 1))", 1 },
        { "Step(a, b, c) = {\n  T = a + 1\n  T, T, c, a < 1\n}\nSamePair(while(Step(0, 0, ())))", 1 },
    };

    /// <summary>Only independently computed values may have different identity verdicts across strategies.</summary>
    public static TheoryData<string, bool> SweepSources => new()
    {
        { BranchWitness, true },
        { RepeatObserver("T, T"), true },
        { RepeatObserver("T(), T"), true },
        { RepeatObserver("a, a"), true },
        { RepeatObserver("T(), T()"), false },
        { RepeatObserver("T, T()"), false },
        { WhileObserver, true },
    };

    // ── Cases ────────────────────────────────────────────────────────────────────────────────

    [Fact]
    public async Task BranchWitness_ReturnsNine_OnEveryRoute()
    {
        var outcomes = await ObserveEveryRouteAsync(BranchWitness);
        foreach (var outcome in outcomes)
        {
            Assert.True(outcome.Ok, outcome.ToString());
            Assert.Equal(9m, Assert.IsType<Result.Atom>(outcome.Value).Value);
            Assert.Equal(new[] { true }, outcome.Verdicts);
        }

        var planned = Planned(outcomes);
        Assert.True(planned.Loop!.OptimizedLoopHits > 0);
        AssertWhollyPlanned(planned.Loop, plannedOperations: 1);
        AssertSameAcrossRoutes(outcomes, compareValues: true);
    }

    [Theory]
    [MemberData(nameof(RepeatRows))]
    public async Task RepeatRows_KeepOneResultForOneEntry_AndExecuteTheTempAsOften(string rows, int additions, bool? sameObject)
    {
        var outcomes = await ObserveEveryRouteAsync(RepeatObserver(rows));
        foreach (var outcome in outcomes)
        {
            Assert.True(outcome.Ok, outcome.ToString());
            var verdict = Assert.IsType<Result.Bool>(outcome.Value).Value;
            Assert.Equal(new[] { verdict }, outcome.Verdicts);
            if (sameObject is { } expected)
                Assert.True(expected == verdict, $"{outcome.Route}: ReferenceEquals was {verdict} for '{rows}'");
        }

        AssertWhollyPlanned(Planned(outcomes).Loop!, additions);
        // The generic strategy runs no planned operation.
        Assert.Equal(0, Generic(outcomes).Loop!.PlannedBuiltinOperations);
        AssertSameAcrossRoutes(outcomes, compareValues: sameObject is not null);
    }

    [Theory]
    [MemberData(nameof(IndependentLiteralSources))]
    public async Task IndependentLiteralEvaluations_MayShareOrSplitTheirObjects(string source)
    {
        // The planner reuses its boxed literal across iterations, the generic evaluator boxes each
        // execution afresh: both are valid answers, so only the shape and the charges are pinned.
        var outcomes = await ObserveEveryRouteAsync(source);
        foreach (var outcome in outcomes)
        {
            Assert.True(outcome.Ok, outcome.ToString());
            var verdict = Assert.IsType<Result.Bool>(outcome.Value).Value;
            Assert.Equal(new[] { verdict }, outcome.Verdicts);
        }

        AssertWhollyPlanned(Planned(outcomes).Loop!, plannedOperations: 0);
        AssertSameAcrossRoutes(outcomes, compareValues: false);
    }

    [Fact]
    public async Task WhileFinalIncomingState_KeepsTheRoundsOneResult()
    {
        var outcomes = await ObserveEveryRouteAsync(WhileObserver);
        foreach (var outcome in outcomes)
        {
            Assert.True(outcome.Ok, outcome.ToString());
            Assert.True(Assert.IsType<Result.Bool>(outcome.Value).Value, outcome.ToString());
            Assert.Equal(new[] { true }, outcome.Verdicts);
        }

        // Two flags (`a < 1` in both rounds) and the one addition of round one.
        AssertWhollyPlanned(Planned(outcomes).Loop!, plannedOperations: 3);
        Assert.Equal(2, Planned(outcomes).Loop!.LoopIterations);
        AssertSameAcrossRoutes(outcomes, compareValues: true);
    }

    [Theory]
    [MemberData(nameof(HandOnSources))]
    public async Task ExportedTempsAndHandovers_KeepOneResult(string source, int loopFallbacks)
    {
        var outcomes = await ObserveEveryRouteAsync(source);
        foreach (var outcome in outcomes)
        {
            Assert.True(outcome.Ok, outcome.ToString());
            Assert.True(Assert.IsType<Result.Bool>(outcome.Value).Value, outcome.ToString());
            Assert.Equal(new[] { true }, outcome.Verdicts);
        }

        var planned = Planned(outcomes).Loop!;
        Assert.Equal(1, planned.OptimizedLoopHits);
        Assert.Equal(loopFallbacks, planned.OptimizedLoopFallbacks);
        Assert.Equal(0, planned.PlannedExpressionFallbacks);
        Assert.Equal(0, planned.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.True(Assert.Single(planned.LoopPlans).Optimized);
        AssertSameAcrossRoutes(outcomes, compareValues: true);
    }

    [Theory]
    [MemberData(nameof(FailingSources))]
    public async Task FailingFixtures_FailWithOneStructuredError_OnEveryRoute(string source, KatLangErrorCode code, int hostCalls)
    {
        var outcomes = await ObserveEveryRouteAsync(source);
        foreach (var outcome in outcomes)
        {
            Assert.False(outcome.Ok, outcome.ToString());
            Assert.Equal(code, outcome.ErrorCode);
            Assert.Equal(hostCalls, outcome.Verdicts.Count);
            Assert.All(outcome.Verdicts, static verdict => Assert.True(verdict));
        }

        var planned = Planned(outcomes).Loop!;
        Assert.Equal(1, planned.OptimizedLoopHits);
        Assert.Equal(0, planned.PlannedExpressionFallbacks);
        Assert.Equal(0, planned.GenericExpressionEvaluationsInsideOptimizedLoops);
        AssertSameAcrossRoutes(outcomes, compareValues: true);
    }

    [Theory]
    [MemberData(nameof(SweepSources))]
    public async Task StepAndDepthLimits_AreStrategyNeutral(string source, bool compareValues)
    {
        var unlimited = await ObserveAsync(Route.Generic, source);
        Assert.True(unlimited.Ok, unlimited.ToString());
        var steps = unlimited.Budget!.Steps;
        Assert.True(steps > 1);
        // Below the run's own consumption every route stops at the same step; at and above it, the
        // limit is not reached and changes nothing.
        for (var maxSteps = 1L; maxSteps <= steps + 1; maxSteps++)
        {
            var outcomes = await ObserveEveryRouteAsync(source, new EvaluationLimits { MaxSteps = maxSteps });
            Assert.All(outcomes, outcome => Assert.Equal(maxSteps >= steps, outcome.Ok));
            if (maxSteps < steps)
                Assert.All(outcomes, outcome => Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, outcome.ErrorCode));
            AssertSameAcrossRoutes(outcomes, compareValues);
        }

        var peak = unlimited.Budget.PeakDepth;
        foreach (var maxDepth in new[] { peak, peak - 1 })
        {
            if (maxDepth < 1)
                continue;
            var outcomes = await ObserveEveryRouteAsync(source, new EvaluationLimits { MaxDepth = maxDepth });
            Assert.All(outcomes, outcome => Assert.Equal(maxDepth >= peak, outcome.Ok));
            AssertSameAcrossRoutes(outcomes, compareValues);
        }
    }

    // ── Harness ──────────────────────────────────────────────────────────────────────────────

    private enum Route
    {
        /// <summary><see cref="Evaluator.RunCountedObserved"/> with optimizations disabled.</summary>
        Generic,

        /// <summary><see cref="Evaluator.RunCountedObserved"/> with optimizations enabled.</summary>
        Planned,

        /// <summary>The public synchronous engine.</summary>
        EngineSync,

        /// <summary>The public asynchronous engine with an asynchronous host operation: the generic twin.</summary>
        EngineAsyncTwin,

        /// <summary><see cref="Evaluator.RunCountedObservedAsync"/> with an asynchronous host operation.</summary>
        ForcedTwin,
    }

    private sealed record Counters(long Steps, long Checkpoints, int PeakDepth, long Items, long Chars);

    private sealed record Outcome(
        Route Route,
        bool Ok,
        Result? Value,
        int EmittedCount,
        KatLangErrorCode? ErrorCode,
        string? Error,
        IReadOnlyList<bool> Verdicts,
        Counters? Budget,
        LoopOptimizationDiagnosticsSnapshot? Loop)
    {
        public override string ToString()
            => $"{Route}: {(Ok ? "ok " + Value : "error " + Error)} verdicts=[{string.Join(",", Verdicts)}]";
    }

    /// <summary>The host's observation log: one verdict per <c>SamePair</c> call, in call order.</summary>
    private sealed class SamePairLog
    {
        private readonly List<bool> _verdicts = [];

        public IReadOnlyList<bool> Verdicts
        {
            get
            {
                lock (_verdicts)
                    return [.. _verdicts];
            }
        }

        public Result Observe(IReadOnlyList<Result> args)
        {
            var pair = (Result.SequenceValue)args[0];
            var same = ReferenceEquals(pair.Items[0], pair.Items[1]);
            lock (_verdicts)
                _verdicts.Add(same);
            return new Result.Bool(same);
        }
    }

    private static HostOperations SamePairOperations(SamePairLog log, bool asynchronous)
        => HostOperations.Create(asynchronous
            ? HostOperation.CreateAsync("SamePair", async (args, _) =>
            {
                await Task.Yield();
                return log.Observe(args);
            }, "pair")
            : HostOperation.Create("SamePair", (args, _) => log.Observe(args), "pair"));

    /// <summary>A source the front end accepts, parsed with the host operations its names resolve to.</summary>
    private static Algorithm.User ParseValid(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.Empty(parsed.Diagnostics);
        return parsed.Root;
    }

    private static async Task<IReadOnlyList<Outcome>> ObserveEveryRouteAsync(string source, EvaluationLimits? limits = null)
    {
        var outcomes = new List<Outcome>();
        foreach (var route in Enum.GetValues<Route>())
            outcomes.Add(await ObserveAsync(route, source, limits));
        return outcomes;
    }

    private static async Task<Outcome> ObserveAsync(Route route, string source, EvaluationLimits? limits = null)
    {
        var log = new SamePairLog();
        var operations = SamePairOperations(log, asynchronous: route is Route.EngineAsyncTwin or Route.ForcedTwin);
        var options = new RunOptions { HostOperations = operations, EvaluationLimits = limits };
        switch (route)
        {
            case Route.EngineSync:
                return FromRunResult(route, KatLangEngine.Run(source, options), log);
            case Route.EngineAsyncTwin:
                return FromRunResult(route, await KatLangEngine.RunAsync(source, options), log);
        }

        var program = new Expr.AlgorithmExpr(ParseValid(source, operations));
        LoopOptimizationDiagnostics? diagnostics = null;
        EvalResult<Evaluator.CountedResult> result;
        EvaluationBudget budget;
        if (route == Route.ForcedTwin)
        {
            (result, budget) = await Evaluator.RunCountedObservedAsync(
                program,
                limits,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: operations);
        }
        else
        {
            // A fresh diagnostics object per run, the same host-operation configuration on both strategies.
            diagnostics = new LoopOptimizationDiagnostics();
            (result, budget) = Evaluator.RunCountedObserved(
                program,
                limits,
                enableOptimizations: route == Route.Planned,
                loopDiagnostics: diagnostics,
                hostOperations: operations);
        }

        Assert.Equal(0, budget.CurrentDepth);
        var counters = new Counters(
            budget.ConsumedSteps,
            budget.ConsumedExpressionCheckpoints,
            budget.PeakDepth,
            budget.MaterializedItems,
            budget.MaterializedStringChars);
        return result.IsError
            ? new Outcome(route, false, null, 0, KatLangError.FromEvalError(result.Error).Code,
                DescribeErrorTree(result.Error), log.Verdicts, counters, diagnostics?.GetSnapshot())
            : new Outcome(route, true, result.Value.Value, result.Value.EmittedCount, null, null,
                log.Verdicts, counters, diagnostics?.GetSnapshot());
    }

    private static Outcome FromRunResult(Route route, RunResult result, SamePairLog log) => result switch
    {
        RunResult.Success success => new(route, true, success.Value, success.EmittedCount, null, null, log.Verdicts, null, null),
        RunResult.EvalFailure failure => new(route, false, null, 0, Assert.Single(failure.Errors).Code,
            string.Join(" | ", failure.Errors.Select(static e => $"{e.Code}: {e.Message} @ {e.Span}")), log.Verdicts, null, null),
        _ => throw new Xunit.Sdk.XunitException($"{route}: unexpected run result {result}"),
    };

    private static Outcome Generic(IReadOnlyList<Outcome> outcomes) => outcomes.Single(static o => o.Route == Route.Generic);

    private static Outcome Planned(IReadOnlyList<Outcome> outcomes) => outcomes.Single(static o => o.Route == Route.Planned);

    /// <summary>
    /// The optimized route ran the loop on the planned path in full, executing
    /// <paramref name="plannedOperations"/> planned operations (<c>PlannedBuiltinOperations</c>).
    /// Otherwise a parity assertion would compare the generic strategy with itself.
    /// </summary>
    private static void AssertWhollyPlanned(LoopOptimizationDiagnosticsSnapshot loop, int plannedOperations)
    {
        Assert.Equal(1, loop.OptimizedLoopHits);
        Assert.Equal(0, loop.OptimizedLoopFallbacks);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(plannedOperations, loop.PlannedBuiltinOperations);
        var plan = Assert.Single(loop.LoopPlans);
        Assert.True(plan.Optimized, plan.FallbackReason);
    }

    /// <summary>
    /// Every route agrees with the generic evaluator: outcome, structured error (the whole error tree
    /// on the evaluator routes, code, message and position on the engines), emitted count, the number
    /// of host calls and — on the evaluator routes — every budget counter. Values and verdicts are
    /// compared only where the identity verdict is fixed.
    /// </summary>
    private static void AssertSameAcrossRoutes(IReadOnlyList<Outcome> outcomes, bool compareValues)
    {
        var oracle = Generic(outcomes);
        var engine = outcomes.Single(static o => o.Route == Route.EngineSync);
        foreach (var outcome in outcomes)
        {
            Assert.True(oracle.Ok == outcome.Ok, $"expected {oracle}, got {outcome}");
            Assert.Equal(oracle.ErrorCode, outcome.ErrorCode);
            Assert.Equal(oracle.EmittedCount, outcome.EmittedCount);
            if (outcome.Ok)
                Assert.Equal(1, outcome.EmittedCount);
            Assert.Equal(oracle.Verdicts.Count, outcome.Verdicts.Count);
            if (compareValues)
            {
                Assert.Equal(oracle.Verdicts, outcome.Verdicts);
                if (oracle.Ok)
                    Assert.True(Result.ValueComparer.Equals(oracle.Value!, outcome.Value!), $"expected {oracle}, got {outcome}");
            }

            if (outcome.Budget is { } budget)
            {
                Assert.Equal(oracle.Error, outcome.Error);
                Assert.Equal(oracle.Budget, budget);
            }
            else
            {
                Assert.Equal(engine.Error, outcome.Error);
            }
        }
    }
}
