using System.Globalization;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// SCANS STACKED AT RUN TIME ARE DISCOVERED WITHOUT ONE NATIVE CALL PER SCAN (lazy collections,
/// issue #204; C#-only host policy, no Lean counterpart: Lean's discovery is a total function with no
/// host stack). A loop that filters its own list every round stacks one <c>filter</c> scan per round,
/// and a scan whose source has no position at its frontier asks the scan below it — through any
/// <c>map</c> and <c>take</c> stages — for exactly one more. That request used to be a native call per
/// scan, so a synchronous run ended with <c>EvaluationStackExhausted</c> once the stack ran out
/// (between 800 and 900 stacked scans on a 1 MiB thread in Release, measured 2026-11-24), and the
/// asynchronous twin hopped to fresh stacks. Now one frame drives every scan of the chain
/// (<c>Evaluator.FilteredList.DiscoverScans</c>): the scan above waits on an explicit list while the scan
/// below runs exactly the iterations its own discovery would run, so the order of verdicts (Lean's
/// <c>LazyList.discover</c>: candidates in order, each reading its source verdict first), the cached
/// accepted and rejected prefixes, the positions readable before a later ordinary failure, the failure's
/// blame, the run budget, cancellation and in-flight joins are those of the nested calls.
/// <para>Unless a test names its route, every program runs on the six established routes
/// (<see cref="SixRouteAgreement"/>), which must agree on the value, every error and the host-call log.
/// The deterministic guard runs the synchronous evaluator on a dedicated 256 KiB thread: a stack of
/// 20,000 scans is discovered there, and each scan judges each of its candidates exactly once.</para>
/// </summary>
public sealed class StackedScanDiscoveryTests
{
    private static async Task<SixRouteAgreement.Observation> Expect(string source, string expected, string hostCalls = "")
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        var outcome = observation.Kind switch
        {
            "ok" => $"ok {observation.Value}",
            "err" => $"err {observation.Errors[0][..observation.Errors[0].IndexOf(':')]}",
            _ => observation.Kind,
        };
        Assert.Equal(expected, outcome);
        Assert.Equal(hostCalls, string.Join(",", observation.HostCalls));
        return observation;
    }

    private static string Height(int height) => height.ToString(CultureInfo.InvariantCulture);

    // ── 1. Every route discovers a tall stack ─────────────────────────────────────────────────

    /// <summary>source, expected outcome — 3,000 scans stacked by a loop.</summary>
    public static TheoryData<string, string> TallStacks() => new()
    {
        { "Step(xs) = xs.filter{x >= 0}\nrepeat(Step([0, 1]), 3000).count", "ok 2" },
        { "Step(xs) = xs.filter{x >= 0}\nrepeat(Step([0, 1]), 3000)", "ok L[0, 1]" },
        { "Step(xs) = xs.filter{x >= 0}\nrepeat(Step([0, 1]), 3000).first", "ok 0" },
        // Rejected candidates stay rejected at every height.
        { "Step(xs) = xs.filter{x > 0}\nrepeat(Step([0, 1, 2]), 3000)", "ok L[1, 2]" },
        // Mixed stages: a scan asks the scan below through a map, and through a take.
        { "Step(xs) = xs.filter{x >= 0}.map{x + 1}\nrepeat(Step([0, 1]), 3000)", "ok L[3000, 3001]" },
        { "Step(xs) = xs.map{x + 1}.filter{x > 0}.take(2)\nrepeat(Step([0, 1, 2]), 3000)", "ok L[3000, 3001]" },
        { "Step(xs) = xs.filter{x >= 0}.take(1)\nrepeat(Step([0, 1]), 3000)", "ok L[0]" },
        // A failing candidate at the bottom: the positions before it stay readable at the top…
        { "Step(xs) = xs.filter{1 / x > 0}\nrepeat(Step([1, 0, 2]), 3000).first", "ok 1" },
        { "Step(xs) = xs.filter{1 / x > 0}\nrepeat(Step([1, 0, 2]), 3000).take(1)", "ok L[1]" },
        // …and a reader that needs the failing one fails with it.
        { "Step(xs) = xs.filter{1 / x > 0}\nrepeat(Step([1, 0, 2]), 3000).count", "err DivisionByZero" },
        { "Step(xs) = xs.filter{1 / x > 0}\nrepeat(Step([1, 0, 2]), 3000)", "err DivisionByZero" },
    };

    [Theory]
    [MemberData(nameof(TallStacks))]
    public async Task AStackOfScansBuiltByALoop_IsDiscoveredOnEveryRoute(string source, string expected)
        => await Expect(source, expected);

    // ── 2. The deterministic guard: a bounded stack, linear work ──────────────────────────────

    // Parsed on the caller's thread; only the evaluation runs on the small one.
    private static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    [Fact]
    public void TwentyThousandStackedScans_AreDiscoveredOnA256KiBThread_JudgingEachCandidateOnce()
    {
        const int Scans = 20_000;
        // `tick()` runs once per verdict: a scan judges each of its candidates exactly once, so the
        // stack does work linear in its height.
        var program = Program("Step(xs) = xs.filter{tick() > 0 and x >= 0}\nrepeat(Step([0, 1]), " + Height(Scans) + ")");
        foreach (var optimized in new[] { false, true })
        {
            var (result, budget) = AstStructuralDepthProcessTests.RunOnThreadWithStack(
                256 * 1024, () => Evaluator.RunCountedObserved(program, enableOptimizations: optimized));
            Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
            Assert.Equal("L[0, 1]", SixRouteAgreement.Neutral(result.Value.Value));
            Assert.Equal(2L * Scans, budget.TickCount);
        }

        // Through a map between every two scans, read whole: the positions are found by the scans
        // and read through the maps deepest first.
        var mapped = Program("Step(xs) = xs.filter{tick() > 0 and x >= 0}.map{x + 1}\nrepeat(Step([0, 1]), " + Height(Scans) + ")");
        var (mappedResult, mappedBudget) = AstStructuralDepthProcessTests.RunOnThreadWithStack(
            256 * 1024, () => Evaluator.RunCountedObserved(mapped, enableOptimizations: true));
        Assert.True(mappedResult.IsOk, mappedResult.IsError ? mappedResult.Error.ToString() : null);
        Assert.Equal("L[20000, 20001]", SixRouteAgreement.Neutral(mappedResult.Value.Value));
        Assert.Equal(2L * Scans, mappedBudget.TickCount);
    }

    [Fact]
    public async Task TwentyThousandStackedScans_AreDiscoveredByTheTwinOnA256KiBThread()
    {
        var program = Program("Step(xs) = xs.filter{x >= 0}\nrepeat(Step([0, 1]), 20000).count");
        var pending = AstStructuralDepthProcessTests.RunOnThreadWithStack(256 * 1024, () =>
            Evaluator.RunCountedAsync(program, new RunScopedAsyncZeroArgPropertyResultCache()).AsTask());
        var result = await pending;
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        Assert.Equal("2", SixRouteAgreement.Neutral(result.Value.Value));
    }

    // ── 3. Order, blame and the budget are those of the nested calls ──────────────────────────

    [Fact]
    public async Task VerdictsAreDemandedInCandidateOrder_EachAfterItsSourceVerdict()
    {
        // Each round adds 10, so a predicate's argument names its scan: the first candidate is
        // judged by every scan from the bottom up before the second candidate is looked at.
        await Expect(
            "Step(xs) = xs.map{x + 10}.filter{trace(x) > 0}\nrepeat(Step([1, 2]), 3).count",
            "ok 2",
            "trace(11),trace(21),trace(31),trace(12),trace(22),trace(32)");
        // A candidate the middle scan rejects sends it back to the scan below for the next one;
        // a rejected candidate is never judged again.
        await Expect(
            "Step(xs) = xs.map{x + 10}.filter{trace(x) != 21}\nrepeat(Step([1, 2]), 3).count",
            "ok 1",
            "trace(11),trace(21),trace(12),trace(22),trace(32)");
        // A reader that needs one position judges only what that position needs.
        await Expect(
            "Step(xs) = xs.map{x + 10}.filter{trace(x) > 0}\nrepeat(Step([1, 2]), 3).first",
            "ok 31",
            "trace(11),trace(21),trace(31)");
    }

    [Fact]
    public async Task AFailureDeepInTheStack_IsBlamedAsOnAStackOfOne()
    {
        // The bottom scan's verdict fails; the failure reaches the reader unchanged, framed by the
        // scan that failed (the written `.filter` call and the candidate) and by the reader. The
        // height is the last line, so both programs render and position every frame alike.
        var one = await Expect("Step(xs) = xs.filter{1 / x > 0}\nrepeat(Step([1, 0, 2]), H).count\nH = 1", "err DivisionByZero");
        var tall = await Expect("Step(xs) = xs.filter{1 / x > 0}\nrepeat(Step([1, 0, 2]), H).count\nH = 2000", "err DivisionByZero");
        Assert.Equal(one.Errors, tall.Errors);
        Assert.Contains("while evaluating filter predicate for item 1", tall.Errors[0], StringComparison.Ordinal);
    }

    [Fact]
    public async Task AStepLimit_IsReachedAtTheSameStepOnBothRoutes()
    {
        const string source = "Step(xs) = xs.filter{x >= 0}\nrepeat(Step([0, 1, 2]), 400).count";
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var unlimited = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        Assert.True(unlimited.Result.IsOk);
        var steps = unlimited.Budget.ConsumedSteps;
        foreach (var limit in new[] { steps, steps - 1 })
        {
            var limits = new EvaluationLimits { MaxSteps = limit };
            var sync = Evaluator.RunCountedObserved(program, limits, enableOptimizations: false);
            var twin = await Evaluator.RunCountedObservedAsync(program, limits, new RunScopedAsyncZeroArgPropertyResultCache());
            Assert.Equal(limit == steps, sync.Result.IsOk);
            Assert.Equal(sync.Result.IsOk, twin.Result.IsOk);
            if (!sync.Result.IsOk)
            {
                Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, sync.Result.Error.Code);
                Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, twin.Result.Error.Code);
            }

            Assert.Equal(sync.Budget.ConsumedSteps, twin.Budget.ConsumedSteps);
            Assert.Equal(sync.Budget.ConsumedExpressionCheckpoints, twin.Budget.ConsumedExpressionCheckpoints);
        }
    }

    // ── 4. Cancellation, joins and cycles ─────────────────────────────────────────────────────

    [Fact]
    public async Task Cancellation_DuringATallStack_EndsTheRunWithoutAnotherVerdict()
    {
        foreach (var asynchronous in new[] { false, true })
        {
            using var cancellation = new CancellationTokenSource();
            var calls = 0;
            Result Stop()
            {
                if (Interlocked.Increment(ref calls) == 100) cancellation.Cancel();
                return new Result.Atom(1);
            }

            var operations = asynchronous
                ? HostOperations.Create(HostOperation.CreateAsync("stop", async (_, _) =>
                {
                    await Task.Yield();
                    return Stop();
                }))
                : HostOperations.Create(HostOperation.Create("stop", (_, _) => Stop()));
            var options = new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token };
            const string source = "Step(xs) = xs.filter{stop() > 0 and x >= 0}\nrepeat(Step([0, 1, 2, 3]), 2000).count";
            var thrown = asynchronous
                ? await Assert.ThrowsAnyAsync<OperationCanceledException>(() => KatLangEngine.RunAsync(source, options))
                : Assert.ThrowsAny<OperationCanceledException>(() => KatLangEngine.Run(source, options));
            Assert.Equal(cancellation.Token, thrown.CancellationToken);
            Assert.Equal(100, Volatile.Read(ref calls));
        }
    }

    [Fact]
    public async Task OverlappingDiscoveriesOfAStack_JoinTheVerdictBelow()
    {
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.CreateAsync("gate", async (_, _) =>
        {
            Interlocked.Increment(ref calls);
            await release.Task;
            return new Result.Atom(1);
        }));
        var parsed = Parser.Parse("[1, 2].filter{gate() > 0 and x > 0}.map{x + 1}.filter{tick() > 0 and x > 0}", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);
        var budget = EvaluationBudget.Create(null, operations);
        budget.MarkAsynchronousRun();
        var ctx = Evaluator.EvalCtx.Empty with
        {
            Budget = budget,
            CallStack = [operations.RuntimePreludeAlgorithm],
            Services = Evaluator.RunServices.Unconfigured with
            {
                EnableLoopOptimization = false,
                EnableSequencePipelineOptimization = false,
                ZeroArgPropertyResultCache = new RunScopedAsyncZeroArgPropertyResultCache(),
            },
        };
        var staged = Evaluator.EvalCounted(new Expr.AlgorithmExpr(parsed.Root), ctx, []);
        Assert.True(staged.IsOk);
        var top = Assert.IsAssignableFrom<Evaluator.LazyList>(Assert.IsType<Result.ListValue>(staged.Value.Value).Lazy);

        // Both discoveries drive the scan below the top one and meet its first verdict in flight.
        var first = top.Discover(1, asynchronous: true);
        var second = top.Discover(1, asynchronous: true);
        try
        {
            Assert.False(first.IsCompleted);
            Assert.False(second.IsCompleted);
            Assert.Equal(1, Volatile.Read(ref calls));
        }
        finally
        {
            release.SetResult();
        }

        Assert.Null(await first);
        Assert.Null(await second);
        Assert.Equal(1, top.Discovered);
        Assert.Equal(1, calls);
        // The top scan's verdict was computed once, by one of the two.
        Assert.Equal(1, budget.TickCount);
    }

    [Theory]
    // The top scan's predicate needs the scan it is part of.
    [InlineData("Step(xs) = xs.filter{x > 0}\nS = repeat(Step([1, 2]), 30).filter{S.count >= x}\nS")]
    // Every scan's predicate needs the top of the stack: the bottom one meets its own verdict.
    [InlineData("Step(xs) = xs.filter{x > 0 and S.count >= 0}\nS = repeat(Step([1, 2]), 30)\nS")]
    public async Task APredicateThatNeedsItsOwnStack_IsADemandCycle(string source)
        => await Expect(source, "err DemandCycle");
}
