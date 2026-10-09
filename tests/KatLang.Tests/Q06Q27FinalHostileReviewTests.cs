using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

public class Q06Q27FinalHostileReviewTests
{
    // A prebuilt cell cannot be injected through the host entry point. Exercise the actual
    // private async dispatch with its caller context, without adding a production test seam.
    private static ValueTask<EvalResult<Evaluator.CountedResult>> EvaluateTwin(Expr expression, Evaluator.EvalCtx ctx)
        => (ValueTask<EvalResult<Evaluator.CountedResult>>)typeof(Evaluator)
            .GetMethod("EvalCountedAsync", System.Reflection.BindingFlags.Static | System.Reflection.BindingFlags.NonPublic)!
            .Invoke(null, [expression, ctx with { EnableLoopOptimization = false, EnableSequencePipelineOptimization = false }, Array.Empty<(string, Result)>()])!;

    private static EvalError Inner(EvalError error)
    {
        while (error is EvalError.WithContext context) error = context.Inner;
        return error;
    }

    private static Expr Consumer(BuiltinId builtin, bool empty = false)
    {
        Expr collection = new Expr.ListLiteral(new OutputBundle(empty ? [] : [new Expr.Num(1)]));
        Expr slot = new Expr.Param("f");
        Expr[] args = builtin switch
        {
            BuiltinId.@map or BuiltinId.@filter => [collection, slot],
            BuiltinId.@reduce => [collection, slot, new Expr.Num(0)],
            BuiltinId.@repeat => [slot, new Expr.Num(empty ? 0 : 1), new Expr.Num(0)],
            BuiltinId.@while => [slot, new Expr.Num(0)],
            _ => throw new ArgumentOutOfRangeException(nameof(builtin)),
        };
        return new Expr.Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(builtin)), new OutputBundle(args));
    }

    // Every wait below is bounded, so a consumer that joins the cell's in-flight VALUE (which
    // cannot complete before `release`, set only in the finally block) fails the test instead
    // of hanging the suite. The bound is a hang guard, never a latency claim: both consumers
    // run as thread-pool work, while the timer enforcing the bound is queued ahead of pool work
    // at high priority, so a tight bound fails spuriously on a loaded CI runner (5 s did).
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task TwoCallbackConsumers_ProjectASharedInFlightCellWithoutJoiningItsValue(bool hasCallable)
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        var projections = 0;
        using var stop = new CancellationTokenSource();
        var originalSpan = new SourceSpan(7, 3, 7, 9);
        Algorithm? callable = hasCallable ? new Algorithm.User(null, [], [], [], [new Expr.Num(8)]) : null;
        var cell = new NeedCell(
            () => throw new InvalidOperationException("A sync VALUE demand must not start."),
            async () =>
            {
                Interlocked.Increment(ref starts);
                entered.TrySetResult();
                await release.Task.WaitAsync(stop.Token);
                return new EvalError.DivByZero();
            },
            () => { Interlocked.Increment(ref projections); return EvalResult<Algorithm?>.Ok(callable); },
            span: originalSpan, token: stop.Token);
        var valueFlight = cell.DemandAsync().AsTask();
        await entered.Task.WaitAsync(WaitLimit);
        Task<EvalResult<Evaluator.CountedResult>>? sync = null, twin = null;
        try
        {
            var first = Evaluator.EvalCtx.Empty.WithNeedEnv([("f", cell)]);
            var second = Evaluator.EvalCtx.Empty.WithNeedEnv([("f", cell)]);
            for (var hop = 0; hop < 3; hop++)
            {
                Assert.Same(cell, Evaluator.SupplyCell(new Expr.Param("f"), first, []));
                Assert.Same(cell, Evaluator.SupplyCell(new Expr.Param("f"), second, []));
            }
            sync = Task.Run(() => Evaluator.EvalCounted(Consumer(BuiltinId.@map), first, []));
            twin = Task.Run(async () => await EvaluateTwin(Consumer(BuiltinId.@filter), second));
            var results = await Task.WhenAll(sync, twin).WaitAsync(WaitLimit);
            Assert.All(results, result => Assert.Equal(hasCallable ? KatLangErrorCode.ArityMismatch : KatLangErrorCode.NotAnAlgorithm, result.Error.Code));
            if (!hasCallable) Assert.All(results, result => Assert.Equal(originalSpan, Inner(result.Error).Span));
            Assert.False(valueFlight.IsCompleted);
            Assert.False(stop.IsCancellationRequested);
            Assert.Equal(1, starts);
            Assert.Equal(1, projections);
        }
        finally
        {
            release.TrySetResult();
            await valueFlight.WaitAsync(WaitLimit);
            if (sync is not null) await sync.WaitAsync(WaitLimit);
            if (twin is not null) await twin.WaitAsync(WaitLimit);
        }
        var storedValue = await valueFlight;
        Assert.IsType<EvalError.DivByZero>(storedValue.Error);
        Assert.Same(callable, cell.ProjectCallable().Value);
        Assert.Same(storedValue.Error, cell.Demand().Error);
        Assert.Equal(1, starts);
    }

    [Theory]
    [InlineData(BuiltinId.@map)]
    [InlineData(BuiltinId.@filter)]
    [InlineData(BuiltinId.@reduce)]
    [InlineData(BuiltinId.@repeat)]
    public async Task AnUnusedSlotNeverProjectsOrStartsItsCell(BuiltinId builtin)
    {
        var starts = 0;
        var projections = 0;
        EvalResult<Evaluator.CountedResult> Evaluate() { starts++; return new EvalError.DivByZero(); }
        var cell = new NeedCell(Evaluate, () => new(Evaluate()), () =>
        {
            projections++;
            throw new InvalidOperationException("This unused CALLABLE channel must not be read.");
        });
        foreach (var twin in new[] { false, true })
        {
            var ctx = Evaluator.EvalCtx.Empty.WithNeedEnv([("f", cell)]);
            var result = twin ? await EvaluateTwin(Consumer(builtin, empty: true), ctx)
                : Evaluator.EvalCounted(Consumer(builtin, empty: true), ctx, []);
            Assert.True(result.IsOk);
            Assert.Equal(0, ctx.Budget.ConsumedSteps);
            Assert.Equal(0, ctx.Budget.PeakDepth);
        }
        Assert.Equal(0, starts);
        Assert.Equal(0, projections);
    }

    [Theory]
    [InlineData("map([1], 5)", "map([1], { 5 })")]
    [InlineData("filter([1], 5)", "filter([1], { true })")]
    [InlineData("reduce([1], 5, 0)", "reduce([1], { 5 }, 0)")]
    [InlineData("repeat(5, 1, 0)", "repeat({ 5 }, 1, 0)")]
    [InlineData("while(5, 0)", "while({ true }, 0)")]
    [InlineData("count(filter(range(1, 3), 5))", "count(filter(range(1, 3), { true }))")]
    public async Task MissingCallablePaysNoInvocationOrIterationCharge(string rejected, string realCallable)
    {
        var programs = new[] { rejected, realCallable }.Select(source => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root)).ToArray();
        foreach (var route in new[] { 0, 1, 2 })
        {
            var failed = route == 2 ? await Evaluator.RunCountedObservedAsync(programs[0], zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache())
                : Evaluator.RunCountedObserved(programs[0], enableOptimizations: route == 1);
            var control = route == 2 ? await Evaluator.RunCountedObservedAsync(programs[1], zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache())
                : Evaluator.RunCountedObserved(programs[1], enableOptimizations: route == 1);
            Assert.IsType<EvalError.NotAnAlgorithm>(Inner(failed.Result.Error));
            Assert.Equal(KatLangErrorCode.ArityMismatch, control.Result.Error.Code);
            Assert.Equal(0, failed.Budget.ConsumedSteps);
            Assert.Equal(0, failed.Budget.PeakDepth);
            Assert.Equal(1, control.Budget.ConsumedSteps);
            Assert.Equal(control.Budget.ConsumedExpressionCheckpoints, failed.Budget.ConsumedExpressionCheckpoints);
            Assert.Equal(control.Budget.MaterializedItems, failed.Budget.MaterializedItems);
        }
    }

    [Theory]
    [InlineData("F(*fs) = map([1], fs)\nF(5)", "fs", "map")]
    [InlineData("F(*fs) = filter([1], fs)\nF(5)", "fs", "filter")]
    [InlineData("F(*fs) = reduce([1], fs, 0)\nF(5)", "fs", "reduce")]
    [InlineData("F(*fs) = [1].map(fs)\nF(5)", "fs", "map")]
    [InlineData("F(*fs) = count(filter(range(1, 3), fs))\nF(5)", "fs", "filter")]
    public async Task AWholeCollectorHasNoOriginalCellSpanSoProjectionBlamesTheWrittenSlot(string source, string slot, string builtin)
    {
        var start = source.LastIndexOf(slot, StringComparison.Ordinal);
        var expected = new SourceSpan(1, start + 1, 1, start + slot.Length + 1);
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", observation.Kind);
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors).Source!;
        Assert.IsType<EvalError.NotAnAlgorithm>(Inner(error));
        Assert.Equal(expected, error.Span);
        var frames = new List<string>();
        while (error is EvalError.WithContext context) { frames.Add(context.Context); error = context.Inner; }
        Assert.Contains(source.Contains("].map", StringComparison.Ordinal)
            ? "while evaluating dotCall .map of [1]" : $"while evaluating call to {builtin}", frames);
        Assert.DoesNotContain(frames, frame => frame.Contains("for item", StringComparison.Ordinal) || frame.Contains("while evaluating map transform", StringComparison.Ordinal) || frame.Contains("while evaluating reduce step", StringComparison.Ordinal));
    }

    [Fact]
    public void EveryBuiltinArityPayloadNamesItsActualMinimumBeforeDemandingArguments()
    {
        foreach (var descriptor in BuiltinRegistry.AllBuiltins)
        {
            var minimum = descriptor.ArityFacts.MinTopLevelArgumentCount;
            // A bare builtin takes the zero-supply VALUE-demand path, independently
            // of an explicit call's binder; both must report the same true minimum.
            var bareFailure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(descriptor.Id.ToString()));
            var bareMismatch = Assert.IsType<EvalError.ArityMismatch>(Inner(Assert.Single(bareFailure.Errors).Source!));
            Assert.Equal((minimum, 0), (bareMismatch.Expected, bareMismatch.Actual));
            foreach (var actual in new[] { 0, minimum - 1 }.Distinct())
            {
                var source = descriptor.Id + "(" + string.Join(",", Enumerable.Repeat("1 / 0", actual)) + ")";
                var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
                var mismatch = Assert.IsType<EvalError.ArityMismatch>(Inner(Assert.Single(failure.Errors).Source!));
                Assert.Equal((minimum, actual), (mismatch.Expected, mismatch.Actual));
            }
        }
    }

    [Theory]
    [InlineData("map([1], f)")]
    [InlineData("filter([1], f)")]
    [InlineData("reduce([1], f, 0)")]
    [InlineData("repeat(f, 1, 0)")]
    [InlineData("count(filter(range(1, 3), f))")]
    public async Task ThreeForwardingLevelsKeepTheOriginalArgumentSpanAndNoInvocationFrame(string use)
    {
        var source = $"Inner(f) = {use}\nMiddle(g) = Inner(g)\nOuter(h) = Middle(h)\nOuter(1 / 0)";
        await SixRouteAgreement.OnEveryRouteAsync(source);
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors).Source!;
        Assert.IsType<EvalError.NotAnAlgorithm>(Inner(error));
        Assert.Equal(new SourceSpan(4, 7, 4, 12), error.Span);
        var frames = new List<string>();
        while (error is EvalError.WithContext context) { frames.Add(context.Context); error = context.Inner; }
        Assert.Equal(new[] { "while evaluating call to Outer", "while evaluating call to Middle", "while evaluating call to Inner" }, frames.Take(3));
        Assert.DoesNotContain(frames, frame => frame.Contains("for item", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("F([0]) = 0\nF([n]) = n\nF([1], [2])", KatLangErrorCode.ArityMismatch)]
    [InlineData("F(0) = 0\nF(n) = n\nA = F\nB = A\nB(1, 2)", KatLangErrorCode.ArityMismatch)]
    [InlineData("F(0) = 0\nF(n) = n\nApp(f) = f(1, 2)\nApp(F)", KatLangErrorCode.ArityMismatch)]
    [InlineData("F(0, a) = a\nF(n, a) = n\nmap([2], F)", KatLangErrorCode.ArityMismatch)]
    [InlineData("F(0, a) = a\nF(n, a) = n\nrepeat(F, 1, 0)", KatLangErrorCode.ArityMismatch)]
    [InlineData("F((0, 1)) = 1\nF((1, 0)) = 2\nF([0, 1])", KatLangErrorCode.NoMatchingBranch)]
    [InlineData("F(0) = 0\nF(1) = 1\nF(2)", KatLangErrorCode.NoMatchingBranch)]
    public async Task FamilySupplyCardinalityPrecedesMatchingWhileValidSupplyCanFailToMatch(string source, KatLangErrorCode expected)
    {
        SourceProvenance.ParseValid(source);
        await SixRouteAgreement.OnEveryRouteAsync(source);
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        Assert.Equal(expected, Assert.Single(failure.Errors).Code);
    }

    [Fact]
    public void CollectorClausesAreRejectedBeforeRuntimeTaxonomyApplies()
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError("F(0, *xs) = count(xs)\nF(n, *xs) = n\nF()");
        Assert.Contains(diagnostics, d => d.Code == DiagnosticCode.InvalidCollectingBinding);
    }
}
