using KatLang.Evaluation;
using System.Numerics;

namespace KatLang.Tests;

public class NeedCellTests
{
    private static EvalResult<Evaluator.CountedResult> Value(int number = 7)
        => EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom((Decimal128)number), 1));

    [Fact]
    public async Task SixtyFourOverlappingDemandsStartOnceAndReuseCompletion()
    {
        var starts = 0;
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var cell = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            Interlocked.Increment(ref starts);
            entered.SetResult();
            await release.Task;
            return Value();
        });
        var demands = Enumerable.Range(0, 64).Select(_ => Task.Run(async () => await cell.DemandAsync())).ToArray();
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
        release.SetResult();
        var values = await Task.WhenAll(demands).WaitAsync(TimeSpan.FromSeconds(10));
        Assert.All(values, value => Assert.True(value.IsOk));
        Assert.Equal(1, starts);
        Assert.True(cell.Demand().IsOk);
        Assert.Equal(1, starts);
    }

    [Fact]
    public async Task OrdinaryFailureAndHostExceptionAreStickyAcrossSyncAndAsync()
    {
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Fail() { starts++; return new EvalError.DivByZero(); }
        var cell = new NeedCell(Fail, () => new(Fail()));
        var first = cell.Demand();
        Assert.Equal(KatLangErrorCode.DivisionByZero, first.Error.Code);
        Assert.Same(first.Error, (await cell.DemandAsync()).Error);
        Assert.Same(first.Error, cell.Demand().Error);
        Assert.Equal(1, starts);

        var thrown = new InvalidOperationException("original host failure");
        var hostStarts = 0;
        EvalResult<Evaluator.CountedResult> Throw() { hostStarts++; throw thrown; }
        var host = new NeedCell(Throw, () => new(Throw()));
        Assert.Same(thrown, Assert.Throws<InvalidOperationException>(() => host.Demand()));
        Assert.Same(thrown, await Assert.ThrowsAsync<InvalidOperationException>(async () => await host.DemandAsync()));
        Assert.Equal(1, hostStarts);
    }

    [Fact]
    public async Task CancellationDuringSuspensionNeverRestarts()
    {
        using var stop = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        var cell = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            starts++;
            entered.SetResult();
            await Task.Delay(Timeout.Infinite, stop.Token);
            return Value();
        });
        var first = cell.DemandAsync().AsTask();
        await entered.Task;
        stop.Cancel();
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => first);
        Assert.True(first.IsCanceled);
        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await cell.DemandAsync());
        Assert.ThrowsAny<OperationCanceledException>(() => cell.Demand());
        Assert.Equal(1, starts);
    }

    [Fact]
    public void PreCancelledDemandHasNoEffectAndCallableProjectionDoesNotForce()
    {
        using var stop = new CancellationTokenSource();
        stop.Cancel();
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Evaluate() { starts++; return Value(); }
        var cancelled = new NeedCell(Evaluate, () => new(Evaluate()), token: stop.Token);
        Assert.ThrowsAny<OperationCanceledException>(() => cancelled.Demand());
        Assert.Equal(0, starts);
        var algorithm = new Algorithm.Builtin(BuiltinId.@map);
        var callable = new NeedCell(Evaluate, () => new(Evaluate()), () => EvalResult<Algorithm?>.Ok(algorithm));
        Assert.Same(algorithm, callable.ProjectCallable().Value);
        Assert.Equal(0, starts);
        Assert.True(callable.Demand().IsOk);
        Assert.Equal(1, starts);
    }

    [Fact]
    public async Task HostCancellationWithoutTheRunToken_IsStickyOnBothChannels()
    {
        var cancelled = new OperationCanceledException("host cancelled");
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Cancel()
        {
            starts++;
            throw cancelled;
        }
        var algorithm = new Algorithm.User(null, [], [], [], [new Expr.Num(7)]);
        var cell = new NeedCell(Cancel, () => new(Cancel()), () => EvalResult<Algorithm?>.Ok(algorithm));
        Assert.Same(cancelled, await Assert.ThrowsAsync<OperationCanceledException>(() => cell.DemandAsync().AsTask()));
        Assert.Same(cancelled, Assert.Throws<OperationCanceledException>(() => cell.Demand()));
        Assert.Same(cancelled, Assert.Throws<OperationCanceledException>(() => cell.ProjectCallable()));
        Assert.Equal(1, starts);
    }

    [Fact]
    public async Task DirectAndIndirectAsyncCyclesCompleteWithDemandCycle()
    {
        var span = new SourceSpan(new SourcePosition(2, 3), new SourcePosition(2, 4));
        NeedCell? direct = null;
        direct = new NeedCell(() => direct!.Demand(), () => direct!.DemandAsync(), span: span);
        Assert.Equal(KatLangErrorCode.DemandCycle, direct.Demand().Error.Code);
        Assert.Equal(span, direct.Demand().Error.Span);

        NeedCell? left = null, right = null;
        left = new NeedCell(() => right!.Demand(), async () => { await Task.Yield(); return await right!.DemandAsync(); });
        right = new NeedCell(() => left.Demand(), async () => { await Task.Yield(); return await left.DemandAsync(); });
        var result = await left.DemandAsync().AsTask().WaitAsync(TimeSpan.FromSeconds(10));
        Assert.Equal(KatLangErrorCode.DemandCycle, result.Error.Code);
        Assert.Equal(KatLangErrorCode.DemandCycle, right.Demand().Error.Code);
    }

    [Fact]
    public async Task IndependentlyStartedChainsDetectWaitGraphCycle()
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        NeedCell? left = null, right = null;
        async ValueTask<EvalResult<Evaluator.CountedResult>> Evaluate(Func<NeedCell> next)
        {
            if (Interlocked.Increment(ref starts) == 2) entered.SetResult();
            await entered.Task;
            return await next().DemandAsync();
        }
        left = new NeedCell(() => right!.Demand(), () => Evaluate(() => right!));
        right = new NeedCell(() => left.Demand(), () => Evaluate(() => left));
        var results = await Task.WhenAll(Task.Run(async () => await left.DemandAsync()), Task.Run(async () => await right.DemandAsync()))
            .WaitAsync(TimeSpan.FromSeconds(10));
        Assert.All(results, result => Assert.Equal(KatLangErrorCode.DemandCycle, result.Error.Code));
        Assert.Equal(2, starts);
    }
    [Fact]
    public void ReachedResourceLimitEndsBothChannelsWithoutChangingCompletedValue()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 1 });
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Evaluate() { starts++; return Value(); }
        var callable = new Algorithm.Builtin(BuiltinId.@map);
        var completed = new NeedCell(Evaluate, () => new(Evaluate()), () => EvalResult<Algorithm?>.Ok(callable), budget: budget);
        Assert.True(completed.Demand().IsOk);
        Assert.Null(budget.TryEnterInvocation());
        var failure = Assert.IsType<EvalError.EvaluationDepthExceeded>(budget.TryEnterInvocation());
        budget.ExitInvocation();
        Assert.Same(failure, completed.Demand().Error);
        Assert.Same(failure, completed.ProjectCallable().Error);
        Assert.Same(failure, budget.TryChargeStep());
        Assert.Equal(1, starts);
        Assert.Equal(1, budget.ConsumedSteps);
        Assert.Equal(0, budget.CurrentDepth);
    }

    [Fact]
    public void OneHundredThousandProductionParameterTransports_ShareOneAddressOnAConstrainedStack()
    {
        AstStructuralDepthProcessTests.RunOnThreadWithStack(512 * 1024, () =>
        {
            var starts = 0;
            var projections = 0;
            var span = new SourceSpan(2, 3, 2, 4);
            var algorithm = new Algorithm.User(null, [], [], [], [new Expr.Num(7)]);
            var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 1, MaxSteps = 1 });
            EvalResult<Evaluator.CountedResult> Evaluate() { starts++; return Value(); }
            var original = new NeedCell(Evaluate, () => new(Evaluate()),
                () => { projections++; return EvalResult<Algorithm?>.Ok(algorithm); }, span: span, budget: budget);
            var current = original;
            var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
            for (var hop = 0; hop < 100_000; hop++)
            {
                ctx = ctx.WithNeedEnv([("x", current)]);
                current = Evaluator.SupplyCell(new Expr.Param("x"), ctx, []);
                Assert.Same(original, current);
            }
            Assert.Equal(0, starts);
            Assert.Equal(0, budget.ConsumedSteps);
            Assert.Equal(0, budget.PeakDepth);
            Assert.Equal(span, current.Span);
            Assert.Same(algorithm, current.ProjectCallable().Value);
            Assert.Equal(0, starts);
            Assert.True(current.Demand().IsOk);
            Assert.True(current.DemandAsync().GetAwaiter().GetResult().IsOk);
            Assert.Equal(1, starts);
            Assert.Equal(1, projections);
            Assert.Equal(0, budget.ConsumedSteps);
        }, TimeSpan.FromSeconds(30));
    }

}
