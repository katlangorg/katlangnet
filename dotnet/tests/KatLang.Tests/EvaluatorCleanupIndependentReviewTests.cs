using System.Collections.Concurrent;
using KatLang.Evaluation;
using KatLang.Formatting;

namespace KatLang.Tests;

/// <summary>Independent probes of the October 2026 cleanup's graph and input-ownership boundaries.</summary>
public sealed class EvaluatorCleanupIndependentReviewTests
{
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);
    private static TaskCompletionSource Signal() => new(TaskCreationOptions.RunContinuationsAsynchronously);
    private static EvalResult<Evaluator.CountedResult> Value(int number = 7)
        => EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom(number), 1));

    [Fact]
    public async Task DiamondAndDuplicateWaitEdges_AreReferenceCountedAndCleaned()
    {
        var budget = EvaluationBudget.Create(null);
        var release = Signal();
        var entered = Signal();
        var starts = 0;
        var leaf = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            Interlocked.Increment(ref starts);
            await release.Task;
            return Value();
        }, budget: budget);
        var left = new NeedCell(() => throw new InvalidOperationException(), () => leaf.DemandAsync(), budget: budget);
        var right = new NeedCell(() => throw new InvalidOperationException(), () => leaf.DemandAsync(), budget: budget);
        NeedCell? parent = null;
        parent = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            // Two active demand frames for left produce one distinct edge with multiplicity two.
            var first = left.DemandAsync().AsTask();
            var duplicate = left.DemandAsync().AsTask();
            var other = right.DemandAsync().AsTask();
            Assert.Equal(2, parent!.ActiveDependencyCount);
            Assert.Equal(1, left.ActiveDependencyCount);
            Assert.Equal(1, right.ActiveDependencyCount);
            entered.SetResult();
            var results = await Task.WhenAll(first, duplicate, other);
            Assert.All(results, result => Assert.True(result.IsOk));
            return results[0];
        }, budget: budget);
        var demand = parent.DemandAsync().AsTask();
        try
        {
            await entered.Task.WaitAsync(WaitLimit);
            Assert.Equal(1, starts);
        }
        finally { release.TrySetResult(); }
        var failure = await Record.ExceptionAsync(async () => Assert.True((await demand.WaitAsync(WaitLimit)).IsOk));
        Assert.Null(failure);
        Assert.All(new[] { parent, left, right, leaf }, cell => Assert.Equal(0, cell.ActiveDependencyCount));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task BudgetlessGraph_DetectsAnOverlappingCycleAndRemovesAllEdges(bool suspend)
    {
        var entered = Signal();
        var starts = 0;
        NeedCell? left = null, right = null;
        async ValueTask<EvalResult<Evaluator.CountedResult>> Evaluate(Func<NeedCell> next)
        {
            if (Interlocked.Increment(ref starts) == 2) entered.SetResult();
            await entered.Task;
            if (suspend) await Task.Yield();
            return await next().DemandAsync();
        }
        left = new NeedCell(() => right!.Demand(), () => Evaluate(() => right!));
        right = new NeedCell(() => left.Demand(), () => Evaluate(() => left));
        var outcomes = await Task.WhenAll(left.DemandAsync().AsTask(), right.DemandAsync().AsTask()).WaitAsync(WaitLimit);
        Assert.All(outcomes, outcome => Assert.Equal(KatLangErrorCode.DemandCycle, outcome.Error.Code));
        Assert.Equal(0, left.ActiveDependencyCount);
        Assert.Equal(0, right.ActiveDependencyCount);
        Assert.Equal(KatLangErrorCode.DemandCycle, left.Demand().Error.Code);
    }

    [Theory]
    [InlineData("failure")]
    [InlineData("exception")]
    [InlineData("cancellation")]
    public async Task NestedBudgetExit_RestoresTheOuterParentBeforeItsNextDemand(string exit)
    {
        var outerBudget = EvaluationBudget.Create(null);
        var innerBudget = EvaluationBudget.Create(null);
        NeedCell? outer = null;
        var nestedEdges = -1;
        var outerEdges = -1;
        var inner = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            await Task.Yield();
            nestedEdges = outer!.ActiveDependencyCount;
            return exit switch
            {
                "failure" => new EvalError.DivByZero(),
                "exception" => throw new InvalidOperationException("nested"),
                "cancellation" => throw new OperationCanceledException("nested"),
                _ => throw new ArgumentOutOfRangeException(nameof(exit)),
            };
        }, budget: innerBudget);
        var next = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            await Task.Yield();
            outerEdges = outer!.ActiveDependencyCount;
            return Value();
        }, budget: outerBudget);
        outer = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            if (exit == "failure")
                Assert.Equal(KatLangErrorCode.DivisionByZero, (await inner.DemandAsync()).Error.Code);
            else if (exit == "exception")
                await Assert.ThrowsAsync<InvalidOperationException>(async () => await inner.DemandAsync());
            else
                await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await inner.DemandAsync());
            Assert.Equal(0, outer!.ActiveDependencyCount);
            return await next.DemandAsync();
        }, budget: outerBudget);
        Assert.True((await outer.DemandAsync().AsTask().WaitAsync(WaitLimit)).IsOk);
        Assert.Equal(0, nestedEdges);
        Assert.Equal(1, outerEdges);
        Assert.All(new[] { outer, inner, next }, cell => Assert.Equal(0, cell.ActiveDependencyCount));
    }

    [Theory]
    [InlineData(false, "success")]
    [InlineData(true, "success")]
    [InlineData(false, "failure")]
    [InlineData(true, "failure")]
    [InlineData(false, "cancellation")]
    [InlineData(true, "cancellation")]
    public async Task SuspendedNestedHostRuns_KeepFailureCancellationAndRecursiveRunsIndependent(bool threadPool, string exit)
    {
        var calls = new ConcurrentQueue<string>();
        using var cancelled = new CancellationTokenSource();
        var innerOperations = HostOperations.Create(HostOperation.CreateAsync("pause", async (_, token) =>
        {
            await Task.Yield();
            calls.Enqueue("inner");
            if (exit == "cancellation") { cancelled.Cancel(); token.ThrowIfCancellationRequested(); }
            return new Result.Atom(3);
        }));
        var innerOptions = new RunOptions { HostOperations = innerOperations, EvaluationCancellationToken = cancelled.Token };
        async ValueTask<Result> Nested()
        {
            await Task.Yield();
            if (exit == "cancellation")
            {
                var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
                    await KatLangEngine.RunAsync("F(x) = x\nF(pause())", innerOptions));
                Assert.Equal(cancelled.Token, error.CancellationToken);
                return new Result.Atom(4);
            }
            var inner = await KatLangEngine.RunAsync(exit == "failure"
                ? "F(x) = x / 0\nF(pause())" : "F(x) = x + x\nF(pause())", innerOptions);
            if (exit == "failure")
                Assert.Equal(KatLangErrorCode.DivisionByZero, Assert.Single(Assert.IsType<RunResult.EvalFailure>(inner).Errors).Code);
            else
                Assert.Equal("6", OutputFormatters.Exact.Format(Assert.IsType<RunResult.Success>(inner)));
            // A third evaluator run inherits the nested host's execution context after suspension.
            var recursiveOperations = HostOperations.Create(HostOperation.CreateAsync("again", async (_, _) =>
            {
                await Task.Yield();
                var third = await KatLangEngine.RunAsync("H(x) = x + x\nH(5)");
                return Assert.IsType<RunResult.Success>(third).Value;
            }));
            var recursive = await KatLangEngine.RunAsync("G(x) = x + 1\nG(again())", new RunOptions { HostOperations = recursiveOperations });
            Assert.Equal("11", OutputFormatters.Exact.Format(Assert.IsType<RunResult.Success>(recursive)));
            return new Result.Atom(4);
        }
        var outerOperations = HostOperations.Create(HostOperation.CreateAsync("nested", async (_, _) =>
        {
            calls.Enqueue("outer");
            return threadPool ? await Task.Run(async () => await Nested()) : await Nested();
        }));
        var outer = await KatLangEngine.RunAsync("Twice(x) = x + x\nTwice(nested())", new RunOptions { HostOperations = outerOperations })
            .WaitAsync(WaitLimit);
        Assert.Equal("8", OutputFormatters.Exact.Format(Assert.IsType<RunResult.Success>(outer)));
        Assert.Equal(new[] { "outer", "inner" }, calls.ToArray());
    }

    [Fact]
    public async Task SharedPreparedAstAndHostConfiguration_CreateFreshCellsForEveryRun()
    {
        var entered = Signal();
        var release = Signal();
        const int runs = 12;
        var starts = 0;
        var operations = HostOperations.Create(HostOperation.CreateAsync("pause", async (args, _) =>
        {
            if (Interlocked.Increment(ref starts) == runs) entered.SetResult();
            await release.Task;
            return args[0];
        }, "x"));
        var parsed = await SourceProvenance.ParseValidAsync("F(x) = x + x + x\nF(pause(7))", new RunOptions { HostOperations = operations });
        var root = new Expr.AlgorithmExpr(parsed.Root);
        var tasks = Enumerable.Range(0, runs).Select(_ => Evaluator.RunAsync(root, operations, null, 7, CancellationToken.None)).ToArray();
        try { await entered.Task.WaitAsync(WaitLimit); }
        finally { release.TrySetResult(); }
        var results = await Task.WhenAll(tasks).WaitAsync(WaitLimit);
        Assert.All(results, result => { Assert.True(result.IsOk); Assert.Equal(new Result.Atom(21), result.Value); });
        Assert.Equal(runs, starts);
        Assert.Equal(new Result.Atom(21), (await Evaluator.RunAsync(root, operations, null, 7, CancellationToken.None)).Value);
        Assert.Equal(runs + 1, starts);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task HostSharedPatternNodes_KeepRepeatedNameInspectionAndTheirPatternKind(bool structural, bool mismatch)
    {
        var parsed = SourceProvenance.ParseValid(structural
            ? $"F([x, y], [x, y], [x, y]) = x + y\nF([2, 3], [2, 3], [2, {(mismatch ? 4 : 3)}])"
            : $"F(x, x, x) = x\nF(2, 2, {(mismatch ? 3 : 2)})").Root;
        var property = Assert.Single(parsed.Properties, property => property.Name == "F");
        var algorithm = Assert.IsType<Algorithm.User>(property.Value);
        var shared = algorithm.ParameterPatterns[0];
        var root = new Expr.AlgorithmExpr(parsed with
        {
            Properties = parsed.Properties.Select(p => p == property
                ? p with { Value = algorithm with { ParameterPatterns = new[] { shared, shared, shared } } } : p).ToArray(),
        });
        var sync = Evaluator.Run(root);
        var asyncResult = await Evaluator.RunAsync(root);
        if (mismatch)
        {
            Assert.Equal(KatLangErrorCode.ArityMismatch, sync.Error.Code);
            var syncError = KatLangError.FromEvalError(sync.Error);
            var asyncError = KatLangError.FromEvalError(asyncResult.Error);
            Assert.Equal((syncError.Code, syncError.Message, syncError.Span), (asyncError.Code, asyncError.Message, asyncError.Span));
        }
        else
        {
            Assert.True(sync.IsOk);
            Assert.Equal(new Result.Atom(structural ? 5 : 2), sync.Value);
            Assert.Equal(sync.Value, asyncResult.Value);
        }
    }
}
