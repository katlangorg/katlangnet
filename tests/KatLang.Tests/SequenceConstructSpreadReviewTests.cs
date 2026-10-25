using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

public class SequenceConstructSpreadReviewTests
{
    private static Expr Spread(Expr operand, int layers)
    {
        for (var i = 0; i < layers; i++) operand = new Expr.SequenceSpread(operand);
        return operand;
    }

    public static TheoryData<string, string, string, string> BoundaryCases => new()
    {
        { "7", "S[7, 3]", "S[7, 3]", "S[7, 3]" },
        { "true", "S[true, 3]", "S[true, 3]", "S[true, 3]" },
        { "()", "3", "3", "3" },
        { "[]", "3", "3", "3" },
        { "(1, 2)", "S[1, 2, 3]", "S[1, 2, 3]", "S[1, 2, 3]" },
        { "[1, 2]", "S[1, 2, 3]", "S[1, 2, 3]", "S[1, 2, 3]" },
        { "[[7]]", "S[L[7], 3]", "S[7, 3]", "S[7, 3]" },
        { "[[[7]]]", "S[L[L[7]], 3]", "S[L[7], 3]", "S[7, 3]" },
        { "[(1, 2)]", "S[S[1, 2], 3]", "S[1, 2, 3]", "S[1, 2, 3]" },
        { "[()]", "S[S[], 3]", "3", "3" },
        { "[[]]", "S[L[], 3]", "3", "3" },
        { "[[1, 2], [3, 4]]", "S[L[1, 2], L[3, 4], 3]", "S[L[1, 2], L[3, 4], 3]", "S[L[1, 2], L[3, 4], 3]" },
        { "((1, 2), 3)", "S[S[1, 2], 3, 3]", "S[S[1, 2], 3, 3]", "S[S[1, 2], 3, 3]" },
    };

    [Theory]
    [MemberData(nameof(BoundaryCases))]
    public async Task SpreadLeaf_EachLayerHasAnIndependentShapeOracle(
        string source, string first, string second, string third)
    {
        var operand = Assert.Single(SourceProvenance.ParseValid(source).Root.Output);
        var expected = new[] { first, second, third };
        for (var layers = 1; layers <= 3; layers++)
        {
            var leaf = Spread(operand, layers);
            var join = new Expr.SequenceConstruct(leaf, new Expr.Num(3));
            var capture = new Expr.Capture([leaf, new Expr.Num(3)]);
            var pinned = $"ok raw={expected[layers - 1]} n=1";
            Assert.Equal(pinned, AsyncEvaluationHarness.NeutralOf(Evaluator.RunCounted(join)));
            Assert.Equal(pinned, AsyncEvaluationHarness.NeutralOf(Evaluator.RunCounted(capture)));
            Assert.Equal(pinned, AsyncEvaluationHarness.NeutralOf(await AsyncEvaluationHarness.Complete(
                Evaluator.RunCountedAsync(join, new PassThroughAsyncZeroArgPropertyResultCache()))));
        }
    }

    [Theory]
    [InlineData(1, "S[L[L[7]], 3]", "S[L[L[7]], L[L[7]], 3]")]
    [InlineData(2, "S[L[7], 3]", "S[L[7], L[7], 3]")]
    [InlineData(3, "S[7, 3]", "S[7, 7, 3]")]
    public async Task SpreadLeaf_FreshOperandRunsOnceAcrossRealSuspension(
        int layers, string once, string twice)
    {
        // An explicit host call bypasses property caching. The second fixture writes the
        // same call twice and must perform two effects, so a cache hit cannot hide replay.
        var data = new Result.ListValue([new Result.ListValue([new Result.ListValue([new Result.Atom(7)])])]);
        foreach (var writtenCalls in new[] { 1, 2 })
        {
            var leaf = Spread(new Expr.Call(new Expr.Resolve("Pulse"), []), layers);
            Expr join = new Expr.SequenceConstruct(leaf, new Expr.Num(3));
            if (writtenCalls == 2) join = new Expr.SequenceConstruct(leaf, join);
            var pinned = $"ok raw={(writtenCalls == 1 ? once : twice)} n=1";
            var syncCalls = 0;
            var syncHost = HostOperations.Create(HostOperation.Create("Pulse", (_, _) =>
            {
                syncCalls++;
                return data;
            }));
            var (sync, syncBudget) = Evaluator.RunCountedObserved(join, hostOperations: syncHost);
            Assert.Equal(pinned, AsyncEvaluationHarness.NeutralOf(sync));
            Assert.Equal(writtenCalls, syncCalls);

            var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var asyncCalls = 0;
            var asyncHost = HostOperations.Create(HostOperation.CreateAsync("Pulse", async (_, _) =>
            {
                Interlocked.Increment(ref asyncCalls);
                reached.TrySetResult();
                await release.Task;
                return data;
            }));
            var pending = Evaluator.RunCountedObservedAsync(join, hostOperations: asyncHost).AsTask();
            try
            {
                await reached.Task.WaitAsync(TimeSpan.FromSeconds(45));
                Assert.False(pending.IsCompleted, "the spread operand must really suspend");
            }
            finally
            {
                release.TrySetResult();
            }
            var (asyncResult, asyncBudget) = await pending.WaitAsync(TimeSpan.FromSeconds(45));
            Assert.Equal(pinned, AsyncEvaluationHarness.NeutralOf(asyncResult));
            Assert.Equal(writtenCalls, asyncCalls);
            Assert.Equal(syncBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
            Assert.Equal(syncBudget.ConsumedExpressionCheckpoints, asyncBudget.ConsumedExpressionCheckpoints);
            Assert.Equal(syncBudget.MaterializedItems, asyncBudget.MaterializedItems);
            Assert.Equal(syncBudget.PeakDepth, asyncBudget.PeakDepth);
        }
    }

    [Fact]
    public async Task SpreadLeaf_OutputlessPropertyKeepsItsErrorAndOperandSpanAfterSuspension()
    {
        var operandSpan = new SourceSpan(4, 5, 4, 6);
        var leaf = new Expr.SequenceSpread(new Expr.Resolve("A") { Span = operandSpan })
            { Span = new SourceSpan(4, 5, 4, 7) };
        var empty = new Algorithm.User(null, [], [], [new Property("Unused", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))], []);
        Expr Root(Expr row) => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("A", empty)], [row]));
        var join = Root(new Expr.SequenceConstruct(leaf, new Expr.Num(3)));
        var written = Evaluator.RunCounted(Root(new Expr.Capture([leaf, new Expr.Num(3)])));
        var sync = Evaluator.RunCounted(join);
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var asyncResult = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(join, cache));
        foreach (var outcome in new[] { written, sync, asyncResult })
        {
            Assert.True(outcome.IsError);
            var error = outcome.Error;
            while (error is EvalError.WithContext context) error = context.Inner;
            Assert.IsType<EvalError.SpreadMissingOutput>(error);
            Assert.Equal(operandSpan, outcome.Error.Span);
        }
        Assert.Equal(1, cache.AsyncAccesses);
        Assert.Equal(0, cache.SyncAccesses);
        Assert.Single(cache.ThreadHops);
    }

    [Theory]
    [InlineData("[()]", "S[S[], 3]", 3)]
    [InlineData("[[7]]", "S[L[7], 3]", 4)]
    public async Task SpreadLeaf_ReservationCountsTheSuppliedItemsExactly(string source, string expected, long items)
    {
        // Operand list: 1 slot; nested list, if present: 1; join: 2. A lone
        // spread item creates no sequence. These independent totals detect over/undercharge.
        var operand = Assert.Single(SourceProvenance.ParseValid(source).Root.Output);
        var join = new Expr.SequenceConstruct(new Expr.SequenceSpread(operand), new Expr.Num(3));
        foreach (var cap in new[] { items - 1, items })
        {
            var limit = new EvaluationLimits { MaxMaterializedItems = cap };
            var (sync, budget) = Evaluator.RunCountedObserved(join, limit);
            var (asyncResult, asyncBudget) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                join, limit, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));
            Assert.True((cap < items) == sync.IsError,
                $"cap={cap}, materialized={budget.MaterializedItems}, outcome={AsyncEvaluationHarness.NeutralOf(sync)}");
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(asyncResult));
            Assert.Equal(budget.MaterializedItems, asyncBudget.MaterializedItems);
            Assert.Equal(budget.ConsumedSteps, asyncBudget.ConsumedSteps);
            Assert.Equal(budget.ConsumedExpressionCheckpoints, asyncBudget.ConsumedExpressionCheckpoints);
            if (sync.IsOk)
            {
                Assert.Equal($"ok raw={expected} n=1", AsyncEvaluationHarness.NeutralOf(sync));
                Assert.Equal(items, budget.MaterializedItems);
            }
            else Assert.Equal(KatLangErrorCode.MaterializationLimitExceeded, sync.Error.Code);
        }
    }

    [Fact]
    public void StackedAndGroupedSpreadAgreeInValueButCanDifferUnderAResourceLimit()
    {
        var operand = new Expr.ListLiteral([new Expr.Num(1), new Expr.Num(2)]);
        var inner = new Expr.SequenceSpread(operand);
        var stacked = new Expr.SequenceSpread(inner);
        var grouped = new Expr.SequenceSpread(new Expr.Capture([inner]));
        var (a, aBudget) = Evaluator.RunCountedObserved(stacked);
        var (b, bBudget) = Evaluator.RunCountedObserved(grouped);
        Assert.Equal("ok raw=S[1, 2] n=2", AsyncEvaluationHarness.NeutralOf(a));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(a), AsyncEvaluationHarness.NeutralOf(b));
        // List: 2; each spread capture: 2; the grouped spelling's extra capture: 2.
        Assert.Equal(6, aBudget.MaterializedItems);
        Assert.Equal(8, bBudget.MaterializedItems);
        var cap = new EvaluationLimits { MaxMaterializedItems = 6 };
        Assert.True(Evaluator.RunCountedObserved(stacked, cap).Result.IsOk);
        var limited = Evaluator.RunCountedObserved(grouped, cap).Result;
        Assert.True(limited.IsError);
        Assert.Equal(KatLangErrorCode.MaterializationLimitExceeded, limited.Error.Code);
    }
}
