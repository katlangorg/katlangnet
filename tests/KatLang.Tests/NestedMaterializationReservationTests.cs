using KatLang.Evaluation;
using KatLang.Tests.AsyncEvaluation;
using Xunit.Abstractions;
using CountedResult = KatLang.Evaluator.CountedResult;

namespace KatLang.Tests;

public class NestedMaterializationReservationTests(ITestOutputHelper output)
{
    // Independently derived immediate construction totals, not a comparison between twins.
    // S = sequence; L = exact list. A nested value occupies ONE parent item.
    public static TheoryData<string, string, long> Cases => new()
    {
        { "()", "S[]", 0 }, { "(1)", "1", 0 }, { "(())", "S[]", 0 },
        { "[]", "L[]", 0 }, { "(1,2)", "S[1, 2]", 2 }, { "((1,2))", "S[1, 2]", 2 },
        { "[()]", "L[S[]]", 1 }, { "[(1)]", "L[1]", 1 }, { "[(1,2)]", "L[S[1, 2]]", 3 },
        { "[[]]", "L[L[]]", 1 }, { "[[1]]", "L[L[1]]", 2 }, { "[[1,2]]", "L[L[1, 2]]", 3 },
        { "((1,2),3)", "S[S[1, 2], 3]", 4 },
        { "[((1,2),3)]", "L[S[S[1, 2], 3]]", 5 },
        { "([1,2],3)", "S[L[1, 2], 3]", 4 },
        { "[([1,2],3)]", "L[S[L[1, 2], 3]]", 5 },
        { "[[(1,2)]]", "L[L[S[1, 2]]]", 4 },
        { "[{1,2}]", "L[S[1, 2]]", 3 },
        { "[{(1,2),3}]", "L[S[S[1, 2], 3]]", 5 },
        { "[{(1,2)}]", "L[S[1, 2]]", 3 },
        { "[(),()]", "L[S[], S[]]", 2 },
        // two immediate () items are two stored slots, though neither has a payload
        { "((),())", "S[S[], S[]]", 2 }, { "[((),())]", "L[S[S[], S[]]]", 3 },
        { "A=1,2,3\n[A*]", "L[1, 2, 3]", 9 },
        { "A=1,2,3\n[(A*)]", "L[S[1, 2, 3]]", 10 },
        { "A=1,2,3\n[(A*,4)]", "L[S[1, 2, 3, 4]]", 11 },
        { "[(()*)]", "L[S[]]", 1 },
        { "[(()*,1)]", "L[1]", 1 },
        { "[([]*)]", "L[S[]]", 1 },
        { "A=[7]\n[(A*)]", "L[7]", 2 },
        { "P=(1,2)\n[P,P]", "L[S[1, 2], S[1, 2]]", 4 }, // cached child reused, parent 2
        { "P=(1,2)\n[P(),P()]", "L[S[1, 2], S[1, 2]]", 6 }, // two fresh captures + parent 2
        // input list + callback construction(s) + map's output list
        { "Pair(x)=x,x\nmap([1,2],Pair)", "L[S[1, 1], S[2, 2]]", 8 },
        { "Pair(x)=[(x,x)]\nmap([1,2],Pair)", "L[L[S[1, 1]], L[S[2, 2]]]", 10 },
        // input list 2 + two callback constructions of sequence 2/list 1
        { "R(x,acc)=[(x,acc)]\nreduce([1,2],R,0)", "L[S[2, L[S[1, 0]]]]", 8 },
        // two steps each capture 2/list 1; singleton final state reuses its value
        { "Step(x)=[(x,x)]\nrepeat(Step(1), 2)", "L[S[L[S[1, 1]], L[S[1, 1]]]]", 6 },
        // two captures 2 each + list 2 + selection sequence 2
        { "[(1,2),(3,4)][1,0]", "S[S[3, 4], S[1, 2]]", 8 },
    };

    private static Expr Ast(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
    private static Expr Root(Expr row) => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [row]));

    private static Expr Gated(Expr ast)
    {
        var root = Assert.IsType<Expr.AlgorithmExpr>(ast).Algorithm;
        var user = Assert.IsType<Algorithm.User>(root);
        return new Expr.AlgorithmExpr(user with
        {
            Output = [new Expr.Call(new Expr.Resolve("if"),
                [new Expr.Call(new Expr.Resolve("Gate"), []), Assert.Single(root.Output), new Expr.Num(0)])]
        });
    }

    private void Observe(string source, string route, EvalResult<CountedResult> result, EvaluationBudget budget)
        => output.WriteLine("OBS " + System.Text.Json.JsonSerializer.Serialize(new
        {
            source, route, result = AsyncEvaluationHarness.NeutralOf(result),
            budget.MaterializedItems, budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth
        }));

    private static void AssertSuccess(EvalResult<CountedResult> result, EvaluationBudget budget, string shape, long items)
    {
        Assert.Equal($"ok raw={shape} n=1", AsyncEvaluationHarness.NeutralOf(result));
        Assert.Equal(items, budget.MaterializedItems);
        Assert.Equal(0, budget.CurrentDepth);
    }

    public static IEnumerable<object[]> SyncCases =>
        Cases.SelectMany(row => new[] { false, true }.Select(optimized => new[] { row[0], row[1], row[2], optimized }));

    [Theory]
    [MemberData(nameof(SyncCases))]
    public void ImmediateBoundaries_SyncThresholds(string source, string shape, long items, bool optimized)
    {
        var ast = Ast(source);
        var (result, budget) = Evaluator.RunCountedObserved(ast, enableOptimizations: optimized);
        Observe(source, optimized ? "optimized" : "generic", result, budget);
        AssertSuccess(result, budget, shape, items);
        var limits = new EvaluationLimits { MaxMaterializedItems = Math.Max(1, items) };
        var exact = Evaluator.RunCountedObserved(ast, limits, enableOptimizations: optimized);
        AssertSuccess(exact.Result, exact.Budget, shape, items);
        if (items < 2) return;
        var below = Evaluator.RunCountedObserved(ast, limits with { MaxMaterializedItems = items - 1 }, enableOptimizations: optimized);
        Assert.True(below.Result.IsError);
        Assert.IsType<EvalError.MaterializationLimitExceeded>(below.Result.Error);
    }

    private static async Task<(EvalResult<CountedResult> Result, EvaluationBudget Budget)> Suspended(Expr ast, EvaluationLimits? limits)
    {
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var host = HostOperations.Create(HostOperation.CreateAsync("Gate", async (_, _) =>
        {
            Interlocked.Increment(ref calls);
            reached.TrySetResult();
            await release.Task;
            return new Result.Bool(true);
        }));
        var pending = Evaluator.RunCountedObservedAsync(ast, limits, hostOperations: host).AsTask();
        try
        {
            await reached.Task.WaitAsync(TimeSpan.FromSeconds(45));
            Assert.False(pending.IsCompleted, "the async evaluator must genuinely suspend");
        }
        finally { release.TrySetResult(); }
        var result = await pending.WaitAsync(TimeSpan.FromSeconds(45));
        Assert.Equal(1, calls);
        return result;
    }

    [Theory]
    [MemberData(nameof(Cases))]
    public async Task ImmediateBoundaries_RealSuspensionThresholdsAndWorkParity(string source, string shape, long items)
    {
        var ast = Gated(Ast(source));
        var syncHost = HostOperations.Create(HostOperation.Create("Gate", (_, _) => new Result.Bool(true)));
        foreach (var limit in items < 2 ? new[] { Math.Max(1, items) } : new[] { items, items - 1 })
        {
            var limits = new EvaluationLimits { MaxMaterializedItems = limit };
            var sync = Evaluator.RunCountedObserved(ast, limits, hostOperations: syncHost);
            var twin = await Suspended(ast, limits);
            Observe(source, $"suspended-{limit}", twin.Result, twin.Budget);
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync.Result), AsyncEvaluationHarness.NeutralOf(twin.Result));
            Assert.Equal(sync.Budget.MaterializedItems, twin.Budget.MaterializedItems);
            Assert.Equal(sync.Budget.ConsumedSteps, twin.Budget.ConsumedSteps);
            Assert.Equal(sync.Budget.ConsumedExpressionCheckpoints, twin.Budget.ConsumedExpressionCheckpoints);
            Assert.Equal(sync.Budget.PeakDepth, twin.Budget.PeakDepth);
            if (limit >= items) AssertSuccess(twin.Result, twin.Budget, shape, items);
            else
            {
                Assert.True(twin.Result.IsError);
                Assert.IsType<EvalError.MaterializationLimitExceeded>(twin.Result.Error);
            }
        }
    }

    [Theory]
    [InlineData("[(1,2)]", 3)]
    [InlineData("[{1,2}]", 3)]
    [InlineData("[((1,2),3)]", 5)]
    public void PublicEngine_EnforcesNestedReservation(string source, long items)
    {
        Assert.IsType<RunResult.Success>(KatLangEngine.Run(source,
            new RunOptions { EvaluationLimits = new() { MaxMaterializedItems = items } }));
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source,
            new RunOptions { EvaluationLimits = new() { MaxMaterializedItems = items - 1 } }));
        Assert.Equal(KatLangErrorCode.MaterializationLimitExceeded, Assert.Single(failure.Errors).Code);
    }

    [Theory]
    [InlineData("empty", "L[S[]]", 1)]
    [InlineData("singleton", "L[7]", 1)]
    [InlineData("singleton-nested", "L[S[1, 2]]", 3)]
    [InlineData("empty-slots", "L[S[S[], S[]]]", 3)]
    [InlineData("singleton-list", "L[L[1, 2]]", 3)]
    [InlineData("join", "S[S[1, 2], 3]", 5)]
    public async Task HostBuiltBoundaries_UseActualSlotsAndKeepNestedValues(string kind, string shape, long items)
    {
        var pair = new Expr.Capture([new Expr.Num(1), new Expr.Num(2)]);
        Expr row = kind switch
        {
            "empty" => new Expr.ListLiteral([new Expr.Capture([])]),
            "singleton" => new Expr.ListLiteral([new Expr.Capture([new Expr.Num(7)])]),
            "singleton-nested" => new Expr.ListLiteral([new Expr.Capture([pair])]),
            "empty-slots" => new Expr.ListLiteral([new Expr.Capture([new Expr.EmptySequence(0), new Expr.EmptySequence(0)])]),
            "singleton-list" => new Expr.ListLiteral([new Expr.Capture([new Expr.ListLiteral([new Expr.Num(1), new Expr.Num(2)])])]),
            "join" => new Expr.SequenceConstruct(new Expr.SequenceSpread(new Expr.ListLiteral([pair])), new Expr.Num(3)),
            _ => throw new ArgumentOutOfRangeException(nameof(kind))
        };
        var ast = Root(row);
        foreach (var optimized in new[] { false, true })
        {
            var exact = Evaluator.RunCountedObserved(ast, new() { MaxMaterializedItems = items }, enableOptimizations: optimized);
            AssertSuccess(exact.Result, exact.Budget, shape, items);
            if (items >= 2)
            {
                var below = Evaluator.RunCountedObserved(ast, new() { MaxMaterializedItems = items - 1 }, enableOptimizations: optimized);
                Assert.True(below.Result.IsError);
                Assert.IsType<EvalError.MaterializationLimitExceeded>(below.Result.Error);
            }
        }
        var gated = Gated(ast);
        var twin = await Suspended(gated, new() { MaxMaterializedItems = items });
        AssertSuccess(twin.Result, twin.Budget, shape, items);
        if (items >= 2)
        {
            var below = await Suspended(gated, new() { MaxMaterializedItems = items - 1 });
            Assert.True(below.Result.IsError);
            Assert.IsType<EvalError.MaterializationLimitExceeded>(below.Result.Error);
        }
    }

    [Theory]
    [InlineData("capture")]
    [InlineData("block")]
    public async Task HostBuiltUnfoldedRefusal_IsPositionedLikeTheOrdinaryRoute(string kind)
    {
        // Only the element node is positioned (its rows are not), so a refused reservation
        // takes its span from the unfolded arm's own rule, which must be the ordinary
        // dispatch's for the same node: the element's span, in both twins.
        var span = new SourceSpan(2, 5, 2, 12);
        Expr Element() => kind == "capture"
            ? new Expr.Capture([new Expr.Num(1), new Expr.Num(2)]) { Span = span }
            : new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [new Expr.Num(1), new Expr.Num(2)])) { Span = span };
        var limits = new EvaluationLimits { MaxCollectionItems = 1 };
        var ordinary = Evaluator.RunCountedObserved(Root(new Expr.Capture([Element(), new Expr.Num(3)])), limits);
        var unfolded = Evaluator.RunCountedObserved(Root(new Expr.ListLiteral([Element()])), limits);
        var twin = await Suspended(Gated(Root(new Expr.ListLiteral([Element()]))), limits);
        foreach (var outcome in new[] { ordinary, unfolded, twin })
        {
            var error = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(outcome.Result.Error);
            Assert.Equal(2, error.Requested);
            Assert.Equal(span, error.Span);
            Assert.Equal(0, outcome.Budget.MaterializedItems);
        }
    }

    [Theory]
    [InlineData("[(1,1/0)]", 0)]
    [InlineData("[{1,1/0}]", 0)]
    [InlineData("[(1,2),1/0]", 2)]
    [InlineData("[{(1,2),1/0}]", 2)]
    public async Task FailedSupply_IsNotReservedAndCompletedChildrenAreNotRefunded(string source, long completedItems)
    {
        // A failing child's incomplete supply is never reserved. Previously completed
        // siblings retain their own reservations even though their parent never finishes.
        var ast = Ast(source);
        var limits = new EvaluationLimits { MaxMaterializedItems = completedItems == 0 ? 1 : 10, MaxCollectionItems = completedItems == 0 ? 1 : 10 };
        var sync = Evaluator.RunCountedObserved(ast, limits);
        var twin = await Suspended(Gated(ast), limits);
        foreach (var outcome in new[] { sync, twin })
        {
            Assert.True(outcome.Result.IsError);
            Assert.Equal(KatLangErrorCode.DivisionByZero, outcome.Result.Error.Code);
            Assert.Equal(completedItems, outcome.Budget.MaterializedItems);
            Assert.Equal(0, outcome.Budget.CurrentDepth);
        }
        Assert.Equal(sync.Result.Error.Span, twin.Result.Error.Span);
    }

    [Theory]
    [InlineData("[(1,2),1/0]")]
    [InlineData("[{1,2},1/0]")]
    public async Task CompletedInnerReservation_PrecedesLaterFailureAndKeepsFirstRowSpan(string source)
    {
        var ast = Ast(source);
        var limits = new EvaluationLimits { MaxCollectionItems = 1 };
        var sync = Evaluator.RunCountedObserved(ast, limits);
        var twin = await Suspended(Gated(ast), limits);
        foreach (var outcome in new[] { sync, twin })
        {
            Assert.True(outcome.Result.IsError);
            var error = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(outcome.Result.Error);
            Assert.Equal(2, error.Requested);
            Assert.Equal(new SourceSpan(1, 3, 1, 4), error.Span);
            Assert.Equal(0, outcome.Budget.MaterializedItems); // refused reservation mutates nothing
            Assert.Equal(0, outcome.Budget.CurrentDepth);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task SuspensionAfterCompletedChild_ReservesEachBoundaryOnceAndConservesOnCancellation(bool cancel)
    {
        var cache = new HoldingAsyncZeroArgPropertyResultCache(holdAtAccess: 1);
        using var cancellation = new CancellationTokenSource();
        var pending = Evaluator.RunCountedObservedAsync(Ast("P=0\n[(1,2),P]"),
            zeroArgPropertyResultCache: cache, cancellationToken: cancellation.Token).AsTask();
        try
        {
            await cache.Reached.WaitAsync(TimeSpan.FromSeconds(45));
            Assert.False(pending.IsCompleted);
            Assert.Equal(2, cache.ObservedBudget!.MaterializedItems);
            if (cancel) cancellation.Cancel();
        }
        finally { cache.Release(); }
        if (cancel)
        {
            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await pending.WaitAsync(TimeSpan.FromSeconds(45)));
            Assert.Equal(cancellation.Token, thrown.CancellationToken);
            Assert.Equal(2, cache.ObservedBudget!.MaterializedItems);
        }
        else
        {
            var completed = await pending.WaitAsync(TimeSpan.FromSeconds(45));
            AssertSuccess(completed.Result, completed.Budget, "L[S[1, 2], 0]", 4);
        }
        Assert.Equal(0, cache.ObservedBudget.CurrentDepth);
        Assert.Equal(1, cache.AsyncAccesses);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task NestedChildEffects_RunOnceBeforeReservationAndLaterElementsWait(bool rejectInner)
    {
        Expr Call(string name) => new Expr.Call(new Expr.Resolve(name), []);
        var ast = Root(new Expr.ListLiteral([new Expr.Capture([Call("Pulse"), new Expr.Num(2)]), Call("Later")]));
        var limits = new EvaluationLimits { MaxCollectionItems = rejectInner ? 1 : 10 };
        var syncTrace = new List<string>();
        var syncHost = HostOperations.Create(
            HostOperation.Create("Pulse", (_, _) => { syncTrace.Add("Pulse"); return new Result.Atom(7); }),
            HostOperation.Create("Later", (_, _) => { syncTrace.Add("Later"); return new Result.Atom(9); }));
        var sync = Evaluator.RunCountedObserved(ast, limits, hostOperations: syncHost);
        var trace = new List<string>();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var asyncHost = HostOperations.Create(
            HostOperation.CreateAsync("Pulse", async (_, _) =>
            {
                trace.Add("Pulse"); reached.TrySetResult(); await release.Task;
                return new Result.Atom(7);
            }),
            HostOperation.Create("Later", (_, _) => { trace.Add("Later"); return new Result.Atom(9); }));
        var pending = Evaluator.RunCountedObservedAsync(ast, limits, hostOperations: asyncHost).AsTask();
        try
        {
            await reached.Task.WaitAsync(TimeSpan.FromSeconds(45));
            Assert.False(pending.IsCompleted);
            Assert.Equal(new[] { "Pulse" }, trace);
        }
        finally { release.TrySetResult(); }
        var twin = await pending.WaitAsync(TimeSpan.FromSeconds(45));
        Assert.Equal(rejectInner ? new[] { "Pulse" } : new[] { "Pulse", "Later" }, trace);
        Assert.Equal(syncTrace, trace);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync.Result), AsyncEvaluationHarness.NeutralOf(twin.Result));
        Assert.Equal(sync.Budget.MaterializedItems, twin.Budget.MaterializedItems);
        Assert.Equal(sync.Budget.ConsumedSteps, twin.Budget.ConsumedSteps);
        Assert.Equal(sync.Budget.ConsumedExpressionCheckpoints, twin.Budget.ConsumedExpressionCheckpoints);
        Assert.Equal(sync.Budget.PeakDepth, twin.Budget.PeakDepth);
        if (rejectInner)
        {
            Assert.IsType<EvalError.CollectionSizeLimitExceeded>(twin.Result.Error);
            Assert.Equal(0, twin.Budget.MaterializedItems);
        }
        else AssertSuccess(twin.Result, twin.Budget, "L[S[7, 2], 9]", 4);
    }

    [Fact]
    public async Task PlannedLoop_RuntimeCallbackConstructionKeepsItsOwnReservations()
    {
        // Each iteration: input list 1 + callback sequence 2/list 1 = 4.
        // The completed singleton loop state reuses its already materialized value.
        const string source = "R(x,acc)=[(x,acc)]\nStep(s)=reduce([s],R,0)\nrepeat(Step(5), 2)";
        const string shape = "L[S[L[S[5, 0]], 0]]";
        var ast = Ast(source);
        var diagnostics = new KatLang.Optimizations.Loops.LoopOptimizationDiagnostics();
        var planned = Evaluator.RunCountedObserved(ast, new() { MaxMaterializedItems = 8 }, loopDiagnostics: diagnostics);
        AssertSuccess(planned.Result, planned.Budget, shape, 8);
        Assert.True(diagnostics.OptimizedLoopHits > 0, "must execute the planned route, not merely enable it");
        var generic = Evaluator.RunCountedObserved(ast, new() { MaxMaterializedItems = 8 }, enableOptimizations: false);
        AssertSuccess(generic.Result, generic.Budget, shape, 8);
        Assert.Equal(generic.Budget.ConsumedSteps, planned.Budget.ConsumedSteps);
        Assert.Equal(generic.Budget.ConsumedExpressionCheckpoints, planned.Budget.ConsumedExpressionCheckpoints);
        Assert.Equal(generic.Budget.PeakDepth, planned.Budget.PeakDepth);
        foreach (var optimized in new[] { false, true })
        {
            var below = Evaluator.RunCountedObserved(ast, new() { MaxMaterializedItems = 7 }, enableOptimizations: optimized);
            Assert.Equal(KatLangErrorCode.MaterializationLimitExceeded, below.Result.Error.Code);
        }
        var twin = await Suspended(Gated(ast), new() { MaxMaterializedItems = 8 });
        AssertSuccess(twin.Result, twin.Budget, shape, 8);
        var rejectedTwin = await Suspended(Gated(ast), new() { MaxMaterializedItems = 7 });
        Assert.Equal(KatLangErrorCode.MaterializationLimitExceeded, rejectedTwin.Result.Error.Code);
    }
}
