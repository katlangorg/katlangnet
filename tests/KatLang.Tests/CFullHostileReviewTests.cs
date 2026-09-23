using KatLang.Optimizations.Sequences;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>Independent C-full review probes, with hand-written supply expectations.</summary>
public class CFullHostileReviewTests
{
    private static readonly string[] Values =
        ["1", "()", "[]", "(1, 2)", "[1, 2]", "((1, 2), 3)", "[[1, 2], 3]", "[(1, 2)]", "[()]"];

    public static TheoryData<string, int, string> FlatCallbackRejections()
    {
        var cells = new TheoryData<string, int, string>();
        foreach (var value in Values)
        foreach (var (pattern, required) in new[]
        {
            ("a, b, c", 3), ("a, *xs, b", 2), ("(a, b), c", 2), ("a, (b, c)", 2),
        })
            cells.Add(pattern, required, value);
        return cells;
    }

    [Theory]
    [MemberData(nameof(FlatCallbackRejections))]
    public async Task CallbackArity_CountsElementsBeforeAnyPatternOpening(string pattern, int required, string value)
    {
        var defs = $"F({pattern}) = true\nAlias = F\nApply(f, xs) = map(xs, f)\nForward(g, xs) = Apply(g, xs)\n";
        foreach (var direct in new[] { $"F({value})", $"({value}).F" })
        {
            var error = RootError(await AcrossStrategies(defs + direct));
            if (error is EvalError.VariadicArityMismatch variadic)
            {
                Assert.Equal(required, variadic.ExpectedMinimum);
                Assert.Equal(1, variadic.Actual);
            }
            else
            {
                var fixedError = Assert.IsType<EvalError.ArityMismatch>(error);
                Assert.Equal(required, fixedError.Expected);
                Assert.Equal(1, fixedError.Actual);
            }
        }
        foreach (var call in new[] { $"map([{value}], F)", $"filter([{value}], F)", $"Forward(Alias, [{value}])" })
        {
            var result = await AcrossStrategies(defs + call);
            var error = Assert.IsType<EvalError.ArityMismatch>(RootError(result));
            Assert.Equal(required, error.Expected);
            Assert.Equal(1, error.Actual);
        }
    }

    [Theory]
    [InlineData("F(a, b, c) = 0\nF(1, (2, 3))", 3, 2)]
    [InlineData("Inc(x) = x + 1\nUse(f, x, y) = f(x) + y\nUse(Inc, (2, 3))", 2, 1)]
    [InlineData("Step(a, b) = a, b\nrepeat(Step, 1, (1, 2))", 2, 1)]
    public async Task FlatBindingArity_ReportsCompleteBindingInputLengths(string source, int expected, int actual)
    {
        var error = Assert.IsType<EvalError.ArityMismatch>(RootError(await AcrossStrategies(source)));
        Assert.Equal(expected, error.Expected);
        Assert.Equal(actual, error.Actual);
    }

    [Theory]
    [InlineData("a, b, c", 3)]
    [InlineData("a, *xs, b", 2)]
    [InlineData("(a, b), c", 2)]
    public async Task FusedFilterCount_RejectsStructuredRowsWithOrdinaryArity(string pattern, int required)
    {
        var source = $"P({pattern}) = true\n[(1, 2, 3), [1, 2, 3]].filter(P).count";
        var ast = AsyncEvaluationHarness.Ast(source);
        var diagnostics = new SequencePipelineDiagnostics();
        var (fused, _) = Evaluator.RunCountedObserved(ast, sequenceDiagnostics: diagnostics);
        var generic = await AcrossStrategies(source);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(fused));
        Assert.Equal(1, diagnostics.GetSnapshot().FilterCountFusionHits);
        var error = Assert.IsType<EvalError.ArityMismatch>(RootError(fused));
        Assert.Equal(required, error.Expected);
        Assert.Equal(1, error.Actual);
    }

    [Fact]
    public async Task CountedMultiSlotOrigin_DoesNotChangeOrdinarySupplyOrForwarding()
    {
        const string defs = "Step(a, b) = a, b\nColl(*xs) = xs\nFwd(*xs) = Coll(xs*)\nFwd2(*xs) = Fwd(xs*)\n";
        var multi = await AcrossStrategies(defs + "repeat(Step, 1, 1, 2)");
        var single = await AcrossStrategies(defs + "(1, 2)");
        Assert.Equal(2, multi.Value.EmittedCount);
        Assert.Equal(1, single.Value.EmittedCount);
        Assert.True(Result.ValueComparer.Equals(multi.Value.Value, single.Value.Value));

        foreach (var origin in new[] { "(1, 2)", "repeat(Step, 1, 1, 2)", "if(true, repeat(Step, 1, 1, 2), 0)" })
        {
            foreach (var call in new[] { $"Coll({origin})", $"Fwd2({origin})", $"({origin}).Fwd2", $"Fwd2([{origin}]*)" })
                AssertValue(await AcrossStrategies(defs + call), "[(1, 2)]");
            AssertValue(await AcrossStrategies(defs + $"Fwd2(({origin})*)"), "[1, 2]");
        }
    }

    [Theory]
    [InlineData("()")]
    [InlineData("[]")]
    [InlineData("(1, 2)")]
    [InlineData("[1, 2]")]
    public async Task Reducer_ResuppliesOneAccumulatorOnEveryIteration(string initial)
    {
        const string defs = "R(x, *acc) = acc\nAlias = R\nApply(f, initial) = reduce([7, 8], f, initial)\nForward(g, initial) = Apply(g, initial)\n";
        var expected = $"[[{initial}]]";
        AssertValue(await AcrossStrategies(defs + $"reduce([7, 8], R, {initial})"), expected);
        AssertValue(await AcrossStrategies(defs + $"Forward(Alias, {initial})"), expected);
        AssertValue(await AcrossStrategies(defs + $"[7, 8].reduce(R, {initial})"), expected);

        // Explicit structure, on the accumulator side alone, opens exactly one level.
        AssertValue(await AcrossStrategies($"R(x, (*acc)) = [acc*, x]\nreduce([7, 8], R, [{initial}])"), $"[{initial}, 7, 8]");
    }

    [Theory]
    [InlineData("a, b, c")]
    [InlineData("a, *xs, b, c")]
    [InlineData("(a, b), c, d")]
    public async Task Reducer_NeitherElementNorAccumulatorCanSupplyMissingSlots(string pattern)
    {
        foreach (var item in new[] { "(1, 2)", "[1, 2]", "()", "[]" })
        foreach (var accumulator in new[] { "(3, 4)", "[3, 4]", "()", "[]" })
        {
            var result = await AcrossStrategies($"R({pattern}) = 0\nreduce([{item}], R, {accumulator})");
            var error = Assert.IsType<EvalError.ArityMismatch>(RootError(result));
            Assert.Equal(3, error.Expected);
            Assert.Equal(2, error.Actual);
        }
    }

    [Theory]
    [InlineData("()")]
    [InlineData("[]")]
    [InlineData("(1, 2)")]
    [InlineData("[1, 2]")]
    public async Task LoopState_PreservesEmptyAndStructuredSlotsAcrossIterations(string value)
    {
        const string defs = "R(x, n) = x, n + 1\nW(x, n) = x, n + 1, n < 2\nColl(*xs) = xs\n";
        foreach (var call in new[] { $"repeat(R, 2, {value}, 0)", $"while(W, {value}, 0)" })
        {
            var raw = await AcrossStrategies(defs + call);
            Assert.True(raw.IsOk);
            Assert.Equal(2, raw.Value.EmittedCount);
            AssertValue(await AcrossStrategies(defs + $"Coll({call})"), $"[({value}, 2)]");
            AssertValue(await AcrossStrategies(defs + $"Coll({call}*)"), $"[{value}, 2]");
        }
    }

    [Theory]
    [InlineData("map", "[[(1, 2)], [()], [[]], [[1, 2]]]")]
    [InlineData("filter", "[(1, 2), (), [], [1, 2]]")]
    [InlineData("reduce", "[[1, 2], [[], [(), [(1, 2), []]]]]")]
    public async Task ForwardedCallback_SuspendsAfterBindingWithoutOpeningOrRedemanding(string operation, string expected)
    {
        var body = operation == "filter" ? "Observe(xs).count == 1" : "Observe(xs)";
        var call = operation == "reduce" ? "reduce(xs, f, [])" : $"{operation}(xs, f)";
        var source = $"F(*xs) = {body}\nAlias = F\nApply(f, xs) = {call}\nForward(g, xs) = Apply(g, xs)\nForward(Alias, [(1, 2), (), [], [1, 2]])";
        var syncSeen = new List<Result>();
        var syncOps = HostOperations.Create(HostOperation.Create("Observe", (args, _) =>
        {
            syncSeen.Add(args[0]);
            return args[0];
        }, "value"));
        var syncOptions = new RunOptions { HostOperations = syncOps };
        var syncRoot = (await SourceProvenance.ParseValidAsync(source, syncOptions)).Root;
        var (sync, syncBudget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(syncRoot),
            enableOptimizations: false, hostOperations: syncOps);
        AssertValue(sync, expected);

        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var seen = new List<Result>();
        var asyncOps = HostOperations.Create(HostOperation.CreateAsync("Observe", async (args, _) =>
        {
            seen.Add(args[0]);
            // Zero-demand during ordinary forwarding observes []; park at the first
            // invocation with actual callback supply, after its binder has run.
            if (Assert.IsType<Result.ListValue>(args[0]).Items.Count > 0 && !entered.Task.IsCompleted)
            {
                entered.SetResult();
                await release.Task;
            }
            return args[0];
        }, "value"));
        var parsed = await SourceProvenance.ParseValidAsync(source, new RunOptions { HostOperations = asyncOps });
        var pending = Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), hostOperations: asyncOps).AsTask();
        try
        {
            await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
            Assert.False(pending.IsCompleted);
            var supplied = Assert.IsType<Result.ListValue>(seen[^1]);
            Assert.Equal(operation == "reduce" ? 2 : 1, supplied.Items.Count);
            Assert.IsType<Result.SequenceValue>(supplied.Items[0]);
        }
        finally
        {
            release.TrySetResult();
        }
        var (actual, budget) = await pending.WaitAsync(TimeSpan.FromSeconds(10));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(actual));
        Assert.Equal(syncBudget.ConsumedSteps, budget.ConsumedSteps);
        Assert.Equal(syncSeen.Count, seen.Count);
        for (var i = 0; i < seen.Count; i++)
            Assert.True(Result.ValueComparer.Equals(syncSeen[i], seen[i]));
        // Each callback has exactly one collected element (reduce has two); all
        // preceding eager demands saw the empty supply and no demand followed it.
        var sizes = seen.Select(value => Assert.IsType<Result.ListValue>(value).Items.Count).ToArray();
        Assert.Equal(Enumerable.Repeat(operation == "reduce" ? 2 : 1, 4), sizes.TakeLast(4));
        Assert.All(sizes.SkipLast(4), size => Assert.Equal(0, size));
    }

    private static EvalError RootError(EvalResult<Evaluator.CountedResult> result)
    {
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context) error = context.Inner;
        return error;
    }

    private static void AssertValue(EvalResult<Evaluator.CountedResult> actual, string expected)
    {
        Assert.True(actual.IsOk, actual.IsError ? actual.Error.ToString() : "");
        var value = Evaluator.Run(AsyncEvaluationHarness.Ast(expected));
        Assert.True(value.IsOk);
        Assert.True(Result.ValueComparer.Equals(value.Value, actual.Value.Value), AsyncEvaluationHarness.NeutralOf(actual));
        Assert.Equal(1, actual.Value.EmittedCount);
    }

    private static async Task<EvalResult<Evaluator.CountedResult>> AcrossStrategies(string source)
    {
        var ast = AsyncEvaluationHarness.Ast(source);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (planned, _) = Evaluator.RunCountedObserved(ast);
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (asynchronous, asyncBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(asynchronous));
        Assert.Equal(genericBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        Assert.Equal(0, cache.SyncAccesses);
        return generic;
    }
}
