using System.Reflection;
using KatLang.Evaluation;

namespace KatLang.Tests;

public partial class LoopStepCallableDispatchTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task Independent_ZeroIterationsDoNotEvenProjectTheCallable(bool asynchronous)
    {
        var projections = 0;
        var step = new NeedCell(
            () => throw new InvalidOperationException("unused step VALUE"),
            () => throw new InvalidOperationException("unused step VALUE"),
            () => { projections++; return EvalResult<Algorithm?>.Ok(new Algorithm.Builtin(BuiltinId.count)); });
        var arguments = new[]
        {
            new Evaluator.ResolvedArgumentAlgorithm(null, false) { Cell = step },
            new Evaluator.ResolvedArgumentAlgorithm(null, false) { Cell = NeedCell.Ready(new(new Result.Atom(0), 1)) },
            new Evaluator.ResolvedArgumentAlgorithm(null, false) { Cell = NeedCell.Ready(new(new Result.Atom(7), 1)) }
        };
        var method = typeof(Evaluator).GetMethod("EvalNeedLoop", BindingFlags.Static | BindingFlags.NonPublic)!;
        var invocation = (ValueTask<EvalResult<Evaluator.CountedResult>>)method.Invoke(null,
            [BuiltinId.@repeat, arguments, Evaluator.EvalCtx.Empty, Array.Empty<(string, Result)>(), asynchronous])!;
        var result = await invocation;
        Assert.True(result.IsOk);
        Assert.Equal("7", SixRouteAgreement.Neutral(result.Value.Value));
        Assert.Equal(0, projections);
    }

    // This corpus was reconstructed from the ordinary call contracts, independently of the
    // implementation round's table. In particular every builtin, including both loop builtins,
    // is observed as an ordinary invocation and as a one-row wrapper.
    public static TheoryData<string, string, string, string, int, bool> IndependentInvocations()
    {
        var data = new TheoryData<string, string, string, string, int, bool>();
        void Add(string id, string definitions, string callable, string supply, int slots, bool spread = false)
            => data.Add(id, definitions, callable, supply, slots, spread);
        var unary = new[] { "atoms", "order", "orderDesc", "count", "first", "last", "distinct", "min", "max", "sum", "avg" };
        foreach (var builtin in unary)
        {
            Add(builtin + "-list", "", builtin, "[3, 1, 2]", 1);
            Add(builtin + "-empty", "", builtin, "[]", 1);
            Add(builtin + "-empty-element", "", builtin, "[()]", 1);
            Add(builtin + "-sequence", "", builtin, "(4, 2)", 1);
            Add(builtin + "-surplus", "", builtin, "trace(1) / 0, 2", 2);
        }
        Add("range", "", "range", "trace(2), trace(4)", 2);
        Add("contains", "", "contains", "[(), [1], 'x'], ()", 2);
        foreach (var builtin in new[] { "take", "skip" })
        {
            Add(builtin, "", builtin, "[(), 2, 3], 2", 2);
            Add(builtin + "-bad-control", "", builtin, "trace([1]), trace('x')", 2);
        }
        Add("if-lazy-empty", "", "if", "trace(false), trace(1) / 0, trace(())", 3);
        Add("if-lazy-random", "", "if", "true, Math.RandomInt(1, 9), Math.RandomInt(1, 9) / 0", 3);
        Add("map-family", "C(0) = 5\nC(x) = trace(x) + 1\n", "map", "[0, 2], C", 2);
        Add("filter-family", "C(0) = false\nC(x) = trace(x) > 1\n", "filter", "[0, 2], C", 2);
        Add("reduce-family", "C(0, a) = a\nC(x, a) = trace(x) + a\n", "reduce", "[0, 2, 3], C, trace(10)", 3);
        Add("map-failed-callback", "", "map", "[1], { 1 / 0 + x }", 2);
        Add("repeat-step", "", "repeat", "{ x + 1 }, 2, 0", 3);
        Add("while-step", "", "while", "{ x + 1, x < 2 }, 0", 2);
        Add("while-false", "", "while", "{ false }, true", 2);
        Add("family-order", "F(x) = 7\nF(0) = 8\n", "F", "0", 1);
        Add("family-no-match", "F(0) = 1\nF(1) = 2\n", "F", "trace(5)", 1);
        Add("family-failed-inspection", "F(0, y) = 1\nF(x, y) = 2\n", "F", "trace(1) / 0, trace(2)", 2);
        Add("family-shared-inspection", "F(0, y) = 1\nF(1, y) = 2\nF(x, y) = x\n", "F", "trace(3), trace(9) / 0", 2);
        Add("family-repeated-conflict", "F(x, x, z) = z\nF(a, b, z) = a\n", "F", "trace(1), trace(2), trace(3) / 0", 3);
        // Collectors in written clause heads are rejected by the front end; the ordinary
        // explicit parameter-list forms below are the legal collector controls.
        Add("list-collector", "F([x, *tail]) = tail\n", "F", "[1, 2, ()]", 1);
        Add("sequence-collector", "F((x, *tail)) = (x, tail)\n", "F", "(1, 2, ())", 1);
        Add("family-two-rows", "F(0, b) = 1, b\nF(a, b) = a + 1, b\n", "F", "1, 3", 2, true);
        Add("family-spread", "F(0, b) = { (1, b)* }\nF(a, b) = { (a + 1, b)* }\n", "F", "1, 3", 2, true);
        Add("family-empty-row", "F(0) = ()\nF(x) = ()\n", "F", "1", 1);
        Add("family-zero-rows", "F(0) = { ()* }\nF(x) = { ()* }\n", "F", "1", 1, true);
        Add("family-nested-loop", "F(0) = 0\nF(x) = repeat(count, 1, [x])\n", "F", "3", 1);
        Add("math", "", "abs", "trace(-3)", 1);
        Add("host", "", "trace", "trace(7)", 1);
        Add("user", "F(x) = x + 1\n", "F", "trace(2)", 1);
        return data;
    }

    [Theory]
    [MemberData(nameof(IndependentInvocations))]
    public async Task Independent_AllCallableRoutesAgreeWithOrdinaryInvocationAndRows(
        string id, string definitions, string callable, string supply, int slots, bool spread)
    {
        // A directly written family in repeat's initial VALUE slots would be formula-lifted.
        // Use the established neutral user argument to transport its independent CALLABLE channel.
        var callbackTransport = id is "map-family" or "filter-family" or "reduce-family";
        string Complete(string prefix, string expression) => definitions + prefix + (callbackTransport
            ? $"Supply(callback) = {{\n{expression.Replace(supply, supply.Replace(", C", ", callback", StringComparison.Ordinal), StringComparison.Ordinal)}\n}}\nSupply(C)"
            : expression);
        var callSource = Complete("", $"{callable}({supply})");
        var (ordinary, _) = await AllRoutesAsync(callSource, seed: 313);
        var parameters = string.Join(", ", Enumerable.Range(0, slots).Select(i => $"p{i}"));
        var wrapperBody = $"{callable}({parameters})";
        if (spread) wrapperBody = "{ " + wrapperBody + "* }";
        var wrapper = $"W({parameters}) = {wrapperBody}\n";
        foreach (var iterations in new[] { 0, 1, 2 })
        {
            var directSource = Complete("", $"repeat({callable}, {iterations}, {supply})");
            var (direct, _) = await AllRoutesAsync(directSource, seed: 313);
            var (wrapped, _) = await AllRoutesAsync(Complete(wrapper, $"repeat(W, {iterations}, {supply})"), seed: 313);
            Assert.True(direct.Semantic == wrapped.Semantic, $"{id}/{iterations}: {direct} != {wrapped}");
            if (iterations == 1)
            {
                Assert.True(direct.Semantic == ordinary.Semantic, $"{id}: {direct} != {ordinary}");
                if (direct.Kind == "err")
                    Assert.Equal(Innermost(GenericError(callSource)) with { Span = null },
                        Innermost(GenericError(directSource)) with { Span = null });
            }
            foreach (var route in new[]
            {
                Complete($"AliasOne = {callable}\nAliasTwo = AliasOne\nAliasThree = AliasTwo\n", $"repeat(AliasThree, {iterations}, {supply})"),
                Complete("", $"{callable}.repeat({iterations}, {supply})"),
                Complete($"Run(f, *s) = repeat(f, {iterations}, s*)\nNext(g, *s) = Run(g, s*)\n", $"Next({callable}, {supply})"),
            })
            {
                var (routed, _) = await AllRoutesAsync(route, seed: 313);
                Assert.True(direct.Semantic == routed.Semantic, $"{id}/{iterations}: {direct} != {routed}");
            }
        }
    }

    [Theory]
    [InlineData("first", "[()]", "W(c) = first(c)\n")]
    [InlineData("last", "[()]", "W(c) = last(c)\n")]
    [InlineData("if", "true, (), 9", "W(c, t, e) = if(c, t, e)\n")]
    [InlineData("reduce", "[], { e + a }, ()", "W(c, f, a) = reduce(c, f, a)\n")]
    [InlineData("repeat", "{ if(x == x, (), ())* }, 1, 0", "W(f, n, x) = repeat(f, n, x)\n")]
    public async Task Independent_EmptyBuiltinResultIsOneSlotInEverySpelling(string builtin, string supply, string wrapper)
    {
        foreach (var step in new[] { builtin, "A", "W" })
        {
            var definitions = wrapper + $"A = {builtin}\n";
            var (flag, _) = await AllRoutesAsync(definitions + $"while({step}, {supply})");
            Assert.True(Assert.Single(flag.Errors).StartsWith("TypeMismatch:", StringComparison.Ordinal), flag.ToString() + "\n" + definitions + $"while({step}, {supply})");
            Assert.Contains("sequence value with 0 sequence elements", flag.Errors[0], StringComparison.Ordinal);
        }
        // A second unary call distinguishes [] from [()] without relying on final rendering.
        if (builtin is "first" or "last")
        {
            // The second call selects from `()`, which has no position: BadIndex (SEQ-04, Q-27).
            var (twice, _) = await AllRoutesAsync($"repeat({builtin}, 2, {supply})");
            Assert.IsType<EvalError.BadIndex>(Innermost(GenericError($"repeat({builtin}, 2, {supply})")));
        }
    }

    [Theory]
    [InlineData("F(0) = 1\nF(1) = 2\n", "F", "5", "F")]
    [InlineData("F(0) = 1\nF(1) = 2\nA = F\nB = A\nC = B\n", "C", "5", "C")]
    [InlineData("Lib = {\n public F(0) = 1\n public F(1) = 2\n}\n", "Lib.F", "5", "Lib.F")]
    [InlineData("open Lib\nLib = {\n public F(0) = 1\n public F(1) = 2\n}\n", "F", "5", "F")]
    public async Task Independent_NoMatchNamesWrittenIdentityAcrossRoutes(string definitions, string step, string supply, string expected)
    {
        foreach (var expression in new[] { $"repeat({step}, 1, {supply})", $"{step}.repeat(1, {supply})", $"while({step}, {supply})",
            $"Run(f, *s) = repeat(f, 1, s*)\nNext(g, *s) = Run(g, s*)\nNext({step}, {supply})" })
        {
            var (observed, _) = await AllRoutesAsync(definitions + expression);
            Assert.StartsWith("NoMatchingBranch:", Assert.Single(observed.Errors), StringComparison.Ordinal);
            var error = GenericError(definitions + expression);
            Assert.Equal(expected, Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error)).AlgorithmName);
            Assert.Contains("while evaluating call to " + expected, Frames(error));
        }
    }

    [Theory]
    [InlineData("F(0) = 0\nF(x) = trace(x) + 1\nrepeat(F, 3, 1)")]
    [InlineData("repeat(range, 1, 1, 4)")]
    [InlineData("repeat(map, 1, [1, 2], { trace(x) + 1 })")]
    [InlineData("repeat(if, 1, false, trace(1) / 0, trace('abc'))")]
    [InlineData("F(0) = 0, false\nF(x) = x - 1, x > 1\nwhile(F, 3)")]
    public async Task Independent_ExactBudgetBoundariesAreStrategyNeutral(string source)
    {
        var (_, budget) = await AllRoutesAsync(source);
        foreach (var delta in new[] { -1, 0, 1 })
        {
            await AllRoutesAsync(source, limits: new EvaluationLimits { MaxSteps = Math.Max(1, budget.Steps + delta) });
            await AllRoutesAsync(source, limits: new EvaluationLimits { MaxDepth = Math.Max(1, budget.PeakDepth + delta) });
            await AllRoutesAsync(source, limits: new EvaluationLimits { MaxMaterializedItems = Math.Max(1, budget.MaterializedItems + delta) });
        }
    }

    [Theory]
    [InlineData("F(0) = 1\nF(x) = x + 1\nrepeat(F, 1, awaitValue(1))")]
    [InlineData("F(0) = 1\nF(x) = awaitValue(x)\nrepeat(F, 1, 1)")]
    [InlineData("repeat(count, 1, awaitValue([1]))")]
    [InlineData("repeat(if, 1, true, awaitValue(1), 0)")]
    [InlineData("repeat(map, 1, [1], { awaitValue(x) })")]
    [InlineData("repeat(filter, 1, [1], { awaitValue(x) > 0 })")]
    [InlineData("repeat(reduce, 1, [1], { awaitValue(e) + a }, 0)")]
    public async Task Independent_CancellationWhileHostIsSuspendedRetainsOriginalToken(string source)
    {
        foreach (var forced in new[] { false, true })
        {
            using var cancellation = new CancellationTokenSource();
            var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var starts = 0;
            var operations = HostOperations.Create(HostOperation.CreateAsync("awaitValue", async (args, token) =>
            {
                Interlocked.Increment(ref starts);
                entered.TrySetResult();
                await Task.Delay(Timeout.Infinite, token);
                return args[0];
            }, "x"));
            Task run;
            if (forced)
            {
                var root = ParseValid(source, operations);
                run = Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(root),
                    zeroArgPropertyResultCache: new KatLang.Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache(),
                    hostOperations: operations, cancellationToken: cancellation.Token).AsTask();
            }
            else run = KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token });
            await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
            Assert.False(run.IsCompleted);
            cancellation.Cancel();
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(TimeSpan.FromSeconds(10)));
            Assert.Equal(cancellation.Token, error.CancellationToken);
            Assert.Equal(1, starts);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task Independent_LoopDispatchJoinsAlreadyInFlightStateCell(bool family)
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        var cell = new NeedCell(() => throw new InvalidOperationException("sync force"), async () =>
        {
            Interlocked.Increment(ref starts);
            entered.TrySetResult();
            await release.Task;
            return EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom(3), 1));
        });
        var first = cell.DemandAsync().AsTask();
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
        var step = family
            ? ParseValid("F(0) = 9\nF(x) = x\n0", HostOperations.Create()).Properties.Single(p => p.Name == "F").Value
            : new Algorithm.Builtin(BuiltinId.count);
        var method = typeof(Evaluator).GetMethod("InvokeLoopStepSupply", BindingFlags.NonPublic | BindingFlags.Static)!;
        var preparedType = method.GetParameters()[1].ParameterType;
        var invocation = (ValueTask<EvalResult<IReadOnlyList<Result>>>)method.Invoke(null,
            [step, Activator.CreateInstance(preparedType), new[] { cell }, Evaluator.EvalCtx.Empty, Array.Empty<(string, Result)>(),
                "repeat", method.GetParameters()[6].ParameterType.GetMethod("FromKnown", BindingFlags.Public | BindingFlags.Static)!.Invoke(null, ["F"]), true])!;
        var joined = invocation.AsTask();
        Assert.False(joined.IsCompleted);
        Assert.Equal(1, starts);
        release.SetResult();
        Assert.True((await first.WaitAsync(TimeSpan.FromSeconds(10))).IsOk);
        var output = await joined.WaitAsync(TimeSpan.FromSeconds(10));
        Assert.True(output.IsOk);
        Assert.Equal(family ? "3" : "1", SixRouteAgreement.Neutral(Assert.Single(output.Value)));
        Assert.Equal(1, starts);
    }

    [Theory]
    [InlineData("F([a, b]) = (a, b)\n", "(1, 2)", "TypeMismatch")]
    [InlineData("F(x, x) = x\n", "1, 2", "BadArity")]
    public async Task Independent_UserInspectionFailureRetainsTheOrdinaryBinderError(
        string definition, string supply, string expectedType)
    {
        var source = definition + $"repeat(F, 1, {supply})";
        var (loop, _) = await AllRoutesAsync(source);
        var (ordinary, _) = await AllRoutesAsync(definition + $"F({supply})");
        Assert.Equal(ordinary.Semantic, loop.Semantic);
        var error = GenericError(source);
        Assert.Equal(expectedType, Innermost(error).GetType().Name);
        for (var current = error; current is EvalError.WithContext frame; current = frame.Inner)
        {
            Assert.IsNotType<LoopStateBindingContext>(frame.ErrorContext);
            Assert.IsNotType<VariadicLoopStateBindingContext>(frame.ErrorContext);
        }
    }
}
