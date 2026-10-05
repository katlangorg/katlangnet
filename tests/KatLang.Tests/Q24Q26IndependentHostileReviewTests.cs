using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

public class Q24Q26IndependentHostileReviewTests
{
    [Fact]
    public async Task EmptyCompletedLoop_HasOrdinaryInternalCountZeroAndOneVisibleRootRow()
    {
        var drop = new Algorithm.User(null,
            [new CaptureParameterPattern("xs", Kind: ParameterKind.Collecting)], [], [],
            [new Expr.SequenceSpread(new Expr.EmptySequence(0))]);
        var loop = new Expr.Call(new Expr.Resolve("repeat"),
            new OutputBundle([new Expr.AlgorithmExpr(drop), new Expr.Num(1), new Expr.Num(5)]));
        var (generic, _) = Evaluator.RunCountedObserved(loop, enableOptimizations: false);
        var planned = Evaluator.RunCounted(loop);
        var twin = await Evaluator.RunCountedAsync(loop,
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        foreach (var result in new[] { generic, planned, twin })
        {
            Assert.True(result.IsOk);
            Assert.Equal("S[]", SixRouteAgreement.Neutral(result.Value.Value));
            Assert.Equal(0, result.Value.EmittedCount);
        }
        var root = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Drop(*xs) = { ()* }\nrepeat(Drop, 1, 5)"));
        Assert.Equal(1, root.EmittedCount);
        Assert.Single(root.OutputRows);
        var spread = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Drop(*xs) = { ()* }\nrepeat(Drop, 1, 5)*"));
        Assert.Equal(0, spread.EmittedCount);
        Assert.Empty(spread.OutputRows);
    }

    [Fact]
    public async Task SpreadFormation_PrecedesOrdinaryDemandForUserAndBuiltinCalls()
    {
        var user = await SixRouteAgreement.OnEveryRouteAsync("F(a, b) = a, b\nF(trace(1), trace(3)*)");
        var builtin = await SixRouteAgreement.OnEveryRouteAsync("range(trace(1), trace(3)*)");
        Assert.Equal("ok", user.Kind);
        Assert.Equal("ok", builtin.Kind);
        Assert.Equal(new[] { "trace(3)", "trace(1)" }, user.HostCalls);
        Assert.Equal(user.HostCalls, builtin.HostCalls);
    }

    [Theory]
    [InlineData("Ignore(x) = 5\nrepeat(Ignore, 2, trace(9))", "5")]
    [InlineData("Ignore(x) = 5\nrepeat(Ignore, 2, { 1 / 0 })", "5")]
    [InlineData("Ignore(x) = 5\nRun(step, x) = repeat(step, 2, x)\nRun(Ignore, trace(9))", "5")]
    [InlineData("Ignore(x) = 5\nOuter(v) = map([1, 2], { repeat(Ignore, 2, v) + 0 * x })\nOuter(trace(9))", "L[5, 5]")]
    [InlineData("Drop(*xs) = { ()* }\nrepeat(Drop, 2, trace(9))", "S[]")]
    public async Task CardinalityDoesNotDemandUnusedTransportedComputations(string source, string expected)
    {
        var result = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", result.Kind);
        Assert.Equal(expected, result.Value);
        Assert.Empty(result.HostCalls);
    }

    [Fact]
    public async Task LoopProperty_UsesItsOwnCacheAndExplicitCallBypassesIt()
    {
        var result = await SixRouteAgreement.OnEveryRouteAsync("Keep(x) = x\nP = repeat(Keep, 0, trace(9))\nP, P, P(), P*");
        Assert.Equal("ok", result.Kind);
        Assert.Equal("S[9, 9, 9, 9]", result.Value);
        Assert.Equal(new[] { "trace(9)", "trace(9)" }, result.HostCalls);
    }

    [Theory]
    [InlineData("repeat((), 1, 1)")]
    [InlineData("repeat(5, 1, 1)")]
    public async Task Q23_NonCallableValueStepsStayRejected(string source)
    {
        // Q-23 made every CALLABLE an eligible step; a value still has no callable identity (NEED-06).
        var result = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", result.Kind);
        Assert.StartsWith("ArityMismatch:", Assert.Single(result.Errors), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("F(0) = 0\nF(n) = n + 1\nrepeat(F, 1, 0)", "0")]
    [InlineData("F(0) = 0\nF(n) = n + 1\nA = F\nrepeat(A, 1, 0)", "0")]
    [InlineData("repeat(count, 1, (1, 2))", "2")]
    [InlineData("A = count\nrepeat(A, 1, (1, 2))", "2")]
    public async Task Q23_FamilyAndBuiltinSteps_AreOrdinaryCallables(string source, string expected)
    {
        // These four rows pinned the rejection while Q-23 was open; the decision (October 2026) makes
        // them the ordinary invocation over the state supply.
        var result = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal(("ok", expected), (result.Kind, result.Value));
    }

    [Theory]
    [InlineData("repeat(Math.Abs, 2, -3)", "3")]
    [InlineData("repeat(trace, 2, 3)", "3")]
    [InlineData("M = { public S(x) = x + 1 }\nrepeat(M.S, 2, 3)", "5")]
    [InlineData("S(x) = x + 1\nA = S\nrepeat(A, 2, 3)", "5")]
    public async Task Q23_AcceptedStepCategoriesStayAccepted(string source, string expected)
    {
        var result = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", result.Kind);
        Assert.Equal(expected, result.Value);
    }

    public static TheoryData<string> SensitivePrograms() => new()
    {
        "Fib(a, b) = b, a + b\nStep(p, n) = repeat(Fib, 2, trace(n), n), n + 1\nrepeat(Step, 4, 0, 0)",
        "Fib(a, b) = b, a + b\nStep(a, b) = { repeat(Fib, 2, a, trace(b))* }\nrepeat(Step, 4, 0, 1)",
        "S(x, x) = { (x + 1, x + 1)* }\nrepeat(S, 4, trace(1), 1)",
        "S((a, b)) = (b, a + b)\nrepeat(S, 4, (trace(1), 2))",
        "Drop(*xs) = { ()* }\nrepeat(Drop, 3, { trace(1) })",
        "I(n) = n + 1, n < 3\nS(p, n) = while(I, trace(n)), n + 1\nrepeat(S, 3, 0, 0)",
        "I(x) = x + 1\nS(n) = repeat(I, 2, trace(n)), n < 4\nwhile(S, 0)",
        "I(n) = n + 1, n < 1\nS(n) = while(I, trace(n)), false\nwhile(S, 0)",
        "I(x) = x + Math.RandomInt(1, 9)\nS(p, n) = repeat(I, 2, trace(n)), n + 1\nrepeat(S, 4, 0, 0)",
        "Fib(a, b) = b, a + b\nmap([1, 2], { repeat(Fib, 2, trace(x), 1) })",
        "Fib(a, b) = b, a + b\nreduce([1, 2], { repeat(Fib, 2, x, 1) }, (0, 1))",
        "I(x) = [x, x]\nmap([1, 2], { repeat(I, 1, x) }).filter({ x.count == 2 })",
        "I(s) = s + 'x'\nS(p, n) = repeat(I, 2, 'a'), n + 1\nrepeat(S, 3, '', 0)",
        "I(s) = s + 'x'\nP = repeat(I, 2, 'a')\nP, P(), P*",
        // The empty branch forces a later handover after several planned nested rows.
        "I(a, b) = a, b\nS(p, n) = if(n < 2, repeat(I, 1, trace(n), n), ()), n + 1\nrepeat(S, 4, 0, 0)",
        "I(a, b) = a, b\nS(p, n) = if(n < 2, repeat(I, 1, n, n), ()), 1 / (3 - n)\nrepeat(S, 5, 0, 0)",
    };

    [Theory]
    [MemberData(nameof(SensitivePrograms))]
    public async Task ExactLimits_CompareEveryCounterAndErrorTreeAcrossThreeRoutes(string source)
    {
        var full = await Observe(source, 0);
        var configurations = new List<EvaluationLimits?> { null, new() { MaxSteps = long.MaxValue } };
        for (var steps = 1L; steps <= full.Budget.ConsumedSteps + 1; steps++)
            configurations.Add(new() { MaxSteps = steps });
        for (var items = 1L; items <= full.Budget.MaterializedItems + 1; items++)
            configurations.Add(new() { MaxMaterializedItems = items });
        for (var items = 1; items <= 8; items++)
            configurations.Add(new() { MaxCollectionItems = items });
        for (var chars = 0L; chars <= full.Budget.MaterializedStringChars + 1; chars++)
            configurations.Add(new() { MaxMaterializedStringChars = chars });
        for (var chars = 0; chars <= 6; chars++)
            configurations.Add(new() { MaxStringLength = chars });
        foreach (var limits in configurations.Distinct())
        {
            var generic = await Observe(source, 0, limits);
            for (var route = 1; route <= 2; route++)
                Assert.True(generic.Text == (await Observe(source, route, limits)).Text,
                    $"route={route}; limits={limits}\n{source}\n{generic.Text}");
        }
    }

    private static async Task<(string Text, EvaluationBudget Budget)> Observe(string source, int route, EvaluationLimits? limits = null)
    {
        var log = new StrategyNeutralBudgetParityTests.HostLog();
        var operations = StrategyNeutralBudgetParityTests.Operations(log);
        var program = StrategyNeutralBudgetParityTests.Program(source, operations);
        var (result, budget) = route == 2
            ? await Evaluator.RunCountedObservedAsync(program, limits,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: operations, randomSeed: 739)
            : Evaluator.RunCountedObserved(program, limits, enableOptimizations: route == 1, hostOperations: operations, randomSeed: 739);
        Assert.Equal(0, budget.CurrentDepth);
        var outcome = result.IsError ? DescribeErrorTree(result.Error)
            : $"{SixRouteAgreement.Neutral(result.Value.Value)};n={result.Value.EmittedCount}";
        return ($"{outcome}\n{budget.ConsumedSteps}/{budget.ConsumedExpressionCheckpoints}/{budget.PeakDepth}/{budget.MaterializedItems}/{budget.MaterializedStringChars}\n{string.Join('|', log.Calls)}", budget);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task HostBuiltUnpackingStep_UsesRowsRatherThanItsPatternKind(bool list)
    {
        // The internal unpacking receiver opens either structure; unlike a source sequence
        // pattern it can open a list. Its output spread must still supply two independent slots.
        var item = new CaptureParameterPattern("x");
        var other = new CaptureParameterPattern("y");
        var step = new Algorithm.User(null, [new UnpackingParameterPattern([item, other])], [], [],
            [new Expr.SequenceSpread(new Expr.Capture(new OutputBundle([new Expr.Param("x"), new Expr.Param("y")]))), new Expr.Num(99)]);
        Expr initial = list
            ? new Expr.ListLiteral([new Expr.Num(20), new Expr.Num(30)])
            : new Expr.Capture(new OutputBundle([new Expr.Num(20), new Expr.Num(30)]));
        var program = new Expr.Call(new Expr.Resolve("repeat"),
            new OutputBundle([new Expr.AlgorithmExpr(step), new Expr.Num(1), initial]));
        var (generic, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        var planned = Evaluator.RunCounted(program);
        var twin = await Evaluator.RunCountedAsync(program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.True(generic.IsOk);
        Assert.Equal("S[20, 30, 99]", SixRouteAgreement.Neutral(generic.Value.Value));
        Assert.Equal(1, generic.Value.EmittedCount);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(twin));
    }
}
