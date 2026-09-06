using System.Numerics;
using KatLang.Evaluation;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// Budget-chokepoint parity of the PLANNED loop nodes that replace a generic construct
/// carrying a dynamic-depth charge (bug-hunt B3, September 2026).
///
/// <para>Dynamic depth is an always-active budget: it has a verdict on every run, so the
/// optimized loop strategy cannot be "forced off" to protect it — it must charge depth
/// exactly where the generic strategy does (<c>BudgetCrossTalkMatrixTests</c>). Three
/// planned nodes did not: a planned <c>if</c> charged no argument-evaluation level for
/// its condition and selected branch (K3-01), a bare read of a zero-parameter local
/// property charged no zero-argument property access (K3-02), and an explicit call
/// <c>T()</c> — or the forwarding call <c>A(x)</c> the front end synthesizes for a
/// parameterized local property — compiled to the memoized per-iteration slot, so the
/// second call in an iteration neither charged nor materialized anything (K3-03). Each
/// planned node now enters the SAME <c>Evaluator.BudgetScopes.cs</c> helper as its generic
/// counterpart, and these tests pin the observable consequences: equal peak depth, equal
/// verdict and structured error at the depth boundary, and equal cumulative string
/// materialization.</para>
/// </summary>
public class LoopPlannedChokepointParityTests
{
    private static (
        EvalResult<Evaluator.CountedResult> Result,
        EvaluationBudget Budget,
        LoopOptimizationDiagnosticsSnapshot Loop) Observe(string source, bool optimized, EvaluationLimits? limits = null)
    {
        var diagnostics = new LoopOptimizationDiagnostics();
        var (result, budget) = Evaluator.RunCountedObserved(
            Program(source),
            limits,
            enableOptimizations: optimized,
            loopDiagnostics: diagnostics);
        return (result, budget, diagnostics.GetSnapshot());
    }

    private static Decimal128 Atom(EvalResult<Evaluator.CountedResult> result)
    {
        Assert.False(result.IsError, $"expected success but got: {(result.IsError ? result.Error : null)}");
        return Assert.IsType<Result.Atom>(result.Value.Value).Value;
    }

    /// <summary>
    /// The optimized run must have taken the planned path in full — one optimized loop,
    /// no planned-expression fallback, nothing evaluated generically inside it — otherwise
    /// a parity assertion would compare the generic strategy with itself.
    /// </summary>
    private static LoopPlanDiagnosticSnapshot AssertWhollyPlanned(LoopOptimizationDiagnosticsSnapshot loop)
    {
        Assert.Equal(1, loop.OptimizedLoopHits);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
        var plan = Assert.Single(loop.LoopPlans);
        Assert.True(plan.Optimized, plan.FallbackReason);
        return plan;
    }

    private static string OutputSummary(LoopPlanDiagnosticSnapshot plan)
        => Assert.Single(plan.Expressions, e => e.Role == "output" && e.Index == 0).PlanSummary!;

    /// <summary>
    /// Both strategies succeed with the same value and the same operational depth peak,
    /// the optimized one on the wholly planned path; returns that path's plan.
    /// </summary>
    private static (LoopPlanDiagnosticSnapshot Plan, int PeakDepth) AssertSameSuccessAndPeakDepth(string source, decimal expectedValue)
    {
        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);

        Assert.Equal(expectedValue, Atom(generic.Result));
        Assert.Equal(expectedValue, Atom(optimized.Result));
        Assert.Equal(generic.Budget.PeakDepth, optimized.Budget.PeakDepth);
        Assert.Equal(0, generic.Budget.CurrentDepth);
        Assert.Equal(0, optimized.Budget.CurrentDepth);

        return (AssertWhollyPlanned(optimized.Loop), optimized.Budget.PeakDepth);
    }

    /// <summary>
    /// At the depth boundary both strategies agree: the peak itself is admitted, and one
    /// level below it both stop with the IDENTICAL structured error tree — kind, context
    /// chain, and span — on the wholly planned path. Returns the optimized error.
    /// </summary>
    private static EvalError AssertSameDepthBoundary(string source, int peakDepth)
    {
        Assert.True(peakDepth > 1, "the boundary must sit above the loop's own argument level to be decisive");

        var admitted = new EvaluationLimits { MaxDepth = peakDepth };
        Assert.Equal(Atom(Observe(source, optimized: false, admitted).Result), Atom(Observe(source, optimized: true, admitted).Result));

        var rejected = new EvaluationLimits { MaxDepth = peakDepth - 1 };
        var generic = Observe(source, optimized: false, rejected);
        var optimized = Observe(source, optimized: true, rejected);
        Assert.True(generic.Result.IsError, "expected the generic run to stop at the depth limit");
        Assert.True(optimized.Result.IsError, "expected the optimized run to stop at the depth limit");
        Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(generic.Result.Error));
        Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(optimized.Result.Error));
        Assert.Equal(ContextChain(generic.Result.Error), ContextChain(optimized.Result.Error));
        Assert.Equal(Span(generic.Result.Error), Span(optimized.Result.Error));
        Assert.Equal(DescribeErrorTree(generic.Result.Error), DescribeErrorTree(optimized.Result.Error));
        Assert.Equal(0, generic.Budget.CurrentDepth);
        Assert.Equal(0, optimized.Budget.CurrentDepth);
        AssertWhollyPlanned(optimized.Loop);

        return optimized.Result.Error;
    }

    [Theory]
    [InlineData("if(1, 1, 2)", 1, 0, 1)]
    [InlineData("if(0, 1, 2)", 2, 0, 1)]
    [InlineData("if(C, 1, 2)", 1, 0, 1)]
    [InlineData("if(C + 0, 1, 2)", 1, 0, 2)]
    [InlineData("if(C(), 1, 2)", 1, 0, 2)]
    [InlineData("if(D, 1, 2)", 1, 0, 2)]
    [InlineData("if(D(), 1, 2)", 1, 0, 3)]
    [InlineData("if(A, 1, 2)", 1, 4, 2)]
    [InlineData("if(A(), 1, 2)", 1, 4, 3)]
    [InlineData("if(1, A, A())", 1, 4, 2)]
    [InlineData("if(0, A, A())", 1, 4, 3)]
    [InlineData("if(0, A(), A)", 1, 4, 2)]
    [InlineData("if(1, if(0, A(), A), B())", 1, 4, 3)]
    [InlineData("(W == W) + if(1, A, 0) + (W == W)", 3, 4, 2)]
    [InlineData("(W == W) + if(1, A(), 0) + (W == W)", 3, 8, 3)]
    [InlineData("A + A() + A", 3, 8, 2)]
    [InlineData("A() + A + A()", 3, 12, 2)]
    [InlineData("A + if(1, B, 0)", 3, 8, 3)]
    [InlineData("B() + B()", 4, 16, 3)]
    [InlineData("B + B", 4, 8, 3)]
    [InlineData("if(0, 1 / 0, C)", 1, 0, 1)]
    [InlineData("if(1, C, B() / 0)", 1, 0, 1)]
    public async Task PlannedArgumentAndMemoMatrix_MatchesAllBoundariesAndAsyncTwin(
        string expression, int increment, int charsPerIteration, int peakDepth)
    {
        var source = "Step = {\n    W = 'aaaa'\n    C = 1\n    D = C\n    A = W == W\n    B = A + A()\n    n + "
            + expression + "\n}\nStep.repeat(3, 0)";
        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);
        Assert.Equal(3m * increment, Atom(generic.Result));
        Assert.Equal(3m * increment, Atom(optimized.Result));
        Assert.Equal(peakDepth, generic.Budget.PeakDepth);
        Assert.Equal(peakDepth, optimized.Budget.PeakDepth);
        Assert.Equal(3L * charsPerIteration, generic.Budget.MaterializedStringChars);
        Assert.Equal(3L * charsPerIteration, optimized.Budget.MaterializedStringChars);
        AssertWhollyPlanned(optimized.Loop);

        for (var depth = 1; depth <= peakDepth + 1; depth++)
            await AssertThreeWayParity(source, new EvaluationLimits { MaxDepth = depth }, whollyPlanned: true);

        if (charsPerIteration != 0)
        {
            foreach (var chars in new[] { 3L * charsPerIteration - 1, 3L * charsPerIteration })
            {
                var limits = new EvaluationLimits { MaxMaterializedStringChars = chars };
                var boundary = Observe(source, optimized: false, limits);
                Assert.Equal(chars < 3L * charsPerIteration, boundary.Result.IsError);
                await AssertThreeWayParity(source, limits, whollyPlanned: true);
            }

            await AssertThreeWayParity(source, new EvaluationLimits { MaxStringLength = 3 }, whollyPlanned: true);
            await AssertThreeWayParity(source, new EvaluationLimits { MaxStringLength = 4 }, whollyPlanned: true);
        }
    }

    private static async Task AssertThreeWayParity(string source, EvaluationLimits limits, bool whollyPlanned)
    {
        var generic = Observe(source, optimized: false, limits);
        var optimized = Observe(source, optimized: true, limits);
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var asyncObserved = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            Program(source), limits, zeroArgPropertyResultCache: cache));

        AssertSameOutcome(generic.Result, optimized.Result);
        AssertSameOutcome(generic.Result, asyncObserved.Result);
        foreach (var budget in new[] { optimized.Budget, asyncObserved.Budget })
        {
            Assert.Equal(generic.Budget.PeakDepth, budget.PeakDepth);
            Assert.Equal(generic.Budget.MaterializedStringChars, budget.MaterializedStringChars);
            Assert.Equal(generic.Budget.MaterializedItems, budget.MaterializedItems);
            Assert.Equal(0, budget.CurrentDepth);
        }

        Assert.Equal(0, generic.Budget.CurrentDepth);
        Assert.Equal(generic.Budget.ConsumedSteps, asyncObserved.Budget.ConsumedSteps);
        Assert.Equal(0, cache.SyncAccesses);
        if (whollyPlanned)
            AssertWhollyPlanned(optimized.Loop);
    }

    private static void AssertSameOutcome(
        EvalResult<Evaluator.CountedResult> expected, EvalResult<Evaluator.CountedResult> actual)
    {
        Assert.Equal(expected.IsError, actual.IsError);
        if (expected.IsError)
        {
            Assert.Equal(DescribeErrorTree(expected.Error), DescribeErrorTree(actual.Error));
            Assert.Equal(expected.Error.Code, actual.Error.Code);
            Assert.Equal(expected.Error.IsResourceLimit, actual.Error.IsResourceLimit);
        }
        else
        {
            Assert.True(Result.ValueComparer.Equals(expected.Value.Value, actual.Value.Value));
            Assert.Equal(expected.Value.EmittedCount, actual.Value.EmittedCount);
        }
    }

    // ── K3-01: planned `if` arguments ────────────────────────────────────────

    [Fact]
    public void PlannedNestedIf_ChargesOneArgumentLevelPerConditionAndBranch()
    {
        // The generic `if` evaluates each argument — the condition, then the selected
        // branch — as one algorithm under one depth-only level, so the inner `if` in the
        // selected branch sits one level deeper than the outer one. `n` walks 0, 1, 3,
        // 6, ... (117 after 40 iterations) and the peak is the repeat's own argument
        // level plus one nested level.
        const string source = "Step = n + if(n < 3, if(n < 1, 1, 2), 3)\nStep.repeat(40, 0)";

        var (plan, peakDepth) = AssertSameSuccessAndPeakDepth(source, 117m);
        Assert.Equal(2, peakDepth);
        Assert.Equal(
            "Add(StateSlot(n), If(LessThan(StateSlot(n), Const(3)), If(LessThan(StateSlot(n), Const(1)), Const(1), Const(2)), Const(3)))",
            OutputSummary(plan));
    }

    [Fact]
    public void PlannedNestedIf_DepthRejectionAtAnArgumentLevel_MatchesGenericStructuredError()
    {
        const string source = "Step = n + if(n < 3, if(n < 1, 1, 2), 3)\nStep.repeat(40, 0)";

        var error = AssertSameDepthBoundary(source, peakDepth: 2);

        // The rejected level is the INNER `if`'s condition: the generic funnel returns the
        // limit error unspanned, the call boundaries exempt resource limits from their
        // context frames, and the innermost boundary stamps its own call span.
        Assert.Empty(ContextChain(error));
        Assert.Equal((1, 22, 1, 36), Span(error));
    }

    [Theory]
    [InlineData("literal condition", "Step = n + if(1, 1, 2)\nStep.repeat(5, 0)", 5)]
    [InlineData("parameter condition", "Step = n + if(n, 1, 2)\nStep.repeat(5, 0)", 6)]
    [InlineData("string branches", "Step = n + (if(1, 'a', 'bb') == 'a')\nStep.repeat(5, 0)", 5)]
    public void PlannedIf_EveryArgumentShape_ChargesOneLevelLikeGeneric(string shape, string source, decimal expected)
    {
        // Literals, parameters, and strings are wrapped in value thunks by the generic
        // argument resolution and evaluated under the level like any other argument.
        Assert.False(string.IsNullOrEmpty(shape));
        var (_, peakDepth) = AssertSameSuccessAndPeakDepth(source, expected);
        Assert.Equal(1, peakDepth);
    }

    // ── K3-02: bare zero-parameter temp reads ─────────────────────────────────

    [Fact]
    public void BareTempRead_ChargesTheZeroArgumentPropertyAccessPerRead()
    {
        // `T + 0` in the selected branch is a value thunk (one level) whose bare `T` read
        // is a zero-argument property access (one dynamic invocation) — depth 2 beneath
        // the loop, on both strategies. Before the fix the planned read charged nothing.
        // `n` walks 0, 7 (the one `T + 0` branch), then +2 for the remaining nine
        // iterations: 25.
        const string source = "Step = {\n    T = 7\n    n + if(n < 5, T + 0, 2)\n}\nStep.repeat(10, 0)";

        var (plan, peakDepth) = AssertSameSuccessAndPeakDepth(source, 25m);
        Assert.Equal(2, peakDepth);
        Assert.Equal("Add(StateSlot(n), If(LessThan(StateSlot(n), Const(5)), Add(TempSlot(T), Const(0)), Const(2)))", OutputSummary(plan));
    }

    [Fact]
    public void BareTempRead_DepthRejection_IsStampedWithThePropertyDeclarationSpan()
    {
        const string source = "Step = {\n    T = 7\n    n + if(n < 5, T + 0, 2)\n}\nStep.repeat(10, 0)";

        var error = AssertSameDepthBoundary(source, peakDepth: 2);

        // Exactly the generic zero-argument access rule: a rejected enter carries the
        // property's declaration span, which the enclosing boundaries then leave alone.
        Assert.Empty(ContextChain(error));
        Assert.Equal((2, 5, 2, 5), Span(error));
    }

    [Fact]
    public void BareTempRead_IsMemoizedPerIterationLikeThePropertyCache()
    {
        // Two bare reads per iteration: the generic property cache serves the second from
        // the first (same iteration environment), so the four-unit string is materialized
        // once per iteration; the planned per-iteration memo must do exactly the same.
        const string source = "Step = {\n    W = if(1, 'aaaa', 'bb')\n    n + (W == W)\n}\nStep.repeat(40, 0)";

        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);

        Assert.Equal(40m, Atom(generic.Result));
        Assert.Equal(40m, Atom(optimized.Result));
        Assert.Equal(160, generic.Budget.MaterializedStringChars);
        Assert.Equal(160, optimized.Budget.MaterializedStringChars);
        Assert.Equal(generic.Budget.PeakDepth, optimized.Budget.PeakDepth);
        AssertWhollyPlanned(optimized.Loop);
    }

    [Fact]
    public void BareTempAsDirectIfArgument_EvaluatesThePropertyOnTheAlgorithmChannel()
    {
        // A bare property reference passed DIRECTLY as an `if` argument resolves to the
        // property's own algorithm: the generic `if` evaluates that body under the
        // argument level — fresh, outside the property cache and without the invocation
        // charge — while the bare reads elsewhere in the same iteration go through the
        // cache. Per iteration: the direct branch materializes 4 units, the first bare
        // read another 4 (a miss), the remaining reads hit — 8 units, 40 iterations.
        const string source = "Step = {\n    W = if(1, 'aaaa', 'bb')\n    n + (if(1, W, 0) == W) + (W == W)\n}\nStep.repeat(40, 0)";

        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);

        Assert.Equal(80m, Atom(generic.Result));
        Assert.Equal(80m, Atom(optimized.Result));
        Assert.Equal(320, generic.Budget.MaterializedStringChars);
        Assert.Equal(320, optimized.Budget.MaterializedStringChars);
        Assert.Equal(2, generic.Budget.PeakDepth);
        Assert.Equal(2, optimized.Budget.PeakDepth);
        var plan = AssertWhollyPlanned(optimized.Loop);
        Assert.Contains("If(Const(1), TempSlot(W), Const(0))", OutputSummary(plan), StringComparison.Ordinal);
    }

    [Fact]
    public void BareTempFailure_MatchesGenericDiagnosticExactly()
    {
        var source = """
            Step = {
                T = 1 / 0
                n + T
            }
            Step.repeat(3, 0)
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Equal(["while evaluating dotCall .repeat of Step"], ContextChain(error));
    }

    // ── K3-03: temp calls ─────────────────────────────────────────────────────

    [Fact]
    public async Task ExplicitTempCall_EvaluatesFreshOnEveryCallUnderTheUserCallChokepoint()
    {
        // `A` versus `A()` is core KatLang semantics: a call bypasses the property cache.
        // Two calls per iteration materialize the ten-unit string twice — 4000 units over
        // 200 iterations on BOTH strategies (the planned loop used to memoize the first
        // call's value and stop at 2000). The call is a dynamic invocation: one depth
        // level beneath the loop, the same as the repeat's own argument level.
        const string source = "Step = {\n    T = 'xxxxxxxxxx'\n    n + (T() == T())\n}\nStep.repeat(200, 0)";

        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);

        Assert.Equal(200m, Atom(generic.Result));
        Assert.Equal(200m, Atom(optimized.Result));
        Assert.Equal(4000, generic.Budget.MaterializedStringChars);
        Assert.Equal(4000, optimized.Budget.MaterializedStringChars);
        Assert.Equal(1, generic.Budget.PeakDepth);
        Assert.Equal(1, optimized.Budget.PeakDepth);
        var plan = AssertWhollyPlanned(optimized.Loop);
        Assert.Equal("Add(StateSlot(n), Equal(TempCall(T), TempCall(T)))", OutputSummary(plan));
        await AssertThreeWayParity(source, new EvaluationLimits { MaxMaterializedStringChars = 3999 }, whollyPlanned: true);
        await AssertThreeWayParity(source, new EvaluationLimits { MaxMaterializedStringChars = 4000 }, whollyPlanned: true);
    }

    [Fact]
    public void ForwardingTempCall_IsAFreshUserCallLikeGeneric()
    {
        // `A` and `Next` read `x`, which the step never binds itself, so both become
        // parameterized properties and every reference is the forwarding call `A(x)` /
        // `Next(x)` — a user call on the generic side. Two `A(x)` calls per iteration
        // therefore materialize the selected branch twice: 36 iterations with x > 3 (two
        // four-unit strings) and 4 with x <= 3 (two two-unit strings) — 304 units.
        const string source = "Step = {\n    A = if(x > 3, 'aaaa', 'bb')\n    Next = x + 1\n    (A == A) + Next - 1\n}\nStep.repeat(40, 0)";

        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);

        Assert.Equal(40m, Atom(generic.Result));
        Assert.Equal(40m, Atom(optimized.Result));
        Assert.Equal(304, generic.Budget.MaterializedStringChars);
        Assert.Equal(304, optimized.Budget.MaterializedStringChars);
        Assert.Equal(2, generic.Budget.PeakDepth);
        Assert.Equal(2, optimized.Budget.PeakDepth);
        var plan = AssertWhollyPlanned(optimized.Loop);
        Assert.Equal("Subtract(Add(Equal(TempCall(A), TempCall(A)), TempCall(Next)), Const(1))", OutputSummary(plan));
    }

    [Fact]
    public void NestedForwardingCalls_ChargeExactlyOneInvocationPerCall()
    {
        const string source = "Step = {\n    A = x + 1\n    B = A + 1\n    B\n}\nStep.repeat(3, 0)";

        var (plan, peakDepth) = AssertSameSuccessAndPeakDepth(source, 6m);
        Assert.Equal("TempCall(B)", OutputSummary(plan));
        Assert.Equal(2, peakDepth);
        AssertSameDepthBoundary(source, peakDepth);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task MixedPlannedAndFallbackRows_ShareThePropertyMemo(bool fallbackFirst)
    {
        var rows = fallbackFirst ? "m + count((T, T))\n    n + (T == T)" : "n + (T == T)\n    m + count((T, T))";
        var source = "Step(n, m, p) = {\n    T = 'xxxx'\n    " + rows + "\n    p + 1\n}\nStep.repeat(3, 0, 0, 0)";

        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);
        Assert.False(generic.Result.IsError);
        Assert.False(optimized.Result.IsError);
        Assert.True(Result.ValueComparer.Equals(generic.Result.Value.Value, optimized.Result.Value.Value));
        Assert.Equal(12, generic.Budget.MaterializedStringChars);
        Assert.Equal(generic.Budget.MaterializedStringChars, optimized.Budget.MaterializedStringChars);
        Assert.Equal(1, optimized.Loop.OptimizedLoopHits);
        Assert.True(optimized.Loop.GenericExpressionEvaluationsInsideOptimizedLoops > 0);
        var plan = Assert.Single(optimized.Loop.LoopPlans);
        Assert.All(plan.Temps, temp => Assert.False(temp.Planned));
        Assert.True(Assert.Single(plan.Expressions, expression => expression.Index == 2).Planned);
        await AssertThreeWayParity(source, new EvaluationLimits { MaxMaterializedStringChars = 11 }, whollyPlanned: false);
        await AssertThreeWayParity(source, new EvaluationLimits { MaxMaterializedStringChars = 12 }, whollyPlanned: false);
    }

    [Fact]
    public void SharedUnselectedBranch_PlanningIsBoundedByDistinctNodes()
    {
        var parsed = SourceProvenance.ParseValid("Step = n + if(1, 1, 0)\nStep.repeat(1, 0)").Root;
        var property = Assert.Single(parsed.Properties);
        var step = Assert.IsType<Algorithm.User>(property.Value);
        Expr shared = new Expr.Num(0);
        for (var depth = 0; depth < 18; depth++)
            shared = new Expr.Binary(BinaryOp.Add, shared, shared);

        var body = new Expr.Call(new Expr.Resolve("if"), [new Expr.Num(1), new Expr.Param("n"), shared]);
        var ast = new Expr.AlgorithmExpr(parsed with { Properties = [property with { Value = step with { Output = [body] } }] });
        var generic = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        Assert.Equal(0m, Atom(generic.Result));

        var diagnostics = new LoopOptimizationDiagnostics();
        var before = GC.GetAllocatedBytesForCurrentThread();
        var optimized = Evaluator.RunCountedObserved(ast, enableOptimizations: true, loopDiagnostics: diagnostics);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(0m, Atom(optimized.Result));
        var plan = AssertWhollyPlanned(diagnostics.GetSnapshot());
        Assert.EndsWith("...", OutputSummary(plan), StringComparison.Ordinal);
        Assert.True(OutputSummary(plan).Length <= 2051);
        Assert.True(allocated < 4_000_000, $"Planning a 19-node shared branch allocated {allocated:N0} bytes.");
    }

    [Fact]
    public void SharedCallNode_StillExecutesFreshAtEveryOccurrence()
    {
        var parsed = SourceProvenance.ParseValid("Step = {\n    T = 'aaaa'\n    n + (T() == T())\n}\nStep.repeat(3, 0)").Root;
        var property = Assert.Single(parsed.Properties);
        var step = Assert.IsType<Algorithm.User>(property.Value);
        var output = Assert.IsType<Expr.Binary>(Assert.Single(step.Output));
        var equality = Assert.IsType<Expr.Binary>(output.Right);
        var sharedEquality = equality with { Right = equality.Left };
        var sharedOutput = output with { Right = sharedEquality };
        var ast = new Expr.AlgorithmExpr(parsed with { Properties = [property with { Value = step with { Output = [sharedOutput] } }] });

        foreach (var optimized in new[] { false, true })
        {
            var diagnostics = new LoopOptimizationDiagnostics();
            var observed = Evaluator.RunCountedObserved(ast, enableOptimizations: optimized, loopDiagnostics: diagnostics);
            Assert.Equal(3m, Atom(observed.Result));
            Assert.Equal(24, observed.Budget.MaterializedStringChars);
            if (optimized)
                AssertWhollyPlanned(diagnostics.GetSnapshot());
        }
    }

    [Theory]
    [InlineData(125, false)]
    [InlineData(126, true)]
    public void DefaultDepthBoundary_RejectsBareTempAtK126(int recursion, bool rejected)
    {
        var source = "Step = {\n    T = 7\n    n + if(n < 5, T + 0, 2)\n}\nf(0) = Step.repeat(3, 0)\nf(k) = f(k - 1)\nf(" + recursion + ")";
        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);
        Assert.Equal(rejected, generic.Result.IsError);
        AssertSameOutcome(generic.Result, optimized.Result);
        Assert.Equal(128, generic.Budget.PeakDepth);
        Assert.Equal(128, optimized.Budget.PeakDepth);
        AssertWhollyPlanned(optimized.Loop);
        if (rejected)
        {
            Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(generic.Result.Error));
            Assert.Equal((2, 5, 2, 5), Span(generic.Result.Error));
        }
        else
        {
            Assert.Equal(11m, Atom(generic.Result));
        }
    }

    [Theory]
    [InlineData("T = T")]
    [InlineData("T = U\n    U = T")]
    public async Task RecursiveTemps_UseGenericFallbackAndRemainDepthBounded(string definitions)
    {
        var source = "Step(n) = {\n    " + definitions + "\n    n + if(n < 1, 1, T())\n}\nStep.repeat(2, 0)";
        var limits = new EvaluationLimits { MaxDepth = 8 };
        var generic = Observe(source, optimized: false, limits);
        Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(generic.Result.Error));
        await AssertThreeWayParity(source, limits, whollyPlanned: false);
    }

    [Fact]
    public async Task LoopBindingShadowsOuterProperty_WithoutCreatingTempAccess()
    {
        const string source = "T = 7\nStep(T) = T + 1\nStep.repeat(3, 0)";
        var optimized = Observe(source, optimized: true);
        Assert.Equal(3m, Atom(optimized.Result));
        Assert.Equal("Add(StateSlot(T), Const(1))", OutputSummary(AssertWhollyPlanned(optimized.Loop)));
        await AssertThreeWayParity(source, new EvaluationLimits { MaxDepth = 1 }, whollyPlanned: true);
    }

    [Theory]
    [InlineData("T + T", true)]
    [InlineData("T() + T()", true)]
    [InlineData("U + U()", true)]
    [InlineData("(T) + (T)", false)]
    [InlineData("(T()) + (T())", true)]
    [InlineData("F(n)", false)]
    [InlineData("{ T = 9\nT }", false)]
    public async Task TempClassification_RespectsCallsGroupingAndScope(string expression, bool planned)
    {
        var source = "Step(n) = {\n    T = 2\n    U = T\n    F(value) = value + 1\n    n + " + expression + "\n}\nStep.repeat(3, 0)";
        var optimized = Observe(source, optimized: true);
        Assert.False(optimized.Result.IsError);
        Assert.Equal(planned, Assert.Single(Assert.Single(optimized.Loop.LoopPlans).Expressions).Planned);
        await AssertThreeWayParity(source, new EvaluationLimits(), whollyPlanned: planned);
    }

    [Fact]
    public async Task IncreasingStringTempSizes_ChargeAllFreshMaterialization()
    {
        const string source = "Step(n) = {\n    T = if(n < 2, 'a', 'aaaa')\n    n + (T() == T())\n}\nStep.repeat(4, 0)";
        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);
        Assert.Equal(4m, Atom(generic.Result));
        Assert.Equal(20, generic.Budget.MaterializedStringChars);
        AssertSameOutcome(generic.Result, optimized.Result);
        AssertWhollyPlanned(optimized.Loop);
        await AssertThreeWayParity(source, new EvaluationLimits { MaxMaterializedStringChars = 19 }, whollyPlanned: true);
        await AssertThreeWayParity(source, new EvaluationLimits { MaxMaterializedStringChars = 20 }, whollyPlanned: true);
    }

    [Fact]
    public async Task LaterTempFailure_PreservesFullErrorAndCounters()
    {
        const string source = "Step(n) = {\n    W = 'aaaa'\n    T = if(n < 2, W, 1 / 0)\n    n + (T == T())\n}\nStep.repeat(4, 0)";
        var generic = Observe(source, optimized: false);
        Assert.IsType<EvalError.DivByZero>(Innermost(generic.Result.Error));
        await AssertThreeWayParity(source, new EvaluationLimits(), whollyPlanned: true);
    }

    [Theory]
    [InlineData("Inner.repeat(2, n)")]
    [InlineData("Inner.while(n)")]
    public async Task NestedLoops_PreserveTempMemoAndAsyncAccounting(string nested)
    {
        var inner = nested.Contains("while", StringComparison.Ordinal) ? "n + 1, n < 3" : "n + 1";
        var source = "Inner = " + inner + "\nStep(n) = {\n    T = 7\n    " + nested + " + if(T, 1, 0)\n}\nStep.repeat(3, 0)";
        var optimized = Observe(source, optimized: true);
        Assert.False(optimized.Result.IsError);
        Assert.True(optimized.Loop.OptimizedLoopHits > 1);
        await AssertThreeWayParity(source, new EvaluationLimits(), whollyPlanned: false);
        for (var depth = 1; depth <= optimized.Budget.PeakDepth; depth++)
            await AssertThreeWayParity(source, new EvaluationLimits { MaxDepth = depth }, whollyPlanned: false);
    }

    [Fact]
    public async Task LoadedStep_PlansFreshCallsWithModuleSourceProvenance()
    {
        var parsed = await Parser.ParseAsync("open 'https://example.test/step'\nStep.repeat(3, 0)", new RunOptions
        {
            AllowedHosts = ["example.test"],
            DownloadCode = (_, _) => ValueTask.FromResult("public Step = {\n    T = 'aaaa'\n    n + (T() == T())\n}"),
        });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        var ast = new Expr.AlgorithmExpr(parsed.Root);
        var diagnostics = new LoopOptimizationDiagnostics();
        var generic = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var optimized = Evaluator.RunCountedObserved(ast, enableOptimizations: true, loopDiagnostics: diagnostics);
        Assert.Equal(3m, Atom(generic.Result));
        AssertSameOutcome(generic.Result, optimized.Result);
        Assert.Equal(24, generic.Budget.MaterializedStringChars);
        Assert.Equal(24, optimized.Budget.MaterializedStringChars);
        Assert.Contains("TempCall(T)", OutputSummary(AssertWhollyPlanned(diagnostics.GetSnapshot())), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("2147483648")]
    [InlineData("9223372036854775807")]
    [InlineData("1e100")]
    public async Task RepeatCountBeyondIntRange_IsNotNarrowedBeforeExecution(string count)
    {
        var source = "Step = n + 1\nStep.repeat(" + count + ", 0)";
        var limits = new EvaluationLimits { MaxSteps = 2 };
        var generic = Observe(source, optimized: false, limits);
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(Innermost(generic.Result.Error));
        Assert.Equal(2, generic.Budget.ConsumedSteps);
        await AssertThreeWayParity(source, limits, whollyPlanned: false);
    }

    [Fact]
    public void TempCallMemoIsolation_DoesNotCopyEveryDeclaredTempPerCall()
    {
        var declarations = string.Join("\n", Enumerable.Range(0, 2000).Select(index => $"T{index} = 1"));
        long Measure(int iterations)
        {
            var ast = Program("Step = {\n" + declarations + "\nn + (T0 == T1())\n}\nStep.repeat(" + iterations + ", 0)");
            var diagnostics = new LoopOptimizationDiagnostics();
            var before = GC.GetAllocatedBytesForCurrentThread();
            var observed = Evaluator.RunCountedObserved(ast, enableOptimizations: true, loopDiagnostics: diagnostics);
            var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.Equal((decimal)iterations, Atom(observed.Result));
            AssertWhollyPlanned(diagnostics.GetSnapshot());
            return allocated;
        }

        var oneIteration = Measure(1);
        var manyIterations = Measure(1001);
        Assert.True(manyIterations - oneIteration < 500_000,
            $"The extra 1000 calls allocated {manyIterations - oneIteration:N0} bytes.");
    }

    [Fact]
    public void TempCall_SuspendsTheCallersTempMemo_LikeAFreshCallEnvironment()
    {
        // A generic user call runs its callee in fresh environments, and the property
        // cache is keyed by their identities: a bare `T` read inside `A(x)` misses on
        // every call even though the caller already cached `T`, and the caller's entry is
        // still served after the call returns. Per iteration: the caller's first `T` read
        // (10 units), one miss inside each of the two `A(x)` calls (10 each), and the
        // caller's final `T == T` served from its untouched entry — 30 units, 20
        // iterations. `n` walks 0, 1, 3, 7, ... (2^20 - 1).
        const string source =
            "Step = {\n    T = 'xxxxxxxxxx'\n    A = x + (T == T)\n    (T == T) + A + A - 2 + (T == T) - 1\n}\nStep.repeat(20, 0)";

        var generic = Observe(source, optimized: false);
        var optimized = Observe(source, optimized: true);

        Assert.Equal(1_048_575m, Atom(generic.Result));
        Assert.Equal(1_048_575m, Atom(optimized.Result));
        Assert.Equal(600, generic.Budget.MaterializedStringChars);
        Assert.Equal(600, optimized.Budget.MaterializedStringChars);
        Assert.Equal(2, generic.Budget.PeakDepth);
        Assert.Equal(2, optimized.Budget.PeakDepth);
        var plan = AssertWhollyPlanned(optimized.Loop);
        Assert.Contains("TempCall(A)", OutputSummary(plan), StringComparison.Ordinal);
        Assert.Contains("TempSlot(T)", OutputSummary(plan), StringComparison.Ordinal);
    }

    [Fact]
    public void TempCall_DepthRejectionInsideTheCallee_MatchesGenericStructuredError()
    {
        // `A(x)` is one invocation and the `if` inside it one more level: depth 2 beneath
        // the loop. One below that, the rejected level is the `if`'s condition, stamped
        // with the `if` call's span by its own boundary and left alone by the call's.
        const string source = "Step = {\n    A = if(x < 100, x + 1, 0)\n    A\n}\nStep.repeat(3, 0)";

        var (plan, peakDepth) = AssertSameSuccessAndPeakDepth(source, 3m);
        Assert.Equal(2, peakDepth);
        Assert.Equal("TempCall(A)", OutputSummary(plan));

        var error = AssertSameDepthBoundary(source, peakDepth);
        Assert.Empty(ContextChain(error));
        Assert.Equal((2, 9, 2, 29), Span(error));
    }

    [Fact]
    public void TempCallFailure_KeepsTheCallContextFrame()
    {
        // The planned call replaces an ordinary call expression, so its failures carry the
        // generic call boundary's frame exactly like a planned `if` does.
        var source = """
            Step = {
                A = x / 0
                A
            }
            Step.repeat(3, 1)
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Equal(
            ["while evaluating dotCall .repeat of Step", "while evaluating call to A"],
            ContextChain(error));
    }

    [Fact]
    public void ExplicitTempCallFailure_KeepsTheCallContextFrame()
    {
        var source = """
            Step = {
                T = 1 / 0
                n + T()
            }
            Step.repeat(3, 0)
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Equal(
            ["while evaluating dotCall .repeat of Step", "while evaluating call to T"],
            ContextChain(error));
    }
}
