using KatLang.Evaluation;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// OPT-FB-1: ONE optimizer fallback event contributes exactly ONE count to
/// <see cref="LoopOptimizationDiagnosticsSnapshot.OptimizedLoopFallbacks"/>, and each event has
/// one owner by construction:
/// <list type="bullet">
/// <item>The loop entry (<c>Evaluator.EvalNeedLoop</c>) owns a fallback decided BEFORE planning:
/// optimization disabled, the asynchronous route, or a step refused by the shape gate.</item>
/// <item>The planner (<c>LoopOptimizer.TryBuildLoopPlanTemplate</c>) owns its own refusal and keeps
/// its specific reason; the loop entry does not record that attempt again.</item>
/// <item>A planned run's mid-iteration handover, a planned row's generic evaluation, a counted
/// parameter's decline and a temporary's planning fallback stay their own diagnostic events.</item>
/// </list>
/// Before the repair a planner refusal was counted twice — once under the planner's reason and
/// once more under "loop plan unsupported step shape" (META-S3-3 review, corpus row E7
/// <c>0/2</c>). Every loop here also runs with optimization disabled: the value or error and every
/// budget counter must be identical, since the repair touches diagnostics only.
/// </summary>
public class LoopFallbackAccountingTests
{
    private const string UnsupportedShape = "loop plan unsupported step shape";
    private const string OutputArityMismatch = "loop plan output arity mismatch";
    private const string SpreadContinuationRow = "loop plan spread continuation row";
    private const string VariadicStep = "variadic loop step";
    private const string OptimizationDisabled = "loop optimization disabled";
    private const string ExpressionDidNotEmitOneValue = "loop expression did not emit exactly one state value";

    private sealed record Run(
        string Outcome,
        LoopFallbackAccountingTests.Budget Budget,
        LoopOptimizationDiagnosticsSnapshot Loops,
        long GenericPreparations,
        long? EmittedCount,
        string? ErrorTree);

    private sealed record Budget(long Steps, long Checkpoints, int PeakDepth, long MaterializedItems, long MaterializedStringChars)
    {
        public static Budget Of(EvaluationBudget budget)
            => new(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
                budget.MaterializedItems, budget.MaterializedStringChars);
    }

    // ── T1/T2: the planner refuses one loop — one fallback, under the planner's own reason ────

    public static TheoryData<string, string, string> PlannerRefusals => new()
    {
        // while: a non-user (family) step, a zero-state step, an output-arity mismatch and a
        // spread continuation row all pass the shape gate and reach the planner.
        { "F(0) = 0, false\nF(n) = n - 1, n > 1\nF(5).while", "1", UnsupportedShape },
        { "Z = false\nZ().while", "S[]", UnsupportedShape },
        { "Step(a, b) = {(a + 1, b + 1)*, a < 3}\nStep(0, 0).while", "S[3, 3]", OutputArityMismatch },
        { "Tick = 42\nS = ((1, false), (2, 2))\nStep = {a + Tick, (S[0])*}\nwhile(Step(9))", "9", SpreadContinuationRow },
        // repeat: a family step and an output-arity mismatch.
        { "F(0) = 0\nF(n) = n - 1\nrepeat(F(5), 2)", "3", UnsupportedShape },
        { "Step(a, b) = {(a + 1, b + 1)*}\nStep(0, 0).repeat(3)", "S[3, 3]", OutputArityMismatch },
    };

    [Theory]
    [MemberData(nameof(PlannerRefusals))]
    public void PlannerRefusal_IsOneFallback_UnderThePlannersReason(string source, string expected, string reason)
    {
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        Assert.Equal("ok " + expected, optimizing.Outcome);
        AssertParity(generic, optimizing);

        var loops = optimizing.Loops;
        Assert.Equal(1, loops.LoopExecutions);
        Assert.Equal(1, loops.LoopPlanBuilds);
        Assert.Equal(0, loops.OptimizedLoopHits);
        Assert.Equal(1, loops.OptimizedLoopFallbacks);
        AssertReasons(loops, (reason, 1));

        // The per-plan snapshot is unchanged: one refused plan, built once, observed once.
        var plan = Assert.Single(loops.LoopPlans);
        Assert.False(plan.Optimized);
        Assert.Equal(reason, plan.FallbackReason);
        Assert.Equal(1, plan.BuildCount);
        Assert.Equal(1, plan.ExecutionCount);
    }

    [Fact]
    public void HistoricalE7_KeepsTheSpecificRefusal_AndTheCompleteFailure()
    {
        const string source = "Bad = min([])\nUse(p) = { A = p.G\n A(0).while }\nUse(Bad.Algorithm)";
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        Assert.Equal("err IllegalInEval", optimizing.Outcome);
        AssertParity(generic, optimizing);
        Assert.Equal(0, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(1, optimizing.Loops.OptimizedLoopFallbacks);
        Assert.Equal(1, optimizing.Loops.LoopPlanBuilds);
        Assert.Equal(1, optimizing.Loops.LoopExecutions);
        AssertReasons(optimizing.Loops, (OutputArityMismatch, 1));
        Assert.Equal(1, optimizing.GenericPreparations);
        var plan = Assert.Single(optimizing.Loops.LoopPlans);
        Assert.False(plan.Optimized);
        Assert.Equal(OutputArityMismatch, plan.FallbackReason);
        Assert.Equal(1, plan.BuildCount);
        Assert.Equal(1, plan.ExecutionCount);
    }

    [Theory]
    [InlineData("Step(x) = x + 1\nStep(0).repeat(3)", "3")]
    [InlineData("Math.Abs(-3).repeat(2)", "3")]
    public void SuccessfulRepeat_IsOneHit_AndNoFallback(string source, string expected)
    {
        var optimizing = RunSource(source, optimize: true);
        AssertParity(RunSource(source, optimize: false), optimizing);

        Assert.Equal("ok " + expected, optimizing.Outcome);
        Assert.Equal(1, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(0, optimizing.Loops.OptimizedLoopFallbacks);
        Assert.Equal(1, optimizing.Loops.LoopPlanBuilds);
        // A planned `Math.Abs` row runs generically: expression-level reasons (one per build,
        // one per planned evaluation), never a loop-level one.
        Assert.DoesNotContain(optimizing.Loops.FallbackReasons.Keys, static reason => reason.StartsWith("loop ", StringComparison.Ordinal));
        Assert.Equal(source.StartsWith("Math", StringComparison.Ordinal) ? 3 : 0,
            optimizing.Loops.FallbackReasons.GetValueOrDefault("unsupported native call: Abs"));
    }

    // ── T3: the shape gate refuses the step before planning ──────────────────────────────

    [Fact]
    public void ShapeGateRefusal_IsOneFallback_AndNeverReachesThePlanner()
    {
        const string source = "C(*xs) = xs\nC(5).repeat(1)";
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        Assert.Equal("ok L[5]", optimizing.Outcome);
        AssertParity(generic, optimizing);
        Assert.Equal(0, optimizing.Loops.LoopPlanBuilds);
        Assert.Empty(optimizing.Loops.LoopPlans);
        Assert.Equal(1, optimizing.Loops.OptimizedLoopFallbacks);
        AssertReasons(optimizing.Loops, (VariadicStep, 1));
        Assert.Equal(1, optimizing.GenericPreparations);
    }

    // ── T4: optimization disabled ───────────────────────────────────────────────────────

    [Fact]
    public void DisabledOptimization_IsOneFallback_AndNoPlanBuild()
    {
        var generic = RunSource("Step(x) = x + 1, x < 3\nStep(0).while", optimize: false);

        Assert.Equal("ok 3", generic.Outcome);
        Assert.Equal(0, generic.Loops.OptimizedLoopHits);
        Assert.Equal(0, generic.Loops.LoopPlanBuilds);
        Assert.Equal(1, generic.Loops.OptimizedLoopFallbacks);
        AssertReasons(generic.Loops, (OptimizationDisabled, 1));
    }

    // ── T5: the asynchronous route never plans; it records its one entry fallback ─────────

    [Fact]
    public async Task AsyncRoute_IsOneFallback_AndNeverPretendsToPlan()
    {
        const string source = "Tick = 1\nStep(x) = x + Tick, x < 3\nStep(0).while";
        var generic = RunSource(source, optimize: false);
        var loops = new LoopOptimizationDiagnostics();
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();

        var (result, budget) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            Program(source), zeroArgPropertyResultCache: cache, loopDiagnostics: loops));

        Assert.Equal("ok 3", Outcome(result));
        Assert.Equal(generic.Budget, Budget.Of(budget));
        Assert.True(cache.AsyncAccesses > 0, "the run did not take the suspending async route");
        Assert.Equal(0, cache.SyncAccesses);
        var snapshot = loops.GetSnapshot();
        Assert.Equal(0, snapshot.OptimizedLoopHits);
        Assert.Equal(0, snapshot.LoopPlanBuilds);
        Assert.Empty(snapshot.LoopPlans);
        Assert.Equal(1, snapshot.OptimizedLoopFallbacks);
        AssertReasons(snapshot, (OptimizationDisabled, 1));
        Assert.Equal(generic.EmittedCount, result.Value.EmittedCount);
    }

    [Fact]
    public async Task AsyncRoute_CancelledWhileSuspended_StillObservesCancellation()
    {
        using var cancel = new CancellationTokenSource();
        var cache = new HoldingAsyncZeroArgPropertyResultCache(holdAtAccess: 1);
        var diagnostics = new LoopOptimizationDiagnostics();
        var pending = Evaluator.RunCountedObservedAsync(
            Program("Tick = 1\nStep(x) = x + Tick, x < 3\nStep(0).while"),
            zeroArgPropertyResultCache: cache,
            loopDiagnostics: diagnostics,
            cancellationToken: cancel.Token).AsTask();
        try
        {
            await cache.Reached.WaitAsync(TimeSpan.FromSeconds(10));
            Assert.False(pending.IsCompleted);
            Assert.Equal(1, diagnostics.OptimizedLoopFallbacks);
            Assert.Equal(0, diagnostics.LoopPlanBuilds);

            cancel.Cancel();
            cache.Release();
            var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(
                () => pending.WaitAsync(TimeSpan.FromSeconds(10)));
            Assert.Equal(cancel.Token, cancelled.CancellationToken);
            AssertReasons(diagnostics.GetSnapshot(), (OptimizationDisabled, 1));
        }
        finally
        {
            cancel.Cancel();
            cache.Release();
            try { await pending.WaitAsync(TimeSpan.FromSeconds(10)); }
            catch (OperationCanceledException) { }
        }
    }

    // ── T6: a zero-iteration repeat decides nothing ────────────────────────────────────

    [Fact]
    public void ZeroIterationRepeat_RecordsNoFallback()
    {
        const string source = "Inc(x) = x + 1\nInc(7).repeat(0)";
        var optimizing = RunSource(source, optimize: true);
        AssertParity(RunSource(source, optimize: false), optimizing);

        Assert.Equal("ok 7", optimizing.Outcome);
        Assert.Equal(1, optimizing.Loops.LoopExecutions);
        Assert.Equal(0, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(0, optimizing.Loops.OptimizedLoopFallbacks);
        Assert.Equal(0, optimizing.Loops.LoopPlanBuilds);
        Assert.Empty(optimizing.Loops.FallbackReasons);
        Assert.Equal(0, optimizing.GenericPreparations);
    }

    // ── T7: two independent refused loops are two events ───────────────────────────────

    [Fact]
    public void TwoRefusedLoops_AreTwoFallbacks_UnderTheSameReason()
    {
        const string source = "F(0) = 0\nF(n) = n - 1\nrepeat(F(5), 2) + repeat(F(9), 1)";
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        Assert.Equal("ok 11", optimizing.Outcome);
        AssertParity(generic, optimizing);
        Assert.Equal(2, optimizing.Loops.LoopExecutions);
        Assert.Equal(2, optimizing.Loops.LoopPlanBuilds);
        Assert.Equal(0, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(2, optimizing.Loops.OptimizedLoopFallbacks);
        AssertReasons(optimizing.Loops, (UnsupportedShape, 2));
    }

    // ── T8: nested loops — each loop's decision is its own event ────────────────────────

    [Fact]
    public void PlannedOuterLoop_RefusedInnerLoops_CountEachInnerRefusalOnce()
    {
        // The outer user step is planned (one hit); each of its two iterations runs the inner
        // family-step `repeat`, which the planner refuses — two inner events, one count each.
        const string source = "F(0) = 0\nF(n) = n - 1\nOuter(x) = repeat(F(x + 3), 1)\nOuter(0).repeat(2)";
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        Assert.Equal("ok 4", optimizing.Outcome);
        AssertParity(generic, optimizing);
        Assert.Equal(3, optimizing.Loops.LoopExecutions);
        Assert.Equal(3, optimizing.Loops.LoopPlanBuilds);
        Assert.Equal(1, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(2, optimizing.Loops.OptimizedLoopFallbacks);
        Assert.Equal(2, optimizing.Loops.FallbackReasons[UnsupportedShape]);
        Assert.Contains(optimizing.Loops.LoopPlans, static plan => plan.Optimized && plan.Identity == "Outer.repeat");
        Assert.Contains(optimizing.Loops.LoopPlans, static plan => !plan.Optimized && plan.FallbackReason == UnsupportedShape);
    }

    [Fact]
    public void RefusedOuterLoop_PlannedInnerLoops_CountTheOuterRefusalOnce()
    {
        // The outer family step is refused by the planner (one event); each of its two rounds
        // runs a planned inner `repeat` (two hits).
        const string source = "Inc(x) = x + 1\nG(0) = 0\nG(n) = Inc(n).repeat(2)\nrepeat(G(1), 2)";
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        Assert.Equal("ok 5", optimizing.Outcome);
        AssertParity(generic, optimizing);
        Assert.Equal(3, optimizing.Loops.LoopExecutions);
        Assert.Equal(3, optimizing.Loops.LoopPlanBuilds);
        Assert.Equal(2, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(1, optimizing.Loops.OptimizedLoopFallbacks);
        AssertReasons(optimizing.Loops, (UnsupportedShape, 1));
    }

    // ── T9: a planned loop ──────────────────────────────────────────────────────────────

    [Fact]
    public void SuccessfulWhile_IsOneHit_AndNoFallback()
    {
        const string source = "Step(x) = x + 1, x < 3\nStep(0).while";
        var optimizing = RunSource(source, optimize: true);
        AssertParity(RunSource(source, optimize: false), optimizing);

        Assert.Equal("ok 3", optimizing.Outcome);
        Assert.Equal(1, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(0, optimizing.Loops.OptimizedLoopFallbacks);
        Assert.Equal(1, optimizing.Loops.LoopPlanBuilds);
        Assert.Empty(optimizing.Loops.FallbackReasons);
        Assert.True(Assert.Single(optimizing.Loops.LoopPlans).Optimized);
    }

    [Fact]
    public void MetaLoop_PlannedAndRefusedSteps_KeepTheirSingleAccounting()
    {
        const string loop = "Loop(meta op) = op.Algorithm(op.Arguments*).while\n";
        var planned = RunSource("Step(x) = x + 1, x < 3\n" + loop + "Step(0).Loop", optimize: true);
        AssertParity(RunSource("Step(x) = x + 1, x < 3\n" + loop + "Step(0).Loop", optimize: false), planned);
        Assert.Equal("ok 3", planned.Outcome);
        Assert.Equal(1, planned.Loops.OptimizedLoopHits);
        Assert.Equal(0, planned.Loops.OptimizedLoopFallbacks);

        // The captured family step reaches the planner, which refuses it: one fallback.
        var refused = RunSource("F(0) = 0, false\nF(n) = n - 1, n > 1\n" + loop + "F(5).Loop", optimize: true);
        AssertParity(RunSource("F(0) = 0, false\nF(n) = n - 1, n > 1\n" + loop + "F(5).Loop", optimize: false), refused);
        Assert.Equal("ok 1", refused.Outcome);
        Assert.Equal(0, refused.Loops.OptimizedLoopHits);
        Assert.Equal(1, refused.Loops.LoopPlanBuilds);
        Assert.Equal(1, refused.Loops.OptimizedLoopFallbacks);
        AssertReasons(refused.Loops, (UnsupportedShape, 1));
    }

    // ── T10: a planned run's mid-iteration handover stays its own event ────────────────

    [Fact]
    public void MidIterationHandover_KeepsTheHit_AndRecordsTheHandoverOnce()
    {
        // `(S[0])*` emits two items, so the first planned iteration hands its assembled next
        // state to the generic continuation; completed work is never replayed (equal budgets).
        const string source = "Tick = 42\nS = ((1, 2), (3, 4))\nStep = {a + b + Tick, (S[0])*}\nrepeat(Step(0, 0), 2)";
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        AssertParity(generic, optimizing);
        Assert.Equal(1, optimizing.Loops.LoopExecutions);
        Assert.Equal(1, optimizing.Loops.LoopPlanBuilds);
        Assert.Equal(1, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(1, optimizing.Loops.OptimizedLoopFallbacks);
        Assert.Equal(1, optimizing.Loops.FallbackReasons[ExpressionDidNotEmitOneValue]);
        // The rows' expression-level reasons are their own events (one at plan construction,
        // one per planned evaluation of the fallback row), never a loop fallback.
        Assert.Equal(2, optimizing.Loops.FallbackReasons["unsupported spread expression"]);
        Assert.Equal(2, optimizing.Loops.FallbackReasons["unsupported local property reference: Tick"]);
        Assert.Equal(2, optimizing.Loops.PlannedExpressionFallbacks);
        Assert.Equal(2, optimizing.Loops.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.DoesNotContain(optimizing.Loops.FallbackReasons.Keys, static reason => reason.StartsWith("loop plan", StringComparison.Ordinal));
        Assert.True(Assert.Single(optimizing.Loops.LoopPlans).Optimized);
    }

    [Theory]
    [InlineData("Step(a, b) = {(1, 2)*, ()*, a != 1}\nStep(9, 0).while", "S[1, 2]", 1)]
    [InlineData("Step(n, a, b) = {n + 1, if(n < 2, a + 1, (1, 2))*, if(n < 2, b + 1, ())*}\nStep(0, 9, 0).repeat(5)", "S[5, 1, 2]", 3)]
    public void MultipleIncompatibleRows_AreOneHandover_WithEveryCauseRetained(
        string source, string expected, long plannedIterations)
    {
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        Assert.Equal("ok " + expected, optimizing.Outcome);
        AssertParity(generic, optimizing);
        var loops = optimizing.Loops;
        Assert.Equal(1, loops.LoopExecutions);
        Assert.Equal(1, loops.LoopPlanBuilds);
        Assert.Equal(1, loops.OptimizedLoopHits);
        Assert.True(loops.OptimizedLoopFallbacks == 1,
            System.Text.Json.JsonSerializer.Serialize(new { optimizing.Outcome, optimizing.GenericPreparations, Loops = loops }));
        Assert.Equal(plannedIterations, loops.LoopIterations);
        AssertReasons(loops, (ExpressionDidNotEmitOneValue, 2), ("unsupported spread expression", 2 + 2 * plannedIterations));
        Assert.Equal(2 * plannedIterations, loops.PlannedExpressionFallbacks);
        Assert.Equal(2 * plannedIterations, loops.GenericExpressionEvaluationsInsideOptimizedLoops);
        var plan = Assert.Single(loops.LoopPlans);
        Assert.True(plan.Optimized);
        Assert.Equal(1, plan.BuildCount);
        Assert.Equal(1, plan.ExecutionCount);
    }

    // ── T11/T12: expression, counted-parameter and temporary fallbacks are not loop fallbacks ──

    [Fact]
    public void CountedParameterFallback_KeepsItsCounters_AndInflatesNoLoopFallback()
    {
        const string source = """
            Pred(text) = {
                Step = if(text == 'a', k + 1, k + 1), k <= 1
                Step(0).while[0] > 0
            }

            ('a').filter(Pred).count
            """;
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        Assert.Equal("ok 1", optimizing.Outcome);
        AssertParity(generic, optimizing);
        Assert.Equal(1, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(0, optimizing.Loops.OptimizedLoopFallbacks);
        Assert.Equal(1, optimizing.Loops.CountedParameterReferencesFallbacks);
        Assert.Equal(1, optimizing.Loops.FallbackReasons[
            "unsupported counted parameter value shape: text (counted parameter is non-numeric: 'a')"]);
        Assert.DoesNotContain(optimizing.Loops.FallbackReasons.Keys, static reason => reason.StartsWith("loop plan", StringComparison.Ordinal));
        var plan = Assert.Single(optimizing.Loops.LoopPlans);
        Assert.True(plan.Optimized);
        Assert.Contains(plan.Expressions, static expression => !expression.Planned);
    }

    [Fact]
    public void ExpressionAndTemporaryFallbacks_KeepTheirDiagnostics_AndInflateNoLoopFallback()
    {
        const string source = "Step(n, m, p) = {\n    T = 'xxxx'\n    m + count((T, T))\n    n + if(T == T, 1, 0)\n    p + 1\n}\nStep(0, 0, 0).repeat(3)";
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        AssertParity(generic, optimizing);
        Assert.Equal(1, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(0, optimizing.Loops.OptimizedLoopFallbacks);
        Assert.True(optimizing.Loops.GenericExpressionEvaluationsInsideOptimizedLoops > 0);
        Assert.DoesNotContain(optimizing.Loops.FallbackReasons.Keys, static reason => reason.StartsWith("loop plan", StringComparison.Ordinal));
        var plan = Assert.Single(optimizing.Loops.LoopPlans);
        Assert.True(plan.Optimized);
        var temp = Assert.Single(plan.Temps);
        Assert.Equal("T", temp.Name);
        Assert.False(temp.Planned);
        Assert.Null(temp.PlanSummary);
        Assert.Equal("local properties require the shared generic cache in a partially planned loop", temp.FallbackReason);
        Assert.Equal(optimizing.Loops.PlannedExpressionFallbacks,
            optimizing.Loops.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(1, plan.BuildCount);
        Assert.Equal(1, plan.ExecutionCount);
        Assert.Contains(plan.Expressions, static expression => !expression.Planned);
    }

    // ── helpers ─────────────────────────────────────────────────────────────────────────

    private static void AssertParity(Run generic, Run optimizing)
    {
        Assert.Equal(generic.Outcome, optimizing.Outcome);
        Assert.Equal(generic.EmittedCount, optimizing.EmittedCount);
        Assert.Equal(generic.ErrorTree, optimizing.ErrorTree);
        Assert.Equal(generic.Budget, optimizing.Budget);
    }

    private static Run RunSource(string source, bool optimize)
    {
        var loops = new LoopOptimizationDiagnostics();
        var observations = new EvaluationObservations();
        var (result, budget) = Evaluator.RunCountedObserved(
            Program(source),
            enableOptimizations: optimize,
            loopDiagnostics: loops,
            observations: observations);
        return new Run(Outcome(result), Budget.Of(budget), loops.GetSnapshot(),
            observations.GenericLoopStepBindingPreparationCount,
            result.IsError ? null : result.Value.EmittedCount,
            result.IsError ? LoopDiagnosticParityAssertions.DescribeErrorTree(result.Error) : null);
    }

    private static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static string Outcome(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? "err " + LoopDiagnosticParityAssertions.Innermost(result.Error).GetType().Name
            : "ok " + SixRouteAgreement.Neutral(result.Value.Value);

    private static void AssertReasons(LoopOptimizationDiagnosticsSnapshot loops, params (string Reason, long Count)[] expected)
        => Assert.Equal(
            expected.OrderBy(static pair => pair.Reason, StringComparer.Ordinal).Select(static pair => $"{pair.Reason}:{pair.Count}"),
            loops.FallbackReasons.OrderBy(static pair => pair.Key, StringComparer.Ordinal).Select(static pair => $"{pair.Key}:{pair.Value}"));
}
