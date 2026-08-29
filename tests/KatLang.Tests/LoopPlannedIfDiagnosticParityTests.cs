using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// Optimizer-transparency regressions for a PLANNED <c>if</c> inside an optimized
/// loop.
///
/// <para>The loop optimizer plans <c>if(cond, a, b)</c> into
/// <c>LoopExprPlan.If</c> and evaluates it directly, which dropped the
/// <c>while evaluating call to if</c> frame the generic evaluator (and Lean)
/// attach at the ordinary <c>if</c> call boundary. The reported reproducer
/// <c>S(n) = if(n &lt; 3, n + 1, 1 / 0)</c> / <c>repeat(S, 5, 1)</c> produced
/// "while evaluating call to repeat: Division by zero" with the optimizer on and
/// "while evaluating call to repeat: while evaluating call to if: Division by
/// zero" with it off.</para>
///
/// <para>The structured comparison machinery is shared with the other planned-node
/// parity suites in <see cref="LoopDiagnosticParityAssertions"/>: the loop
/// optimizer is a C#-only execution strategy over the generic Lean loop semantics
/// (see <c>src/KatLang/SEMANTIC-ALIGNMENT.md</c>, row "Optimized loops": no Lean
/// update, equivalence tests required), so its contract is pinned here as exact
/// optimized-vs-generic diagnostic equivalence — error kind, complete context
/// chain, and span — never by relaxing either side.</para>
/// </summary>
public class LoopPlannedIfDiagnosticParityTests
{
    // ── The reported reproducer ──────────────────────────────────────────────

    [Fact]
    public void Repeat_PlannedIf_FalseBranchDivisionByZero_KeepsIfCallContextFrame()
    {
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0)
            repeat(S, 5, 1)
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Equal(
            ["while evaluating call to repeat", "while evaluating call to if"],
            ContextChain(error));
        Assert.Equal(
            "while evaluating call to repeat: while evaluating call to if: Division by zero",
            KatLangError.FromEvalError(error).Message);
    }

    [Fact]
    public void Repeat_PlannedIf_ReproducerUsesThePlannedIfPath()
    {
        // Proves the regression above really exercised LoopExprPlan.If rather than
        // an incidental generic fallback: the loop is optimized, the whole step
        // output is planned as an `If(...)`, and nothing inside it fell back to the
        // generic evaluator.
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0)
            repeat(S, 5, 1)
            """;

        var (result, loop, _) = RunObserved(source, enableLoopOptimization: true);

        Assert.True(result.IsError);
        Assert.Equal(1, loop.OptimizedLoopHits);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);

        var plan = Assert.Single(loop.LoopPlans, candidate => candidate.Identity == "S.repeat");
        Assert.True(plan.Optimized, $"Expected an optimized plan, got fallback: {plan.FallbackReason}");
        var output = Assert.Single(plan.Expressions, expression => expression.Role == "output" && expression.Index == 0);
        Assert.True(output.Planned);
        Assert.Equal(
            "If(LessThan(StateSlot(n), Const(3)), Add(StateSlot(n), Const(1)), Divide(Const(1), Const(0)))",
            output.PlanSummary);
    }

    // ── Every logical failure position of a planned `if` ─────────────────────

    public static TheoryData<string, string> PlannedIfFailurePositions()
    {
        var data = new TheoryData<string, string>();

        // Condition failure.
        data.Add(
            "condition",
            """
            S(n) = if(1 / 0, n + 1, n)
            repeat(S, 5, 1)
            """);

        // Selected TRUE branch failure (n starts at 1, so the first iteration takes it).
        data.Add(
            "selected true branch",
            """
            S(n) = if(n < 3, 1 / 0, n)
            repeat(S, 5, 1)
            """);

        // Selected FALSE branch failure (taken once n reaches 3).
        data.Add(
            "selected false branch",
            """
            S(n) = if(n < 3, n + 1, 1 / 0)
            repeat(S, 5, 1)
            """);

        // The `if` itself: a string condition has no truth value.
        data.Add(
            "condition without a truth value",
            """
            S(n) = if('x', n + 1, n)
            repeat(S, 5, 1)
            """);

        return data;
    }

    [Theory]
    [MemberData(nameof(PlannedIfFailurePositions))]
    public void PlannedIf_FailureAtAnyPosition_MatchesGenericDiagnosticExactly(string position, string source)
    {
        Assert.False(string.IsNullOrEmpty(position));

        var error = AssertOptimizerTransparentFailure(source);

        Assert.Equal(
            ["while evaluating call to repeat", "while evaluating call to if"],
            ContextChain(error));
    }

    [Fact]
    public void PlannedIf_InvalidTruthCondition_KeepsBadArityUnspannedInBothStructuredTrees()
    {
        // The `if` truth-value rejection is the one planned failure the plan RAISES
        // itself rather than propagates. The generic builtin returns an UNSPANNED
        // BadArity and lets the surrounding call boundary stamp only the context
        // wrappers, so the planned path must not pre-stamp the innermost error:
        // EvalError.WithContext.Inner.Span is public state, and a spanned innermost
        // BadArity is an observable structured-tree divergence even when the rendered
        // message and outermost span agree.
        var source = """
            S(n) = if('x', n + 1, n)
            repeat(S, 5, 1)
            """;

        // The optimized run really exercises the planned `if` (not a fallback).
        var (optimized, loop, _) = RunObserved(source, enableLoopOptimization: true);
        Assert.True(optimized.IsError);
        Assert.Equal(1, loop.OptimizedLoopHits);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
        var plan = Assert.Single(loop.LoopPlans, candidate => candidate.Identity == "S.repeat");
        Assert.True(plan.Optimized, $"Expected an optimized plan, got fallback: {plan.FallbackReason}");
        var output = Assert.Single(plan.Expressions, expression => expression.Role == "output" && expression.Index == 0);
        Assert.True(output.Planned);
        Assert.Equal(
            "If(StringConst(length=1), Add(StateSlot(n), Const(1)), StateSlot(n))",
            output.PlanSummary);

        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);

        // Complete structured trees are equal, and the innermost BadArity is
        // unspanned on BOTH paths.
        Assert.Equal(DescribeErrorTree(generic.Error), DescribeErrorTree(optimized.Error));
        var genericInnermost = Assert.IsType<EvalError.BadArity>(Innermost(generic.Error));
        var optimizedInnermost = Assert.IsType<EvalError.BadArity>(Innermost(optimized.Error));
        Assert.Null(genericInnermost.Span);
        Assert.Null(optimizedInnermost.Span);

        // The context frames are intact and the enclosing public diagnostic still
        // carries the `if(...)` call expression's span (line 1, columns 8..24).
        Assert.Equal(
            ["while evaluating call to repeat", "while evaluating call to if"],
            ContextChain(optimized.Error));
        Assert.Equal(((int?)1, (int?)8, (int?)1, (int?)24), Span(optimized.Error));
        Assert.Equal(((int?)1, (int?)8, (int?)1, (int?)24), Span(generic.Error));
    }

    [Fact]
    public void PlannedIf_NestedFailingIf_NestsBothCallContextFrames()
    {
        // The inner planned `if` is the operand of the outer planned `if`'s false
        // branch, so the generic composition attaches TWO `if` frames.
        var source = """
            S(n) = if(n < 3, n + 1, if(1, 1 / 0, 0))
            repeat(S, 5, 1)
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Equal(
            [
                "while evaluating call to repeat",
                "while evaluating call to if",
                "while evaluating call to if",
            ],
            ContextChain(error));
    }

    [Fact]
    public void PlannedIf_InsideWhileLoop_AlsoKeepsIfCallContextFrame()
    {
        // The same planned-`if` evaluation serves `while`; its continuation slot is
        // planned too, so pin the loop kind that reaches the plan by a second route.
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0), n <= 10
            S.while(1):0
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Contains("while evaluating call to if", ContextChain(error));
    }

    [Fact]
    public void PlannedIf_FailureInsideAnEnclosingExpression_KeepsTheInnerFrames()
    {
        // The failing `repeat` sits inside a binary expression inside a property, so
        // several outer evaluator layers run after the planned `if` fails. None of
        // them may replace the `if` frame or re-span the error onto the enclosing
        // line-2 expression.
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0)
            Total = repeat(S, 5, 1) + 100
            Total
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Equal(
            ["while evaluating call to repeat", "while evaluating call to if"],
            ContextChain(error));

        // The `1 / 0` operand on line 1, not the enclosing line-2 expression.
        var span = Span(error);
        Assert.Equal(1, span.StartLine);
        Assert.Equal(25, span.StartColumn);
        Assert.Equal(1, span.EndLine);
    }

    // ── Preserved behavior: values, laziness, counters, cache ────────────────

    [Fact]
    public void PlannedIf_SuccessfulRuns_AreUnchangedInBothModes()
    {
        // `repeat(S, 2, 1)` never selects the failing false branch, so a lazily
        // evaluated planned `if` succeeds: branch laziness is preserved.
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0)
            repeat(S, 2, 1)
            """;

        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError == false, $"Expected generic success but got: {(generic.IsError ? generic.Error : null)}");
        Assert.Equal([3m], generic.Value.ToAtoms());

        var optimized = Run(source, enableLoopOptimization: true);
        Assert.True(optimized.IsError == false, $"Expected optimized success but got: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal([3m], optimized.Value.ToAtoms());
    }

    [Fact]
    public void PlannedIf_FailingRun_KeepsItsStepCountsAndCacheState()
    {
        // Pins the operational shape of the optimized failing run so adding the
        // missing diagnostic frame cannot change WHEN the loop stops or how much
        // work it does: `n` walks 1 -> 2 -> 3 over two successful iterations and the
        // third iteration selects the failing false branch. The planned-builtin count
        // is one `<`, one `if`, and one `+` per successful iteration, plus the third
        // iteration's `<`, `if`, and failing `/`.
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0)
            repeat(S, 5, 1)
            """;

        var (result, loop, cache) = RunObserved(source, enableLoopOptimization: true);

        Assert.True(result.IsError);
        Assert.Equal(1, loop.OptimizedLoopHits);
        Assert.Equal(1, loop.LoopPlanBuilds);
        Assert.Equal(3, loop.LoopIterations);
        Assert.Equal(3, loop.PlannedExpressionHits);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(9, loop.PlannedBuiltinOperations);

        // The step is a one-parameter callable, so no zero-argument property cache
        // entry is created on either path; the generic run must agree exactly.
        var (_, _, genericCache) = RunObserved(source, enableLoopOptimization: false);
        Assert.Equal(CacheCounters(genericCache), CacheCounters(cache));
    }
}
