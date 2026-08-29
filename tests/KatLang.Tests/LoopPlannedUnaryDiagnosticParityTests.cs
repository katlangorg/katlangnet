using System.Numerics;
using KatLang.Optimizations.Loops;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// Optimizer-transparency regressions for a PLANNED unary operator inside an
/// optimized loop (architecture review item M3).
///
/// <para>The loop optimizer plans <c>-x</c> / <c>not x</c> into
/// <c>LoopExprPlan.Unary</c> and applied it through its own operator copy, which
/// stamped the unary expression's span onto the numeric-conversion failure
/// (<c>ExpectInt</c>'s <c>BadArity</c>) that the generic evaluator returns
/// UNSPANNED — the same program produced the same error KIND with different
/// structured span metadata depending on the evaluation strategy. Both
/// strategies now share <c>Evaluator.ApplyUnaryOperator</c>, whose policy is
/// pinned here: the numeric-conversion failure stays unspanned, while the
/// string rejection KEEPS its unary-expression span (both strategies always
/// stamped it — the fix must not overcorrect).</para>
///
/// <para>REACHABILITY. The optimized loop entry gate routes any loop whose
/// INITIAL state slots are not all numeric atoms to the generic path
/// ("non-scalar loop state slot"), so <c>repeat(S, 2, [1, 2])</c> never reaches
/// the planned evaluator; a planned unary meets a non-numeric operand only when
/// the state CHANGES KIND mid-loop — a fallback-planned sibling slot (or a
/// planned <c>if</c> string branch) writes the value into state and the planned
/// unary fails on a later iteration. The regressions here use those genuinely
/// planned shapes and prove the routing through the loop diagnostics; the
/// review's initial-state shape is kept as a generic-vs-generic parity pin at
/// the gate boundary.</para>
///
/// <para>The structured comparison machinery is shared with
/// <see cref="LoopPlannedIfDiagnosticParityTests"/> via
/// <see cref="LoopDiagnosticParityAssertions"/>; parity is asserted over the
/// ENTIRE error tree node by node (kinds, per-node spans, context payloads),
/// the rendered message, and the rendered span — never by relaxing either side
/// (see <c>src/KatLang/SEMANTIC-ALIGNMENT.md</c>, row "Optimized loops").</para>
/// </summary>
public class LoopPlannedUnaryDiagnosticParityTests
{
    /// <summary>
    /// The canonical planned-path reproducer: `-y` is fully planned, the sibling
    /// state slot is a fallback (property reference) that moves a LIST into `y`
    /// after iteration 1, and iteration 2's planned unary fails numeric
    /// conversion.
    /// </summary>
    private const string PlannedListRegressionSource = """
        Lst = [1, 2]
        S(x, y) = -y, Lst
        repeat(S, 3, 0, 0)
        """;

    private static LoopPlanDiagnosticSnapshot AssertOptimizedLoopPlan(
        LoopOptimizationDiagnosticsSnapshot loop,
        string planIdentity)
    {
        Assert.Equal(1, loop.OptimizedLoopHits);
        var plan = Assert.Single(loop.LoopPlans, candidate => candidate.Identity == planIdentity);
        Assert.True(plan.Optimized, $"Expected an optimized plan, got fallback: {plan.FallbackReason}");
        return plan;
    }

    /// <summary>
    /// Proves the optimized run genuinely applied the PLANNED unary: the loop is
    /// optimized and the unary-bearing expression slot is planned with the
    /// expected plan summary (planned slots never route through the generic
    /// evaluator — only <c>LoopExprPlan.Fallback</c> nodes do).
    /// </summary>
    private static void AssertPlannedUnarySlot(
        LoopOptimizationDiagnosticsSnapshot loop,
        string planIdentity,
        string unaryRole,
        int? unaryIndex,
        string unaryPlanSummary)
    {
        var plan = AssertOptimizedLoopPlan(loop, planIdentity);
        var unary = Assert.Single(
            plan.Expressions,
            expression => expression.Role == unaryRole && expression.Index == unaryIndex);
        Assert.True(unary.Planned, $"Expected a planned unary slot, got fallback: {unary.FallbackReason}");
        Assert.Equal(unaryPlanSummary, unary.PlanSummary);
    }

    // ── The planned-path regression ──────────────────────────────────────────

    [Fact]
    public void Repeat_PlannedUnary_StateBecomesListMidLoop_NumericConversionFailureMatchesGenericExactly()
    {
        // Iteration 1 binds y = 0 (`-y` succeeds) and the fallback sibling moves
        // the list into y's slot; iteration 2 fails numeric conversion INSIDE the
        // planned unary. The generic evaluator returns ExpectInt's BadArity
        // without stamping the unary expression's span; the planned evaluator
        // used to stamp it, so the same program produced two different
        // structured error trees depending on the evaluation strategy.
        var error = AssertOptimizerTransparentFailure(PlannedListRegressionSource);

        Assert.Equal(["while evaluating call to repeat"], ContextChain(error));

        var generic = Run(PlannedListRegressionSource, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        var genericInnermost = Assert.IsType<EvalError.BadArity>(Innermost(generic.Error));
        var optimizedInnermost = Assert.IsType<EvalError.BadArity>(Innermost(error));
        Assert.Null(genericInnermost.Span);
        Assert.Null(optimizedInnermost.Span);
    }

    [Fact]
    public void Repeat_PlannedUnary_RegressionUsesThePlannedUnaryPath()
    {
        // Proves the regression above really compared the planned unary evaluator
        // against generic evaluation, rather than two accidental same-strategy
        // runs: the optimized run plans `-y` (the fallback sibling is only the
        // list DELIVERY vehicle), both iterations apply the planned unary (two
        // planned builtin operations — iteration 2's failing application charges
        // before failing), and the generic run optimizes no loop.
        var (optimized, loop, _) = RunObserved(PlannedListRegressionSource, enableLoopOptimization: true);
        Assert.True(optimized.IsError);
        AssertPlannedUnarySlot(loop, "S.repeat", "output", 0, "Negate(StateSlot(y))");

        var plan = Assert.Single(loop.LoopPlans, candidate => candidate.Identity == "S.repeat");
        var sibling = Assert.Single(plan.Expressions, expression => expression.Role == "output" && expression.Index == 1);
        Assert.False(sibling.Planned);

        Assert.Equal(2, loop.LoopIterations);
        Assert.Equal(2, loop.PlannedExpressionHits);
        Assert.Equal(2, loop.PlannedBuiltinOperations);
        Assert.Equal(1, loop.PlannedExpressionFallbacks);
        Assert.Equal(1, loop.GenericExpressionEvaluationsInsideOptimizedLoops);

        var (generic, genericLoop, _) = RunObserved(PlannedListRegressionSource, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        Assert.Equal(0, genericLoop.OptimizedLoopHits);
        Assert.Equal(0, genericLoop.LoopIterations);
    }

    // ── Every planned unary operator and non-numeric operand kind ────────────

    public static TheoryData<string, string, string, int?, string, string> PlannedUnaryNumericConversionFailures()
        => new()
        {
            // UnaryOp.Minus and UnaryOp.Not are the only unary operators; cross
            // them with both non-numeric non-string operand kinds that can reach
            // a planned unary (exact list via a fallback property sibling,
            // sequence value via a fallback capture sibling) and both loop
            // kinds, including the while continuation slot.
            {
                "minus over list state (repeat)", "S.repeat", "output", 0, "Negate(StateSlot(y))",
                """
                Lst = [1, 2]
                S(x, y) = -y, Lst
                repeat(S, 3, 0, 0)
                """
            },
            {
                "not over list state (repeat)", "S.repeat", "output", 0, "Not(StateSlot(y))",
                """
                Lst = [1, 2]
                S(x, y) = not y, Lst
                repeat(S, 3, 0, 0)
                """
            },
            {
                "minus over sequence state (repeat)", "S.repeat", "output", 0, "Negate(StateSlot(y))",
                """
                S(x, y) = -y, (x, 9)
                repeat(S, 3, 0, 0)
                """
            },
            {
                "not over sequence state (repeat)", "S.repeat", "output", 0, "Not(StateSlot(y))",
                """
                S(x, y) = not y, (x, 9)
                repeat(S, 3, 0, 0)
                """
            },
            {
                "minus in while next-state slot", "S.while", "output", 0, "Negate(StateSlot(y))",
                """
                Lst = [1, 2]
                S(x, y) = -y, Lst, x < 3
                while(S, 0, 0)
                """
            },
            {
                "not in while continuation slot", "S.while", "continuation", null, "Not(StateSlot(y))",
                """
                Lst = [1, 2]
                S(x, y) = x + 1, Lst, not y
                while(S, 0, 0)
                """
            },
        };

    [Theory]
    [MemberData(nameof(PlannedUnaryNumericConversionFailures))]
    public void PlannedUnary_NumericConversionFailure_MatchesGenericStructuredTreeExactly(
        string position, string planIdentity, string unaryRole, int? unaryIndex, string unaryPlanSummary, string source)
    {
        Assert.False(string.IsNullOrEmpty(position));

        var error = AssertOptimizerTransparentFailure(source);

        // The innermost error is ExpectInt's BadArity, UNSPANNED on both paths.
        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        var genericInnermost = Assert.IsType<EvalError.BadArity>(Innermost(generic.Error));
        var optimizedInnermost = Assert.IsType<EvalError.BadArity>(Innermost(error));
        Assert.Null(genericInnermost.Span);
        Assert.Null(optimizedInnermost.Span);

        // The optimized side really exercised the planned unary.
        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        AssertPlannedUnarySlot(loop, planIdentity, unaryRole, unaryIndex, unaryPlanSummary);
    }

    // ── The string rejection KEEPS its span (no overcorrection) ──────────────

    [Fact]
    public void PlannedUnary_StringOperand_KeepsSpannedStringRejectionInBothTrees()
    {
        // A FULLY planned failing shape: the planned `if` selects the string
        // branch once x stops being positive, and the planned unary rejects it.
        // The unary string rejection is stamped with the unary EXPRESSION's span
        // by both strategies — removing the planned ExpectInt stamping must not
        // also strip this one. `-if(x > 0, x - 1, 'ab')` spans line 1,
        // columns 8..30.
        var source = """
            S(x) = -if(x > 0, x - 1, 'ab')
            repeat(S, 3, 1)
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.Equal(["while evaluating call to repeat"], ContextChain(error));

        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        var genericInnermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(generic.Error));
        var optimizedInnermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.Equal("Unary operator is not supported for strings", genericInnermost.Message);
        Assert.Equal("Unary operator is not supported for strings", optimizedInnermost.Message);

        // Absolute span pin on BOTH innermost errors: the shared helper stamps
        // the unary expression's span, so strategy parity alone cannot mask a
        // policy regression here.
        Assert.NotNull(genericInnermost.Span);
        Assert.NotNull(optimizedInnermost.Span);
        Assert.Equal(genericInnermost.Span, optimizedInnermost.Span);
        Assert.Equal(1, genericInnermost.Span!.StartLineNumber);
        Assert.Equal(8, genericInnermost.Span!.StartColumn);
        Assert.Equal(1, genericInnermost.Span!.EndLineNumber);
        Assert.Equal(30, genericInnermost.Span!.EndColumn);

        // The optimized side is FULLY planned: nothing fell back, so the failing
        // application is unambiguously the planned unary over the planned if.
        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        var plan = AssertOptimizedLoopPlan(loop, "S.repeat");
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
        var output = Assert.Single(plan.Expressions, expression => expression.Role == "output" && expression.Index == 0);
        Assert.True(output.Planned);
        Assert.Equal(
            "Negate(If(GreaterThan(StateSlot(x), Const(0)), Subtract(StateSlot(x), Const(1)), StringConst(length=2)))",
            output.PlanSummary);
    }

    [Fact]
    public void PlannedUnary_NotOverString_KeepsSpannedStringRejectionInBothTrees()
    {
        // The `not` operator through the fallback-sibling delivery shape: the
        // string moves into y after iteration 1 and the planned `not y` rejects
        // it with the unary expression's span on both paths.
        var source = """
            Txt = 'ab'
            S(x, y) = not y, Txt
            repeat(S, 3, 0, 0)
            """;

        var error = AssertOptimizerTransparentFailure(source);

        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        var genericInnermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(generic.Error));
        var optimizedInnermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.NotNull(genericInnermost.Span);
        Assert.Equal(genericInnermost.Span, optimizedInnermost.Span);
        Assert.Equal(new SourceSpan(2, 11, 2, 15), genericInnermost.Span);
        Assert.Equal(((int?)2, (int?)11, (int?)2, (int?)15), Span(generic.Error));
        Assert.Equal(((int?)2, (int?)11, (int?)2, (int?)15), Span(error));

        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        AssertPlannedUnarySlot(loop, "S.repeat", "output", 0, "Not(StateSlot(y))");
    }

    [Fact]
    public void PlannedNestedUnary_StringFailureKeepsTheInnerUnaryAbsoluteSpan()
    {
        // The inner minus raises the string TypeMismatch after the planned `if`
        // selects its string branch. The outer planned `not` must propagate that
        // already-spanned failure unchanged rather than replacing it with its own
        // wider span. A separate state slot drives the branch so the outer `not`
        // cannot hold the driver positive. The inner `-if(...)` is line 1,
        // columns 22..40.
        var source = """
            S(x, y) = x - 1, not -if(x > 0, y, 'ab')
            repeat(S, 3, 1, 0)
            """;

        var optimizedError = AssertOptimizerTransparentFailure(source);
        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);

        var expectedSpan = new SourceSpan(1, 22, 1, 40);
        Assert.Equal(expectedSpan, Assert.IsType<EvalError.TypeMismatch>(Innermost(generic.Error)).Span);
        Assert.Equal(expectedSpan, Assert.IsType<EvalError.TypeMismatch>(Innermost(optimizedError)).Span);
        Assert.Equal(((int?)1, (int?)22, (int?)1, (int?)40), Span(generic.Error));
        Assert.Equal(((int?)1, (int?)22, (int?)1, (int?)40), Span(optimizedError));

        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        AssertPlannedUnarySlot(
            loop,
            "S.repeat",
            "output",
            1,
            "Not(Negate(If(GreaterThan(StateSlot(x), Const(0)), StateSlot(y), StringConst(length=2))))");
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
    }

    // ── Successful unary operations ──────────────────────────────────────────

    public static TheoryData<string, string, decimal[]> PlannedUnarySuccesses()
        => new()
        {
            {
                "repeated negation",
                """
                S(a) = -a
                repeat(S, 3, 5)
                """,
                new[] { -5m }
            },
            {
                "repeated not from non-zero",
                """
                S(a) = not a
                repeat(S, 1, 5)
                """,
                new[] { 0m }
            },
            {
                "repeated not from zero",
                """
                S(a) = not a
                repeat(S, 1, 0)
                """,
                new[] { 1m }
            },
            {
                "chained double negation",
                """
                S(x) = - -x
                repeat(S, 2, 3)
                """,
                new[] { 3m }
            },
            {
                "negation in while next-state",
                """
                S(a) = -a, a > 0
                while(S, 5)
                """,
                new[] { -5m }
            },
        };

    [Theory]
    [MemberData(nameof(PlannedUnarySuccesses))]
    public void PlannedUnary_SuccessfulOperation_ProducesIdenticalValuesInBothModes(
        string label, string source, decimal[] expectedAtoms)
    {
        Assert.False(string.IsNullOrEmpty(label));
        var expected = expectedAtoms.Select(static atom => (Decimal128)atom).ToArray();

        var expectedValue = Result.FromItems(expected.Select(static atom => (Result)new Result.Atom(atom)));
        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        Assert.False(generic.IsError, $"Expected generic success but got: {(generic.IsError ? generic.Error : null)}");
        Assert.Equal(expectedValue, generic.Value.Value, Result.ValueComparer);

        var (optimized, _) = RunCountedObserved(source, enableLoopOptimization: true);
        Assert.False(optimized.IsError, $"Expected optimized success but got: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal(expectedValue, optimized.Value.Value, Result.ValueComparer);
        Assert.Equal(generic.Value.Value, optimized.Value.Value, Result.ValueComparer);
        Assert.Equal(generic.Value.EmittedCount, optimized.Value.EmittedCount);
        Assert.Equal(expectedValue.ValueCount(), optimized.Value.EmittedCount);
    }

    [Fact]
    public void PlannedUnary_SuccessfulNegation_UsesThePlannedUnaryPath()
    {
        var source = """
            S(a) = -a
            repeat(S, 3, 5)
            """;

        var (result, loop, _) = RunObserved(source, enableLoopOptimization: true);
        Assert.False(result.IsError);
        AssertPlannedUnarySlot(loop, "S.repeat", "output", 0, "Negate(StateSlot(a))");
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(3, loop.LoopIterations);
    }

    public static TheoryData<string, string, string> PlannedNumericMinusEdgeCases()
        => new()
        {
            {
                "negative zero",
                """
                S(a) = -a
                repeat(S, 1, 0)
                """,
                "-0"
            },
            {
                "Decimal128 quantum",
                """
                S(a) = -a
                repeat(S, 1, 1.50)
                """,
                "-1.50"
            },
            {
                "NaN",
                """
                N = Math.Sqrt(-1)
                S(a) = -a
                repeat(S, 1, N)
                """,
                "NaN"
            },
        };

    [Theory]
    [MemberData(nameof(PlannedNumericMinusEdgeCases))]
    public void PlannedUnary_NumericMinusFastPath_PreservesDecimal128ValueAndCount(
        string label,
        string source,
        string expectedDisplay)
    {
        Assert.False(string.IsNullOrEmpty(label));
        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (optimized, loop) = RunCountedObserved(source, enableLoopOptimization: true);

        Assert.False(generic.IsError, $"Expected generic success but got: {(generic.IsError ? generic.Error : null)}");
        Assert.False(optimized.IsError, $"Expected optimized success but got: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal(generic.Value.Value, optimized.Value.Value, Result.ValueComparer);
        Assert.Equal(generic.Value.EmittedCount, optimized.Value.EmittedCount);
        Assert.Equal(1, optimized.Value.EmittedCount);
        Assert.Equal(expectedDisplay, Evaluator.FormatResultForDiagnostic(optimized.Value.Value));

        if (expectedDisplay == "-0")
            Assert.True(Decimal128.IsNegative(Assert.IsType<Result.Atom>(optimized.Value.Value).Value));
        if (expectedDisplay == "NaN")
            Assert.True(Decimal128.IsNaN(Assert.IsType<Result.Atom>(optimized.Value.Value).Value));

        AssertPlannedUnarySlot(loop, "S.repeat", "output", 0, "Negate(StateSlot(a))");
        Assert.Equal(1, loop.PlannedBuiltinOperations);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
    }

    [Fact]
    public void PlannedUnary_NumericNotFastPath_UsesZeroTruthAndKeepsOneEmission()
    {
        var source = """
            S(a) = not a
            repeat(S, 1, 0)
            """;

        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (optimized, loop) = RunCountedObserved(source, enableLoopOptimization: true);

        Assert.False(generic.IsError);
        Assert.False(optimized.IsError);
        Assert.Equal(new Result.Atom(Decimal128.One), generic.Value.Value, Result.ValueComparer);
        Assert.Equal(generic.Value.Value, optimized.Value.Value, Result.ValueComparer);
        Assert.Equal(1, generic.Value.EmittedCount);
        Assert.Equal(generic.Value.EmittedCount, optimized.Value.EmittedCount);
        AssertPlannedUnarySlot(loop, "S.repeat", "output", 0, "Not(StateSlot(a))");
        Assert.Equal(1, loop.PlannedBuiltinOperations);
    }

    // ── The generic gate boundary ────────────────────────────────────────────

    [Fact]
    public void Repeat_ListInitialState_ReviewedShape_MatchesGenericExactly()
    {
        // The architecture review's literal reproducer. TODAY this routes the
        // loop to the GENERIC path in both modes — the optimized entry gate
        // rejects non-atom initial state slots ("non-scalar loop state slot")
        // before any plan is built — so this is a parity pin at the gate
        // boundary; the genuinely planned reachability is covered by the
        // state-kind-change regressions above. If the gate ever starts
        // admitting non-scalar initial states, the routing assertion below
        // fails and this case must graduate to a planned-path regression.
        var source = """
            S(a) = -a
            repeat(S, 2, [1, 2])
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.Equal(["while evaluating call to repeat"], ContextChain(error));

        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        Assert.Null(Assert.IsType<EvalError.BadArity>(Innermost(generic.Error)).Span);
        Assert.Null(Assert.IsType<EvalError.BadArity>(Innermost(error)).Span);

        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        Assert.Equal(0, loop.OptimizedLoopHits);
        Assert.Contains("non-scalar loop state slot", loop.FallbackReasons.Keys);
    }

    [Fact]
    public void Repeat_EmptySequenceState_StaysTransparentInBothModes()
    {
        // `-()` propagates the empty sequence value unchanged (the shared
        // application's empty arm). An empty INITIAL state routes generic at
        // the same gate as above, and a mid-loop `()` state forces the generic
        // continuation (zero-emission slots), so this pins value parity across
        // that boundary.
        var source = """
            S(a) = -a
            repeat(S, 2, ())
            """;

        var generic = Run(source, enableLoopOptimization: false);
        Assert.False(generic.IsError, $"Expected generic success but got: {(generic.IsError ? generic.Error : null)}");
        var genericValue = Assert.IsType<Result.SequenceValue>(generic.Value);
        Assert.Empty(genericValue.Items);

        var optimized = Run(source, enableLoopOptimization: true);
        Assert.False(optimized.IsError, $"Expected optimized success but got: {(optimized.IsError ? optimized.Error : null)}");
        var optimizedValue = Assert.IsType<Result.SequenceValue>(optimized.Value);
        Assert.Empty(optimizedValue.Items);
    }

    // ── Outer evaluation layers do not re-span the unspanned innermost ───────

    [Fact]
    public void PlannedUnary_FailureInsideEnclosingExpression_KeepsUnspannedInnermost()
    {
        // The failing `repeat` sits inside a binary expression inside a
        // property, so several outer evaluator layers run after the planned
        // unary fails. The innermost BadArity must stay unspanned on both
        // paths; only the surrounding boundaries attach spans, identically in
        // both strategies.
        var source = """
            Lst = [1, 2]
            S(x, y) = -y, Lst
            Total = repeat(S, 3, 0, 0) + 100
            Total
            """;

        var error = AssertOptimizerTransparentFailure(source);

        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        Assert.Null(Assert.IsType<EvalError.BadArity>(Innermost(generic.Error)).Span);
        Assert.Null(Assert.IsType<EvalError.BadArity>(Innermost(error)).Span);

        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        AssertPlannedUnarySlot(loop, "S.repeat", "output", 0, "Negate(StateSlot(y))");
    }
}
