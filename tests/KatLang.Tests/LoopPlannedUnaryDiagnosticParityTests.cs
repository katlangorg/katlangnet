using System.Numerics;
using KatLang.Optimizations.Loops;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// Optimizer-transparency regressions for a PLANNED unary operator inside an
/// optimized loop (architecture review item M3).
///
/// <para>The loop optimizer plans <c>-x</c> / <c>not x</c> into
/// <c>LoopExprPlan.Unary</c> and once applied it through its own operator copy,
/// which stamped the unary expression's span onto the numeric-conversion failure
/// (<c>ExpectInt</c>'s <c>BadArity</c>) while the generic evaluator returned it
/// unspanned — the same program produced the same error KIND with different
/// structured span metadata depending on the evaluation strategy. Both
/// strategies now share <c>Evaluator.ApplyUnaryOperator</c>, whose policy is
/// pinned here: every operand rejection — the numeric-conversion failure and the
/// string rejection alike — carries the unary expression's span (F5), identically
/// on both paths, and the innermost span is never overwritten by an enclosing
/// evaluation layer.</para>
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
/// the gate boundary. A captured caller parameter can also supply any value
/// directly to a planned unary, including `()` without a zero-emission handover.</para>
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
        // planned unary. Both strategies report ExpectInt's BadArity at the written
        // unary `-y` (line 2, columns 11-12; F5) — the planned evaluator once
        // stamped a span the generic one omitted, so the same program produced
        // two different structured error trees depending on the strategy.
        var error = AssertOptimizerTransparentFailure(PlannedListRegressionSource);

        Assert.Equal(["while evaluating call to repeat"], ContextChain(error));

        var generic = Run(PlannedListRegressionSource, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        var genericInnermost = Assert.IsType<EvalError.BadArity>(Innermost(generic.Error));
        var optimizedInnermost = Assert.IsType<EvalError.BadArity>(Innermost(error));
        Assert.Equal(new SourceSpan(2, 11, 2, 13), genericInnermost.Span);
        Assert.Equal(new SourceSpan(2, 11, 2, 13), optimizedInnermost.Span);
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

    public static TheoryData<string, string, string, int?, string, string> PlannedUnaryOperandRejections()
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
                repeat(S, 3, 0, false)
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
                repeat(S, 3, 0, false)
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
                while(S, 0, false)
                """
            },
        };

    [Theory]
    [MemberData(nameof(PlannedUnaryOperandRejections))]
    public void PlannedUnary_OperandRejection_MatchesGenericStructuredTreeExactly(
        string position, string planIdentity, string unaryRole, int? unaryIndex, string unaryPlanSummary, string source)
    {
        Assert.False(string.IsNullOrEmpty(position));

        var error = AssertOptimizerTransparentFailure(source);

        // The innermost error is the operand rejection (ExpectInt's BadArity for `-`, the
        // Boolean-operand TypeMismatch for `not`), carrying the span of the written unary
        // in the step body on both paths (F5), never spanless.
        var rejection = unaryPlanSummary.StartsWith("Not(", StringComparison.Ordinal)
            ? typeof(EvalError.TypeMismatch)
            : typeof(EvalError.BadArity);
        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        var genericInnermost = Innermost(generic.Error);
        var optimizedInnermost = Innermost(error);
        Assert.IsType(rejection, genericInnermost);
        Assert.IsType(rejection, optimizedInnermost);
        Assert.NotNull(genericInnermost.Span);
        Assert.Equal(genericInnermost.Span, optimizedInnermost.Span);
        var stepLine = source.Split('\n').Select((line, index) => (line, index)).Single(row => row.line.StartsWith("S(", StringComparison.Ordinal)).index + 1;
        Assert.Equal(stepLine, Assert.NotNull(genericInnermost.Span).Start.Line);

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
        Assert.Equal(genericInnermost.Span, optimizedInnermost.Span);
        Assert.Equal(new SourceSpan(1, 8, 1, 31), genericInnermost.Span);

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
            repeat(S, 3, 0, false)
            """;

        var error = AssertOptimizerTransparentFailure(source);

        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        var genericInnermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(generic.Error));
        var optimizedInnermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.NotNull(genericInnermost.Span);
        Assert.Equal(genericInnermost.Span, optimizedInnermost.Span);
        Assert.Equal(new SourceSpan(2, 11, 2, 16), genericInnermost.Span);
        Assert.Equal("operator `not` expects a Boolean operand, but the operand was a string: 'ab'", genericInnermost.Message);
        Assert.Equal(new SourceSpan(2, 11, 2, 16), Span(generic.Error));
        Assert.Equal(new SourceSpan(2, 11, 2, 16), Span(error));

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
        // columns 23..41 (`not` needs a Boolean, so the negation feeds a planned comparison).
        var source = """
            S(x, y) = x - 1, not (-if(x > 0, y, 'ab') > 0)
            repeat(S, 3, 1, 0)
            """;

        var optimizedError = AssertOptimizerTransparentFailure(source);
        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);

        var expectedSpan = new SourceSpan(1, 23, 1, 42);
        Assert.Equal(expectedSpan, Assert.IsType<EvalError.TypeMismatch>(Innermost(generic.Error)).Span);
        Assert.Equal(expectedSpan, Assert.IsType<EvalError.TypeMismatch>(Innermost(optimizedError)).Span);
        Assert.Equal(new SourceSpan(1, 23, 1, 42), Span(generic.Error));
        Assert.Equal(new SourceSpan(1, 23, 1, 42), Span(optimizedError));

        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        AssertPlannedUnarySlot(
            loop,
            "S.repeat",
            "output",
            1,
            "Not(GreaterThan(Negate(If(GreaterThan(StateSlot(x), Const(0)), StateSlot(y), StringConst(length=2))), Const(0)))");
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
    }

    // ── Successful unary operations ──────────────────────────────────────────

    public static TheoryData<string, string, string> PlannedUnarySuccesses()
        => new()
        {
            {
                "repeated negation",
                """
                S(a) = -a
                repeat(S, 3, 5)
                """,
                "-5"
            },
            {
                "repeated not from true",
                """
                S(a) = not a
                repeat(S, 1, true)
                """,
                "false"
            },
            {
                "repeated not from false",
                """
                S(a) = not a
                repeat(S, 1, false)
                """,
                "true"
            },
            {
                "chained double negation",
                """
                S(x) = - -x
                repeat(S, 2, 3)
                """,
                "3"
            },
            {
                "negation in while next-state",
                """
                S(a) = -a, a > 0
                while(S, 5)
                """,
                "-5"
            },
        };

    [Theory]
    [MemberData(nameof(PlannedUnarySuccesses))]
    public void PlannedUnary_SuccessfulOperation_ProducesIdenticalValuesInBothModes(
        string label, string source, string expectedDisplay)
    {
        Assert.False(string.IsNullOrEmpty(label));
        // Numeric rows negate numbers; Boolean rows negate Booleans (`not` never sees a number).
        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        Assert.False(generic.IsError, $"Expected generic success but got: {(generic.IsError ? generic.Error : null)}");
        Assert.Equal(expectedDisplay, Evaluator.FormatResultForDiagnostic(generic.Value.Value));

        var (optimized, _) = RunCountedObserved(source, enableLoopOptimization: true);
        Assert.False(optimized.IsError, $"Expected optimized success but got: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal(expectedDisplay, Evaluator.FormatResultForDiagnostic(optimized.Value.Value));
        Assert.Equal(generic.Value.Value, optimized.Value.Value, Result.ValueComparer);
        Assert.Equal(generic.Value.EmittedCount, optimized.Value.EmittedCount);
        Assert.Equal(1, optimized.Value.EmittedCount);
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
    public void PlannedUnary_BooleanNot_KeepsOneEmissionInBothModes()
    {
        var source = """
            S(a) = not a
            repeat(S, 1, false)
            """;

        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (optimized, loop) = RunCountedObserved(source, enableLoopOptimization: true);

        Assert.False(generic.IsError);
        Assert.False(optimized.IsError);
        Assert.Equal(new Result.Bool(true), generic.Value.Value, Result.ValueComparer);
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
        // The innermost BadArity sits at the unary expression `-a` (line 1, columns 8-9)
        // on both paths (F5).
        Assert.Equal(new SourceSpan(1, 8, 1, 10), Assert.IsType<EvalError.BadArity>(Innermost(generic.Error)).Span);
        Assert.Equal(new SourceSpan(1, 8, 1, 10), Assert.IsType<EvalError.BadArity>(Innermost(error)).Span);

        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        Assert.Equal(0, loop.OptimizedLoopHits);
        Assert.Contains("non-scalar loop state slot", loop.FallbackReasons.Keys);
    }

    [Theory]
    [InlineData("-")]
    [InlineData("not ")]
    public void Repeat_EmptySequenceInitialState_IsRejectedInBothModes(string op)
    {
        // This initial state is generic-only. The captured-operand matrix below
        // separately proves that the planned unary also rejects the empty value.
        var source = $"""
            S(a) = {op}a
            repeat(S, 2, ())
            """;

        var error = AssertOptimizerTransparentFailure(source);
        // `{op}a` starts at column 8 of line 1 and ends just past the operand (F5).
        var innermost = Innermost(error);
        Assert.IsType(op == "-" ? typeof(EvalError.BadArity) : typeof(EvalError.TypeMismatch), innermost);
        Assert.Equal(new SourceSpan(1, 8, 1, 9 + op.Length), innermost.Span);

        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        Assert.Equal(0, loop.OptimizedLoopHits);
        Assert.Contains("non-scalar loop state slot", loop.FallbackReasons.Keys);
    }

    public static IEnumerable<object[]> CapturedUnaryNonScalarOperands()
    {
        foreach (var (op, plan) in new[] { ("-", "Negate"), ("not ", "Not") })
        foreach (var operand in new[] { "()", "(1, 2)", "[1, 2]" })
        foreach (var position in new[] { "repeat", "while-output", "while-continuation" })
            yield return [op, plan, operand, position];
    }

    [Theory]
    [MemberData(nameof(CapturedUnaryNonScalarOperands))]
    public void PlannedUnary_CapturedNonScalarOperand_MatchesGenericDiagnosticExactly(
        string op, string unaryPlan, string operand, string position)
    {
        // Empty initial state and a zero-emission state update both bypass the
        // planned unary. Capture an ordinary user parameter instead: the loop
        // starts numeric, and its unary application is wholly planned.
        var continuation = position == "while-continuation";
        var step = continuation ? $"x, {op}value" : $"{op}value";
        if (position == "while-output") step += ", 1";
        var call = position == "repeat" ? "repeat(S, 1, 0)" : "while(S, 0)";
        var source = $$"""
            Use(value) = {
                S(x) = {{step}}
                {{call}}
            }
            Use({{operand}})
            """;

        var error = AssertOptimizerTransparentFailure(source);
        // The planned unary reports the operand rejection (BadArity for `-`, the
        // Boolean-operand TypeMismatch for `not`) at the written unary expression on
        // line 2 (F5); AssertOptimizerTransparentFailure has already proven the span
        // identical on the generic path.
        var innermost = Innermost(error);
        Assert.IsType(op == "-" ? typeof(EvalError.BadArity) : typeof(EvalError.TypeMismatch), innermost);
        var innermostSpan = Assert.NotNull(innermost.Span);
        Assert.Equal(2, innermostSpan.Start.Line);
        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (optimized, loop) = RunCountedObserved(source, enableLoopOptimization: true);
        Assert.True(generic.IsError);
        Assert.True(optimized.IsError);
        Assert.Equal(DescribeErrorTree(error), DescribeErrorTree(generic.Error));
        Assert.Equal(DescribeErrorTree(error), DescribeErrorTree(optimized.Error));

        AssertPlannedUnarySlot(loop, position == "repeat" ? "Use.S.repeat" : "Use.S.while",
            continuation ? "continuation" : "output", continuation ? null : 0,
            $"{unaryPlan}(CapturedSlot(value))");
        Assert.Equal(1, loop.LoopIterations);
        Assert.Equal(1, loop.PlannedBuiltinOperations);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
    }

    // ── Outer evaluation layers do not re-span the innermost unary span ──────

    [Fact]
    public void PlannedUnary_FailureInsideEnclosingExpression_KeepsTheUnaryExpressionSpanInnermost()
    {
        // The failing `repeat` sits inside a binary expression inside a
        // property, so several outer evaluator layers run after the planned
        // unary fails. The innermost BadArity keeps the span of the written
        // unary `-y` (line 2, columns 11-12) on both paths; the surrounding
        // boundaries never overwrite it, identically in both strategies.
        var source = """
            Lst = [1, 2]
            S(x, y) = -y, Lst
            Total = repeat(S, 3, 0, 0) + 100
            Total
            """;

        var error = AssertOptimizerTransparentFailure(source);

        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        Assert.Equal(new SourceSpan(2, 11, 2, 13), Assert.IsType<EvalError.BadArity>(Innermost(generic.Error)).Span);
        Assert.Equal(new SourceSpan(2, 11, 2, 13), Assert.IsType<EvalError.BadArity>(Innermost(error)).Span);

        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        AssertPlannedUnarySlot(loop, "S.repeat", "output", 0, "Negate(StateSlot(y))");
    }
}
