using KatLang.Optimizations.Loops;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// SYN-01 on the PLANNED binary path. The loop optimizer plans <c>x op value</c> into
/// <c>LoopExprPlan.Binary</c>; its numeric fast path handles two numeric atoms, and
/// every other operand pair delegates to the shared <c>Evaluator.ApplyBinaryOperator</c>
/// — the one place the empty sequence value is (no longer) special. These cases prove,
/// with the loop diagnostics, that the optimized run genuinely applied the PLANNED
/// binary to <c>()</c> and reported the identical structured error tree, message, and
/// span as the generic evaluator, for every non-equality operator on either side.
///
/// <para>REACHABILITY. An empty INITIAL state routes the whole loop to the generic path
/// at the entry gate ("non-scalar loop state slot"), and a zero-emission state update
/// forces the generic continuation, so neither shape ever reaches the planned binary.
/// A captured caller parameter supplies <c>()</c> directly to a wholly planned binary
/// application — the same delivery shape <see cref="LoopPlannedUnaryDiagnosticParityTests"/>
/// uses for the planned unary. The breadth sweep in
/// <see cref="OptimizerEquivalenceSweepTests"/> crosses every operator with every
/// operand kind but asserts outcome agreement only; the routing proof lives here.</para>
/// </summary>
public class LoopPlannedBinaryEmptyOperandParityTests
{
    private static readonly (string Op, string Plan)[] NonEqualityOperators =
    [
        ("+", "Add"), ("-", "Subtract"), ("*", "Multiply"), ("/", "Divide"), ("div", "IntegerDivide"),
        ("mod", "Mod"), ("^", "Power"), ("<", "LessThan"), (">", "GreaterThan"), ("<=", "LessOrEqual"),
        (">=", "GreaterOrEqual"), ("and", "And"), ("or", "Or"), ("xor", "Xor"),
    ];

    public static IEnumerable<object[]> CapturedEmptyOperands()
    {
        foreach (var (op, plan) in NonEqualityOperators)
        foreach (var side in new[] { "left", "right" })
        foreach (var position in new[] { "repeat", "while-output", "while-continuation" })
            yield return [op, plan, side, position];
    }

    private static bool IsLogical(string op) => op is "and" or "or" or "xor";

    /// <summary>
    /// The written binary. Arithmetic and ordering pair the captured operand with the
    /// numeric state slot; the logical operators require Boolean operands on BOTH sides
    /// (there is no numeric truthiness), so they pair it with the literal `true`: the
    /// only way the captured side is the one validated when it sits on the right.
    /// </summary>
    private static string BinaryText(string op, string side)
    {
        var other = IsLogical(op) ? "true" : "x";
        return side == "left" ? $"value {op} {other}" : $"{other} {op} value";
    }

    private static string ExpectedOperandMessage(string op, string side, string description)
        => IsLogical(op)
            ? $"operator `{op}` expects Boolean operands, but the {side} operand was {description}"
            : $"operator `{op}` expects numeric scalar operands, but the {side} operand was {description}";

    /// <summary>
    /// The loop starts NUMERIC (state 0), so it is admitted by the optimizer, and the
    /// binary application is wholly planned; only the captured parameter carries the
    /// tested operand. <c>position</c> places the binary in a repeat next-state slot, a
    /// while next-state slot, or the while continuation slot.
    /// </summary>
    private static string Source(string op, string side, string position, string operand)
    {
        var binary = BinaryText(op, side);
        var continuation = position == "while-continuation";
        var step = continuation ? $"x, {binary}" : binary;
        if (position == "while-output") step += ", true";
        var call = position == "repeat" ? "repeat(S, 1, 0)" : "while(S, 0)";
        return $$"""
            Use(value) = {
                S(x) = {{step}}
                {{call}}
            }
            Use({{operand}})
            """;
    }

    private static string PlanSummary(string op, string plan, string side)
    {
        var other = IsLogical(op) ? "Const(true)" : "StateSlot(x)";
        return side == "left" ? $"{plan}(CapturedSlot(value), {other})" : $"{plan}({other}, CapturedSlot(value))";
    }

    /// <summary>
    /// Proves the optimized run genuinely applied the PLANNED binary: the loop is
    /// optimized and the binary-bearing expression slot is planned with the expected
    /// plan summary (planned slots never route through the generic evaluator — only
    /// <c>LoopExprPlan.Fallback</c> nodes do).
    /// </summary>
    private static LoopPlanDiagnosticSnapshot AssertPlannedBinarySlot(
        LoopOptimizationDiagnosticsSnapshot loop,
        string planIdentity,
        string role,
        int? index,
        string planSummary)
    {
        Assert.Equal(1, loop.OptimizedLoopHits);
        var plan = Assert.Single(loop.LoopPlans, candidate => candidate.Identity == planIdentity);
        Assert.True(plan.Optimized, $"Expected an optimized plan, got fallback: {plan.FallbackReason}");
        var binary = Assert.Single(plan.Expressions, expression => expression.Role == role && expression.Index == index);
        Assert.True(binary.Planned, $"Expected a planned binary slot, got fallback: {binary.FallbackReason}");
        Assert.Equal(planSummary, binary.PlanSummary);
        return plan;
    }

    /// <summary>
    /// The span of the innermost context frame — the <c>while evaluating `L op R`</c>
    /// frame that carries the binary expression's span; the innermost TypeMismatch
    /// itself is unspanned by the established policy.
    /// </summary>
    private static SourceSpan? BinaryContextSpan(EvalError error)
    {
        SourceSpan? span = null;
        while (error is EvalError.WithContext context)
        {
            span = context.Span;
            error = context.Inner;
        }

        return span;
    }

    // ── Every planned non-equality operator, both sides, three loop positions ──

    [Theory]
    [MemberData(nameof(CapturedEmptyOperands))]
    public void PlannedBinary_CapturedEmptyOperand_MatchesGenericDiagnosticExactly(
        string op, string plan, string side, string position)
    {
        var source = Source(op, side, position, "()");
        var binaryText = BinaryText(op, side);

        // Whole-tree transparency: kinds, spans, context payloads, message, span.
        var error = AssertOptimizerTransparentFailure(source);

        var innermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.Equal(
            ExpectedOperandMessage(op, side, "a sequence value with 0 sequence elements: ()"),
            innermost.Message);
        Assert.Equal($"while evaluating `{binaryText}`", ContextChain(error)[^1]);

        // Absolute span pin on BOTH strategies: the binary context frame is located at
        // the written binary on line 2 (`    S(x) = ` is eleven characters; the
        // continuation slot follows `x, `).
        var start = position == "while-continuation" ? 15 : 12;
        var expectedSpan = new SourceSpan(2, start, 2, start + binaryText.Length);
        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);
        Assert.Equal(expectedSpan, BinaryContextSpan(generic.Error));
        Assert.Equal(expectedSpan, BinaryContextSpan(error));

        var (genericCounted, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (optimizedCounted, loop) = RunCountedObserved(source, enableLoopOptimization: true);
        Assert.True(genericCounted.IsError);
        Assert.True(optimizedCounted.IsError);
        Assert.Equal(DescribeErrorTree(error), DescribeErrorTree(genericCounted.Error));
        Assert.Equal(DescribeErrorTree(error), DescribeErrorTree(optimizedCounted.Error));

        // The optimized side really exercised the planned binary over the captured `()`.
        var continuation = position == "while-continuation";
        AssertPlannedBinarySlot(
            loop,
            position == "repeat" ? "Use.S.repeat" : "Use.S.while",
            continuation ? "continuation" : "output",
            continuation ? null : 0,
            PlanSummary(op, plan, side));
        Assert.Equal(1, loop.LoopIterations);
        Assert.Equal(1, loop.PlannedBuiltinOperations);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
    }

    // ── `()` is one case of the one non-scalar operand rule on this path too ──

    [Theory]
    [InlineData("(1, 2)", "a sequence value with 2 sequence elements: (1, 2)")]
    [InlineData("[1, 2]", "a list value with 2 elements: [1, 2]")]
    [InlineData("[]", "a list value with 0 elements: []")]
    public void PlannedBinary_CapturedNonEmptyStructure_IsRejectedByTheSameRule(string operand, string description)
    {
        var source = Source("+", "right", "repeat", operand);
        var error = AssertOptimizerTransparentFailure(source);

        var innermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.Equal($"operator `+` expects numeric scalar operands, but the right operand was {description}", innermost.Message);

        var (_, loop) = RunCountedObserved(source, enableLoopOptimization: true);
        AssertPlannedBinarySlot(loop, "Use.S.repeat", "output", 0, "Add(StateSlot(x), CapturedSlot(value))");
    }

    // ── Controls: equality and ordinary scalar results on the planned path ──

    [Theory]
    [InlineData("==", false)]
    [InlineData("!=", true)]
    public void PlannedBinary_StructuralEquality_StillAcceptsTheCapturedEmptyValue(string op, bool expected)
    {
        // `==`/`!=` are decided structurally BEFORE operand validation on both
        // strategies, so a captured `()` compares as an ordinary value (unequal to 0).
        var source = Source(op, "right", "repeat", "()");

        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (optimized, loop) = RunCountedObserved(source, enableLoopOptimization: true);
        Assert.False(generic.IsError, $"Expected generic success but got: {(generic.IsError ? generic.Error : null)}");
        Assert.False(optimized.IsError, $"Expected optimized success but got: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal(new Result.Bool(expected), generic.Value.Value, Result.ValueComparer);
        Assert.Equal(new Result.Bool(expected), optimized.Value.Value, Result.ValueComparer);
        Assert.Equal(generic.Value.EmittedCount, optimized.Value.EmittedCount);

        Assert.Equal(1, loop.OptimizedLoopHits);
        var plan = Assert.Single(loop.LoopPlans, candidate => candidate.Identity == "Use.S.repeat");
        var slot = Assert.Single(plan.Expressions, expression => expression.Role == "output" && expression.Index == 0);
        Assert.True(slot.Planned, $"Expected a planned equality slot, got fallback: {slot.FallbackReason}");
        Assert.Contains("CapturedSlot(value)", slot.PlanSummary, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("+", "Add", "3")]
    [InlineData("*", "Multiply", "0")]
    [InlineData(">", "GreaterThan", "false")]
    public void PlannedBinary_CapturedNumericOperand_StillComputesInBothModes(string op, string plan, string expected)
    {
        var source = Source(op, "right", "repeat", "3");

        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (optimized, loop) = RunCountedObserved(source, enableLoopOptimization: true);
        Assert.False(generic.IsError, $"Expected generic success but got: {(generic.IsError ? generic.Error : null)}");
        Assert.False(optimized.IsError, $"Expected optimized success but got: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal(expected, Evaluator.FormatResultForDiagnostic(generic.Value.Value));
        Assert.Equal(expected, Evaluator.FormatResultForDiagnostic(optimized.Value.Value));
        Assert.Equal(generic.Value.EmittedCount, optimized.Value.EmittedCount);

        AssertPlannedBinarySlot(loop, "Use.S.repeat", "output", 0, PlanSummary(op, plan, "right"));
        Assert.Equal(1, loop.PlannedBuiltinOperations);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
    }

    [Theory]
    [InlineData("and", "And", true, true)]
    [InlineData("and", "And", false, false)]
    [InlineData("or", "Or", false, true)]
    [InlineData("xor", "Xor", true, false)]
    public void PlannedBinary_CapturedBooleanOperand_StillComputesLogicallyInBothModes(string op, string plan, bool operand, bool expected)
    {
        // The logical operators are Boolean-only on the planned path too: `true op value`
        // over a captured Boolean is applied by the shared operator and yields a Boolean.
        var source = Source(op, "right", "repeat", operand ? "true" : "false");

        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (optimized, loop) = RunCountedObserved(source, enableLoopOptimization: true);
        Assert.False(generic.IsError, $"Expected generic success but got: {(generic.IsError ? generic.Error : null)}");
        Assert.False(optimized.IsError, $"Expected optimized success but got: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal(new Result.Bool(expected), generic.Value.Value, Result.ValueComparer);
        Assert.Equal(new Result.Bool(expected), optimized.Value.Value, Result.ValueComparer);
        Assert.Equal(generic.Value.EmittedCount, optimized.Value.EmittedCount);

        AssertPlannedBinarySlot(loop, "Use.S.repeat", "output", 0, PlanSummary(op, plan, "right"));
        Assert.Equal(1, loop.PlannedBuiltinOperations);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
    }

    // ── The generic gate and handover boundaries ────────────────────────────

    [Fact]
    public void Repeat_EmptySequenceInitialState_IsRejectedInBothModesAtTheGenericGate()
    {
        // An empty initial state never reaches a plan: the optimizer's entry gate
        // routes the loop generic in both modes, and the generic step then rejects
        // `()` as an ordinary non-scalar operand. This pins the gate boundary; the
        // captured-operand matrix above is the genuinely planned coverage.
        var source = """
            S(x) = x - 1
            repeat(S, 2, ())
            """;

        var error = AssertOptimizerTransparentFailure(source);
        Assert.Equal(["while evaluating call to repeat", "while evaluating `x - 1`"], ContextChain(error));
        var innermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.Contains("the left operand was a sequence value with 0 sequence elements: ()", innermost.Message);

        var (_, loop, _) = RunObserved(source, enableLoopOptimization: true);
        Assert.Equal(0, loop.OptimizedLoopHits);
        Assert.Contains("non-scalar loop state slot", loop.FallbackReasons.Keys);
    }

    [Fact]
    public void Repeat_StateBecomesEmptyMidLoop_IsRejectedIdenticallyInBothModes()
    {
        // A fallback sibling moves `()` into y's slot after iteration 1; the
        // zero-emission update hands the loop to the generic continuation, whose
        // `y + 1` on iteration 2 reports the ordinary empty-operand rejection. Both
        // strategies must agree on the whole diagnostic.
        var source = """
            Emp = ()
            S(x, y) = y + 1, Emp
            repeat(S, 3, 0, 0)
            """;

        var error = AssertOptimizerTransparentFailure(source);
        Assert.Equal(["while evaluating call to repeat", "while evaluating `y + 1`"], ContextChain(error));
        var innermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.Contains("the left operand was a sequence value with 0 sequence elements: ()", innermost.Message);
    }
}
