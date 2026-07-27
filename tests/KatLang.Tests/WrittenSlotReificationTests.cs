using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Focused coverage for WRITTEN-SLOT REIFICATION
/// (<c>EvalExplicitSequenceValueExprSlots</c>; Lean
/// <c>evalExplicitSequenceValueExprSlots</c>): a non-spread expression
/// occupying one syntactic value slot — a list-literal element, a written
/// pattern argument item, or the reduce initial accumulator — contributes
/// exactly ONE persistent value, even when the expression's counted supply
/// emitted zero or many items (index projections, loop results, counted
/// callback parameters). Only an explicit spread supplies the value's items into the
/// surrounding slots. This matches every sibling receiver (capture, call
/// arguments, root rows beside other rows, deconstruction). Lean twins: the
/// <c>list-written-slot-reifies-projection</c> and
/// <c>reduce-empty-initial-is-one-value</c> LanguageSpec cases.
/// </summary>
public class WrittenSlotReificationTests
{
    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result.ListValue List(params Result[] items) => new(items);

    private static Result.SequenceValue Seq(params Result[] items) => new(items);

    private static void AssertSemanticallyEqual(Result expected, Result actual)
        => Assert.True(
            Result.ValueComparer.Equals(expected, actual),
            $"Expected {expected} but got {actual}");

    private static Result EvaluateAllModes(string source)
    {
        var ast = Parser.Parse(source).Root;
        var expr = new Expr.Block(ast);

        var plainOptimized = Evaluator.Run(
            expr, new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true, loopDiagnostics: null,
            enableSequencePipelineOptimization: true, sequenceDiagnostics: null);
        var plainGeneric = Evaluator.Run(
            expr, new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: false, loopDiagnostics: null,
            enableSequencePipelineOptimization: false, sequenceDiagnostics: null);
        var counted = Evaluator.RunCounted(expr);
        var engineRun = KatLangEngine.Run(source);

        Assert.True(plainOptimized.IsOk, $"optimizer-on evaluation failed: {(plainOptimized.IsError ? plainOptimized.Error.ToString() : "")}");
        Assert.True(plainGeneric.IsOk, $"optimizer-off evaluation failed: {(plainGeneric.IsError ? plainGeneric.Error.ToString() : "")}");
        Assert.True(counted.IsOk, $"counted evaluation failed: {(counted.IsError ? counted.Error.ToString() : "")}");
        var success = Assert.IsType<RunResult.Success>(engineRun);

        AssertSemanticallyEqual(plainOptimized.Value, plainGeneric.Value);
        AssertSemanticallyEqual(plainOptimized.Value, counted.Value.Value);
        AssertSemanticallyEqual(plainOptimized.Value, success.Value);
        return plainOptimized.Value;
    }

    private static void AssertEvaluates(string source, Result expected)
        => AssertSemanticallyEqual(expected, EvaluateAllModes(source));

    private const string PairSource = "S = ((1, 2), (3, 4))\n";

    // ── List literals: one persistent value per non-spread element ──────────

    [Theory]
    [InlineData("[7]", "[7]")]
    [InlineData("A = (1, 2)\n[A]", "[(1, 2)]")]
    [InlineData("B = [1, 2]\n[B]", "[[1, 2]]")]
    [InlineData("[()]", "[()]")]
    [InlineData("[[]]", "[[]]")]
    [InlineData("P = ()\n[P]", "[()]")]
    [InlineData("A = (1, [2, 3])\n[A, 4]", "[(1, [2, 3]), 4]")]
    [InlineData("B = [1, (2, 3)]\n[B, 4]", "[[1, (2, 3)], 4]")]
    public void ListLiteral_NonSpreadElement_IsOnePersistentValue(string source, string expectedDisplay)
    {
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(expectedDisplay, run.ToDisplayString());
    }

    [Fact]
    public void ListLiteral_MultiEmittingProjection_ReifiesAsOneElement()
    {
        // The audited defect: `S:0` emits a two-item counted supply, but it
        // occupies ONE written list slot, so it contributes the pair as one
        // element — matching capture, call arguments, and deconstruction.
        AssertEvaluates(PairSource + "[S:0, 5]", List(Seq(Atom(1), Atom(2)), Atom(5)));
        AssertEvaluates(PairSource + "[S:0, S:1]", List(Seq(Atom(1), Atom(2)), Seq(Atom(3), Atom(4))));

        // Parentheses are ordinary redundant grouping, not the only escape
        // hatch: `[(S:0), 5]` is the same list.
        AssertEvaluates(PairSource + "[(S:0), 5]", List(Seq(Atom(1), Atom(2)), Atom(5)));
    }

    [Fact]
    public void ListLiteral_ExplicitSpread_OpensExactlyOneBoundary()
    {
        // The contrast required by the spread rule: only written `...` opens
        // the projected value into the surrounding slots.
        AssertEvaluates(PairSource + "[S:0..., 5]", List(Atom(1), Atom(2), Atom(5)));
        AssertEvaluates(PairSource + "[S:0..., S:1...]", List(Atom(1), Atom(2), Atom(3), Atom(4)));
    }

    [Fact]
    public void ListLiteral_LoopResult_ReifiesAsOneElement()
        => AssertEvaluates(
            "[repeat({a + 1, b + a}, 3, 0, 0), 9]",
            List(Seq(Atom(3), Atom(3)), Atom(9)));

    [Fact]
    public void ListLiteral_CallbackParameter_ReifiesAsOneElementPerSlot()
    {
        // A counted callback parameter re-emits its projected count, but each
        // written list slot still reifies it as one value.
        AssertEvaluates(
            "((1, 2), (3, 4)).map({[x, x]})",
            List(
                List(Seq(Atom(1), Atom(2)), Seq(Atom(1), Atom(2))),
                List(Seq(Atom(3), Atom(4)), Seq(Atom(3), Atom(4)))));
    }

    // ── Written pattern arguments: the same reification rule ────────────────

    [Fact]
    public void WrittenPatternArgument_MultiEmittingItem_IsOneWrittenSlot()
    {
        // `(S:0, 5)` supplies TWO written items to the sequence-value pattern:
        // the reified pair and the atom — so `F((x, y))` binds x = (1, 2).
        AssertEvaluates(
            PairSource + "F((x, y)) = (x == (1, 2)) + y\nF((S:0, 5))",
            Atom(6));

        // With an explicit spread the same written group supplies three items.
        AssertEvaluates(
            PairSource + "F((x, y, z)) = x + y + z\nF((S:0..., 5))",
            Atom(8));
    }

    // ── Reduce initial accumulator: one written accumulator slot ────────────

    [Fact]
    public void ReduceEmptyCollection_ReturnsInitialAsOneValue()
    {
        // The initial expression's multi-item supply must not leak through the
        // empty-collection return: the result is ONE sequence value (count 1),
        // shown as a single row.
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "R(x, acc) = acc + x\nInit = 1, 2\nreduce((), R, Init)"));
        Assert.Equal("(1, 2)", run.ToDisplayString());

        AssertEvaluates(
            "R(x, acc) = acc + x\nInit = 1, 2\nreduce((), R, Init)",
            Seq(Atom(1), Atom(2)));
    }

    [Theory]
    [InlineData("Add(a, b) = a + b\nreduce((), Add, 5)", "5")]
    [InlineData("Add(a, b) = a + b\nreduce([], Add, 5)", "5")]
    [InlineData("R(x, acc) = acc + x\nreduce([], R, [5])", "[5]")]
    [InlineData("R(x, acc) = acc + x\nreduce((), R, ())", "()")]
    [InlineData("R(x, acc) = acc + x\nreduce((), R, [])", "[]")]
    [InlineData("R(x, acc) = acc + x\nreduce([], R, (1, [2, 3]))", "(1, [2, 3])")]
    public void ReduceEmptyCollection_InitialAccumulatorKinds_ArePreservedAsOneValue(
        string source, string expectedDisplay)
    {
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(expectedDisplay, run.ToDisplayString());
    }

    [Fact]
    public void ReduceNonEmptyCollection_ThreadsTheSameReifiedInitial()
    {
        // Consistency between the empty and non-empty paths: the same initial
        // accumulator value enters the reducer as one value.
        AssertEvaluates(
            "Append(item, ...history) = (history..., item)\nInit = 1, 2\nreduce((9), Append, Init)",
            Seq(Atom(1), Atom(2), Atom(9)));

        // Dotted and ordinary forms agree.
        AssertEvaluates(
            "Add(a, b) = a + b\n(1, 2, 3).reduce(Add, 10)",
            Atom(16));
        AssertEvaluates(
            "Add(a, b) = a + b\nreduce((1, 2, 3), Add, 10)",
            Atom(16));
    }
}
