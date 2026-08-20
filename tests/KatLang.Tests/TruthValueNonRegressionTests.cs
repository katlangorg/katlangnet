using System.Numerics;
namespace KatLang.Tests;

/// <summary>
/// Non-regression pins for KatLang truth testing, captured BEFORE the `atoms`
/// builtin gained recursive list traversal (issue #136). Truth testing flattens
/// through <see cref="Result.ToAtoms"/> (Lean: <c>Result.atoms</c>), which is
/// sequence-only and keeps list values opaque; the first flattened numeric atom
/// decides. The `atoms` builtin uses a SEPARATE recursive collector, so nothing
/// in this file may change when the builtin's semantics change: lists have no
/// truth value, and `atoms` does not define truthiness.
/// Lean parity: the truth guards in CoreTests.lean.
/// </summary>
public class TruthValueNonRegressionTests
{
    private static EvalResult<Result> EvalFull(string source)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));

        return Evaluator.Run(new Expr.AlgorithmExpr(parseResult.Root));
    }

    private static void AssertEval(string source, params Decimal128[] expected)
    {
        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value.ToHostAtoms());
    }

    private static EvalError AssertEvalFails(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");
        return result.Error;
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    private static void AssertIfConditionInvalid(string source)
        => Assert.IsType<EvalError.BadArity>(Innermost(AssertEvalFails(source)));

    // ── Numeric atom conditions ──────────────────────────────────────────────

    [Theory]
    [InlineData("if(0, 10, 20)", 20)]
    [InlineData("if(1, 10, 20)", 10)]
    [InlineData("if(-1, 10, 20)", 10)]
    [InlineData("if(5, 10, 20)", 10)]
    public void If_AtomCondition_ZeroIsFalse_AnyOtherNumberIsTrue(string source, decimal expected)
        => AssertEval(source, expected);

    // ── Sequence conditions: first flattened numeric atom decides ────────────

    [Theory]
    [InlineData("if((5), 10, 20)", 10)]
    [InlineData("if((1, 2), 10, 20)", 10)]
    [InlineData("if((0, 5), 10, 20)", 20)]
    [InlineData("if(((0, 1), 2), 10, 20)", 20)]
    [InlineData("if(('a', 3), 10, 20)", 10)]
    public void If_SequenceCondition_FirstFlattenedAtomDecides(string source, decimal expected)
        => AssertEval(source, expected);

    // ── Atom-free conditions are invalid (BadArity) ──────────────────────────

    [Theory]
    [InlineData("if((), 10, 20)")]
    [InlineData("if('x', 10, 20)")]
    [InlineData("if(('a', 'b'), 10, 20)")]
    public void If_AtomFreeCondition_IsInvalid(string source)
        => AssertIfConditionInvalid(source);

    // ── List conditions: lists have no truth value ───────────────────────────

    [Theory]
    [InlineData("if([], 10, 20)")]
    [InlineData("if([1], 10, 20)")]
    [InlineData("if([0], 10, 20)")]
    [InlineData("if([[1]], 10, 20)")]
    [InlineData("if(([1], 'a'), 10, 20)")]
    public void If_ListCondition_IsInvalid(string source)
        => AssertIfConditionInvalid(source);

    // ── Mixed sequence/list conditions: list elements are skipped ────────────

    [Theory]
    [InlineData("if((1, [2]), 10, 20)", 10)]
    [InlineData("if((0, [1]), 10, 20)", 20)]
    [InlineData("if(([1], 0), 10, 20)", 20)]
    [InlineData("if(([0], 1), 10, 20)", 10)]
    public void If_MixedCondition_ListElementsContributeNoAtoms(string source, decimal expected)
        => AssertEval(source, expected);

    // ── Loop continuation is numeric, not truthiness ─────────────────────────

    [Fact]
    public void While_ListContinuationSlot_IsInvalid()
        => Assert.IsType<EvalError.BadArity>(Innermost(AssertEvalFails("Step(x) = [1]\nStep.while(5)")));

    // ── List operands stay out of numeric truth operators ────────────────────

    [Theory]
    [InlineData("[1] and 1")]
    [InlineData("1 or [0]")]
    [InlineData("not [1]")]
    public void ListOperand_IsInvalidInLogicalOperators(string source)
        => AssertEvalFails(source);

    // ── TruthValue() helper contract (direct pins) ───────────────────────────

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result SequenceValue(params Result[] items) => new Result.SequenceValue(items);

    private static Result ListValue(params Result[] items) => new Result.ListValue(items);

    [Fact]
    public void TruthValue_Atoms_ZeroFalse_NonzeroTrue()
    {
        Assert.False(Atom(0).TruthValue());
        Assert.True(Atom(5).TruthValue());
        Assert.True(Atom(-1).TruthValue());
    }

    [Fact]
    public void TruthValue_AtomFreeValues_AreNull()
    {
        Assert.Null(Str("x").TruthValue());
        Assert.Null(SequenceValue().TruthValue());
        Assert.Null(SequenceValue(Str("a"), Str("b")).TruthValue());
    }

    [Fact]
    public void TruthValue_Sequences_FirstFlattenedAtomDecides()
    {
        Assert.True(SequenceValue(Atom(1), Atom(0)).TruthValue());
        Assert.False(SequenceValue(Atom(0), Atom(5)).TruthValue());
        Assert.False(SequenceValue(SequenceValue(Atom(0), Atom(1)), Atom(2)).TruthValue());
        Assert.True(SequenceValue(Str("a"), Atom(3)).TruthValue());
    }

    [Fact]
    public void TruthValue_Lists_AreAlwaysNull_EvenWithNumericContent()
    {
        Assert.Null(ListValue().TruthValue());
        Assert.Null(ListValue(Atom(1)).TruthValue());
        Assert.Null(ListValue(Atom(0)).TruthValue());
        Assert.Null(ListValue(ListValue(Atom(1))).TruthValue());
    }

    [Fact]
    public void TruthValue_MixedValues_SkipListElements()
    {
        Assert.True(SequenceValue(Atom(1), ListValue(Atom(0))).TruthValue());
        Assert.False(SequenceValue(ListValue(Atom(1)), Atom(0)).TruthValue());
        Assert.Null(SequenceValue(ListValue(Atom(1)), Str("a")).TruthValue());
    }

    // ── ToAtoms() truth-testing view contract (direct pins) ──────────────────

    [Fact]
    public void ToAtoms_FlattensSequencesOnly_ListsAndStringsAreOpaque()
    {
        Assert.Equal([7m], Atom(7).ToAtoms());
        Assert.Empty(Str("x").ToAtoms());
        Assert.Equal([1m, 2m, 3m], SequenceValue(Atom(1), SequenceValue(Atom(2), Atom(3))).ToAtoms());
        Assert.Empty(ListValue(Atom(1), Atom(2)).ToAtoms());
        Assert.Equal([1m, 3m], SequenceValue(Atom(1), ListValue(Atom(2)), Atom(3)).ToAtoms());
    }
}
