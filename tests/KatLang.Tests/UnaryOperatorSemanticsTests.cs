using System.Globalization;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Absolute semantic pins for the shared unary application used by the generic
/// expression-spine machine, its async twin, and planned non-numeric evaluation.
/// These complement strategy-parity tests, which cannot detect a defect shared by
/// every caller.
/// </summary>
public class UnaryOperatorSemanticsTests
{
    private static Result Apply(UnaryOp op, Result operand, SourceSpan? span = null)
    {
        var result = Evaluator.ApplyUnaryOperator(op, operand, span);
        Assert.False(result.IsError, $"Expected success but got: {(result.IsError ? result.Error : null)}");
        return result.Value;
    }

    [Theory]
    [InlineData(UnaryOp.Minus)]
    [InlineData(UnaryOp.Not)]
    public void EmptySequence_PropagatesAsTheZeroEmittingEmptyValue(UnaryOp op)
    {
        var value = Assert.IsType<Result.SequenceValue>(
            Apply(op, Result.SequenceValue.TakeOwnership([])));

        Assert.Empty(value.Items);
        Assert.Equal(0, value.ValueCount());
    }

    [Fact]
    public void NumericOperands_PreserveDecimal128UnarySemantics()
    {
        var negatedZero = Assert.IsType<Result.Atom>(Apply(UnaryOp.Minus, new Result.Atom(Decimal128.Zero))).Value;
        Assert.Equal(Decimal128.Zero, negatedZero);
        Assert.True(Decimal128.IsNegative(negatedZero));

        var quantum = Decimal128.Parse("1.50", NumberStyles.Float, CultureInfo.InvariantCulture);
        var negatedQuantum = Assert.IsType<Result.Atom>(Apply(UnaryOp.Minus, new Result.Atom(quantum))).Value;
        Assert.Equal("-1.50", negatedQuantum.ToString(CultureInfo.InvariantCulture));

        var negatedNaN = Assert.IsType<Result.Atom>(Apply(UnaryOp.Minus, new Result.Atom(Decimal128.NaN))).Value;
        Assert.True(Decimal128.IsNaN(negatedNaN));

        Assert.Equal(
            Decimal128.One,
            Assert.IsType<Result.Atom>(Apply(UnaryOp.Not, new Result.Atom(Decimal128.NegativeZero))).Value);
        Assert.Equal(
            Decimal128.Zero,
            Assert.IsType<Result.Atom>(Apply(UnaryOp.Not, new Result.Atom(Decimal128.NaN))).Value);
    }

    [Theory]
    [InlineData(UnaryOp.Minus, "-3")]
    [InlineData(UnaryOp.Not, "0")]
    public void SingletonSequence_NormalizesToItsNumericAtom(UnaryOp op, string expected)
    {
        var operand = Result.SequenceValue.TakeOwnership([new Result.Atom(3)]);
        var value = Assert.IsType<Result.Atom>(Apply(op, operand));

        Assert.Equal(
            Decimal128.Parse(expected, NumberStyles.Float, CultureInfo.InvariantCulture),
            value.Value);
        Assert.Equal(1, value.ValueCount());
    }

    [Theory]
    [InlineData(UnaryOp.Minus)]
    [InlineData(UnaryOp.Not)]
    public void StringFailure_HasTheUnaryExpressionSpan(UnaryOp op)
    {
        var span = new SourceSpan(7, 3, 7, 12);
        var result = Evaluator.ApplyUnaryOperator(op, new Result.Str("text"), span);

        Assert.True(result.IsError);
        var error = Assert.IsType<EvalError.TypeMismatch>(result.Error);
        Assert.Equal("Unary operator is not supported for strings", error.Message);
        Assert.Equal(span, error.Span);
    }

    [Fact]
    public void OtherNonNumericFailures_KeepExpectIntBadArityUnspanned()
    {
        Result[] operands =
        [
            Result.ListValue.TakeOwnership([new Result.Atom(1), new Result.Atom(2)]),
            Result.SequenceValue.TakeOwnership([new Result.Atom(1), new Result.Atom(2)]),
        ];

        foreach (var op in new[] { UnaryOp.Minus, UnaryOp.Not })
        {
            foreach (var operand in operands)
            {
                var result = Evaluator.ApplyUnaryOperator(op, operand, new SourceSpan(9, 2, 9, 8));

                Assert.True(result.IsError);
                Assert.Null(Assert.IsType<EvalError.BadArity>(result.Error).Span);
            }
        }
    }
}
