using System.Globalization;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Absolute semantic pins for the shared unary application used by the generic
/// expression-spine machine, its async twin, and planned non-numeric evaluation.
/// These complement strategy-parity tests, which cannot detect a defect shared by
/// every caller.
///
/// <para>Unary minus is numeric negation: non-numeric operands keep the
/// numeric-conversion <see cref="EvalError.BadArity"/>, strings their TypeMismatch, and a
/// Boolean is a value-kind TypeMismatch. Unary <c>not</c> is Boolean negation and rejects
/// every non-Boolean operand — numbers included, there is no numeric truthiness — with the
/// Boolean-operand <see cref="EvalError.TypeMismatch"/>. Every rejection carries the unary
/// expression's span when the caller supplies one (F5).</para>
/// </summary>
public class UnaryOperatorSemanticsTests
{
    private static Result Apply(UnaryOp op, Result operand, SourceSpan? span = null)
    {
        var result = Evaluator.ApplyUnaryOperator(op, operand, span);
        Assert.False(result.IsError, $"Expected success but got: {(result.IsError ? result.Error : null)}");
        return result.Value;
    }

    private static EvalError Fail(UnaryOp op, Result operand, SourceSpan? span = null)
    {
        var result = Evaluator.ApplyUnaryOperator(op, operand, span);
        Assert.True(result.IsError, $"Expected failure but got: {(result.IsOk ? result.Value : null)}");
        return result.Error;
    }

    [Fact]
    public void EmptySequence_IsTheNumericConversionFailureOfMinusAtTheUnarySpan()
    {
        // SYN-01: `()` is an ordinary operand and fails numeric conversion like
        // `(1, 2)`; the BadArity carries the unary expression's span (F5) — the
        // same location policy as the string rejection below.
        var span = new SourceSpan(7, 3, 7, 9);
        var error = Fail(UnaryOp.Minus, Result.SequenceValue.TakeOwnership([]), span);

        Assert.Equal(span, Assert.IsType<EvalError.BadArity>(error).Span);
    }

    [Fact]
    public void EmptySequence_IsTheBooleanOperandRejectionOfNotAtTheUnarySpan()
    {
        var span = new SourceSpan(7, 3, 7, 9);
        var error = Assert.IsType<EvalError.TypeMismatch>(Fail(UnaryOp.Not, Result.SequenceValue.TakeOwnership([]), span));

        Assert.Equal(
            "operator `not` expects a Boolean operand, but the operand was a sequence value with 0 sequence elements: ()",
            error.Message);
        Assert.Equal(span, error.Span);
    }

    [Theory]
    [InlineData(UnaryOp.Minus)]
    [InlineData(UnaryOp.Not)]
    public void SpanlessApplication_InventsNoSpan(UnaryOp op)
    {
        // A host-built unary node without a source span still reports the same
        // structured rejection; the helper attaches a span only when it has one.
        var error = Fail(op, Result.SequenceValue.TakeOwnership([]), span: null);

        Assert.IsType(op == UnaryOp.Minus ? typeof(EvalError.BadArity) : typeof(EvalError.TypeMismatch), error);
        Assert.Null(error.Span);
    }

    [Fact]
    public void NumericOperands_PreserveDecimal128MinusSemantics()
    {
        var negatedZero = Assert.IsType<Result.Atom>(Apply(UnaryOp.Minus, new Result.Atom(Decimal128.Zero))).Value;
        Assert.Equal(Decimal128.Zero, negatedZero);
        Assert.True(Decimal128.IsNegative(negatedZero));

        var quantum = Decimal128.Parse("1.50", NumberStyles.Float, CultureInfo.InvariantCulture);
        var negatedQuantum = Assert.IsType<Result.Atom>(Apply(UnaryOp.Minus, new Result.Atom(quantum))).Value;
        Assert.Equal("-1.50", negatedQuantum.ToString(CultureInfo.InvariantCulture));

        var negatedNaN = Assert.IsType<Result.Atom>(Apply(UnaryOp.Minus, new Result.Atom(Decimal128.NaN))).Value;
        Assert.True(Decimal128.IsNaN(negatedNaN));
    }

    [Fact]
    public void Not_IsBooleanNegation()
    {
        Assert.False(Assert.IsType<Result.Bool>(Apply(UnaryOp.Not, new Result.Bool(true))).Value);
        Assert.True(Assert.IsType<Result.Bool>(Apply(UnaryOp.Not, new Result.Bool(false))).Value);
    }

    [Fact]
    public void Not_RejectsEveryNumber_ThereIsNoNumericTruth()
    {
        // Zero, negative zero, NaN, and an ordinary number alike: a number has no truth
        // value, so `not` reports the Boolean-operand mismatch naming the number.
        var span = new SourceSpan(2, 4, 2, 10);
        foreach (var (number, rendered) in new (Decimal128, string)[]
        {
            (Decimal128.Zero, "0"),
            (Decimal128.NegativeZero, "-0"),
            (Decimal128.NaN, "NaN"),
            (Decimal128.One, "1"),
        })
        {
            var error = Assert.IsType<EvalError.TypeMismatch>(Fail(UnaryOp.Not, new Result.Atom(number), span));
            Assert.Equal($"operator `not` expects a Boolean operand, but the operand was numeric value {rendered}", error.Message);
            Assert.Equal(span, error.Span);
        }
    }

    [Fact]
    public void Minus_RejectsABoolean_ThereIsNoNumericView()
    {
        var span = new SourceSpan(3, 1, 3, 6);
        var error = Assert.IsType<EvalError.TypeMismatch>(Fail(UnaryOp.Minus, new Result.Bool(true), span));

        Assert.Equal("operator `-` expects a numeric scalar operand, but the operand was a Boolean value: true", error.Message);
        Assert.Equal(span, error.Span);
    }

    [Fact]
    public void SingletonSequence_NormalizesToItsSingleValue()
    {
        var negated = Assert.IsType<Result.Atom>(Apply(UnaryOp.Minus, Result.SequenceValue.TakeOwnership([new Result.Atom(3)])));
        Assert.Equal(Decimal128.Parse("-3", NumberStyles.Float, CultureInfo.InvariantCulture), negated.Value);
        Assert.Equal(1, negated.ValueCount());

        var flag = Assert.IsType<Result.Bool>(Apply(UnaryOp.Not, Result.SequenceValue.TakeOwnership([new Result.Bool(true)])));
        Assert.False(flag.Value);
        Assert.Equal(1, flag.ValueCount());

        // A singleton NUMBER is still a number: `not (3)` is the Boolean-operand rejection.
        Assert.IsType<EvalError.TypeMismatch>(Fail(UnaryOp.Not, Result.SequenceValue.TakeOwnership([new Result.Atom(3)])));
    }

    [Theory]
    [InlineData(UnaryOp.Minus, "Unary operator is not supported for strings")]
    [InlineData(UnaryOp.Not, "operator `not` expects a Boolean operand, but the operand was a string: 'text'")]
    public void StringFailure_HasTheUnaryExpressionSpan(UnaryOp op, string message)
    {
        var span = new SourceSpan(7, 3, 7, 13);
        var error = Assert.IsType<EvalError.TypeMismatch>(Fail(op, new Result.Str("text"), span));

        Assert.Equal(message, error.Message);
        Assert.Equal(span, error.Span);
    }

    [Fact]
    public void OtherNonNumericFailures_CarryTheUnaryExpressionSpan()
    {
        // A list value and a multi-item sequence value are the other operand
        // shapes that fail numeric conversion (minus) and the Boolean-operand rule
        // (not); every one of them reports its rejection AT the unary expression
        // (F5), never a spanless error.
        Result[] operands =
        [
            Result.ListValue.TakeOwnership([new Result.Atom(1), new Result.Atom(2)]),
            Result.SequenceValue.TakeOwnership([new Result.Atom(1), new Result.Atom(2)]),
        ];
        var span = new SourceSpan(9, 2, 9, 9);

        foreach (var operand in operands)
        {
            Assert.Equal(span, Assert.IsType<EvalError.BadArity>(Fail(UnaryOp.Minus, operand, span)).Span);
            Assert.Equal(span, Assert.IsType<EvalError.TypeMismatch>(Fail(UnaryOp.Not, operand, span)).Span);
        }
    }
}
