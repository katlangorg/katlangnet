using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Batch 3 / L19 — the binary-operator evaluation order that makes the empty
/// sequence value transparent BEFORE string operands are rejected.
///
/// <para><c>Evaluator.ApplyBinaryOperator</c> (Lean: <c>evalBinaryCounted</c>) checks,
/// in this order: structural <c>==</c>/<c>!=</c>; empty-value transparency (an empty
/// sequence value on either side yields the OTHER operand unchanged, both empty yields
/// empty); string rejection (string/string, then string/non-string); numeric-scalar
/// validation; divisor and exponent rules; operator dispatch. Because transparency
/// precedes string rejection, <c>'a' + ()</c> is <c>'a'</c> rather than a string
/// arithmetic error — the modeled rule, previously unpinned. Transparency is one
/// shared step for every non-equality operator and is symmetric, so the pin covers
/// every operator on both sides; the controls prove it is empty-sequence-specific,
/// not a general permission for string arithmetic.</para>
/// </summary>
public class EmptySequenceTransparencyTests
{
    private static Result Value(string source)
    {
        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        if (result.IsError)
            Assert.Fail($"`{source}` failed: {KatLangError.FromEvalError(result.Error).Message}");
        return result.Value;
    }

    private static EvalError.TypeMismatch TypeMismatchOf(string source)
    {
        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        if (result.IsOk)
            Assert.Fail($"`{source}` unexpectedly succeeded with {result.Value}");

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return Assert.IsType<EvalError.TypeMismatch>(error);
    }

    private static void AssertString(string expected, string source)
    {
        var value = Assert.IsType<Result.Str>(Value(source));
        Assert.Equal(expected, value.Value);
    }

    private static void AssertAtom(Decimal128 expected, string source)
        => Assert.Equal(expected, Assert.IsType<Result.Atom>(Value(source)).Value);

    /// <summary>Every binary operator spelling except structural <c>==</c>/<c>!=</c>.</summary>
    public static IEnumerable<object[]> NonEqualityOperators()
        => new[] { "+", "-", "*", "/", "div", "mod", "^", "<", ">", "<=", ">=", "and", "or", "xor" }
            .Select(static op => new object[] { op });

    // ── The fundamental pin ─────────────────────────────────────────────────

    [Fact]
    public void StringPlusEmpty_IsTheString()
        => AssertString("a", "'a' + ()");

    [Fact]
    public void EmptyPlusString_IsTheString()
        => AssertString("a", "() + 'a'");

    // ── Operator-independent and symmetric ──────────────────────────────────

    [Theory]
    [MemberData(nameof(NonEqualityOperators))]
    public void StringThroughEmpty_IsTransparentForEveryNonEqualityOperator(string op)
    {
        AssertString("a", $"'a' {op} ()");
        AssertString("a", $"() {op} 'a'");
    }

    // ── Controls: string rejection is intact everywhere else ────────────────

    [Theory]
    [MemberData(nameof(NonEqualityOperators))]
    public void StringWithNonEmptyOperand_StaysRejected(string op)
    {
        // The same operators reject a string operand whenever the other side is
        // NOT the empty sequence value — a number, another string, or an empty
        // LIST (exact lists are never transparent) — with the unchanged structured
        // error and message.
        Assert.Contains("string and non-string", TypeMismatchOf($"'a' {op} 1").Message);
        Assert.Contains("string and non-string", TypeMismatchOf($"1 {op} 'a'").Message);
        Assert.Contains("only support == and !=", TypeMismatchOf($"'a' {op} 'b'").Message);
        Assert.Contains("string and non-string", TypeMismatchOf($"'a' {op} []").Message);
        Assert.Contains("string and non-string", TypeMismatchOf($"[] {op} 'a'").Message);
    }

    [Fact]
    public void EqualityOperators_ComparStructurallyBeforeTransparency()
    {
        // `==`/`!=` are decided before the transparency step: a string and the
        // empty sequence value are simply different values.
        AssertAtom(Decimal128.Zero, "'a' == ()");
        AssertAtom(Decimal128.One, "'a' != ()");
        AssertAtom(Decimal128.Zero, "() == 'a'");
        AssertAtom(Decimal128.One, "() != 'a'");
    }

    [Fact]
    public void TransparencyReturnsTheStringOperandItself()
    {
        // The surviving operand is the string VALUE (no coercion, no wrapping):
        // it keeps behaving as a string afterwards.
        AssertAtom(Decimal128.One, "('a' + ()) == 'a'");
        AssertString("a", "(() + 'a') + ()");
        Assert.Contains("string and non-string", TypeMismatchOf("('a' + ()) + 1").Message);
    }
}
