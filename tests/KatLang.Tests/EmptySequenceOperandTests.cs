using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// SYN-01 — the empty sequence value is an ORDINARY operand for scalar
/// operators, never an identity that erases or bypasses the operator.
///
/// <para><c>Evaluator.ApplyBinaryOperator</c> (Lean: <c>evalBinaryCounted</c>) checks,
/// in this order: structural <c>==</c>/<c>!=</c>; string rejection (string/string, then
/// string/non-string); numeric-scalar validation; divisor and exponent rules; operator
/// dispatch. <c>()</c> takes part in none of those as a special case — it carries no
/// numeric scalar value, so every non-equality operator rejects it through the same
/// <see cref="EvalError.TypeMismatch"/> path that already rejected <c>(1, 2)</c> and
/// <c>[]</c>, on either side and for both operands empty. The controls below pin what
/// the change deliberately does NOT touch: structural equality over empty sequences,
/// the string contract, ordinary arithmetic/ordering/logical results, and the empty
/// <em>supply</em> neutrality of capture/collect/spread.</para>
///
/// <para>Unary operators retain their existing numeric-conversion validation:
/// unsupported sequence/list operands, including <c>()</c>, raise
/// <see cref="EvalError.BadArity"/>; strings retain their TypeMismatch.</para>
///
/// <para>Before this change the binary empty-operand cases SUCCEEDED and
/// returned the other operand (<c>10 / ()</c> was <c>10</c>, <c>() &gt; 10</c> was
/// <c>10</c>, <c>() and 7</c> was <c>7</c>, <c>() + 'text'</c> was <c>text</c>), so each
/// assertion here fails against the old rule for the right reason rather than merely
/// observing that something went wrong.</para>
/// </summary>
public class EmptySequenceOperandTests
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

    /// <summary>
    /// Asserts the SYN-01 rejection: the program fails with the numeric-scalar
    /// operand diagnostic naming the given side and the empty sequence value.
    /// Naming the side rules out a fix that only handles one operand position.
    /// </summary>
    private static void AssertEmptyOperandRejected(string source, string side)
    {
        var message = TypeMismatchOf(source).Message;
        Assert.Contains("expects numeric scalar operands", message);
        Assert.Contains($"the {side} operand was a sequence value with 0 sequence elements: ()", message);
    }

    /// <summary>Every binary operator spelling except structural <c>==</c>/<c>!=</c>.</summary>
    public static IEnumerable<object[]> NonEqualityOperators()
        => new[] { "+", "-", "*", "/", "div", "mod", "^", "<", ">", "<=", ">=", "and", "or", "xor" }
            .Select(static op => new object[] { op });

    // ── The four original SYN-01 reproductions ──────────────────────────────

    [Fact]
    public void DivisionByEmpty_IsRejected_NotTheDividend()
        => AssertEmptyOperandRejected("10 / ()", "right");

    [Fact]
    public void OrderingWithEmptyLeft_IsRejected_NotTheOtherOperand()
        => AssertEmptyOperandRejected("() > 10", "left");

    [Fact]
    public void LogicalAndWithEmptyLeft_IsRejected_NotTheOtherOperand()
        => AssertEmptyOperandRejected("() and 7", "left");

    [Fact]
    public void EmptyPlusString_IsRejected_NotTheString()
    {
        // `()` no longer bypasses the string contract: this reaches the ordinary
        // string/non-string rejection, exactly like `1 + 'text'`.
        Assert.Contains("string and non-string", TypeMismatchOf("() + 'text'").Message);
        Assert.Contains("string and non-string", TypeMismatchOf("'text' + ()").Message);
    }

    // ── Systematic: every operator, both sides, and both operands empty ─────

    [Theory]
    [MemberData(nameof(NonEqualityOperators))]
    public void EmptyOperand_IsRejectedByEveryNonEqualityOperator(string op)
    {
        AssertEmptyOperandRejected($"() {op} 1", "left");
        AssertEmptyOperandRejected($"1 {op} ()", "right");
        // Both empty: the left operand is validated first, so it is the one blamed.
        AssertEmptyOperandRejected($"() {op} ()", "left");
    }

    [Theory]
    [MemberData(nameof(NonEqualityOperators))]
    public void EmptyOperand_AgainstAString_KeepsTheStringContract(string op)
    {
        // The string arm is reached BEFORE numeric-scalar validation, so a string
        // paired with `()` reports the string/non-string contract rather than the
        // empty-operand message. Either way it is an error, never a passthrough.
        Assert.Contains("string and non-string", TypeMismatchOf($"'a' {op} ()").Message);
        Assert.Contains("string and non-string", TypeMismatchOf($"() {op} 'a'").Message);
    }

    [Theory]
    [MemberData(nameof(NonEqualityOperators))]
    public void RedundantEmptyParentheses_AreRejectedTheSameWay(string op)
    {
        // `(())` and `((()))` normalize to `()`; normalization must not
        // reintroduce a passthrough at a different arity depth.
        AssertEmptyOperandRejected($"(()) {op} 1", "left");
        AssertEmptyOperandRejected($"1 {op} ((()))", "right");
    }

    [Fact]
    public void EmptyProperty_AsOperand_IsRejected()
        // A NAMED empty operand takes the same path as the literal: the defect was
        // never about the literal spelling.
        => AssertEmptyOperandRejected("A = ()\nA / 2", "left");

    [Fact]
    public void EmptyOperand_FromASpreadCapture_IsRejected()
        // `A*` over an empty list captures `()`; the captured value is an ordinary
        // operand and is rejected like any other.
        => AssertEmptyOperandRejected("A = []\nB = { A* }\nB + 1", "left");

    // ── Controls: the string contract is intact everywhere else ─────────────

    [Theory]
    [MemberData(nameof(NonEqualityOperators))]
    public void StringWithNonEmptyOperand_StaysRejected(string op)
    {
        // Unchanged by SYN-01: the same operators reject a string operand against a
        // number, another string, or an empty LIST, with the same structured error.
        Assert.Contains("string and non-string", TypeMismatchOf($"'a' {op} 1").Message);
        Assert.Contains("string and non-string", TypeMismatchOf($"1 {op} 'a'").Message);
        Assert.Contains("only support == and !=", TypeMismatchOf($"'a' {op} 'b'").Message);
        Assert.Contains("string and non-string", TypeMismatchOf($"'a' {op} []").Message);
        Assert.Contains("string and non-string", TypeMismatchOf($"[] {op} 'a'").Message);
    }

    // ── Controls: structural equality is decided before operand validation ──

    [Fact]
    public void EqualityOperators_CompareEmptyStructurally()
    {
        // `==`/`!=` are total over all value kinds and are decided BEFORE operand
        // validation, so they keep working with empty sequence operands.
        AssertAtom(Decimal128.One, "() == ()");
        AssertAtom(Decimal128.Zero, "() != ()");
        AssertAtom(Decimal128.One, "() == (())");
        AssertAtom(Decimal128.Zero, "() != (())");
        AssertAtom(Decimal128.One, "() != (1)");
        AssertAtom(Decimal128.One, "() != (1, 2)");
        AssertAtom(Decimal128.Zero, "() == 0");
        AssertAtom(Decimal128.Zero, "() == []");
        AssertAtom(Decimal128.Zero, "'a' == ()");
        AssertAtom(Decimal128.One, "'a' != ()");
        AssertAtom(Decimal128.Zero, "() == 'a'");
        AssertAtom(Decimal128.One, "() != 'a'");
        AssertAtom(Decimal128.One, "A = ()\nB = ()\nA == B");
    }

    // ── Controls: ordinary operator behavior is untouched ───────────────────

    [Theory]
    [InlineData("-")]
    [InlineData("not ")]
    public void UnaryNonScalarOperands_UseTheSameExistingValidation(string op)
    {
        foreach (var operand in new[] { "()", "(())", "(1, 2)", "[]", "[1]", "[1, 2]" })
        {
            var source = op + operand;
            var ast = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
            var plain = Evaluator.Run(ast);
            var counted = Evaluator.RunCountedObserved(ast).Result;
            Assert.True(plain.IsError, $"`{source}` must reject the non-scalar operand");
            Assert.True(counted.IsError);
            Assert.IsType<EvalError.BadArity>(LoopDiagnosticParityAssertions.Innermost(plain.Error));
            // The BadArity is located at the whole unary expression (F5).
            Assert.Equal(new SourceSpan(1, 1, 1, source.Length), LoopDiagnosticParityAssertions.Innermost(plain.Error).Span);
            Assert.Equal(
                LoopDiagnosticParityAssertions.DescribeErrorTree(plain.Error),
                LoopDiagnosticParityAssertions.DescribeErrorTree(counted.Error));
        }

        Assert.Equal("Unary operator is not supported for strings", TypeMismatchOf(op + "'text'").Message);
    }

    [Theory]
    [InlineData("-")]
    [InlineData("not ")]
    public void UnaryEmptyValue_FromAPropertyOrSpreadCapture_IsRejected(string op)
    {
        foreach (var definition in new[] { "Empty = ()", "Items = []\nEmpty = (Items*)" })
        {
            var ast = new Expr.AlgorithmExpr(SourceProvenance.ParseValid($"{definition}\n{op}Empty").Root);
            var result = Evaluator.Run(ast);
            Assert.True(result.IsError);
            Assert.IsType<EvalError.BadArity>(LoopDiagnosticParityAssertions.Innermost(result.Error));
        }
    }

    [Theory]
    [InlineData("-()")]
    [InlineData("not ()")]
    public void UnaryOperandFailure_PreservesChildDiagnosticBlame(string unary)
    {
        // Evaluation of the operand fails first; the outer unary must preserve
        // the division's error and its narrower absolute span — the written group
        // `(1 / 0)` the unary consumes (the grouped-expression span rule, F6).
        var source = unary.Replace("()", "(1 / 0)");
        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        Assert.True(result.IsError);
        var error = Assert.IsType<EvalError.DivByZero>(LoopDiagnosticParityAssertions.Innermost(result.Error));
        var start = source.IndexOf('(') + 1;
        Assert.Equal(new SourceSpan(1, start, 1, start + 6), error.Span);
    }

    [Fact]
    public void OrdinaryUnaryOperators_StillCompute()
    {
        AssertAtom(-7, "-7");
        AssertAtom(7, "- -7");
        AssertAtom(0, "-0");
        AssertAtom(1, "not 0");
        AssertAtom(0, "not 7");
        AssertAtom(0, "not -7");
    }

    [Fact]
    public void OrdinaryArithmetic_StillComputes()
    {
        AssertAtom(5, "2 + 3");
        AssertAtom(-1, "2 - 3");
        AssertAtom(6, "2 * 3");
        AssertAtom(5, "10 / 2");
        AssertAtom(3, "7 div 2");
        AssertAtom(1, "7 mod 2");
        AssertAtom(8, "2 ^ 3");
    }

    [Fact]
    public void OrdinaryComparisons_StillProduceNumericBooleans()
    {
        // The ordering operators return 1/0 — never one of their operands.
        AssertAtom(Decimal128.One, "10 > 1");
        AssertAtom(Decimal128.Zero, "1 > 10");
        AssertAtom(Decimal128.One, "1 < 10");
        AssertAtom(Decimal128.One, "1 <= 1");
        AssertAtom(Decimal128.One, "1 >= 1");
        AssertAtom(Decimal128.Zero, "1 >= 2");
    }

    [Fact]
    public void OrdinaryLogicalOperators_KeepTheirSemantics()
    {
        AssertAtom(Decimal128.One, "1 and 7");
        AssertAtom(Decimal128.Zero, "0 and 7");
        AssertAtom(Decimal128.One, "0 or 7");
        AssertAtom(Decimal128.Zero, "0 or 0");
        AssertAtom(Decimal128.One, "1 xor 0");
        AssertAtom(Decimal128.Zero, "1 xor 1");
    }

    [Fact]
    public void StringsThatWereNeverEmptyRelated_AreUnaffected()
    {
        AssertString("ab", "'ab'");
        AssertAtom(Decimal128.One, "'ab' == 'ab'");
        AssertAtom(Decimal128.Zero, "'ab' != 'ab'");
    }

    // ── Controls: empty SUPPLY neutrality is unchanged ──────────────────────

    [Fact]
    public void EmptySequence_IsStillARealValue()
    {
        AssertEmptySequence(Value("()"));
        AssertEmptySequence(Value("A = ()\nA"));
        AssertAtom(Decimal128.Zero, "count(())");
        AssertAtom(Decimal128.Zero, "A = ()\nA.count");
    }

    [Fact]
    public void EmptySpread_StillContributesNoItems()
    {
        // Supply neutrality — the genuine arity-algebra law — is untouched: the
        // spread of `()` adds nothing to the surrounding item supply.
        AssertAtom(7, "Empty = ()\nEmpty*, 7");
        AssertAtom(7, "(()*, 7)");
        AssertAtom(7, "F(a) = a\nF(()*, 7)");
    }

    [Fact]
    public void EmptySequence_StaysAVisibleNonSpreadSlot()
    {
        var value = Assert.IsType<Result.SequenceValue>(Value("Empty = ()\n(Empty, 7)"));
        Assert.Equal(2, value.Items.Count);
        AssertEmptySequence(value.Items[0]);
    }

    [Fact]
    public void CollectingBinding_StillCollectsEmptyAsAnExactEmptyList()
    {
        // `[]` stays the collecting-binding result and stays DISTINCT from `()`.
        AssertEmptyList(Value("x, *rest = 1\nrest"));
        AssertEmptyList(Value("F(*items) = items\nF()"));
        AssertAtom(Decimal128.Zero, "F(*items) = items\nF() == ()");
    }

    // ── The canonical SYN-01 programs verbatim, with their public diagnostic ──

    private static EvalError ErrorOf(string source)
    {
        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        if (result.IsOk)
            Assert.Fail($"`{source}` unexpectedly succeeded with {result.Value}");
        return result.Error;
    }

    public static TheoryData<string, string> CanonicalNumericPrograms()
        => new()
        {
            { "10 / ()", "right" },
            { "() / 10", "left" },
            { "() > 10", "left" },
            { "10 > ()", "right" },
            { "() and 7", "left" },
            { "7 and ()", "right" },
            { "() or 7", "left" },
            { "7 or ()", "right" },
        };

    [Theory]
    [MemberData(nameof(CanonicalNumericPrograms))]
    public void CanonicalProgram_ReportsTheStructuredTypeMismatchAtTheWholeExpression(string source, string side)
    {
        // The public diagnostic: the TypeMismatch family (never a value, never an
        // arity error), blaming the empty side by name, carrying the ordinary
        // `while evaluating` context, and located at the whole binary expression.
        var rendered = KatLangError.FromEvalError(ErrorOf(source));

        Assert.Equal(KatLangErrorCode.TypeMismatch, rendered.Code);
        Assert.Contains($"while evaluating `{source}`", rendered.Message);
        Assert.Contains($"the {side} operand was a sequence value with 0 sequence elements: ()", rendered.Message);
        Assert.Equal(
            ((int?)1, (int?)1, (int?)1, (int?)source.Length),
            (rendered.StartLine, rendered.StartColumn, rendered.EndLine, rendered.EndColumn));
    }

    [Theory]
    [InlineData("() + 'text'")]
    [InlineData("'text' + ()")]
    public void CanonicalStringProgram_ReportsTheStringContractAtTheWholeExpression(string source)
    {
        var rendered = KatLangError.FromEvalError(ErrorOf(source));

        Assert.Equal(KatLangErrorCode.TypeMismatch, rendered.Code);
        Assert.Contains("Cannot apply operator to string and non-string operands", rendered.Message);
        Assert.Equal(
            ((int?)1, (int?)1, (int?)1, (int?)source.Length),
            (rendered.StartLine, rendered.StartColumn, rendered.EndLine, rendered.EndColumn));
    }

    // ── `()` is one case of the ONE non-scalar operand rule ─────────────────

    [Theory]
    [InlineData("(1, 2) + 3", "left", "a sequence value with 2 sequence elements: (1, 2)")]
    [InlineData("3 + (1, 2)", "right", "a sequence value with 2 sequence elements: (1, 2)")]
    [InlineData("[1, 2] + 3", "left", "a list value with 2 elements: [1, 2]")]
    [InlineData("3 + [1, 2]", "right", "a list value with 2 elements: [1, 2]")]
    [InlineData("[] + 3", "left", "a list value with 0 elements: []")]
    [InlineData("() + 3", "left", "a sequence value with 0 sequence elements: ()")]
    public void NonScalarOperands_AreRejectedByTheSameOperandRule(string source, string side, string description)
    {
        // A multi-item sequence value, an exact list (empty or not), and the empty
        // sequence value all fail the same numeric-scalar validation with the same
        // structured error; the message differs only in how it describes the value.
        var rendered = KatLangError.FromEvalError(ErrorOf(source));

        Assert.Equal(KatLangErrorCode.TypeMismatch, rendered.Code);
        Assert.Contains($"the {side} operand was {description}", rendered.Message);
        Assert.Equal(
            ((int?)1, (int?)1, (int?)1, (int?)source.Length),
            (rendered.StartLine, rendered.StartColumn, rendered.EndLine, rendered.EndColumn));
    }

    // ── `()` is a value; a no-output body is not ────────────────────────────

    [Theory]
    [InlineData("A = {\n}\nA + 1")]
    [InlineData("A = {\n}\n1 + A")]
    [InlineData("{} + 1")]
    public void NoOutputBody_IsNotTheEmptySequenceValue(string source)
    {
        // `{}` has no value at all, so demanding it as an operand is the
        // missing-output family and never reaches operand validation; `()` IS a
        // value and reaches operand validation, where it is rejected. The two must
        // never be conflated, and neither is a passthrough.
        Assert.Equal(KatLangErrorCode.MissingOutput, KatLangError.FromEvalError(ErrorOf(source)).Code);
        Assert.Equal(KatLangErrorCode.TypeMismatch, KatLangError.FromEvalError(ErrorOf("() + 1")).Code);
    }

    // ── Nested and contextual forms keep the same rule and their blame ──────

    [Theory]
    [InlineData("F(a) = a / 2\nF(())", "while evaluating call to F", "a / 2", "left")]
    [InlineData("F(a) = 2 / a\nF(())", "while evaluating call to F", "2 / a", "right")]
    [InlineData("if(1, () + 1, 0)", "while evaluating call to if", "() + 1", "left")]
    [InlineData("M(a) = a + 1\nmap(((), 2), M)", "while evaluating call to map", "a + 1", "left")]
    [InlineData("S(x) = x - 1\nrepeat(S, 2, ())", "while evaluating call to repeat", "x - 1", "left")]
    [InlineData("A = ()\nB = A > 0\nB", "while evaluating `A > 0`", "A > 0", "left")]
    public void EmptyOperand_InNestedContexts_IsRejectedWithContextualBlame(
        string source, string outermostContext, string binaryText, string side)
    {
        // The rejection is the same wherever the operator runs — a user call, a
        // selected `if` branch, a callback, a loop step, a property body — and the
        // ordinary contextual diagnostics wrap it rather than being lost.
        var error = ErrorOf(source);
        var chain = LoopDiagnosticParityAssertions.ContextChain(error);

        Assert.Equal(outermostContext, chain[0]);
        Assert.Equal($"while evaluating `{binaryText}`", chain[^1]);
        var innermost = Assert.IsType<EvalError.TypeMismatch>(LoopDiagnosticParityAssertions.Innermost(error));
        Assert.Contains($"the {side} operand was a sequence value with 0 sequence elements: ()", innermost.Message);

        // Plain and counted evaluation report the identical structured tree.
        var counted = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root)).Result;
        Assert.True(counted.IsError);
        Assert.Equal(
            LoopDiagnosticParityAssertions.DescribeErrorTree(error),
            LoopDiagnosticParityAssertions.DescribeErrorTree(counted.Error));
    }

    // `Result`'s record equality is not KatLang value equality (two distinct
    // empty backing collections are not reference-equal), so empty collection
    // values are asserted structurally by kind and emptiness.
    private static void AssertEmptySequence(Result value)
        => Assert.Empty(Assert.IsType<Result.SequenceValue>(value).Items);

    private static void AssertEmptyList(Result value)
        => Assert.Empty(Assert.IsType<Result.ListValue>(value).Items);
}
