using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorOperatorTests
{
    private static void AssertNumericScalarOperandFailure(string source, params string[] expectedSubstrings)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected numeric scalar operand failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        foreach (var expectedSubstring in expectedSubstrings)
            Assert.Contains(expectedSubstring, formatted);
        Assert.DoesNotContain("Bad arity", formatted);

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;

        Assert.IsType<EvalError.TypeMismatch>(error);
    }

    // â”€â”€ Numbers â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Number_ReturnsValue()
        => AssertEval("42", 42);

    [Fact]
    public void Eval_NegativeNumber_ReturnsNegatedValue()
        => AssertEval("-5", -5);

    [Fact]
    public void Eval_DoubleNegative_ReturnsPositive()
        => AssertEval("--5", 5);

    [Fact]
    public void Eval_Zero_ReturnsZero()
        => AssertEval("0", 0);

    [Fact]
    public void Eval_LargeNumber_ReturnsCorrectValue()
        => AssertEval("9876543210", 9876543210.0m);

    [Fact]
    public void Eval_FloatingPoint_ReturnsValue()
        => AssertEval("3.14", 3.14m);

    [Fact]
    public void Eval_FloatingPoint_Arithmetic()
    {
        AssertEval("1.5 + 2.5", 4.0m);
        AssertEval("3.0 * 2.5", 7.5m);
    }

    // â”€â”€ Arithmetic â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Addition_ReturnsSum()
        => AssertEval("1 + 2", 3);

    [Fact]
    public void Eval_Subtraction_ReturnsDifference()
        => AssertEval("5 - 3", 2);

    [Fact]
    public void Eval_Multiplication_ReturnsProduct()
        => AssertEval("4 * 3", 12);

    [Fact]
    public void Eval_ChainedAddition_LeftAssociative()
        => AssertEval("10 - 3 - 2", 5);

    [Fact]
    public void Eval_MixedOperations_CorrectPrecedence()
        => AssertEval("1 + 2 * 3", 7);

    [Fact]
    public void Eval_ParenthesesOverridePrecedence()
        => AssertEval("(1 + 2) * 3", 9);

    [Fact]
    public void Eval_ComplexArithmetic()
        => AssertEval("5 * 3 - 2", 13);

    [Fact]
    public void Eval_BinaryMinusWithUnaryMinus()
        => AssertEval("5 - -3", 8);

    [Fact]
    public void Eval_NegativeResult()
        => AssertEval("3 - 10", -7);

    // â”€â”€ Comparisons â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_LessThan_True_Returns1()
        => AssertEval("3 < 5", 1);

    [Fact]
    public void Eval_LessThan_False_Returns0()
        => AssertEval("5 < 3", 0);

    [Fact]
    public void Eval_LessThan_Equal_Returns0()
        => AssertEval("3 < 3", 0);

    [Fact]
    public void Eval_GreaterThan_True_Returns1()
        => AssertEval("5 > 3", 1);

    [Fact]
    public void Eval_GreaterThan_False_Returns0()
        => AssertEval("3 > 5", 0);

    [Fact]
    public void Eval_GreaterThan_Equal_Returns0()
        => AssertEval("3 > 3", 0);

    [Fact]
    public void Eval_Division()
        => AssertEval("10 / 4", 2.5m);

    [Fact]
    public void Eval_IntegerDivision()
        => AssertEval("10 div 3", 3);

    [Fact]
    public void Eval_IntegerDivision_Truncates()
        => AssertEval("-7 div 2", -3);

    [Fact]
    public void Eval_IntegerDivision_NegativeDivisor_Truncates()
        => AssertEval("7 div -2", -3);

    [Fact]
    public void Eval_DivisionByZero_Fails()
        => AssertEvalFails("5 / 0");

    [Fact]
    public void Eval_IntegerDivisionByZero_Fails()
        => AssertEvalFails("5 div 0");

    [Fact]
    public void Eval_Modulo()
        => AssertEval("10 mod 3", 1);

    // Modulo keeps the sign of the dividend (truncating remainder). The Lean
    // core mirrors this with Int.tmod; see CoreTests truncatingModuloMatchesRuntime.
    [Fact]
    public void Eval_Modulo_NegativeDividend_KeepsDividendSign()
        => AssertEval("-7 mod 2", -1);

    [Fact]
    public void Eval_Modulo_NegativeDivisor_KeepsDividendSign()
        => AssertEval("7 mod -2", 1);

    [Fact]
    public void Eval_Modulo_LeftSequenceValueOperand_ReportsNumericScalarDiagnostic()
        => AssertNumericScalarOperandFailure(
            "(3, 4, 5, 6) mod 2",
            "while evaluating `(3, 4, 5, 6) mod 2`",
            "operator `mod` expects numeric scalar operands",
            "left operand was a sequence value with 4 sequence elements: (3, 4, 5, 6)");

    [Fact]
    public void Eval_Modulo_RightSequenceValueOperand_ReportsNumericScalarDiagnostic()
        => AssertNumericScalarOperandFailure(
            "2 mod (3, 4, 5, 6)",
            "while evaluating `2 mod (3, 4, 5, 6)`",
            "operator `mod` expects numeric scalar operands",
            "right operand was a sequence value with 4 sequence elements: (3, 4, 5, 6)");

    [Fact]
    public void Eval_ModuloByZero_Fails()
        => AssertEvalFails("10 mod 0");

    [Fact]
    public void Eval_Power()
        => AssertEval("2 ^ 10", 1024);

    [Fact]
    public void Eval_Power_ZeroExponent()
        => AssertEval("5 ^ 0", 1);

    [Fact]
    public void Eval_Power_NegativeExponent()
        => AssertEval("2 ^ -3", 0.125m);

    // â”€â”€ Comparison operators â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_LessEqual_True()
        => AssertEval("3 <= 3", 1);

    [Fact]
    public void Eval_LessEqual_False()
        => AssertEval("4 <= 3", 0);

    [Fact]
    public void Eval_GreaterEqual_True()
        => AssertEval("3 >= 3", 1);

    [Fact]
    public void Eval_GreaterEqual_False()
        => AssertEval("2 >= 3", 0);

    [Fact]
    public void Eval_Equal_True()
        => AssertEval("5 == 5", 1);

    [Fact]
    public void Eval_Equal_False()
        => AssertEval("5 == 6", 0);

    [Fact]
    public void Eval_NotEqual_True()
        => AssertEval("5 != 6", 1);

    [Fact]
    public void Eval_NotEqual_False()
        => AssertEval("5 != 5", 0);

    // ── Structural value equality (==, !=) ───────────────────────────────────
    // `==` and `!=` compare KatLang values structurally across all value kinds:
    // numbers by value, strings by exact value, and sequence values by length
    // plus recursive pairwise equality. Different value kinds compare unequal
    // rather than raising a type mismatch. Ordering and arithmetic operators keep
    // their numeric-scalar-only path (covered separately below).

    [Fact]
    public void Eval_Equal_SequenceValue_SameReference_ReturnsOne()
        => AssertEval(
            """
            A = 1, 2
            A == A
            """,
            1);

    [Fact]
    public void Eval_Equal_IndependentSequences_StructurallyEqual_ReturnsOne()
        => AssertEval(
            """
            A = 1, 2
            B = 1, 2
            A == B
            """,
            1);

    [Fact]
    public void Eval_Equal_Sequences_DifferentElement_ReturnsZero()
        => AssertEval(
            """
            A = 1, 2
            B = 1, 3
            A == B
            """,
            0);

    [Fact]
    public void Eval_Equal_Sequences_DifferentLength_ReturnsZero()
        => AssertEval(
            """
            A = 1, 2
            B = 1, 2, 3
            A == B
            """,
            0);

    [Fact]
    public void Eval_Equal_NestedSequences_StructurallyEqual_ReturnsOne()
        => AssertEval(
            """
            A = 1, (2, 3)
            B = 1, (2, 3)
            A == B
            """,
            1);

    [Fact]
    public void Eval_Equal_NestedSequences_DifferentInnerElement_ReturnsZero()
        => AssertEval(
            """
            A = 1, (2, 3)
            B = 1, (2, 4)
            A == B
            """,
            0);

    [Fact]
    public void Eval_Equal_NumberVsSequence_DifferentKinds_ReturnsZero()
        => AssertEval("1 == (1, 2)", 0);

    [Fact]
    public void Eval_NotEqual_NumberVsSequence_DifferentKinds_ReturnsOne()
        => AssertEval("1 != (1, 2)", 1);

    [Fact]
    public void Eval_NotEqual_SequenceValue_SameReference_ReturnsZero()
        => AssertEval(
            """
            A = 1, 2
            A != A
            """,
            0);

    [Fact]
    public void Eval_NotEqual_Sequences_DifferentElement_ReturnsOne()
        => AssertEval(
            """
            A = 1, 2
            B = 1, 3
            A != B
            """,
            1);

    [Fact]
    public void Eval_Equal_GroupedSpread_ComparesAsSingleSequenceValue_ReturnsOne()
        => AssertEval(
            """
            A = 1, 2
            (A*) == A
            """,
            1);

    // Spread item supplies must not be silently vectorized by equality. A spread
    // `A*` cannot be a binary operand: `A* == A*` is a targeted misplaced-spread
    // parse error (a spread expression cannot be used as a scalar operand). This
    // boundary is owned by the parser and is unchanged by structural equality —
    // equality never turns a spread item supply into an elementwise comparison. The
    // grouped form `(A*) == A` (covered above) is the supported way to compare
    // an opened-then-regrouped sequence value.
    [Fact]
    public void Eval_Equal_OpenedItemSupplies_NotSilentlyVectorized_IsParseError()
    {
        var parseResult = Parser.Parse(
            """
            A = 1, 2
            A* == A*
            """);
        Assert.True(parseResult.HasErrors);
    }

    [Fact]
    public void Eval_Add_SequenceValueOperands_StillRejectedWithNumericScalarDiagnostic()
        => AssertNumericScalarOperandFailure(
            """
            A = 1, 2
            A + A
            """,
            "while evaluating `A + A`",
            "operator `+` expects numeric scalar operands",
            "left operand was a sequence value with 2 sequence elements: (1, 2)");

    [Fact]
    public void Eval_LessThan_SequenceValueOperands_StillRejectedWithNumericScalarDiagnostic()
        => AssertNumericScalarOperandFailure(
            """
            A = 1, 2
            A < A
            """,
            "while evaluating `A < A`",
            "operator `<` expects numeric scalar operands",
            "left operand was a sequence value with 2 sequence elements: (1, 2)");

    // Structural equality preserves nesting; it must not flatten sequence values.
    // (1, (2, 3)) has shape [1, [2, 3]] while ((1, 2), 3) has shape [[1, 2], 3], so
    // even though both flatten to the same atoms they are structurally unequal.
    [Fact]
    public void Eval_Equal_NestedShapesDiffer_NotFlattened_ReturnsZero()
        => AssertEval("(1, (2, 3)) == ((1, 2), 3)", 0);

    // Sequence equality is ordered pairwise structural equality, not set equality.
    [Fact]
    public void Eval_Equal_DifferentOrder_IsOrderSensitive_ReturnsZero()
        => AssertEval("(1, 2) == (2, 1)", 0);

    // Empty sequence equality is stable across independently bound properties:
    // two distinct properties each bound to `()` compare equal.
    [Fact]
    public void Eval_Equal_EmptyPropertiesAcrossBindings_ReturnsOne()
        => AssertEval(
            """
            A = ()
            B = ()
            A == B
            """,
            1);

    [Fact]
    public void Eval_NotEqual_EmptyPropertiesAcrossBindings_ReturnsZero()
        => AssertEval(
            """
            A = ()
            B = ()
            A != B
            """,
            0);

    // Display formatting must not affect equality: equality compares numeric values,
    // so 1.2 and 1.20 are equal regardless of rendered decimal scale. The leading
    // DisplayDecimals directive (a display-only setting) does not change this.
    [Fact]
    public void Eval_Equal_DecimalScaleDoesNotAffectValueEquality_ReturnsOne()
        => AssertEval(
            """
            DisplayDecimals = 0
            1.2 == 1.20
            """,
            1);

    // â”€â”€ Logical operators â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_And_TrueTrue()
        => AssertEval("1 and 1", 1);

    [Fact]
    public void Eval_And_TrueFalse()
        => AssertEval("1 and 0", 0);

    [Fact]
    public void Eval_And_FalseFalse()
        => AssertEval("0 and 0", 0);

    [Fact]
    public void Eval_Or_TrueFalse()
        => AssertEval("1 or 0", 1);

    [Fact]
    public void Eval_Or_FalseFalse()
        => AssertEval("0 or 0", 0);

    [Fact]
    public void Eval_Xor_TrueFalse()
        => AssertEval("1 xor 0", 1);

    [Fact]
    public void Eval_Xor_TrueTrue()
        => AssertEval("1 xor 1", 0);

    [Fact]
    public void Eval_Xor_FalseFalse()
        => AssertEval("0 xor 0", 0);

    [Fact]
    public void Eval_Not_Zero()
        => AssertEval("not 0", 1);

    [Fact]
    public void Eval_Not_NonZero()
        => AssertEval("not 5", 0);

    [Fact]
    public void Eval_Not_DoubleNegation()
        => AssertEval("not not 1", 1);

    // â”€â”€ Operator combinations â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_CompoundExpression_IfWithComparison()
    {
        var source = """
            X = 10
            if(X >= 5, 1, 0)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_LogicalInIf()
    {
        var source = """
            A = 3
            B = 7
            if(A > 0 and B > 0, 1, 0)
            """;
        AssertEval(source, 1);
    }

    // â”€â”€ BinaryOp.Pow evaluator coverage â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Pow_IntegerExponentCases_Work()
    {
        AssertEval("2 ^ 0", 1);
        AssertEval("2 ^ 3", 8);
        AssertEval("5 ^ 4", 625);
        AssertEval("(-2) ^ 3", -8);
        AssertEval("(-2) ^ 4", 16);
        AssertEval("0 ^ 5", 0);
        AssertEval("0 ^ 0", 1);
        AssertEval("1 ^ 25", 1);
    }

    [Fact]
    public void Eval_Pow_NegativeIntegerExponentCases_Work()
    {
        AssertEval("2 ^ -3", 0.125m);
        AssertEval("10 ^ -2", 0.01m);
        AssertEval("(-2) ^ -3", -0.125m);
        AssertEval("1 ^ -25", 1);
    }

    [Fact]
    public void Eval_Pow_BindsTighterThanPrefixUnaryOnTheLeft()
    {
        // `^` binds tighter than the prefix unary operators on the LEFT (the
        // base), while the exponent side re-enters the unary level:
        // `-2 ^ 2` is `-(2 ^ 2)` and `2 ^ -2` stays `2 ^ (-2)`.
        AssertEval("-2 ^ 2", -4);
        AssertEval("(-2) ^ 2", 4);
        AssertEval("2 ^ -2", 0.25m);
        AssertEval("-2 ^ -2", -0.25m);
        AssertEval("2 ^ 3 ^ 2", 512);
        AssertEval("1 + -2 ^ 2", -3);
        AssertEval("2 * -3 ^ 2", -18);
        AssertEval("-(2 ^ 2)", -4);
        AssertEval("(-2) ^ 3", -8);
        AssertEval("2 ^ (-2)", 0.25m);
    }

    [Fact]
    public void Eval_Pow_UnaryAndRightAssociativityCombine()
    {
        // A unary base negates the WHOLE right-associative chain, and a unary
        // exponent applies to the whole tail it introduces.
        AssertEval("-2 ^ 3 ^ 2", -512);
        AssertEval("2 ^ -2 ^ 2", 0.0625m);

        // `not` sits in the same prefix-unary tier: `not 0 ^ 0` is
        // `not (0 ^ 0)`, and a `not` exponent stays valid.
        AssertEval("not 0 ^ 0", 0);
        AssertEval("2 ^ not 0", 2);
    }

    [Fact]
    public void Eval_Pow_FractionalExponentCases_UseMathPow()
    {
        // 27^1.5 = 81·√3 = 140.2961154130790607757231536619757...
        AssertEvalApprox("9 ^ 0.5", 3m, decimalPlaces: 30);
        AssertEvalApprox(
            "27 ^ 1.5",
            Decimal128.Parse("140.2961154130790607757231536619757", System.Globalization.CultureInfo.InvariantCulture),
            decimalPlaces: 30);
    }

    [Fact]
    public void Eval_Pow_FractionalExponent_MatchesMathPowNormalization()
    {
        AssertEval("0.0000000000000001 ^ 1.5 == Math.Pow(0.0000000000000001, 1.5)", 1);
    }

    [Fact]
    public void Eval_Pow_ZeroToNegativeInteger_FailsClearly()
    {
        AssertEvalFailsWithIllegalInEval("0 ^ -1", "zero cannot be raised to a negative integer exponent");
    }

    [Fact]
    public void Eval_Pow_ExponentOne_DoesNotOverflowFromFinalSquaring()
    {
        AssertEval("79228162514264337593543950335 ^ 1", 79228162514264337593543950335m);
    }

    // ── Beyond the old decimal range ─────────────────────────────────────────
    // These inputs overflowed System.Decimal and raised NumericOverflow; with
    // Decimal128 they are ordinary exact results. Genuine overflow past
    // Decimal128's range saturates to an infinity — see Decimal128NumericsTests.

    [Fact]
    public void Eval_Pow_BeyondOldDecimalRange_SucceedsExactly()
    {
        AssertEval("10 ^ 30", Decimal128.Parse("1e30", System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture));
    }

    [Fact]
    public void Eval_Pow_NormalRange_Succeeds()
    {
        AssertEval("10 ^ 2", 100);
    }

    [Fact]
    public void Eval_Mul_BeyondOldDecimalRange_SucceedsExactly()
    {
        // decimal.MaxValue is ~7.9e28; doubling it overflowed System.Decimal but
        // is an exact 30-digit Decimal128 value (beyond C#'s decimal literal range,
        // hence the parse).
        AssertEval(
            "79228162514264337593543950335 * 2",
            Decimal128.Parse("158456325028528675187087900670", System.Globalization.CultureInfo.InvariantCulture));
    }
}
