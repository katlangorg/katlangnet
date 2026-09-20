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
        => AssertEvalBool("3 < 5", true);

    [Fact]
    public void Eval_LessThan_False_Returns0()
        => AssertEvalBool("5 < 3", false);

    [Fact]
    public void Eval_LessThan_Equal_Returns0()
        => AssertEvalBool("3 < 3", false);

    [Fact]
    public void Eval_GreaterThan_True_Returns1()
        => AssertEvalBool("5 > 3", true);

    [Fact]
    public void Eval_GreaterThan_False_Returns0()
        => AssertEvalBool("3 > 5", false);

    [Fact]
    public void Eval_GreaterThan_Equal_Returns0()
        => AssertEvalBool("3 > 3", false);

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

    // G-3: `div` truncates the EXACT quotient, not the quotient after IEEE rounded
    // it to 34 digits — the shared Decimal128Numerics.IntegerDivide, reached by the
    // generic spine, the async twin, and the planned loop arm alike.
    [Fact]
    public void Eval_IntegerDivision_ExactAt34Digits_DoesNotRoundUpBeforeTruncating()
        => AssertEvalLoopModes(
            "8999999999999999999999999999999999 div 3\n8999999999999999999999999999999999 mod 3",
            Decimal128.Parse("2999999999999999999999999999999999", System.Globalization.CultureInfo.InvariantCulture),
            2);

    [Fact]
    public void Eval_IntegerDivision_SmallQuotientNearAnIntegerBoundary_TruncatesExactly()
        {
        AssertEvalLoopModes("Y = 3e32\n(13 * Y - 1) div Y\n(12 * Y + 1) div Y", 12, 12);
        AssertEvalBool("Y = 3e32\n(13 * Y - 1) mod Y == Y - 1", true);
    }

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
        => AssertEvalBool("3 <= 3", true);

    [Fact]
    public void Eval_LessEqual_False()
        => AssertEvalBool("4 <= 3", false);

    [Fact]
    public void Eval_GreaterEqual_True()
        => AssertEvalBool("3 >= 3", true);

    [Fact]
    public void Eval_GreaterEqual_False()
        => AssertEvalBool("2 >= 3", false);

    [Fact]
    public void Eval_Equal_True()
        => AssertEvalBool("5 == 5", true);

    [Fact]
    public void Eval_Equal_False()
        => AssertEvalBool("5 == 6", false);

    [Fact]
    public void Eval_NotEqual_True()
        => AssertEvalBool("5 != 6", true);

    [Fact]
    public void Eval_NotEqual_False()
        => AssertEvalBool("5 != 5", false);

    // ── Structural value equality (==, !=) ───────────────────────────────────
    // `==` and `!=` compare KatLang values structurally across all value kinds:
    // numbers by value, strings by exact value, and sequence values by length
    // plus recursive pairwise equality. Different value kinds compare unequal
    // rather than raising a type mismatch. Ordering and arithmetic operators keep
    // their numeric-scalar-only path (covered separately below).

    [Fact]
    public void Eval_Equal_SequenceValue_SameReference_ReturnsOne()
        => AssertEvalBool(
            """
            A = 1, 2
            A == A
            """,
            true);

    [Fact]
    public void Eval_Equal_IndependentSequences_StructurallyEqual_ReturnsOne()
        => AssertEvalBool(
            """
            A = 1, 2
            B = 1, 2
            A == B
            """,
            true);

    [Fact]
    public void Eval_Equal_Sequences_DifferentElement_ReturnsZero()
        => AssertEvalBool(
            """
            A = 1, 2
            B = 1, 3
            A == B
            """,
            false);

    [Fact]
    public void Eval_Equal_Sequences_DifferentLength_ReturnsZero()
        => AssertEvalBool(
            """
            A = 1, 2
            B = 1, 2, 3
            A == B
            """,
            false);

    [Fact]
    public void Eval_Equal_NestedSequences_StructurallyEqual_ReturnsOne()
        => AssertEvalBool(
            """
            A = 1, (2, 3)
            B = 1, (2, 3)
            A == B
            """,
            true);

    [Fact]
    public void Eval_Equal_NestedSequences_DifferentInnerElement_ReturnsZero()
        => AssertEvalBool(
            """
            A = 1, (2, 3)
            B = 1, (2, 4)
            A == B
            """,
            false);

    [Fact]
    public void Eval_Equal_NumberVsSequence_DifferentKinds_ReturnsZero()
        => AssertEvalBool("1 == (1, 2)", false);

    [Fact]
    public void Eval_NotEqual_NumberVsSequence_DifferentKinds_ReturnsOne()
        => AssertEvalBool("1 != (1, 2)", true);

    [Fact]
    public void Eval_NotEqual_SequenceValue_SameReference_ReturnsZero()
        => AssertEvalBool(
            """
            A = 1, 2
            A != A
            """,
            false);

    [Fact]
    public void Eval_NotEqual_Sequences_DifferentElement_ReturnsOne()
        => AssertEvalBool(
            """
            A = 1, 2
            B = 1, 3
            A != B
            """,
            true);

    [Fact]
    public void Eval_Equal_GroupedSpread_ComparesAsSingleSequenceValue_ReturnsOne()
        => AssertEvalBool(
            """
            A = 1, 2
            (A*) == A
            """,
            true);

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
        => AssertEvalBool("(1, (2, 3)) == ((1, 2), 3)", false);

    // Sequence equality is ordered pairwise structural equality, not set equality.
    [Fact]
    public void Eval_Equal_DifferentOrder_IsOrderSensitive_ReturnsZero()
        => AssertEvalBool("(1, 2) == (2, 1)", false);

    // Empty sequence equality is stable across independently bound properties:
    // two distinct properties each bound to `()` compare equal.
    [Fact]
    public void Eval_Equal_EmptyPropertiesAcrossBindings_ReturnsOne()
        => AssertEvalBool(
            """
            A = ()
            B = ()
            A == B
            """,
            true);

    [Fact]
    public void Eval_NotEqual_EmptyPropertiesAcrossBindings_ReturnsZero()
        => AssertEvalBool(
            """
            A = ()
            B = ()
            A != B
            """,
            false);

    // Display formatting must not affect equality: equality compares numeric values,
    // so 1.2 and 1.20 are equal regardless of rendered decimal scale. The leading
    // DisplayDecimals directive (a display-only setting) does not change this.
    [Fact]
    public void Eval_Equal_DecimalScaleDoesNotAffectValueEquality_ReturnsOne()
        => AssertEvalBool(
            """
            DisplayDecimals = 0
            1.2 == 1.20
            """,
            true);

    // â”€â”€ Logical operators â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_And_TrueTrue()
        => AssertEvalBool("true and true", true);

    [Fact]
    public void Eval_And_TrueFalse()
        => AssertEvalBool("true and false", false);

    [Fact]
    public void Eval_And_FalseFalse()
        => AssertEvalBool("false and false", false);

    [Fact]
    public void Eval_Or_TrueFalse()
        => AssertEvalBool("true or false", true);

    [Fact]
    public void Eval_Or_FalseFalse()
        => AssertEvalBool("false or false", false);

    [Fact]
    public void Eval_Xor_TrueFalse()
        => AssertEvalBool("true xor false", true);

    [Fact]
    public void Eval_Xor_TrueTrue()
        => AssertEvalBool("true xor true", false);

    [Fact]
    public void Eval_Xor_FalseFalse()
        => AssertEvalBool("false xor false", false);

    [Fact]
    public void Eval_Not_Zero()
        => AssertEvalBool("not false", true);

    [Fact]
    public void Eval_Not_NonZero()
        => AssertEvalBool("not true", false);

    [Fact]
    public void Eval_Not_DoubleNegation()
        => AssertEvalBool("not not true", true);

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

        // `not` binds below `^` (and below every comparison): `not 0 ^ 0` is `not (0 ^ 0)` — a
        // Boolean operator applied to the NUMBER 1, so it is the Boolean-operand rejection
        // (never a re-association); `not 0 ^ 0 == 1` negates the whole comparison; and a
        // parenthesized Boolean exponent is the numeric-scalar rejection of `^` (the bare
        // `2 ^ not false` is a parse error: `not` cannot be an operand of `^`).
        AssertEvalFailsWithTypeMismatch("not 0 ^ 0", "operator `not` expects a Boolean operand, but the operand was numeric value 1");
        AssertEvalBool("not 0 ^ 0 == 1", false);
        AssertEvalFailsWithTypeMismatch("2 ^ (not false)", "operator `^` expects numeric scalar operands, but the right operand was a Boolean value: true");
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
        AssertEvalBool("0.0000000000000001 ^ 1.5 == Math.Pow(0.0000000000000001, 1.5)", true);
    }

    [Theory]
    [InlineData("0 ^ -1")]
    [InlineData("0 ^ -0.5")]
    [InlineData("0 ^ -2.5")]
    [InlineData("Math.Pow(0, -0.5)")]
    public void Eval_Pow_ZeroToNegativeExponent_FailsClearly(string source)
    {
        // Integral or not, a negative exponent on a zero base is the one
        // reciprocal-like domain error — never IEEE's Infinity — through `^` and
        // the shared Math.Pow implementation alike.
        AssertEvalFailsWithIllegalInEval(source, "zero cannot be raised to a negative exponent");
    }

    [Fact]
    public void Eval_Pow_ZeroToNonNegativeExponent_IsUnchanged()
    {
        AssertEval("0 ^ 0", 1);
        AssertEval("0 ^ 1", 0);
        AssertEval("0 ^ 0.5", 0);
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
