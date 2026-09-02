using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorMathTests
{
    // â”€â”€ Math built-in â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_MathPi_ReturnsMathPI()
    {
        var result = Eval("Math.Pi");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi, result.Value[0]);
    }

    [Fact]
    public void Eval_MathExp_ReturnsNaturalExponential()
    {
        // The oracle is Decimal128.Exp itself — Math.Exp is wired directly to
        // it, never through double or a stored constant.
        var result = Eval("Math.Exp(1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(Decimal128.Exp(Decimal128.One), result.Value[0]);
    }

    [Fact]
    public void Eval_RemovedMathE_UsesOrdinaryClosedMemberFailure()
        => AssertUnknownDotMember(ClosedMemberProbe("", "Math.E"), "E");

    [Theory]
    [InlineData("Math.Exp()", 0)]
    [InlineData("Math.Exp(1, 2)", 2)]
    public void Eval_MathExp_RequiresOneArgument(string source, int actual)
        => AssertEvalFailsWithArityMismatch(source, expected: 1, actual);

    [Fact]
    public void Eval_MathPi_InExpression()
    {
        var result = Eval("Math.Pi * 2");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2, result.Value[0]);
    }

    [Fact]
    public void Eval_MathExp_InExpression()
    {
        var result = Eval("Math.Exp(1) + 1");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(Decimal128.Exp(Decimal128.One) + 1, result.Value[0]);
    }

    [Fact]
    public void Eval_MathPi_InPropertyBody()
    {
        var source = """
            Circumference = Math.Pi * 2 * r
            Circumference(5)
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2 * 5, result.Value[0]);
    }

    [Fact]
    public void Eval_MathPi_UserPropertyOverrides()
    {
        var source = """
            Math = { Pi = 3
            Pi }
            Math.Pi
            """;
        AssertEval(source, 3);
    }

    // â”€â”€ Math functions â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_MathAbs_Positive()
        => AssertEval("Math.Abs(5)", 5);

    [Fact]
    public void Eval_MathAbs_Negative()
        => AssertEval("Math.Abs(-3)", 3);

    [Fact]
    public void Eval_MathCeil()
        => AssertEval("Math.Ceil(2.3)", 3);

    [Fact]
    public void Eval_MathFloor()
        => AssertEval("Math.Floor(2.7)", 2);

    [Fact]
    public void Eval_MathRound()
        => AssertEval("Math.Round(2.5, 0)", 3);

    [Fact]
    public void Eval_MathRound_Up()
        => AssertEval("Math.Round(3.5, 0)", 4);

    [Fact]
    public void Eval_MathRound_WithDigits()
        => AssertEval("Math.Round(1.234, 2)", 1.23m);

    [Fact]
    public void Eval_MathRound_WithDigits_RoundsMidpointAwayFromZero()
        => AssertEval("Math.Round(1.225, 2)", 1.23m);

    [Fact]
    public void Eval_MathRound_WithDigits_WorksAfterOpenMath()
        => AssertEval("open Math\nRound(1.236, 2)", 1.24m);

    [Fact]
    public void Eval_MathRound_WithFractionalDigits_Fails()
        => AssertEvalFailsWithIllegalInEval("Math.Round(1.234, 2.5)", "digits must be an integer");

    [Fact]
    public void Eval_MathSign_Positive()
        => AssertEval("Math.Sign(42)", 1);

    [Fact]
    public void Eval_MathSign_Negative()
        => AssertEval("Math.Sign(-7)", -1);

    [Fact]
    public void Eval_MathSign_Zero()
        => AssertEval("Math.Sign(0)", 0);

    [Fact]
    public void Eval_MathSqrt()
        => AssertEval("Math.Sqrt(9)", 3);

    [Fact]
    public void Eval_MathPow()
        => AssertEval("Math.Pow(2, 10)", 1024);

    // Reference values for these tests are independent 34-digit mathematical
    // constants (Wolfram-style references), NOT System.Math results — comparing
    // against double would just re-validate the removed 15-16 digit pipeline.
    // AssertApproximatelyEqual at 30+ places demonstrates precision far beyond
    // double while tolerating Decimal128's not-guaranteed-correctly-rounded
    // final digits.

    [Fact]
    public void Eval_MathLn()
        => AssertEvalApprox("Math.Ln(Math.Exp(1))", 1, decimalPlaces: 32);

    [Fact]
    public void Eval_MathLg()
        => AssertEvalApprox("Math.Lg(1000)", 3, decimalPlaces: 32);

    [Fact]
    public void Eval_MathLog()
        => AssertEvalApprox("Math.Log(8, 2)", 3, decimalPlaces: 32);

    [Fact]
    public void Eval_MathSin()
        => AssertEval("Math.Sin(0)", 0);

    [Fact]
    public void Eval_MathCos()
        => AssertEval("Math.Cos(0)", 1);

    [Fact]
    public void Eval_MathAsin()
        // asin(1) = π/2 = 1.570796326794896619231321691639751...
        => AssertEvalApprox(
            "Math.Asin(1)",
            Decimal128.Parse("1.570796326794896619231321691639751", System.Globalization.CultureInfo.InvariantCulture),
            decimalPlaces: 32);

    [Fact]
    public void Eval_MathAcos()
        => AssertEvalApprox("Math.Acos(1)", 0, decimalPlaces: 32);

    [Fact]
    public void Eval_MathTan()
        => AssertEval("Math.Tan(0)", 0);

    [Fact]
    public void Eval_MathTan_NearSingularity_ReturnsLargeMagnitude()
    {
        // Math.Pi/2 is slightly ABOVE the true π/2 (Pi rounds up in its last
        // digit), so tan lands just past the singularity: a huge NEGATIVE value
        // near -1/((Pi - π)/2) ≈ -1.7e34. Under the old double pipeline the
        // argument only carried ~16 digits, capping the magnitude near 1e16 —
        // the 1e30 bound proves the full 34-digit argument reached tan.
        var result = Eval("Math.Tan(Math.Pi/2)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.True(
            Decimal128.Abs(result.Value[0]) > Decimal128.ScaleB(Decimal128.One, 30),
            $"Tan near singularity should have huge magnitude, got {result.Value[0]}");
        Assert.True(Decimal128.IsNegative(result.Value[0]), "Math.Pi/2 sits past the true π/2, so tan is negative");
    }

    [Fact]
    public void Eval_MathSin_PiOverSix()
        // sin(π/6) = 0.5; the argument is the rounded Pi/6, so allow the final digits to differ.
        => AssertEvalApprox("Math.Sin(Math.Pi/6)", Decimal128.Parse("0.5", System.Globalization.CultureInfo.InvariantCulture), decimalPlaces: 32);

    [Fact]
    public void Eval_MathAtan()
        // atan(1) = π/4 = 0.7853981633974483096156608458198757...
        => AssertEvalApprox(
            "Math.Atan(1)",
            Decimal128.Parse("0.7853981633974483096156608458198757", System.Globalization.CultureInfo.InvariantCulture),
            decimalPlaces: 32);

    [Fact]
    public void Eval_MathAtan2()
        => AssertEvalApprox(
            "Math.Atan2(1, 1)",
            Decimal128.Parse("0.7853981633974483096156608458198757", System.Globalization.CultureInfo.InvariantCulture),
            decimalPlaces: 32);

    [Fact]
    public void Eval_MathAtan2_BindsArgumentsInConventionalYXOrder()
    {
        // Asymmetric arguments: atan2(y: 1, x: 0) is π/2, while the swapped
        // reading atan2(y: 0, x: 1) would be 0 — symmetric probes like (1, 1)
        // cannot tell the two argument orders apart.
        var elevated = Eval("Math.Atan2(1, 0)");
        Assert.True(elevated.IsOk);
        Assert.Single(elevated.Value);
        AssertApproximatelyEqual(
            Decimal128.Parse("1.570796326794896619231321691639751", System.Globalization.CultureInfo.InvariantCulture),
            elevated.Value[0],
            decimalPlaces: 32);

        var flat = Eval("Math.Atan2(0, 1)");
        Assert.True(flat.IsOk);
        Assert.Single(flat.Value);
        Assert.Equal(Decimal128.Zero, flat.Value[0]);
    }

    // ── Trig normalization (floating-point residue cleanup) ─────────────────

    [Fact]
    public void Eval_MathRandom_ReturnsNumberInUnitInterval()
    {
        var result = Eval("Math.Random(0, 1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.True(result.Value[0] >= 0m && result.Value[0] < 1m);
    }

    [Fact]
    public void Eval_MathRandom_ReturnsNumberInHalfOpenRange()
    {
        var result = Eval("Math.Random(1, 100)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.True(result.Value[0] >= 1m && result.Value[0] < 100m);
    }

    [Fact]
    public void Eval_MathRandom_RejectsEmptyRange()
        => AssertEvalFailsWithIllegalInEval("Math.Random(1, 1)", "start must be less than end");

    [Fact]
    public void Eval_MathRandom_RequiresBoundsForPropertyStyleAccess()
    {
        var error = GetEvalError("Math.Random");
        Assert.NotNull(error);
        while (error is EvalError.WithContext context)
            error = context.Inner;

        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(error);
        Assert.Equal(["start", "end"], unresolved.ParamNames);
    }

    [Fact]
    public void Eval_MathRandom_RequiresBoundsForExplicitCall()
        => AssertEvalFailsWithArityMismatch("Math.Random()", expected: 2, actual: 0);

    [Fact]
    public void Eval_MathRandomInt_ReturnsOnlyWholeNumberInPositiveInterval()
        => AssertEval("Math.RandomInt(5, 6)", 5m);

    [Fact]
    public void Eval_MathRandomInt_ReturnsOnlyWholeNumberInNegativeInterval()
        => AssertEval("Math.RandomInt(-5, -4)", -5m);

    [Fact]
    public void Eval_MathRandomInt_DoesNotUseInt32RangeLimits()
        => AssertEval("Math.RandomInt(3000000000, 3000000001)", 3000000000m);

    [Fact]
    public void Eval_MathRandomInt_ReturnsWholeNumberInHalfOpenRange()
    {
        var result = Eval("Math.RandomInt(1, 7)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);

        var value = result.Value[0];
        Assert.True(Decimal128.IsInteger(value));
        Assert.True(value >= 1m && value < 7m);
    }

    [Theory]
    [InlineData("Math.RandomInt(2.99, 3.2)")]
    [InlineData("Math.RandomInt(1.5, 10)")]
    [InlineData("Math.RandomInt(1, 10.5)")]
    public void Eval_MathRandomInt_RejectsDecimalBounds(string source)
        => AssertEvalFailsWithIllegalInEval(source, "bounds must be whole numbers");

    [Theory]
    [InlineData("Math.RandomInt(10, 10)")]
    [InlineData("Math.RandomInt(20, 10)")]
    public void Eval_MathRandomInt_RejectsEmptyOrReversedRange(string source)
        => AssertEvalFailsWithIllegalInEval(source, "start must be less than end");

    [Theory]
    [InlineData("Math.RandomInt()", 0)]
    [InlineData("Math.RandomInt(1)", 1)]
    [InlineData("Math.RandomInt(1, 2, 3)", 3)]
    public void Eval_MathRandomInt_RequiresTwoArguments(string source, int actual)
        => AssertEvalFailsWithArityMismatch(source, expected: 2, actual);

    [Fact]
    public void Eval_MathRand_IsUnknownMember()
        => AssertUnknownDotMember(ClosedMemberProbe("", "Math.Rand"), "Rand");

    [Fact]
    public void Eval_MathRandCall_IsUnknownMember()
        => AssertUnknownDotMember(ClosedMemberProbe("", "Math.Rand()"), "Rand");

    [Fact]
    public void Eval_MathRandInt_IsUnknownMember()
        => AssertUnknownDotMember(ClosedMemberProbe("", "Math.RandInt(1, 7)"), "RandInt");

    [Fact]
    public void Eval_ExplicitZeroParameterCall_ReevaluatesRandomPropertyBody()
    {
        const int maxAttempts = 20;
        var source = """
            Fun = Math.Random(0, 1), Math.Random(0, 1)
            Fun(), Fun()
            """;

        for (var attempt = 0; attempt < maxAttempts; attempt++)
        {
            var result = Eval(source);
            Assert.True(result.IsOk);
            Assert.Equal(4, result.Value.Count);
            Assert.All(result.Value, value => Assert.True(value >= 0m && value < 1m));

            if (result.Value.Distinct().Count() == result.Value.Count)
                return;
        }

        Assert.Fail("Expected explicit zero-parameter calls to re-evaluate the random property body.");
    }

    [Fact]
    public void Eval_PropertyStyleZeroParameterAccess_ReusesCachedRandomPropertyBody()
    {
        var result = Eval(
            """
            Fun = Math.Random(0, 1), Math.Random(0, 1)
            Fun, Fun
            """);

        Assert.True(result.IsOk);
        Assert.Equal(4, result.Value.Count);
        Assert.All(result.Value, value => Assert.True(value >= 0m && value < 1m));
        Assert.Equal(result.Value[0], result.Value[2]);
        Assert.Equal(result.Value[1], result.Value[3]);
    }

    // Math.Pi is π rounded to 34 digits (about 1.16e-34 ABOVE the true π), so
    // sin/tan of it are the tiny negative residual of that rounding, not zero.
    // The old pipeline snapped anything below 1e-15 to exactly 0 — that
    // workaround is gone, and the residual is now the honest full-precision
    // answer. These bounds pin both that it is non-zero and that it is tiny.

    [Fact]
    public void Eval_MathSin_Pi_ReturnsTinyRoundingResidual()
    {
        var result = Eval("Math.Sin(Math.Pi)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        var residual = result.Value[0];
        Assert.NotEqual(Decimal128.Zero, residual);
        Assert.True(Decimal128.IsNegative(residual), "Pi rounds up past π, so sin(Pi) is negative");
        Assert.True(Decimal128.Abs(residual) < Decimal128.ScaleB(Decimal128.One, -33));
    }

    [Fact]
    public void Eval_MathCos_PiOver2_ReturnsTinyRoundingResidual()
    {
        var result = Eval("Math.Cos(Math.Pi / 2)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.True(Decimal128.Abs(result.Value[0]) < Decimal128.ScaleB(Decimal128.One, -33));
    }

    [Fact]
    public void Eval_MathTan_Pi_ReturnsTinyRoundingResidual()
    {
        var result = Eval("Math.Tan(Math.Pi)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        var residual = result.Value[0];
        Assert.NotEqual(Decimal128.Zero, residual);
        Assert.True(Decimal128.Abs(residual) < Decimal128.ScaleB(Decimal128.One, -33));
    }

    [Fact]
    public void Eval_MathSin_Zero_ReturnsZero()
        => AssertEval("Math.Sin(0)", 0);

    [Fact]
    public void Eval_MathCos_Zero_ReturnsOne()
        => AssertEval("Math.Cos(0)", 1);

    [Fact]
    public void Eval_MathSin_One_ReturnsFullPrecision()
    {
        // sin(1) = 0.8414709848078965066525023216302990... — the result must
        // carry meaningful digits FAR beyond double's ~16, tolerating only the
        // final couple of Decimal128 digits.
        var result = Eval("Math.Sin(1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        AssertApproximatelyEqual(
            Decimal128.Parse("0.8414709848078965066525023216302990", System.Globalization.CultureInfo.InvariantCulture),
            result.Value[0],
            decimalPlaces: 32);
    }

    [Fact]
    public void Eval_MathSin_Pi_ViaOpen_ReturnsTinyRoundingResidual()
    {
        var source = """
            open Math
            Sin(Pi)
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.True(Decimal128.Abs(result.Value[0]) < Decimal128.ScaleB(Decimal128.One, -33));
    }

    [Fact]
    public void Eval_MathSqrt_InExpression()
        => AssertEval("Math.Sqrt(16) + 1", 5);

    [Fact]
    public void Eval_MathFn_ViaOpen()
    {
        var source = """
            open Math
            Abs(-5)
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_MathFn_ViaOpen_TwoParam()
    {
        var source = """
            open Math
            Pow(2, 8)
            """;
        AssertEval(source, 256);
    }
}
