using System.Globalization;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// The Decimal128 numeric core: KatLang numbers are IEEE 754 Decimal128 end-to-end
/// (34 significant decimal digits), with no <c>decimal</c> or <c>double</c> stage
/// anywhere in literal parsing, arithmetic, or the math functions.
///
/// <para><b>Precision coverage.</b> Transcendental expectations are independent
/// 34-digit mathematical references (Wolfram-style constants), never
/// <c>System.Math</c> results — comparing against double would re-validate the
/// removed ~16-digit pipeline. Comparisons use a decimal-place tolerance because
/// .NET's initial Decimal128 transcendentals are high precision but not guaranteed
/// correctly rounded; basic arithmetic (add/multiply/divide/sqrt) IS correctly
/// rounded per IEEE 754 and is asserted exactly where appropriate.</para>
///
/// <para><b>IEEE semantics coverage.</b> Where KatLang specifies behavior it is
/// preserved (division/modulo by a zero-valued divisor — the EVALUATED value,
/// signed zeros and computed zeros included — stays <see cref="EvalError.DivByZero"/>,
/// zero to a negative integer power stays an error); everywhere else the natural
/// Decimal128 behavior holds: overflow saturates to an infinity, domain violations
/// produce NaN, comparisons with NaN are false, and structural value equality
/// (<c>==</c>, <c>distinct</c>, <c>contains</c>) treats NaN as one value.</para>
/// </summary>
public class Decimal128NumericsTests
{
    private static Decimal128 N(string text)
        => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);

    private static Algorithm ParseValidRoot(string source)
    {
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
        {
            Assert.Fail(
                "Source must parse cleanly, but the front end reported:"
                + Environment.NewLine
                + string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => "  - " + d.Message.Split('\n')[0])));
        }

        return parsed.Root;
    }

    private static EvalResult<IReadOnlyList<Decimal128>> Eval(string source)
        => Evaluator.RunFlat(new Expr.AlgorithmExpr(ParseValidRoot(source)));

    private static Decimal128 EvalSingle(string source)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Single(result.Value);
        return result.Value[0];
    }

    private static EvalError EvalError(string source)
    {
        var result = Eval(source);
        Assert.True(result.IsError, $"Expected `{source}` to fail, but it produced: {(result.IsError ? null : string.Join(", ", result.Value))}");
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static void AssertApprox(string source, Decimal128 expected, int decimalPlaces)
        => EvaluatorTestSupport.AssertApproximatelyEqual(expected, EvalSingle(source), decimalPlaces);

    // ── Transcendental precision (the migration's motivation) ────────────────
    // References: sin(1)  = 0.84147098480789650665250232163029899962...
    //             cos(1)  = 0.54030230586813971740093660744297660373...
    //             tan(1)  = 1.55740772465490223050697480745836017006...
    //             sqrt(2) = 1.41421356237309504880168872420969807857...
    //             e       = 2.71828182845904523536028747135266249776...
    //             ln(2)   = 0.69314718055994530941723212145817656808...
    // Asserting 32 decimal places demonstrates roughly twice double's ~16
    // significant digits survive end-to-end through the language surface.

    [Fact]
    public void Sin_One_Carries34DigitPrecision()
        => AssertApprox("Math.Sin(1)", N("0.8414709848078965066525023216302990"), 32);

    [Fact]
    public void Cos_One_Carries34DigitPrecision()
        => AssertApprox("Math.Cos(1)", N("0.5403023058681397174009366074429766"), 32);

    [Fact]
    public void Tan_One_Carries34DigitPrecision()
        => AssertApprox("Math.Tan(1)", N("1.557407724654902230506974807458360"), 31);

    [Fact]
    public void Sqrt_Two_IsCorrectlyRounded()
        // Sqrt is an IEEE basic operation: correctly rounded, asserted exactly.
        => Assert.Equal(N("1.414213562373095048801688724209698"), EvalSingle("Math.Sqrt(2)"));

    [Fact]
    public void Exp_One_Carries34DigitPrecision()
        // Math.Exp is wired directly to Decimal128.Exp — never through double,
        // Pow, or a stored constant — so exp(1) reproduces e's 34-digit
        // expansion to transcendental tolerance.
        => AssertApprox("Math.Exp(1)", N("2.718281828459045235360287471352662"), 32);

    [Fact]
    public void Exp_HalfSquared_Carries34DigitPrecision()
        // exp(0.5)^2 composes two transcendental draws and still lands on e.
        => AssertApprox("Math.Exp(0.5) ^ 2", N("2.718281828459045235360287471352662"), 30);

    [Fact]
    public void Ln_Two_Carries34DigitPrecision()
        => AssertApprox("Math.Ln(2)", N("0.6931471805599453094172321214581766"), 32);

    [Fact]
    public void TranscendentalResults_AreNotTruncatedTo16Digits()
    {
        // The old pipeline rounded to 15 significant digits; digits 17-34 of
        // sin(1) must now be meaningful. Subtracting the 16-digit prefix
        // 0.8414709848078965 from 0.8414709848078965066525023216302990 leaves
        // the genuine tail, which the old implementation reported as zero.
        var tail = EvalSingle("Math.Sin(1) - 0.8414709848078965");
        EvaluatorTestSupport.AssertApproximatelyEqual(N("6.652502321630299e-18"), tail, 32);
    }

    // ── Trigonometric argument reduction at large magnitude ──────────────────
    // The absolute oracle is SineOracle below: published π digits + BigInteger
    // fixed-point arithmetic + a Taylor series — no Decimal128, System.Math, or
    // double anywhere in its derivation, and its own accuracy (~1e-58) is
    // audited by comparing it against independently published sin(1)/cos(1)
    // digit strings. That justifies the full 30-decimal-place assertions here.

    [Fact]
    public void SineOracle_MatchesPublishedSinAndCosOfOne()
    {
        // Self-audit of the oracle against published constants (Wolfram-style
        // 34-digit references), independent of everything under test.
        AssertScaledClose(N("0.8414709848078965066525023216302990"), SineOracle.SinScaled(1), 30);
        AssertScaledClose(N("0.5403023058681397174009366074429766"), SineOracle.CosScaled(1), 30);
    }

    [Fact]
    public void Sin_1e30_MatchesTheIndependentOracleTo30Digits()
    {
        // A double stage cannot pass this: binary64 cannot even represent 10^30
        // (its nearest value is 10^30 + 1.99e13), and Math.Sin(1e30) is
        // +0.00933… — the wrong sign entirely.
        AssertScaledClose(EvalSingle("Math.Sin(1e30)"), SineOracle.SinScaled(BigInteger.Pow(10, 30)), 30);
    }

    [Fact]
    public void Cos_1e30_MatchesTheIndependentOracleTo30Digits()
        => AssertScaledClose(EvalSingle("Math.Cos(1e30)"), SineOracle.CosScaled(BigInteger.Pow(10, 30)), 30);

    [Fact]
    public void PythagoreanIdentity_HoldsTo33Digits_AtLargeAngle()
    {
        // Supplementary consistency evidence only — correlated errors could
        // satisfy the identity, so it is not an absolute oracle; the oracle
        // tests above carry the absolute claim. It still rules out any shared
        // ~1e-16 double stage.
        var residual = EvalSingle("Math.Sin(1e30) ^ 2 + Math.Cos(1e30) ^ 2 - 1");
        Assert.True(
            Decimal128.Abs(residual) <= Decimal128.ScaleB(Decimal128.One, -33),
            $"Identity residual too large: {residual}");
    }

    /// <summary>Asserts |expected − oracle| below 10^-decimalPlaces, comparing in the oracle's fixed-point domain.</summary>
    private static void AssertScaledClose(Decimal128 actual, BigInteger oracleScaled, int decimalPlaces)
    {
        var actualScaled = ToOracleScale(actual);
        var tolerance = BigInteger.Pow(10, SineOracle.ScaleDigits - decimalPlaces);
        var difference = BigInteger.Abs(actualScaled - oracleScaled);
        Assert.True(
            difference <= tolerance,
            $"Expected {actual} to agree with the oracle value {oracleScaled}e-{SineOracle.ScaleDigits} "
            + $"to {decimalPlaces} decimal places (scaled difference {difference}).");
    }

    /// <summary>
    /// Exact conversion of a finite Decimal128 to the oracle's fixed-point scale via
    /// its invariant positional rendering — no floating-point re-interpretation.
    /// </summary>
    private static BigInteger ToOracleScale(Decimal128 value)
    {
        var text = value.ToString(CultureInfo.InvariantCulture);
        var negative = text.StartsWith('-');
        if (negative)
            text = text[1..];

        var dot = text.IndexOf('.');
        var digits = dot < 0 ? text : text[..dot] + text[(dot + 1)..];
        var fractionDigits = dot < 0 ? 0 : text.Length - dot - 1;
        Assert.InRange(fractionDigits, 0, SineOracle.ScaleDigits);

        var scaled = BigInteger.Parse(digits) * BigInteger.Pow(10, SineOracle.ScaleDigits - fractionDigits);
        return negative ? -scaled : scaled;
    }

    /// <summary>
    /// Independent high-precision sine/cosine oracle: the first 100 published
    /// decimal digits of π (OEIS A000796), BigInteger fixed-point arithmetic, and
    /// the Taylor series — fully independent of Decimal128, <c>System.Math</c>,
    /// and binary floating point.
    ///
    /// <para>Accuracy audit: argument reduction runs at scale 10^100, so the
    /// π-truncation error (&lt; 1e-100) amplified by the 10^30/2π quotient
    /// (~1.6e29) stays below 1e-70 in the reduced argument; the series runs at
    /// scale 10^60 with ~30 truncating operations, keeping the total error below
    /// ~1e-58. The 30-decimal-place assertions therefore have &gt; 10^28 margin,
    /// and <see cref="SineOracle_MatchesPublishedSinAndCosOfOne"/> checks the
    /// oracle itself against independently published constants.</para>
    /// </summary>
    private static class SineOracle
    {
        public const int ScaleDigits = 60;

        // π = 3.<these 100 digits>… (OEIS A000796).
        private const string PiFractionalDigits =
            "1415926535897932384626433832795028841971"
            + "6939937510582097494459230781640628620899"
            + "86280348253421170679";

        private static readonly BigInteger ReductionScale = BigInteger.Pow(10, 100);
        private static readonly BigInteger SeriesScale = BigInteger.Pow(10, ScaleDigits);
        private static readonly BigInteger PiAtReductionScale = BigInteger.Parse("3" + PiFractionalDigits);
        private static readonly BigInteger PiAtSeriesScale = PiAtReductionScale / BigInteger.Pow(10, 100 - ScaleDigits);

        /// <summary>sin(n) · 10^60 for a non-negative integer n.</summary>
        public static BigInteger SinScaled(BigInteger n)
            => SinOfReduced(n * ReductionScale % (2 * PiAtReductionScale));

        /// <summary>cos(n) · 10^60 via cos(t) = sin(t + π/2).</summary>
        public static BigInteger CosScaled(BigInteger n)
            => SinOfReduced(((n * ReductionScale) + (PiAtReductionScale / 2)) % (2 * PiAtReductionScale));

        private static BigInteger SinOfReduced(BigInteger reducedAtReductionScale)
        {
            // Down to series scale, then quadrant-fold into [0, π/2]:
            // sin(x) = -sin(x - π) for x > π, and sin(x) = sin(π - x) above π/2.
            var x = reducedAtReductionScale / BigInteger.Pow(10, 100 - ScaleDigits);
            var sign = BigInteger.One;
            if (x > PiAtSeriesScale)
            {
                x -= PiAtSeriesScale;
                sign = BigInteger.MinusOne;
            }

            if (2 * x > PiAtSeriesScale)
                x = PiAtSeriesScale - x;

            return sign * SinSeries(x);
        }

        private static BigInteger SinSeries(BigInteger x)
        {
            var xSquared = x * x / SeriesScale;
            var term = x;
            var sum = x;
            for (var k = 1; term != 0; k++)
            {
                term = -(term * xSquared / SeriesScale) / ((2 * k) * ((2 * k) + 1));
                sum += term;
            }

            return sum;
        }
    }

    // ── Mathematical constants ───────────────────────────────────────────────

    [Fact]
    public void Pi_IsTheCorrectlyRounded34DigitValue()
        => Assert.Equal(N("3.141592653589793238462643383279503"), EvalSingle("Math.Pi"));

    [Fact]
    public void Exp_Zero_IsExactlyOne()
        // exp(0) = 1 is exact in Decimal128.Exp; the identity survives the
        // language surface and quantum canonicalization unchanged.
        => Assert.Equal(N("1"), EvalSingle("Math.Exp(0)"));

    [Fact]
    public void Constants_CarryPrecisionBeyondDouble()
    {
        // Math.Pi minus double's best π approximation leaves the genuine
        // 18-digit tail double cannot represent ((double)Math.PI is
        // 3.141592653589793115997963...; the written literal below is π's true
        // decimal expansion cut at double's printed 16 digits).
        var tail = EvalSingle("Math.Pi - 3.141592653589793");
        Assert.Equal(N("2.38462643383279503e-16"), tail);
    }

    // ── Arithmetic precision beyond decimal and double ───────────────────────

    [Fact]
    public void Arithmetic_34SignificantDigits_IsExact()
    {
        Assert.Equal(N("9999999999999999999999999999999999"), EvalSingle("9999999999999999999999999999999998 + 1"));
        Assert.Equal(N("1.000000000000000000000000000000001"), EvalSingle("1 + 1e-33"));
    }

    [Fact]
    public void Arithmetic_BeyondOldDecimalRange_IsExact()
    {
        // System.Decimal capped magnitude at ~7.9e28; these are ordinary values now.
        Assert.Equal(N("2e40"), EvalSingle("1e40 + 1e40"));
        Assert.Equal(N("1e60"), EvalSingle("1e30 * 1e30"));
    }

    [Fact]
    public void Average_DoesNotOverflowWhenTheTrueFiniteMeanIsRepresentable()
    {
        const string max = "9999999999999999999999999999999999e6111";

        Assert.Equal(Decimal128.MaxValue, EvalSingle($"avg(({max}, {max}))"));
        Assert.Equal(Decimal128.Zero, EvalSingle($"avg(({max}, {max}, -{max}, -{max}))"));
        Assert.Equal(
            N("3333333333333333333333333333333333e6111"),
            EvalSingle($"avg(({max}, {max}, -{max}))"));

        // Cancellation can leave a result at the subnormal floor. These cases
        // also pin one final ties-to-even rounding, including a written zero that
        // contributes to the divisor even though it contributes no coefficient.
        Assert.Equal(Decimal128.Epsilon, EvalSingle($"avg(({max}, {max}, -{max}, -{max}, 3e-6176))"));
        Assert.Equal(Decimal128.Zero, EvalSingle($"avg(({max}, {max}, -{max}, -{max}, 3e-6176, 0))"));
        Assert.Equal(N("2e-6176"), EvalSingle($"avg(({max}, {max}, -{max}, -{max}, 9e-6176, 0))"));
    }

    [Fact]
    public void DecimalFractions_AddExactly()
        // The classic binary-floating-point failure: exact in decimal arithmetic.
        => Assert.Equal(Decimal128.One, EvalSingle("0.1 + 0.2 == 0.3"));

    [Fact]
    public void Division_IsCorrectlyRoundedTo34Digits()
    {
        Assert.Equal(N("0.3333333333333333333333333333333333"), EvalSingle("1 / 3"));
        Assert.Equal(
            "0.3333333333333333333333333333333333",
            Assert.IsType<RunResult.Success>(KatLangEngine.Run("1 / 3")).ToDisplayString());
    }

    [Fact]
    public void IntegerDivision_TruncatesTheRoundedDecimal128Quotient()
    {
        // Both operands are exactly representable integers, but their mathematical
        // quotient is 2.999… and needs more than 34 significant digits. KatLang's
        // Decimal128 `div` rule is Truncate(x / y), so the quotient first rounds to
        // 3 and then truncates to 3. Lean's unbounded Int.tdiv returns 2 instead:
        // integer-looking source alone is therefore not the numeric model boundary.
        const string dividend = "9999999999999999999999999999999998";
        const string divisor = "3333333333333333333333333333333333";

        Assert.Equal(N("3"), EvalSingle($"{dividend} div {divisor}"));
        Assert.Equal(
            N("3333333333333333333333333333333332"),
            EvalSingle($"{dividend} mod {divisor}"));
    }

    // ── Numeric literals parse directly into Decimal128 ──────────────────────

    [Fact]
    public void Literal_34SignificantDigits_RoundTripsExactly()
    {
        var text = "1234567890123456789012345678901234";
        Assert.Equal(N(text), EvalSingle(text));
        Assert.Equal(text, Assert.IsType<RunResult.Success>(KatLangEngine.Run(text)).ToDisplayString());
    }

    [Fact]
    public void Literal_ScientificNotation_ParsesAtFullRange()
    {
        // Far beyond both double (~1e308) and System.Decimal (~7.9e28).
        Assert.Equal(N("1e6144"), EvalSingle("1e6144"));
        Assert.Equal(N("1.5e10"), EvalSingle("1.5e10"));
        Assert.Equal(N("2.5e-320"), EvalSingle("2.5e-320"));
        Assert.Equal(N("123.456"), EvalSingle("1.23456e2"));
    }

    [Fact]
    public void Literal_MoreThan34Digits_RoundsToNearest()
        // IEEE round-half-even at the 34-digit boundary, mirroring how extra
        // FRACTIONAL digits already rounded under System.Decimal.
        => Assert.Equal(N("1234567890123456789012345678901234"), EvalSingle("12345678901234567890123456789012341 / 10"));

    [Fact]
    public void Literal_ExceedingDecimal128Range_IsRejectedAtParseTime()
    {
        // 1e6145 overflows Decimal128 to an infinity during parsing; the lexer
        // keeps its established too-large diagnostic instead of a silent Infinity.
        var result = KatLangEngine.Run("1e6145");
        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.Contains(failure.Errors, error => error.Message.Contains("Number literal is too large"));
    }

    [Fact]
    public void Values_RoundTripThroughDisplayAndParsing()
    {
        foreach (var text in new[]
        {
            "0", "7", "-5", "1.5", "0.0000001", "123456789012345678901234567890.1234",
            "9999999999999999999999999999999999",
        })
        {
            var displayed = Assert.IsType<RunResult.Success>(KatLangEngine.Run(text)).ToDisplayString();
            var reparsed = text.StartsWith('-')
                ? Assert.IsType<RunResult.Success>(KatLangEngine.Run(displayed)).ToDisplayString()
                : displayed;
            Assert.Equal(displayed, reparsed);
            Assert.Equal(N(text), N(displayed));
        }
    }

    // ── Specified behavior preserved: zero-valued divisors stay errors ───────
    // The check is on the EVALUATED divisor value, exactly as the Lean model
    // specifies — a literal zero, a zero-valued property, a computed zero, a
    // negative zero, and an underflowed-to-zero literal all reject identically.

    [Theory]
    [InlineData("1 / 0")]
    [InlineData("0 / 0")]
    [InlineData("5 mod 0")]
    [InlineData("5 div 0")]
    [InlineData("z = 0\n1 / z")]
    [InlineData("1 / (1 - 1)")]
    [InlineData("1 / -0")]
    [InlineData("5 mod (2 - 2)")]
    [InlineData("1 / 1e-9999")] // the literal underflows to a zero VALUE before the division
    public void DivisionByZeroValuedDivisor_StaysTheSpecifiedError(string source)
        => Assert.IsType<EvalError.DivByZero>(EvalError(source));

    [Fact]
    public void ZeroToNegativeIntegerPower_StaysTheSpecifiedError()
    {
        var error = Assert.IsType<EvalError.IllegalInEval>(EvalError("0 ^ -1"));
        Assert.Contains("negative integer exponent", error.Reason);
    }

    // ── IEEE special values ──────────────────────────────────────────────────

    [Fact]
    public void Overflow_SaturatesToPositiveInfinity()
    {
        var value = EvalSingle("9e6144 * 10");
        Assert.True(Decimal128.IsPositiveInfinity(value));
        Assert.Equal("Infinity", Assert.IsType<RunResult.Success>(KatLangEngine.Run("9e6144 * 10")).ToDisplayString());
    }

    [Fact]
    public void Overflow_SaturatesToNegativeInfinity()
    {
        var value = EvalSingle("(0 - 9e6144) * 10");
        Assert.True(Decimal128.IsNegativeInfinity(value));
    }

    [Fact]
    public void InfinityArithmetic_FollowsIeee()
    {
        Assert.True(Decimal128.IsNaN(EvalSingle("9e6144 * 10 - 9e6144 * 10")));   // ∞ - ∞
        Assert.True(Decimal128.IsPositiveInfinity(EvalSingle("9e6144 * 10 + 1")));
        Assert.Equal(Decimal128.Zero, EvalSingle("1 / (9e6144 * 10)"));            // 1/∞ (the divisor VALUE is an infinity, not zero)
    }

    [Fact]
    public void DomainViolations_ProduceNaNOrInfinity()
    {
        Assert.True(Decimal128.IsNaN(EvalSingle("Math.Sqrt(-1)")));
        Assert.True(Decimal128.IsNaN(EvalSingle("Math.Ln(-1)")));
        Assert.True(Decimal128.IsNegativeInfinity(EvalSingle("Math.Ln(0)")));
        Assert.True(Decimal128.IsNaN(EvalSingle("Math.Asin(2)")));
        Assert.True(Decimal128.IsNaN(EvalSingle("(-2) ^ 0.5")));
    }

    [Fact]
    public void NaN_DisplaysAsNaN_AndInfinitiesDisplaySigned()
    {
        Assert.Equal("NaN", Assert.IsType<RunResult.Success>(KatLangEngine.Run("Math.Sqrt(-1)")).ToDisplayString());
        Assert.Equal("-Infinity", Assert.IsType<RunResult.Success>(KatLangEngine.Run("Math.Ln(0)")).ToDisplayString());
    }

    [Fact]
    public void NaN_OrderingComparisons_AreAllFalse()
    {
        Assert.Equal(Decimal128.Zero, EvalSingle("Math.Sqrt(-1) < 1"));
        Assert.Equal(Decimal128.Zero, EvalSingle("Math.Sqrt(-1) > 1"));
        Assert.Equal(Decimal128.Zero, EvalSingle("Math.Sqrt(-1) <= 1"));
        Assert.Equal(Decimal128.Zero, EvalSingle("Math.Sqrt(-1) >= 1"));
    }

    [Fact]
    public void NaN_StructuralEquality_TreatsNaNAsOneValue()
    {
        // KatLang `==` is STRUCTURAL value equality (it also compares strings and
        // sequences), so it stays a reflexive equivalence relation: NaN is the
        // same value as NaN, exactly like .NET's Equals/collection semantics.
        // The IEEE `NaN != NaN` convention lives in the ordering operators above.
        Assert.Equal(Decimal128.One, EvalSingle("Math.Sqrt(-1) == Math.Sqrt(-1)"));
        Assert.Equal(Decimal128.Zero, EvalSingle("Math.Sqrt(-1) != Math.Sqrt(-1)"));
        Assert.Equal(Decimal128.One, EvalSingle("contains((1, Math.Sqrt(-1)), Math.Sqrt(-1))"));
        Assert.Equal("[NaN]", Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("distinct((Math.Sqrt(-1), Math.Sqrt(-1)))")).ToDisplayString());
    }

    [Fact]
    public void NaN_IsTruthy_LikeEveryNonZeroNumber()
        // The truth rule is "zero is false, any other numeric atom is true";
        // NaN is not zero.
        => Assert.Equal(Decimal128.One, EvalSingle("if(Math.Sqrt(-1), 1, 2)"));

    [Fact]
    public void MinMax_PropagateNaN()
    {
        Assert.True(Decimal128.IsNaN(EvalSingle("min((3, Math.Sqrt(-1), 1))")));
        Assert.True(Decimal128.IsNaN(EvalSingle("max((3, Math.Sqrt(-1), 1))")));
    }

    [Fact]
    public void Order_UsesTheTotalOrder_NaNFirstAscending()
    {
        Assert.Equal(
            "[NaN, -1, 1]",
            Assert.IsType<RunResult.Success>(KatLangEngine.Run("order((1, Math.Sqrt(-1), -1))")).ToDisplayString());
        Assert.Equal(
            "[1, -1, NaN]",
            Assert.IsType<RunResult.Success>(KatLangEngine.Run("orderDesc((1, Math.Sqrt(-1), -1))")).ToDisplayString());
    }

    [Fact]
    public void NonFiniteNumbers_AreRejectedWhereIntegersAreRequired()
    {
        Assert.IsType<EvalError.IllegalInEval>(EvalError("range(9e6144 * 10, 5)"));
        Assert.IsType<EvalError.IllegalInEval>(EvalError("repeat({s + 1}, Math.Sqrt(-1), 0)"));
        Assert.IsType<EvalError.BadIndex>(EvalError("(1, 2, 3):(Math.Sqrt(-1))"));
    }

    [Fact]
    public void Range_BoundsBeyondExactIntegerStepping_AreRejected()
    {
        // Above 1e34 consecutive integers are no longer representable (adding 1
        // would be absorbed), so bounds there cannot be enumerated faithfully.
        var error = Assert.IsType<EvalError.IllegalInEval>(EvalError("range(2e34, 2e34)"));
        Assert.Contains("range start", error.Reason);

        // At 1e34 itself and below, stepping is exact.
        Assert.Equal(
            new[] { N("9999999999999999999999999999999999"), N("1e34") },
            Eval("range(1e34 - 1, 1e34)").Value);
    }

    // ── Signed zero ──────────────────────────────────────────────────────────

    [Fact]
    public void NegativeZero_EqualsZero_ButDisplaysItsSign()
    {
        Assert.Equal(Decimal128.One, EvalSingle("-0 == 0"));
        Assert.Equal(Decimal128.Zero, EvalSingle("-0 < 0"));
        Assert.Equal("-0", Assert.IsType<RunResult.Success>(KatLangEngine.Run("-0")).ToDisplayString());
        Assert.Equal("0", Assert.IsType<RunResult.Success>(KatLangEngine.Run("-0 + 0")).ToDisplayString());
    }

    [Fact]
    public void NegativeZero_IsFalsy_AndHasSignZero()
    {
        Assert.Equal(N("2"), EvalSingle("if(-0, 1, 2)"));
        Assert.Equal(Decimal128.Zero, EvalSingle("Math.Sign(-0)"));
    }

    [Fact]
    public void Sign_OfNaN_PropagatesNaN()
        => Assert.True(Decimal128.IsNaN(EvalSingle("Math.Sign(Math.Sqrt(-1))")));

    // ── The old 0-28 Round gate is decimal-shaped and gone ───────────────────

    [Fact]
    public void Round_AcceptsDigitCountsBeyondTheOldDecimalScaleLimit()
    {
        Assert.Equal(N("2.5e-31"), EvalSingle("Math.Round(2.5001e-31, 32)"));
        Assert.Equal(N("1.23456789"), EvalSingle("Math.Round(1.23456789, 100)"));
        var error = Assert.IsType<EvalError.IllegalInEval>(EvalError("Math.Round(1.5, 0 - 1)"));
        Assert.Contains("digits", error.Reason);
    }

    [Fact]
    public void Round_ClampsBeforeNarrowingAnExtremeDigitCount()
    {
        Assert.Equal(Decimal128.Epsilon, EvalSingle("Math.Round(1e-6176, 1e34)"));
        Assert.Equal(6176, Evaluator.ClampRoundDigits(N("6177")));
        Assert.Equal(6176, Evaluator.ClampRoundDigits(N("1e34")));
    }

    [Fact]
    public void CanonicalizeMathResult_CoarsestQuantumIsAlreadyTerminal()
    {
        var value = Decimal128.Quantize(
            Decimal128.MaxValue,
            Decimal128.ScaleB(Decimal128.One, 6111));

        var canonical = Evaluator.CanonicalizeMathResult(value);

        Assert.Equal(value, canonical);
        Assert.True(Decimal128.HaveSameQuantum(value, canonical));
    }

    [Fact]
    public void CanonicalizeMathResult_TrailingZeroAtCoarsestQuantumTerminatesUnchanged()
    {
        // 1e6112 stores as coefficient 10 at the COARSEST quantum 1e6111, so
        // value-exact coarsening is blocked only by the exponent ceiling. The
        // loop's termination there rests on ScaleB clamping the target quantum
        // at 6111 (Quantize then returns the same value at the same quantum);
        // this pins that premise, which replaced the former explicit
        // `quantumExponent >= 6111` guard.
        var value = Decimal128.ScaleB(Decimal128.One, 6112);
        Assert.Equal(6111, Decimal128.ILogB(Decimal128.GetQuantum(value)));

        var canonical = Evaluator.CanonicalizeMathResult(value);

        Assert.Equal(value, canonical);
        Assert.True(Decimal128.HaveSameQuantum(value, canonical));
    }

    [Theory]
    [InlineData("Math.Random(0 - (9e6144 * 10), 1)")]
    [InlineData("Math.Random(0, 9e6144 * 10)")]
    public void Random_RejectsEitherNonFiniteBound(string source)
    {
        var error = Assert.IsType<EvalError.IllegalInEval>(EvalError(source));
        Assert.Contains("bounds must be finite", error.Reason);
    }

    [Fact]
    public void Random_RejectsFiniteBoundsWhoseDifferenceOverflows()
    {
        const string max = "9999999999999999999999999999999999e6111";
        var error = Assert.IsType<EvalError.IllegalInEval>(
            EvalError($"Math.Random(0 - {max}, {max})"));
        Assert.Contains("range is too large", error.Reason);
    }

    // ── Quantum-preserving display (formatting is presentation only) ─────────

    [Fact]
    public void Display_PreservesArithmeticQuantum_LikeDecimalDid()
    {
        Assert.Equal("1.0", Assert.IsType<RunResult.Success>(KatLangEngine.Run("0.5 + 0.5")).ToDisplayString());
        Assert.Equal("10.00", Assert.IsType<RunResult.Success>(KatLangEngine.Run("2.50 * 4")).ToDisplayString());
        Assert.Equal("1.50", Assert.IsType<RunResult.Success>(KatLangEngine.Run("1.50")).ToDisplayString());
    }

    [Fact]
    public void ExactTranscendentalResults_DisplayCanonically()
    {
        // .NET reports transcendental results at the maximum-precision quantum;
        // the evaluator applies IEEE `reduce` (value-preserving) so mathematically
        // exact results display cleanly instead of as 3.000…000 with 33 zeros.
        // Inexact results are untouched — every digit there is significant.
        Assert.Equal("3", Assert.IsType<RunResult.Success>(KatLangEngine.Run("Math.Lg(1000)")).ToDisplayString());
        Assert.Equal("1", Assert.IsType<RunResult.Success>(KatLangEngine.Run("Math.Sin(Math.Pi / 2)")).ToDisplayString());
        Assert.Equal("2", Assert.IsType<RunResult.Success>(KatLangEngine.Run("Math.Log(100, 10)")).ToDisplayString());
        Assert.Equal("2", Assert.IsType<RunResult.Success>(KatLangEngine.Run("4 ^ 0.5")).ToDisplayString());
        Assert.Equal(
            "0.841470984807896506652502321630299",
            Assert.IsType<RunResult.Success>(KatLangEngine.Run("Math.Sin(1)")).ToDisplayString());
    }

    [Fact]
    public void PowWithIntegerExponent_StaysExactWithIntegralQuantum()
    {
        // The by-squaring integer path: exact value AND clean display (the
        // IEEE Pow function would return 1024.000000000000000000000000000000).
        Assert.Equal("1024", Assert.IsType<RunResult.Success>(KatLangEngine.Run("2 ^ 10")).ToDisplayString());
        Assert.Equal("1024", Assert.IsType<RunResult.Success>(KatLangEngine.Run("Math.Pow(2, 10)")).ToDisplayString());
        Assert.Equal(N("1267650600228229401496703205376"), EvalSingle("2 ^ 100"));
    }

    [Theory]
    [InlineData("10", "-6146", "1e-6146")]
    [InlineData("(-10)", "-6147", "-1e-6147")]
    public void NegativeIntegerExponent_WithRepresentableSubnormalReciprocal_DoesNotCollapseToZero(
        string baseExpression, string exponent, string expected)
    {
        // The exact integer path normally computes the positive power and takes
        // its reciprocal. At this boundary the positive intermediate overflows
        // even though the reciprocal is a representable Decimal128 subnormal;
        // both public spellings must preserve that non-zero result.
        var expectedValue = N(expected);
        Assert.Equal(expectedValue, EvalSingle($"{baseExpression} ^ {exponent}"));
        Assert.Equal(expectedValue, EvalSingle($"Math.Pow({baseExpression}, {exponent})"));
    }

    [Theory]
    [InlineData("(-1)", "9223372036854775807", "-1")]
    [InlineData("(-1)", "9223372036854775806", "1")]
    [InlineData("(-1)", "-9223372036854775807", "-1")]
    [InlineData("2", "9223372036854775807", "Infinity")]
    [InlineData("(-1)", "-9223372036854775808", "1")]
    public void IntegralExponent_LongBoundaryMatchesTheDocumentedRouting(
        string baseExpression, string exponent, string expectedDisplay)
    {
        // Magnitudes through long.MaxValue take the bounded by-squaring path;
        // long.MinValue's magnitude is one larger and delegates to Decimal128.Pow.
        // Both public spellings must agree across that exact routing boundary.
        var viaOperator = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run($"{baseExpression} ^ {exponent}")).ToDisplayString();
        var viaMathPow = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run($"Math.Pow({baseExpression}, {exponent})")).ToDisplayString();

        Assert.Equal(expectedDisplay, viaOperator);
        Assert.Equal(viaOperator, viaMathPow);
    }

    // ── Integral exponents beyond long: delegated, IEEE-exact special bases ──
    // The exact-by-squaring guarantee covers |exponent| <= long.MaxValue; larger
    // integral exponents delegate to Decimal128.Pow. IEEE 754 fully specifies
    // pow for the special bases, and these cases pin that behavior — by sign and
    // parity — through BOTH public spellings, which must agree exactly because
    // they share one implementation.

    public static TheoryData<string, string, string> HugeIntegralExponentCases()
    {
        const string HugeOdd = "9223372036854775809";  // long.MaxValue + 2
        const string HugeEven = "9223372036854775810"; // long.MaxValue + 3

        return new TheoryData<string, string, string>
        {
            { "1", HugeOdd, "1" },
            { "(-1)", HugeOdd, "-1" },
            { "(-1)", HugeEven, "1" },
            { "0", HugeOdd, "0" },
            { "(-0)", HugeOdd, "-0" },
            { "(-0)", HugeEven, "0" },
            { "(9e6144 * 10)", HugeOdd, "Infinity" },       // +∞ ^ huge
            { "(0 - 9e6144 * 10)", HugeOdd, "-Infinity" },  // -∞ ^ huge-odd
            { "(0 - 9e6144 * 10)", HugeEven, "Infinity" },  // -∞ ^ huge-even
            { "Math.Sqrt(-1)", HugeOdd, "NaN" },            // NaN ^ huge
            { "2", "1e34", "Infinity" },                    // ordinary base saturates
            { "0.5", "1e34", "0" },                         // ordinary base underflows
        };
    }

    [Theory]
    [MemberData(nameof(HugeIntegralExponentCases))]
    public void HugeIntegralExponents_ResolveBySignAndParity_ThroughBothSpellings(
        string baseExpression, string exponent, string expectedDisplay)
    {
        var operatorDisplay = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run($"{baseExpression} ^ {exponent}")).ToDisplayString();
        var mathPowDisplay = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run($"Math.Pow({baseExpression}, {exponent})")).ToDisplayString();

        Assert.Equal(expectedDisplay, operatorDisplay);
        Assert.Equal(operatorDisplay, mathPowDisplay);
    }

    [Fact]
    public void ZeroToHugeNegativeIntegralExponent_StaysTheSpecifiedError_OnBothSpellings()
    {
        var viaOperator = Assert.IsType<EvalError.IllegalInEval>(EvalError("0 ^ (0 - 9223372036854775809)"));
        Assert.Contains("negative integer exponent", viaOperator.Reason);

        var viaMathPow = Assert.IsType<EvalError.IllegalInEval>(EvalError("Math.Pow(0, 0 - 9223372036854775809)"));
        Assert.Equal(viaOperator.Reason, viaMathPow.Reason);
    }

    // ── Canonical rendering parses back as KatLang syntax ────────────────────
    // Decimal128's invariant rendering is POSITIONAL for every finite value —
    // it never emits scientific notation, so no uppercase-E (which the lexer
    // would read as an identifier) can appear. These tests are the regression
    // guard for that platform property across representation classes: parsed
    // scientific literals, quantum-coarsened (Quantize/ScaleB) cohort members,
    // range extremes, and subnormals.

    [Fact]
    public void FiniteRendering_NeverEmitsAnExponentMarker_AndReparsesToTheSameValue()
    {
        var representationSamples = new[]
        {
            N("1e30"), N("1e-30"), N("1e6144"), Decimal128.Epsilon, Decimal128.MaxValue,
            Decimal128.NegativeZero, N("1.50"), Decimal128.ScaleB(Decimal128.One, 34),
            Decimal128.Quantize(N("3e30"), Decimal128.ScaleB(Decimal128.One, 30)),
            Decimal128.GetQuantum(N("1e40")),
        };

        // A deterministic sweep across the full coefficient/exponent space: parse
        // constructs the exact cohort member (coefficient, exponent), so this
        // covers representations no arithmetic path happens to produce.
        var seeded = new Random(1234);
        var sweep = Enumerable.Range(0, 500).Select(_ =>
        {
            var digits = seeded.Next(1, 35);
            var coefficient = string.Concat(Enumerable.Range(0, digits)
                .Select(i => (char)('0' + (i == 0 ? seeded.Next(1, 10) : seeded.Next(0, 10)))));
            var exponent = seeded.Next(-6100, 6101);
            return N($"{coefficient}e{exponent}");
        });

        foreach (var value in representationSamples.Concat(sweep))
        {
            var rendered = value.ToString(CultureInfo.InvariantCulture);
            Assert.DoesNotContain('E', rendered);
            Assert.DoesNotContain('e', rendered);

            var reparsed = N(rendered);
            Assert.Equal(value, reparsed);
        }
    }

    [Fact]
    public void RenderedValues_ReparseThroughTheFullLanguageSurface()
    {
        // End-to-end: display a value, feed the display text back through the
        // LEXER and evaluator, and get the same value. Negative renderings
        // re-enter through unary minus. (NaN/Infinity are display-only forms:
        // they are identifiers to the lexer, exactly like before the migration.)
        foreach (var source in new[] { "1e30", "1e-30", "1e6144", "1e-6176", "-0", "1.50", "0.5 + 0.5" })
        {
            var firstRun = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
            var rendered = firstRun.ToDisplayString();

            var secondRun = Assert.IsType<RunResult.Success>(KatLangEngine.Run(rendered));
            Assert.Equal(rendered, secondRun.ToDisplayString());
            Assert.Equal(Assert.Single(firstRun.Atoms), Assert.Single(secondRun.Atoms));
        }
    }

    [Fact]
    public void FractionalQuantum_SurvivesTheDisplayRoundTrip()
    {
        // Quantum preservation is documented display behavior for fractional
        // quanta (trailing zeros): positional text carries it exactly. A
        // positive-exponent cohort member (1 x 10^30) necessarily renders as
        // plain digits, so only its VALUE round-trips — that is inherent to
        // positional text, not a renderer defect.
        foreach (var text in new[] { "1.50", "10.00", "0.000100" })
        {
            var value = N(text);
            var reparsed = N(value.ToString(CultureInfo.InvariantCulture));
            Assert.True(Decimal128.HaveSameQuantum(value, reparsed));
        }
    }

    // ── Literal boundaries ───────────────────────────────────────────────────

    [Fact]
    public void Literal_35Digits_RoundsHalfEven_InBothTieDirections()
    {
        // Both ties land on the EVEN 34-digit coefficient …002 (value …020): the
        // first rounds UP from …015, the second rounds DOWN from …025. The
        // reference value …020 is exactly representable (34-digit coefficient
        // …002 at exponent 1), so its own parse involves no rounding.
        var even = N("10000000000000000000000000000000020");
        Assert.Equal(even, EvalSingle("10000000000000000000000000000000015"));
        Assert.Equal(even, EvalSingle("10000000000000000000000000000000025"));
        Assert.NotEqual(N("1e34"), even);
    }

    [Fact]
    public void Literal_MaximumFinite_ParsesExactly()
        => Assert.Equal(Decimal128.MaxValue, EvalSingle("9999999999999999999999999999999999e6111"));

    [Fact]
    public void Literal_MinimumSubnormal_ParsesExactly()
        => Assert.Equal(Decimal128.Epsilon, EvalSingle("1e-6176"));

    [Fact]
    public void Literal_RoundingToJustBeyondMaximumFinite_IsRejected()
    {
        // 9.9999999999999999999999999999999995e6144 ties up to 1e6145 — past the
        // finite range — so the literal itself is a too-large diagnostic even
        // though its written digits are below MaxValue's first 34.
        var result = KatLangEngine.Run("9999999999999999999999999999999999.5e6111");
        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.Contains(failure.Errors, error => error.Message.Contains("Number literal is too large"));
    }

    [Fact]
    public void UnderflowedLiteral_NegatedByTheUnaryOperator_IsNegativeZero()
    {
        // Literals are unsigned; 1e-9999 quietly underflows to a positive zero
        // (carrying the minimum quantum, so it DISPLAYS as 0.000…0 — the same
        // quantum-faithful rendering as every other value) and the unary minus
        // then produces the observable signed zero.
        var negated = Assert.Single(Assert.IsType<RunResult.Success>(KatLangEngine.Run("-1e-9999")).Atoms);
        Assert.Equal(Decimal128.Zero, negated);
        Assert.True(Decimal128.IsNegative(negated));
        Assert.StartsWith("-0.0", Assert.IsType<RunResult.Success>(KatLangEngine.Run("-1e-9999")).ToDisplayString());

        var positive = Assert.Single(Assert.IsType<RunResult.Success>(KatLangEngine.Run("1e-9999")).Atoms);
        Assert.Equal(Decimal128.Zero, positive);
        Assert.False(Decimal128.IsNegative(positive));
    }

    // ── Structural comparer invariants over nested values ────────────────────

    [Fact]
    public void StructuralEqualityAndHash_TreatQuantumSignedZeroAndNaN_AsOneValue_Nested()
    {
        var left = new Result.SequenceValue([
            new Result.Atom(Decimal128.NaN),
            new Result.ListValue([new Result.Atom(Decimal128.NegativeZero), new Result.Atom(N("1.5"))]),
        ]);
        var right = new Result.SequenceValue([
            new Result.Atom(Decimal128.NaN),
            new Result.ListValue([new Result.Atom(Decimal128.Zero), new Result.Atom(N("1.50"))]),
        ]);

        Assert.True(Result.ValueComparer.Equals(left, right));
        Assert.Equal(Result.ValueComparer.GetHashCode(left), Result.ValueComparer.GetHashCode(right));

        // A genuinely different nested number still separates them.
        var different = new Result.SequenceValue([
            new Result.Atom(Decimal128.NaN),
            new Result.ListValue([new Result.Atom(Decimal128.Zero), new Result.Atom(N("2.5"))]),
        ]);
        Assert.False(Result.ValueComparer.Equals(left, different));
    }

    [Fact]
    public void Distinct_CollapsesNestedValuesDifferingOnlyByNaNIdentityAndZeroSign()
        => Assert.Equal(
            "[(NaN, -0)]",
            Assert.IsType<RunResult.Success>(
                KatLangEngine.Run("distinct(((Math.Sqrt(-1), -0), (Math.Sqrt(-1), 0)))")).ToDisplayString());

    // ── NaN literal patterns use structural numeric equality ─────────────────
    // Source syntax cannot spell a NaN literal, but the public AST can build
    // Pattern.LitInt(NaN); matching and match-equivalence must use the same
    // structural semantics as == / distinct / contains, or a NaN clause could
    // never match anything — including itself — and hashed clause-family
    // comparers would see an irreflexive equality.

    private static Algorithm.User ClauseBody(Decimal128 value)
        => new(Parent: null, Parameters: [], Opens: [], Properties: [], Output: [new Expr.Num(value)]);

    private static EvalResult<IReadOnlyList<Decimal128>> CallHostBuiltConditional(
        Algorithm.Conditional family, Decimal128 argument)
    {
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("F", family, IsPublic: true)],
            Output: [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(argument)]))]);

        return Evaluator.RunFlat(new Expr.AlgorithmExpr(root));
    }

    [Fact]
    public void LitIntNaNPattern_MatchesANaNAtom_AndFallsThroughForOtherValues()
    {
        var family = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(new Pattern.LitInt(Decimal128.NaN), ClauseBody(1)),
                new CondBranch(new Pattern.Bind("x"), ClauseBody(2)),
            ]);

        var nanCall = CallHostBuiltConditional(family, Decimal128.NaN);
        Assert.False(nanCall.IsError, $"NaN call failed: {(nanCall.IsError ? nanCall.Error : null)}");
        Assert.Equal(Decimal128.One, Assert.Single(nanCall.Value));

        var ordinaryCall = CallHostBuiltConditional(family, 5);
        Assert.False(ordinaryCall.IsError);
        Assert.Equal((Decimal128)2, Assert.Single(ordinaryCall.Value));
    }

    [Fact]
    public void LitIntNaNPattern_IsMatchEquivalentToItself_AndDuplicateClausesAreRejected()
    {
        Assert.True(new Pattern.LitInt(Decimal128.NaN).IsMatchEquivalent(new Pattern.LitInt(Decimal128.NaN)));

        var comparer = Pattern.CreateMatchEquivalenceComparer(null);
        Assert.True(comparer.Equals(new Pattern.LitInt(Decimal128.NaN), new Pattern.LitInt(Decimal128.NaN)));
        Assert.Equal(
            comparer.GetHashCode(new Pattern.LitInt(Decimal128.NaN)),
            comparer.GetHashCode(new Pattern.LitInt(Decimal128.NaN)));

        // Two NaN-literal clauses are match-equivalent duplicates, exactly like
        // two `F(0)` clauses — the reflexivity the comparer machinery assumes.
        var duplicated = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(new Pattern.LitInt(Decimal128.NaN), ClauseBody(1)),
                new CondBranch(new Pattern.LitInt(Decimal128.NaN), ClauseBody(2)),
            ]);

        var result = CallHostBuiltConditional(duplicated, Decimal128.NaN);
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        Assert.IsType<EvalError.DuplicateBranchPattern>(error);
    }

    [Fact]
    public void LitIntPatterns_IgnoreQuantumAndZeroSign_LikeStructuralEquality()
    {
        var comparer = Pattern.CreateMatchEquivalenceComparer(null);
        Assert.True(comparer.Equals(new Pattern.LitInt(N("1.5")), new Pattern.LitInt(N("1.50"))));
        Assert.Equal(
            comparer.GetHashCode(new Pattern.LitInt(N("1.5"))),
            comparer.GetHashCode(new Pattern.LitInt(N("1.50"))));
        Assert.True(comparer.Equals(new Pattern.LitInt(Decimal128.NegativeZero), new Pattern.LitInt(Decimal128.Zero)));

        // Runtime matching agrees: a -0 literal clause matches a +0 argument.
        var family = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(new Pattern.LitInt(Decimal128.NegativeZero), ClauseBody(1)),
                new CondBranch(new Pattern.Bind("x"), ClauseBody(2)),
            ]);

        var zeroCall = CallHostBuiltConditional(family, Decimal128.Zero);
        Assert.False(zeroCall.IsError);
        Assert.Equal(Decimal128.One, Assert.Single(zeroCall.Value));
    }
}
