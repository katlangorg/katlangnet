using System.Globalization;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Final audit (September 2026): the runtime's <c>Decimal128.Log</c> loses about
/// log10(1/|x − 1|) significant digits for arguments near 1 (cancellation in ln(1 + ε)),
/// and <c>Decimal128.Pow</c> inherits that loss for near-1 bases whose exponent takes the
/// delegated (fractional or beyond-<c>long</c>) path — <c>Math.Ln(1 + 1e-33)</c> kept five
/// correct digits and <c>(1 + 1e-33) ^ 9223372036854775808</c> was smaller than the same
/// base to the power <c>9223372036854775807</c>. The tutorial promises logarithm and power
/// results "correct to roughly the last digit or two", so the near-1 band now takes the
/// log1p reformulation (<see cref="Decimal128Numerics.NaturalLog"/>; the exponentiation
/// <c>Exp(y · ln x)</c> over it for the delegated power band), exactly like the endpoint
/// reformulation <c>Asin</c>/<c>Acos</c> already received.
///
/// <para>The logarithm expectations use an alternating series on BigInteger, independent
/// of the production LogP1 primitive. Power expectations use the generalized binomial
/// series directly, without logarithms or exponentials, at 90 decimal digits (never a
/// <see cref="Decimal128"/> transcendental function), rounded to the 34-digit lattice by
/// <see cref="Decimal128.Parse(string)"/>. Every assertion allows one unit in the last
/// place, the documented accuracy class of these members.</para>
/// </summary>
public class Decimal128NearOneLogarithmTests
{
    // ── Oracle ─────────────────────────────────────────────────────────────

    private const int Scale = 90;
    private static readonly BigInteger One = BigInteger.Pow(10, Scale);

    /// <summary>ln(1 + num/den) · 10^Scale, truncated, by the alternating power series.</summary>
    private static BigInteger LnOnePlusScaled(BigInteger num, BigInteger den)
    {
        var sum = BigInteger.Zero;
        var power = num * One / den; // ε · 10^Scale
        for (var n = 1; n < 2000; n++)
        {
            var term = power / n;
            if (term.IsZero) break;
            sum += (n % 2 == 1) ? term : -term;
            power = power * num / den;
        }
        return sum;
    }

    /// <summary>
    /// (1 + epsilonNumerator/epsilonDenominator)^(exponentNumerator/exponentDenominator)
    /// by the generalized binomial theorem. Used only for small exponent-times-epsilon,
    /// so terms shrink rapidly. This tests power without the production log/exp decomposition.
    /// </summary>
    private static BigInteger BinomialPowerScaled(
        BigInteger epsilonNumerator, BigInteger epsilonDenominator,
        BigInteger exponentNumerator, BigInteger exponentDenominator)
    {
        var sum = One;
        var term = One;
        for (var n = 1; n < 5000; n++)
        {
            term = term * (exponentNumerator - (n - 1) * exponentDenominator) * epsilonNumerator
                / (exponentDenominator * epsilonDenominator * n);
            if (term.IsZero) return sum;
            sum += term;
        }
        throw new InvalidOperationException("The binomial oracle did not converge in its supported test region.");
    }

    /// <summary>A scaled oracle value as the nearest Decimal128 (the parser rounds to 34 digits).</summary>
    private static Decimal128 ToDecimal128(BigInteger scaled)
    {
        var negative = scaled.Sign < 0;
        var digits = BigInteger.Abs(scaled).ToString(CultureInfo.InvariantCulture);
        // digits represent value · 10^Scale → place the decimal point Scale digits from the right.
        var text = digits.Length > Scale
            ? digits[..^Scale] + "." + digits[^Scale..]
            : "0." + new string('0', Scale - digits.Length) + digits;
        return Decimal128.Parse((negative ? "-" : "") + text, CultureInfo.InvariantCulture);
    }

    private static Decimal128 UlpOf(Decimal128 value)
    {
        var e33 = value.ToString("E33", CultureInfo.InvariantCulture);
        var exponent = int.Parse(e33[(e33.IndexOf('E') + 1)..], CultureInfo.InvariantCulture);
        return Decimal128.Parse("1E" + (exponent - 33).ToString(CultureInfo.InvariantCulture), CultureInfo.InvariantCulture);
    }

    private static void AssertWithinOneUlp(string source, Decimal128 expected)
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        var actual = Assert.Single(success.Atoms);
        var ulp = UlpOf(expected);
        Assert.True(
            Decimal128.Abs(actual - expected) <= ulp,
            $"{source}: expected {expected:E33} ± {ulp:E0}, got {actual:E33}");
    }

    // ── Logarithms near 1 ─────────────────────────────────────────────────

    [Theory]
    [InlineData("1e-33", 1, 33)]
    [InlineData("1e-20", 1, 20)]
    [InlineData("1e-10", 1, 10)]
    [InlineData("1e-3", 1, 3)]
    public void Ln_OnePlusEpsilon_IsCorrectToTheLastDigit(string epsilon, int num, int scale)
    {
        var oracle = ToDecimal128(LnOnePlusScaled(num, BigInteger.Pow(10, scale)));
        AssertWithinOneUlp($"Math.Ln(1 + {epsilon})", oracle);
        AssertWithinOneUlp($"ln(1 + {epsilon})", oracle);
    }

    [Fact]
    public void Ln_OneMinusEpsilon_IsCorrectToTheLastDigit()
    {
        var oracle = ToDecimal128(LnOnePlusScaled(-1, BigInteger.Pow(10, 33)));
        AssertWithinOneUlp("Math.Ln(1 - 1e-33)", oracle);
    }

    [Fact]
    public void Lg_And_Log_NearOne_AreCorrectToTheLastDigit()
    {
        var ln = LnOnePlusScaled(1, BigInteger.Pow(10, 33));
        // ln 10 = 3 ln 2 + ln 1.25, with ln 2 = -ln(1 - 1/2) and ln 1.25 = ln(1 + 1/4): every
        // series argument stays well inside the convergence disc.
        var ln10 = 3 * (-LnOnePlusScaled(-1, 2)) + LnOnePlusScaled(1, 4);
        var lg = ln * One / ln10;
        AssertWithinOneUlp("Math.Lg(1 + 1e-33)", ToDecimal128(lg));

        // log_(1+1e-33)(2) = ln 2 / ln(1 + 1e-33)
        var ln2 = -LnOnePlusScaled(-1, 2);
        AssertWithinOneUlp("Math.Log(2, 1 + 1e-33)", ToDecimal128(ln2 * One / ln));
    }

    [Theory]
    [InlineData("1.5")]
    [InlineData("0.5")]
    [InlineData("2")]
    [InlineData("10")]
    public void Ln_AwayFromOne_IsUnchanged(string argument)
    {
        // The reformulation is confined to the near-1 band; elsewhere the member is the
        // runtime's logarithm exactly as before.
        var x = Decimal128.Parse(argument, CultureInfo.InvariantCulture);
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run($"Math.Ln({argument})"));
        Assert.Equal(Decimal128.Log(x), Assert.Single(success.Atoms));
    }

    // ── Powers of near-1 bases on the delegated path ──────────────────────

    [Fact]
    public void Pow_NearOneBase_BeyondLongExponent_IsCorrectAndMonotone()
    {
        var oracle = ToDecimal128(BinomialPowerScaled(
            1, BigInteger.Pow(10, 33), BigInteger.Parse("9223372036854775808"), 1));
        AssertWithinOneUlp("1.000000000000000000000000000000001 ^ 9223372036854775808", oracle);

        // Monotone across the certified/delegated boundary: a base above 1 raised to a
        // larger exponent is never smaller.
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "B = 1.000000000000000000000000000000001\nB ^ 9223372036854775807 <= B ^ 9223372036854775808"));
        Assert.Equal("true", success.ToDisplayString());
    }

    [Fact]
    public void Pow_NearOneBase_FractionalExponent_IsCorrectToTheLastDigit()
    {
        // (1 + 1e-20) ^ 12345678901234567890.5
        var oracle = ToDecimal128(BinomialPowerScaled(
            1, BigInteger.Pow(10, 20), BigInteger.Parse("123456789012345678905"), 10));
        AssertWithinOneUlp("1.00000000000000000001 ^ 12345678901234567890.5", oracle);
    }

    [Theory]
    [InlineData("0.99", -1, -1)]
    [InlineData("1.01", 1, -1)]
    [InlineData("0.99", -1, 1)]
    [InlineData("1.01", 1, 1)]
    public void Pow_BandEdgesAndNegativeProducts_MatchTheBinomialOracle(string basis, int epsilon, int exponent)
    {
        var expected = ToDecimal128(BinomialPowerScaled(epsilon, 100, exponent, 2));
        AssertWithinOneUlp($"{basis} ^ ({exponent} / 2)", expected);
        AssertWithinOneUlp($"Math.Pow({basis}, {exponent} / 2)", expected);
        AssertWithinOneUlp($"pow({basis}, {exponent} / 2)", expected);
    }
    /// <summary>
    /// The exponent product is carried EXACTLY: a power is ill-conditioned in
    /// <c>t = exponent · ln(base)</c>, so rounding <c>t</c> to 34 digits lost about
    /// <c>log10 |t|</c> digits (the first version of the band composition was 123 ulp off
    /// for <c>0.99 ^ 12345.5</c> and two thousand ulp off for <c>(1 + 1e-15) ^ 2^63</c>,
    /// worse than the platform it replaced). The expectations here were computed by TWO
    /// independent arbitrary-precision oracles (exact binary powering times a square root at
    /// 80 and 90 digits, no logarithms) during the final hostile pass and are pinned as
    /// constants; the band edge must also be continuous with the platform's own value one
    /// ulp outside it.
    /// </summary>
    [Theory]
    [InlineData("0.99 ^ 12345.5", "1.301052747181870188981021925664986E-54")]
    [InlineData("1.01 ^ 12345.5", "2.236248352468809080535004248345207E+53")]
    [InlineData("0.999 ^ 1234567.5", "3.680318717377267562370741852310185E-537")]
    [InlineData("1.000000000000001 ^ 9223372036854775808", "4.566465141612069314961254152679748E+4005")]
    // One ulp outside the band the platform power is kept: the two spellings must agree.
    [InlineData("0.989999999999999999999999999999999 ^ 12345.5", "1.301052747181870188981021925648762E-54")]
    [InlineData("1.010000000000000000000000000000001 ^ 12345.5", "2.236248352468809080535004248372541E+53")]
    public void Pow_NearOneBase_LargeExponentProduct_IsCorrectToTheLastDigit(string source, string expected)
        => AssertWithinOneUlp(source, Decimal128.Parse(expected, CultureInfo.InvariantCulture));

    [Theory]
    [InlineData("10000000000.5")] // fractional: takes the new path
    [InlineData("1e40")] // integral beyond long: takes the new path
    public void Pow_NearOneBase_ProductPastTheExponentialRange_OverflowsAndUnderflowsLikeTheLimit(string exponent)
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            $"1.01 ^ {exponent}\n0.99 ^ {exponent}\n1.01 ^ -{exponent}"));
        Assert.Equal(
            [Decimal128.PositiveInfinity, Decimal128.Zero, Decimal128.Zero],
            success.Atoms);
    }
}
