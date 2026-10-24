using System.Globalization;
using System.Numerics;
using System.Runtime.InteropServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// Logarithms and delegated powers near 1. Final audit (September 2026): the preview-era
/// runtime's <c>Decimal128.Log</c> lost about log10(1/|x − 1|) significant digits for
/// arguments near 1 (cancellation in ln(1 + ε)), and <c>Decimal128.Pow</c> inherited that
/// loss for near-1 bases whose exponent takes the delegated (fractional or beyond-<c>long</c>)
/// path — <c>Math.Ln(1 + 1e-33)</c> kept five correct digits and
/// <c>(1 + 1e-33) ^ 9223372036854775808</c> was smaller than the same base to the power
/// <c>9223372036854775807</c>. KatLang then evaluated the logarithm family through a log1p
/// reformulation. Since DEC-RC2-1 (October 2026) <c>Ln</c>, <c>Lg</c> and <c>Log</c> are the
/// platform <see cref="Decimal128.Log(Decimal128)"/>, <see cref="Decimal128.Log10"/> and
/// <see cref="Decimal128.Log(Decimal128, Decimal128)"/> again: the .NET 11 RC2 accuracy
/// correction removed the cancellation, so the reformulation and its [0.5, 1.5] window are
/// gone. The delegated near-1 power keeps KatLang's exact-product path
/// (<see cref="Decimal128Numerics.NearOnePower"/>), which the RC2 audit still found more
/// accurate than the platform power.
///
/// <para>The logarithm expectations use an alternating series on BigInteger at 90 digits,
/// independent of every Decimal128 transcendental function, and are compared EXACTLY with the
/// result (never through a 34-digit rounding of the reference). Power expectations use the
/// generalized binomial series directly, without logarithms or exponentials, at 90 decimal
/// digits, rounded to the 34-digit lattice by <see cref="Decimal128.Parse(string)"/>. Delegation
/// tests compare the member with the platform call it names and are kept apart from these
/// accuracy tests.</para>
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

    // ── Logarithm oracle and exact distance ───────────────────────────────

    /// <summary>ln(x) · 10^Scale for an exact decimal 0 &lt; x &lt; 2, by the series of ln(1 + (x − 1)).</summary>
    private static BigInteger LnScaled(string exactDecimal)
    {
        var (coefficient, exponent) = ExactDecimal(exactDecimal);
        var denominator = BigInteger.Pow(10, -exponent);
        return LnOnePlusScaled(coefficient - denominator, denominator);
    }

    /// <summary>ln 10 = 3 ln 2 + ln 1.25: every series argument stays well inside the convergence disc.</summary>
    private static readonly BigInteger Ln10Scaled = 3 * (-LnOnePlusScaled(-1, 2)) + LnOnePlusScaled(1, 4);

    private static (BigInteger Coefficient, int Exponent) ExactDecimal(string text)
    {
        var parts = text.Split(['e', 'E']);
        var exponent = parts.Length == 2 ? int.Parse(parts[1], CultureInfo.InvariantCulture) : 0;
        var dot = parts[0].IndexOf('.');
        if (dot >= 0)
            exponent -= parts[0].Length - dot - 1;
        return (BigInteger.Parse(parts[0].Replace(".", ""), CultureInfo.InvariantCulture), Math.Min(exponent, 0));
    }

    private static Decimal128 EvalSingle(string source)
        => Assert.Single(Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).Atoms);

    /// <summary>
    /// |actual − reference| &lt;= maxUlps ulp, decided EXACTLY on integers: the reference is
    /// <c>referenceScaled · 10^-Scale</c> (more than 34 digits, never rounded to Decimal128),
    /// the ulp is <c>10^(floor(log10 |reference|) − 33)</c>, and the oracle's truncation (a few
    /// units of <c>10^-Scale</c>, far below the ulp of every case here) is charged against the
    /// tolerance.
    /// </summary>
    private static void AssertWithinUlps(string source, BigInteger referenceScaled, string maxUlps)
    {
        var actual = EvalSingle(source);
        Assert.True(Decimal128.IsFinite(actual), $"{source}: non-finite {actual}");
        var magnitude = Decimal128Numerics.CoefficientOf(Decimal128.Abs(actual), out var actualExponent);
        var actualCoefficient = Decimal128.IsNegative(actual) ? -magnitude : magnitude;
        var ulpExponent = BigInteger.Abs(referenceScaled).ToString(CultureInfo.InvariantCulture).Length - 34 - Scale;
        var (limit, limitExponent) = ExactDecimal(maxUlps);
        var common = Math.Min(Math.Min(actualExponent, -Scale), ulpExponent + limitExponent);
        var distance = BigInteger.Abs(actualCoefficient * BigInteger.Pow(10, actualExponent - common)
            - referenceScaled * BigInteger.Pow(10, -Scale - common));
        var oracleUncertainty = 1000 * BigInteger.Pow(10, -Scale - common);
        var allowed = limit * BigInteger.Pow(10, ulpExponent + limitExponent - common);
        Assert.True(distance + oracleUncertainty <= allowed,
            $"{source}: {actual} exceeds {maxUlps} ulp from {ToDecimal128(referenceScaled):E33}.");
    }

    private static void AssertSameBits(Decimal128 expected, Decimal128 actual, string label)
        => Assert.True(
            MemoryMarshal.AsBytes(MemoryMarshal.CreateReadOnlySpan(ref expected, 1))
                .SequenceEqual(MemoryMarshal.AsBytes(MemoryMarshal.CreateReadOnlySpan(ref actual, 1))),
            $"{label}: representation differs: expected {expected}, got {actual}.");

    private static string Bits(Decimal128 value)
        => Convert.ToHexString(MemoryMarshal.AsBytes(MemoryMarshal.CreateReadOnlySpan(ref value, 1)));

    // ── Logarithms near 1 and around the former [0.5, 1.5] window: accuracy ──

    [Theory]
    [InlineData("1e-33", 1, 33)]
    [InlineData("1e-20", 1, 20)]
    [InlineData("1e-10", 1, 10)]
    [InlineData("1e-3", 1, 3)]
    public void Ln_OnePlusEpsilon_IsCorrectToTheLastDigit(string epsilon, int num, int scale)
    {
        var oracle = LnOnePlusScaled(num, BigInteger.Pow(10, scale));
        AssertWithinUlps($"Math.Ln(1 + {epsilon})", oracle, "1");
        AssertWithinUlps($"ln(1 + {epsilon})", oracle, "1");
    }

    [Theory]
    [InlineData("1 - 1e-33", -1, 33)]
    [InlineData("1 - 1e-34", -1, 34)] // the nearest Decimal128 below 1
    [InlineData("1 - 1e-12", -1, 12)]
    public void Ln_OneMinusEpsilon_IsCorrectToTheLastDigit(string source, int num, int scale)
        => AssertWithinUlps($"Math.Ln({source})", LnOnePlusScaled(num, BigInteger.Pow(10, scale)), "1");

    /// <summary>
    /// The edges of the former log1p window and their Decimal128 neighbors (one ulp inside and
    /// outside), plus ordinary arguments the window never covered. The DEC-RC2-1 sweep of the
    /// pinned runtime measured at most 0.5 ulp (plus under 1e-11) for Ln and 0.5000059 ulp for Lg over 1,316
    /// arguments each; one ulp is the per-case check here, not a whole-domain bound.
    /// </summary>
    [Theory]
    [InlineData("0.5")]
    [InlineData("0.4999999999999999999999999999999999")]
    [InlineData("0.5000000000000000000000000000000001")]
    [InlineData("1.5")]
    [InlineData("1.499999999999999999999999999999999")]
    [InlineData("1.500000000000000000000000000000001")]
    [InlineData("0.99")]
    [InlineData("1.01")]
    [InlineData("0.999")]
    [InlineData("1.0000001")]
    [InlineData("0.75")]
    [InlineData("1.75")]
    [InlineData("0.25")]
    public void LnAndLg_AroundTheFormerWindow_MatchTheSeriesOracle(string argument)
    {
        var ln = LnScaled(argument);
        AssertWithinUlps($"Math.Ln({argument})", ln, "1");
        AssertWithinUlps($"lg({argument})", ln * One / Ln10Scaled, "1");
    }

    [Theory]
    [InlineData("10", 1)]
    [InlineData("1e100", 100)]
    [InlineData("0.001", -3)]
    [InlineData("1e-6176", -6176)]       // the smallest subnormal
    public void Ln_OfPowersOfTen_MatchesTheSeriesOracle(string argument, int power)
        => AssertWithinUlps($"Math.Ln({argument})", power * Ln10Scaled, "1");

    [Fact]
    public void Ln_OfTwoAndOfTheLargestFiniteValue_MatchTheSeriesOracle()
    {
        AssertWithinUlps("Math.Ln(2)", -LnOnePlusScaled(-1, 2), "1");
        // MaxValue = (1 - 1e-34) · 10^6145: ln = 6145 ln 10 + ln(1 - 1e-34).
        AssertWithinUlps(
            "Math.Ln(9.999999999999999999999999999999999e6144)",
            6145 * Ln10Scaled + LnOnePlusScaled(-1, BigInteger.Pow(10, 34)),
            "1");
    }

    [Fact]
    public void Lg_And_Log_NearOne_AreCorrectToTheLastDigit()
    {
        var ln = LnOnePlusScaled(1, BigInteger.Pow(10, 33));
        AssertWithinUlps("Math.Lg(1 + 1e-33)", ln * One / Ln10Scaled, "1");
        AssertWithinUlps("Math.Lg(1 - 1e-34)", LnOnePlusScaled(-1, BigInteger.Pow(10, 34)) * One / Ln10Scaled, "1");

        // log_(1+1e-33)(2) = ln 2 / ln(1 + 1e-33)
        var ln2 = -LnOnePlusScaled(-1, 2);
        AssertWithinUlps("Math.Log(2, 1 + 1e-33)", ln2 * One / ln, "1");
    }

    /// <summary>
    /// <c>Log(value, base)</c> with ordinary bases, bases just above and below 1, both arguments
    /// near 1, and tiny/large arguments. The removed ratio-of-logs composition reached 4.2 ulp on
    /// the DEC-RC2-1 sweep (and 5 ulp on <c>Log(1 + 1e-33, 1 - 1e-33)</c>); the platform stayed
    /// within 0.5000059 ulp on its 704 samples.
    /// </summary>
    [Theory]
    [InlineData("1 + 1e-33", "1 - 1e-33")]
    [InlineData("1 + 1e-33", "1 - 1e-34")]
    [InlineData("1 + 1e-20", "1 + 1e-10")]
    [InlineData("0.75", "0.5")]
    [InlineData("2", "1.0000001")]
    [InlineData("2", "0.999")]
    [InlineData("3", "2")]
    [InlineData("1.5", "10")]
    [InlineData("0.9999999999999999999999999999999999", "1.000000000000000000000000000000001")]
    public void Log_OfNearOneAndOrdinaryArguments_MatchesTheSeriesOracle(string value, string newBase)
    {
        static BigInteger Ln(string text) => text switch
        {
            "1 + 1e-33" => LnOnePlusScaled(1, BigInteger.Pow(10, 33)),
            "1 - 1e-33" => LnOnePlusScaled(-1, BigInteger.Pow(10, 33)),
            "1 - 1e-34" => LnOnePlusScaled(-1, BigInteger.Pow(10, 34)),
            "1 + 1e-20" => LnOnePlusScaled(1, BigInteger.Pow(10, 20)),
            "1 + 1e-10" => LnOnePlusScaled(1, BigInteger.Pow(10, 10)),
            "10" => Ln10Scaled,
            "2" => -LnOnePlusScaled(-1, 2),
            "3" => -LnOnePlusScaled(-1, 2) + LnScaled("1.5"),
            _ => LnScaled(text),
        };
        AssertWithinUlps($"Math.Log({value}, {newBase})", Ln(value) * One / Ln(newBase), "1");
        AssertWithinUlps($"log({value}, {newBase})", Ln(value) * One / Ln(newBase), "1");
    }

    [Fact]
    public void Log_OfTheSmallestSubnormalInBaseOneHalf_MatchesTheSeriesOracle()
        // log_0.5(1e-6176) = -6176 ln 10 / ln 0.5
        => AssertWithinUlps("Math.Log(1e-6176, 0.5)", -6176 * Ln10Scaled * One / LnOnePlusScaled(-1, 2), "1");

    /// <summary>
    /// The accepted DEC-RC2-1 tradeoff: at this argument the platform base-10 logarithm selects
    /// the other adjacent Decimal128 (0.5000059 ulp; a 200-digit mpmath reference agrees) where
    /// the removed composition was 0.4999941 ulp away. Pinned as a sample, so the tolerance is
    /// just above one half ulp — this documents the case, it does not license wider errors.
    /// </summary>
    [Fact]
    public void Lg_KnownTradeoffInput_StaysJustAboveHalfAnUlp()
    {
        var lg = LnScaled("0.99999999999265614061247") * One / Ln10Scaled;
        AssertWithinUlps("Math.Lg(0.99999999999265614061247)", lg, "0.51");
        AssertWithinUlps("Math.Log(0.99999999999265614061247, 10)", lg, "0.51");
    }

    // ── Exact answers, signed zeros, quanta and domain verdicts ───────────

    /// <summary>
    /// Exact known answers (base-10 logarithms of powers of ten, exact ratios). The value is
    /// mathematical; the representation is the coarsest exact quantum the shared Math-result
    /// canonicalization chooses, so <c>Lg(1e100)</c> is coefficient 1 at exponent 2.
    /// </summary>
    [Theory]
    [InlineData("Math.Lg(1000)", "3")]
    [InlineData("lg(1000.00)", "3")]
    [InlineData("Math.Lg(10)", "1")]
    [InlineData("Math.Lg(0.001)", "-3")]
    [InlineData("Math.Lg(1e100)", "1e2")]
    [InlineData("Math.Lg(1e-100)", "-1e2")]
    [InlineData("Math.Lg(1e-6176)", "-6176")]
    [InlineData("Math.Log(100, 10)", "2")]
    [InlineData("Math.Log(8, 2)", "3")]
    [InlineData("Math.Log(1024, 2)", "1e1")]
    [InlineData("Math.Log(0.5, 2)", "-1")]
    [InlineData("Math.Log(1e-6176, 10)", "-6176")]
    [InlineData("Math.Log(1e100, 1e-100)", "-1")]
    [InlineData("Math.Log(1e-6176, 1e-6176)", "1")]
    public void ExactLogarithms_AreExactAtTheCanonicalQuantum(string source, string expected)
        => AssertSameBits(Decimal128.Parse(expected, CultureInfo.InvariantCulture), EvalSingle(source), source);

    /// <summary>
    /// Zero results, signed zeros, infinities, NaN and degenerate bases: the platform's IEEE
    /// verdicts through the shared canonicalization (a zero becomes the exponent-0 zero of its
    /// sign). Pinned as the representation contract; no value here is an accuracy claim.
    /// </summary>
    [Theory]
    [InlineData("Math.Ln(1)", "0")]
    [InlineData("ln(1.0000)", "0")]
    [InlineData("Math.Lg(1.00)", "0")]
    [InlineData("Math.Ln(1 + 1e-34)", "0")]      // 1 + 1e-34 rounds to 1 before the call
    [InlineData("Math.Log(1, 10)", "0")]
    [InlineData("Math.Log(1.00, 2)", "0")]
    [InlineData("Math.Log(1, 0.5)", "-0")]       // +0 over a negative logarithm
    [InlineData("Math.Log(1, 1e-6176)", "-0")]
    [InlineData("Math.Log(1, 0)", "-0")]
    [InlineData("Math.Ln(0)", "-Infinity")]
    [InlineData("Math.Ln(-0)", "-Infinity")]
    [InlineData("Math.Lg(0.00)", "-Infinity")]
    [InlineData("Math.Log(0, 2)", "-Infinity")]
    [InlineData("Math.Log(-0, 2)", "-Infinity")]
    [InlineData("Math.Log(0, 0.5)", "Infinity")]
    [InlineData("Math.Ln(exp(20000))", "Infinity")]
    [InlineData("Math.Log(exp(20000), 0.5)", "-Infinity")]
    [InlineData("Math.Ln(-1)", "NaN")]
    [InlineData("Math.Lg(-exp(20000))", "NaN")]
    [InlineData("Math.Ln(sqrt(-1))", "NaN")]
    [InlineData("Math.Log(1, 1)", "NaN")]
    [InlineData("Math.Log(2, 1)", "NaN")]
    [InlineData("Math.Log(1.00, 1.00)", "NaN")]
    [InlineData("Math.Log(0, 0)", "NaN")]
    [InlineData("Math.Log(0, 1)", "NaN")]
    [InlineData("Math.Log(2, 0)", "NaN")]
    [InlineData("Math.Log(2, -0)", "NaN")]
    [InlineData("Math.Log(-2, 2)", "NaN")]
    [InlineData("Math.Log(2, -2)", "NaN")]
    [InlineData("Math.Log(exp(20000), exp(20000))", "NaN")]
    [InlineData("log(sqrt(-1), 2)", "NaN")]
    public void SpecialAndDegenerateArguments_KeepTheirIeeeVerdicts(string source, string expected)
    {
        var actual = EvalSingle(source);
        var reference = expected switch
        {
            "0" => Decimal128.Zero,
            "-0" => Decimal128.NegativeZero,
            "Infinity" => Decimal128.PositiveInfinity,
            "-Infinity" => Decimal128.NegativeInfinity,
            _ => Decimal128.NaN,
        };
        if (Decimal128.IsNaN(reference))
            Assert.True(Decimal128.IsNaN(actual), $"{source}: expected NaN, got {actual}");
        else
            AssertSameBits(reference, actual, source);
    }

    // ── Delegation: the members ARE the platform calls ─────────────────────

    private static readonly RandomSource UnusedRandomness = RandomSourceFactory.Create(0, () => 0);

    private static Decimal128 ApplyMath(string member, params Decimal128[] args)
    {
        var result = Evaluator.ApplyMathNative(member, args, UnusedRandomness);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        return Assert.IsType<Result.Atom>(result.Value).Value;
    }

    /// <summary>
    /// Delegation/parity, not accuracy: over the former window's edges and neighbors, ordinary,
    /// subnormal and extreme arguments, alternate quanta, signed zeros, negative values,
    /// infinities and NaN, <c>Ln</c>/<c>Lg</c>/<c>Log</c> return exactly the platform function's
    /// result after the ONE Math-result canonicalization.
    /// </summary>
    [Fact]
    public void Logarithms_AreThePlatformFunctionsOverEveryInputClass()
    {
        static Decimal128 D(string text) => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);
        var arguments = new[]
        {
            D("1"), D("1.00"), D("0.5"), D("0.50"), D("1.5"), D("0.4999999999999999999999999999999999"),
            D("0.5000000000000000000000000000000001"), D("1.499999999999999999999999999999999"),
            D("1.500000000000000000000000000000001"), Decimal128.BitDecrement(Decimal128.One),
            Decimal128.BitIncrement(Decimal128.One), D("0.99"), D("1.01"), D("0.99999999999265614061247"),
            D("2"), D("10"), D("1000.00"), D("1e100"), D("1e-100"), Decimal128.Epsilon, Decimal128.MaxValue,
            D("0"), D("-0"), D("0e-50"), D("-1"), Decimal128.PositiveInfinity, Decimal128.NegativeInfinity, Decimal128.NaN,
        };
        foreach (var x in arguments)
        {
            AssertSameBits(Evaluator.CanonicalizeMathResult(Decimal128.Log(x)), ApplyMath("Ln", x), $"Ln({x})");
            AssertSameBits(Evaluator.CanonicalizeMathResult(Decimal128.Log10(x)), ApplyMath("Lg", x), $"Lg({x})");
            foreach (var b in arguments)
                AssertSameBits(Evaluator.CanonicalizeMathResult(Decimal128.Log(x, b)), ApplyMath("Log", x, b), $"Log({x}, {b})");
        }
    }

    // ── Changed results: display, `.string` and interpolation ─────────────

    /// <summary>
    /// Two results that changed in DEC-RC2-1, each now the correctly rounded value (the series
    /// oracle above and a 200-digit reference agree). <c>lg(0.5)</c> is
    /// -0.30102999566398119521373889472449302677…, so its nearest Decimal128 ends in a zero that
    /// the shared canonicalization drops: 33 digits are shown, through the unchanged renderer.
    /// </summary>
    [Theory]
    [InlineData("Math.Lg(0.5)", "-0.301029995663981195213738894724493")]
    [InlineData("Math.Acos(0.99999)", "0.004472139681787927172339666304852682")]
    public void ChangedResults_ReachDisplayStringAndInterpolationUnchangedByTheRenderer(string source, string text)
    {
        // Canonical coefficient/exponent are observable independently of display:
        // Lg(0.5)'s trailing zero now reduces its quantum from 1e-34 to 1e-33.
        AssertSameBits(Decimal128.Parse(text, CultureInfo.InvariantCulture), EvalSingle(source), source);
        Assert.Equal(text, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
        // Text results compared as KatLang strings (display does not quote them).
        Assert.Equal("true", Assert.IsType<RunResult.Success>(
            KatLangEngine.Run($"X = {source}\nX.string == '{text}'")).ToDisplayString());
        Assert.Equal("true", Assert.IsType<RunResult.Success>(
            KatLangEngine.Run($"X = {source}\n\"<{{X}}>\" == '<{text}>'")).ToDisplayString());
    }

    [Fact]
    public async Task NearOneLogarithms_AgreeAcrossFlatCountedPlannedAndAsyncRoutes()
    {
        // The receiver properties read the input lists in VALUE position, so the async
        // zero-argument property cache seam is exercised.
        const string source =
            "LnInputs = [1 + 1e-33, 1 - 1e-34, 0.5, 1.5, 0]\n"
            + "LgInputs = [0.99999999999265614061247, 0.5, 1000, 1 + 1e-33, -1]\n"
            + "A = LnInputs\nB = LgInputs\n"
            + "L(x) = log(x, 1 - 1e-33)\n"
            + "A.map(ln)\nB.map(Math.Lg)\nB.map(L)\n"
            + "Step(x, a, b, c) = x + 0, ln(x), Math.Lg(x), log(x, 1 - 1e-33)\n"
            + "Step(0.99999, 0, 0, 0).repeat(2)";
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var flat = Evaluator.RunFlat(program);
        Assert.True(flat.IsOk, flat.IsError ? flat.Error.ToString() : null);
        Assert.Equal(19, flat.Value.Count);

        var counted = Evaluator.RunCounted(program);
        Assert.True(counted.IsOk);
        var countedAtoms = counted.Value.Value.ToHostAtoms();

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var twin = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(program, cache));
        Assert.True(cache.AsyncAccesses > 0);
        Assert.Equal(0, cache.SyncAccesses);
        Assert.True(twin.IsOk);
        var twinAtoms = twin.Value.Value.ToHostAtoms();

        var generic = EvaluatorTestSupport.EvalFull(source,
            enableLoopOptimization: false, enableSequencePipelineOptimization: false);
        var diagnostics = new LoopOptimizationDiagnostics();
        var optimized = Evaluator.Run(program, new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true, loopDiagnostics: diagnostics,
            enableSequencePipelineOptimization: false, sequenceDiagnostics: null);
        Assert.True(generic.IsOk);
        Assert.True(optimized.IsOk);
        // Math calls use the shared fallback inside an actually optimized loop.
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.Equal(2, diagnostics.LoopIterations);
        Assert.True(diagnostics.PlannedExpressionHits > 0);
        Assert.True(diagnostics.PlannedExpressionFallbacks > 0);
        var genericAtoms = generic.Value.ToHostAtoms();
        var optimizedAtoms = optimized.Value.ToHostAtoms();
        Assert.Equal(flat.Value.Count, countedAtoms.Count);
        Assert.Equal(flat.Value.Count, twinAtoms.Count);
        Assert.Equal(flat.Value.Count, genericAtoms.Count);
        Assert.Equal(flat.Value.Count, optimizedAtoms.Count);
        for (var i = 0; i < flat.Value.Count; i++)
        {
            AssertSameBits(flat.Value[i], countedAtoms[i], $"counted[{i}]");
            AssertSameBits(flat.Value[i], twinAtoms[i], $"async[{i}]");
            AssertSameBits(flat.Value[i], genericAtoms[i], $"generic[{i}]");
            AssertSameBits(flat.Value[i], optimizedAtoms[i], $"planned[{i}]");
        }

        // Every route reaches the accurate near-1 result.
        Assert.Equal(EvalSingle("Math.Ln(1 + 1e-33)"), flat.Value[0]);
        Assert.Equal(EvalSingle("Math.Lg(0.99999999999265614061247)"), flat.Value[5]);
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

    /// <summary>
    /// DEC-RC2-1 changed the logarithm inside <see cref="Decimal128Numerics.NearOnePower"/>'s
    /// out-of-range fallback (|exponent · ln base| past 20,000: <c>Exp(exponent · Log(base))</c>,
    /// formerly over the removed log1p helper). These bits were captured from the pre-change
    /// implementation (commit 0def68eb) and are the IEEE limits of the true values: infinity, the
    /// exponent-0 zero, and — through <c>Evaluator.DelegatedPower</c>'s parity sign — their
    /// negatives for an odd power of a negative base. Both sides of the 20,000 cutoff appear
    /// (<c>1.01 ^ 2009900.5</c> is the in-range fixed-point path, <c>1.01 ^ 2010100.5</c> the
    /// fallback), as do the tiniest band bases, the largest finite exponents, and a product just
    /// inside the range whose result is the smallest subnormal.
    /// </summary>
    [Theory]
    [InlineData("1.01 ^ 2010100.5", "00000000000000000000000000000078")]
    [InlineData("1.01 ^ 2009900.5", "00000000000000000000000000000078")]
    [InlineData("0.99 ^ 2010100.5", "00000000000000000000000000004030")]
    [InlineData("0.99 ^ 1990100.5", "00000000000000000000000000004030")]
    [InlineData("1.01 ^ -2010100.5", "00000000000000000000000000004030")]
    [InlineData("1.01 ^ -2009900.5", "00000000000000000000000000004030")]
    [InlineData("1.000000000000000000000000000000001 ^ 1e40", "00000000000000000000000000000078")]
    [InlineData("0.9999999999999999999999999999999999 ^ 1e40", "00000000000000000000000000004030")]
    [InlineData("1.000000000000000000000000000000001 ^ -1e40", "00000000000000000000000000004030")]
    [InlineData("1.000000000000000000000000000000001 ^ 1e6144", "00000000000000000000000000000078")]
    [InlineData("1.01 ^ 9.999999999999999999999999999999999e6144", "00000000000000000000000000000078")]
    [InlineData("0.99 ^ 9.999999999999999999999999999999999e6144", "00000000000000000000000000004030")]
    [InlineData("1.01 ^ -9.999999999999999999999999999999999e6144", "00000000000000000000000000004030")]
    [InlineData("0.9999999999999999999999999999999999 ^ 9.999999999999999999999999999999999e6144", "00000000000000000000000000004030")]
    [InlineData("(-1.01) ^ 10000000000000000000001", "000000000000000000000000000000F8")]
    [InlineData("(-0.99) ^ 10000000000000000000001", "000000000000000000000000000040B0")]
    [InlineData("(-1.01) ^ 10000000000000000000002", "00000000000000000000000000000078")]
    [InlineData("(-0.99) ^ 10000000000000000000002", "00000000000000000000000000004030")]
    [InlineData("(-1.01) ^ -10000000000000000000001", "000000000000000000000000000040B0")]
    [InlineData("(-0.99) ^ -10000000000000000000001", "000000000000000000000000000000F8")]
    [InlineData("0.99 ^ 1415000.5", "01000000000000000000000000000000")] // in range: the smallest subnormal
    [InlineData("0.99 ^ 1416000.5", "00000000000000000000000000004030")]
    public void Pow_NearOneBase_OutOfRangeFallback_KeepsItsLimitsSignsAndRepresentation(string source, string bits)
        => Assert.Equal(bits, Bits(EvalSingle(source)));

    // ── Negative bases and overflowing reciprocals (numeric audit #6) ──────

    /// <summary>
    /// The near-one band is a band of base MAGNITUDES (numeric audit #6, September 2026). It
    /// once admitted only positive bases, so a negative base near -1 with an integral
    /// exponent beyond <c>long</c> took the runtime power and its near-1 cancellation:
    /// <c>(-0.9999999999999999999999999999999999) ^ 1e34</c> kept four correct digits while
    /// its positive twin kept all 34. The law: for an integral exponent, <c>(-b) ^ n</c> is
    /// exactly <c>(-1) ^ n · b ^ n</c> — value, quantum, and zero sign — on both sides of
    /// every routing boundary (the certified path inside <c>long</c>, the delegated path
    /// beyond it, and a negative exponent whose positive power overflows), in and outside
    /// the band.
    /// </summary>
    [Theory]
    [InlineData("0.9999999999999999999999999999999999", "10000000000000000000000000000000000")]
    [InlineData("1.0000000000000000001", "9223372036854775807")] // certified
    [InlineData("1.0000000000000000001", "9223372036854775808")] // just beyond long, even
    [InlineData("1.0000000000000000001", "10000000000000000001")] // beyond long, odd
    [InlineData("1.0000000000000000001", "-9223372036854775809")] // negative, beyond long, odd
    [InlineData("1.000000000000000000000000000000001", "9223372036854775808")]
    [InlineData("0.99", "123456789012345678901")]
    [InlineData("1.01", "-123456789012345678902")]
    [InlineData("1.000000000000002", "-7080000000000000001")] // the positive power overflows
    [InlineData("1.1", "10000000000000000001")] // outside the band
    [InlineData("0.5", "10000000000000000001")]
    public void IntegralPowerOfANegativeBase_IsTheSignedPowerOfItsMagnitude(string magnitude, string exponent)
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            $"B = {magnitude}\nN = {exponent}\n(-B) ^ N\nB ^ N"));
        var ofNegativeBase = success.Atoms[0];
        var ofMagnitude = success.Atoms[1];
        var expected = Decimal128.IsOddInteger(Decimal128.Parse(exponent, CultureInfo.InvariantCulture))
            ? -ofMagnitude
            : ofMagnitude;
        Assert.Equal(expected, ofNegativeBase);
        Assert.True(Decimal128.HaveSameQuantum(expected, ofNegativeBase), $"{ofNegativeBase} vs {expected}");
        Assert.Equal(Decimal128.IsNegative(expected), Decimal128.IsNegative(ofNegativeBase));
    }

    [Fact]
    public void Pow_NegativeNearOneBase_BeyondLongExponent_IsCorrectToTheLastDigit()
    {
        // (1 - 1e-34) ^ 1e34 = e^(-1 - 5e-35 - …), an even power.
        var even = ToDecimal128(BinomialPowerScaled(-1, BigInteger.Pow(10, 34), BigInteger.Pow(10, 34), 1));
        AssertWithinOneUlp("(-0.9999999999999999999999999999999999) ^ 1e34", even);

        // (1 + 1e-19) ^ (1e19 + 1), an odd power: the magnitude, negated.
        var odd = ToDecimal128(BinomialPowerScaled(1, BigInteger.Pow(10, 19), BigInteger.Pow(10, 19) + 1, 1));
        AssertWithinOneUlp("(-1.0000000000000000001) ^ 10000000000000000001", -odd);
        AssertWithinOneUlp("Math.Pow(-1.0000000000000000001, 10000000000000000001)", -odd);
        AssertWithinOneUlp("pow(-1.0000000000000000001, 10000000000000000001)", -odd);
    }

    /// <summary>
    /// A negative integral exponent whose POSITIVE power overflows keeps its pre-B4
    /// delegation (the reciprocal can be a representable subnormal); a near-one base there
    /// now takes the near-one power, where the runtime power lost seven of the result's 27
    /// digits for <c>1.000000000000002 ^ -7080000000000000000</c>. The oracle is the
    /// certified exact integer power — an independent algorithm (exact BigInteger powering
    /// with a certified, once-rounded reciprocal) that the evaluator does not use for this
    /// shape — compared at the subnormal quantum.
    /// </summary>
    [Theory]
    [InlineData("1.000000000000002", -7080000000000000000L)]
    [InlineData("1.000000000000002", -7080000000000000001L)]
    [InlineData("-1.000000000000002", -7080000000000000001L)]
    [InlineData("1.00000000001", -1415000000000000L)]
    [InlineData("1.0000000001", -141550000000000L)]
    public void Pow_NearOneBase_OverflowingPositivePower_MatchesTheCertifiedIntegerPower(string basis, long exponent)
    {
        var b = Decimal128.Parse(basis, CultureInfo.InvariantCulture);
        Assert.True(Decimal128Numerics.TryIntegerPower(b, exponent, out var certified));
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run($"({basis}) ^ {exponent}"));
        var actual = Assert.Single(success.Atoms);
        var ulp = Decimal128.Max(UlpOf(certified), Decimal128.Epsilon);
        Assert.True(
            Decimal128.Abs(actual - certified) <= ulp,
            $"({basis}) ^ {exponent}: expected {certified:E33} ± {ulp:E0}, got {actual:E33}");
    }

    [Theory]
    // An exponent one unit away from an integer is fractional: never rounded into parity.
    [InlineData("(-2) ^ 2.000000000000000000000000000000001")]
    [InlineData("(-2) ^ 2.999999999999999999999999999999999")]
    [InlineData("(-0.995) ^ 12345.5")]
    [InlineData("(-1.0000000000000000001) ^ 10000000000000000000.5")]
    [InlineData("Math.Pow(-1.005, 0.5)")]
    public void FractionalPowerOfANegativeBase_IsNaN_EvenBesideAnInteger(string source)
        => Assert.Equal("NaN", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());

    [Fact]
    public async Task NegativeNearOneBasePower_AgreesAcrossExecutionStrategies()
    {
        // A loop step raising its own (negative) state takes the planned numeric arm.
        const string source = "Step(x) = x ^ 10000000000000000001\nrepeat(Step(-1.0000000000000000001), 1)";
        var generic = EvaluatorTestSupport.Eval(source, enableLoopOptimization: false);
        var planned = EvaluatorTestSupport.Eval(source, enableLoopOptimization: true);
        Assert.False(generic.IsError);
        Assert.False(planned.IsError);
        Assert.Equal(generic.Value, planned.Value);

        var magnitude = Assert.Single(Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("1.0000000000000000001 ^ 10000000000000000001")).Atoms);
        Assert.Equal(-magnitude, Assert.Single(generic.Value));

        var asynchronous = await NumericSemanticLawReviewTests.RunSuspending(source);
        Assert.Equal(-magnitude, Assert.Single(asynchronous.Atoms));
    }
}
