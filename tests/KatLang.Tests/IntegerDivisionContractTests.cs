using System.Globalization;
using System.Numerics;
using KatLang.Rendering;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// G-3 (September 2026): <c>div</c> is the EXACT quotient rounded toward zero to a
/// Decimal128 integer (<see cref="Decimal128Numerics.IntegerDivide"/>), never
/// <c>Truncate(x / y)</c>, whose quotient is rounded to 34 significant digits BEFORE
/// the truncation and can therefore land on the wrong neighboring integer.
///
/// <para><b>The contract.</b> Let <c>q = x / y</c> be the exact quotient and <c>t</c>
/// its truncation toward zero. Whenever <c>t</c> is representable — throughout the
/// exact consecutive-integer domain <c>|t| &lt;= 10^34</c> and for every representable
/// sparse integer beyond it — <c>x div y</c> IS <c>t</c>, and with the exact finite
/// remainder <c>r = x mod y</c> the truncated-division identity
/// mathematical identity holds. Its Decimal128 recomposition additionally requires
/// exact intermediate arithmetic. A truncated quotient that needs
/// more than 34 significant digits is rounded TOWARD ZERO to 34 digits (its leading
/// digits), so finite <c>div</c> results stay truncations; special values keep the
/// operator's IEEE contract; a zero-valued divisor stays the specified error.</para>
///
/// <para><b>What is pinned here.</b> The two reproductions from the review (a 34-digit
/// quotient that rounded up to <c>3e33</c>, and the small quotient
/// <c>(13 * 3e32 - 1) div 3e32</c> that rounded up to <c>13</c>), the mirror-image case
/// on the OTHER side of the integer boundary (<c>12 * 3e32 + 1</c>, where the rounding
/// lands DOWN on the integer and no adjustment may happen), every sign combination, exact
/// divisibility, ordinary small operands, digit extraction at the consecutive-integer
/// boundary, sparse quotients beyond it, a deterministic matrix of operands constructed
/// around Decimal128 rounding boundaries and checked against an independent
/// <see cref="BigInteger"/> oracle (helper, evaluator, and planned loop alike), the
/// planned-loop numeric arm observed to actually execute, and sync/counted/async
/// (genuinely suspending) parity. Corpus-wide parity for the canonical cases lives in
/// <c>CorpusExecutionEquivalenceTests</c> / <c>AsyncTwinDifferentialTests</c>.</para>
/// </summary>
public class IntegerDivisionContractTests
{
    private static readonly (int Dividend, int Divisor)[] SignCombinations = [(1, 1), (-1, 1), (1, -1), (-1, -1)];
    private static readonly BigInteger OverflowThreshold = (2 * BigInteger.Pow(10, 34) - 1) * 5 * BigInteger.Pow(10, 6110);

    private static Decimal128 N(string text)
        => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);

    private static string Display(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString();

    private static string Format(Decimal128 value) => ValueTextRenderer.FormatNumberInvariant(value);

    /// <summary>The Decimal128 <c>coefficient × 10^exponent</c>, exactly (the coefficient fits 34 digits).</summary>
    private static Decimal128 Scaled(BigInteger coefficient, int exponent)
        => Decimal128.ScaleB((Decimal128)(Int128)coefficient, exponent);

    /// <summary>KatLang source spelling of an exact <c>coefficient × 10^exponent</c> operand.</summary>
    private static string Literal(BigInteger coefficient, int exponent)
        => exponent == 0
            ? coefficient.ToString(CultureInfo.InvariantCulture)
            : $"{coefficient.ToString(CultureInfo.InvariantCulture)}e{exponent.ToString(CultureInfo.InvariantCulture)}";

    // ── The independent oracle ─────────────────────────────────────────────

    /// <summary>
    /// The exact contract on <see cref="BigInteger"/>s: the truncated quotient of the two
    /// exact rationals, rounded toward zero to a Decimal128 integer, and the exact
    /// remainder (which is always representable: it is a multiple of the finer quantum
    /// and smaller than the divisor in magnitude).
    /// </summary>
    private static (Decimal128 Quotient, Decimal128 Remainder) ExactContract(
        BigInteger dividendCoefficient, int dividendExponent, BigInteger divisorCoefficient, int divisorExponent)
    {
        var commonExponent = Math.Min(dividendExponent, divisorExponent);
        var numerator = dividendCoefficient * BigInteger.Pow(10, dividendExponent - commonExponent);
        var denominator = divisorCoefficient * BigInteger.Pow(10, divisorExponent - commonExponent);
        // BigInteger division truncates toward zero and its remainder takes the
        // dividend's sign — exactly KatLang's `div`/`mod` convention. A zero result
        // keeps the IEEE sign too: the quotient's sign for `div` (`-7 div 8` is `-0`)
        // and the dividend's sign for `mod` (`-6 mod 3` is `-0`).
        var truncated = BigInteger.DivRem(numerator, denominator, out var remainder);
        var quotientNegative = (dividendCoefficient.Sign < 0) != (divisorCoefficient.Sign < 0);
        // (A zero remainder keeps the operands' finer quantum, `-0.00000` at 10^-5,
        // exactly as the IEEE remainder does; negating the scaled zero preserves it.)
        var remainderValue = Scaled(remainder, commonExponent);
        if (remainder.IsZero && dividendCoefficient.Sign < 0)
            remainderValue = -remainderValue;
        return (TowardZeroDecimal128(truncated, quotientNegative), remainderValue);
    }

    /// <summary>
    /// An integer rounded toward zero to a Decimal128: itself when it has at most 34
    /// significant digits, otherwise its leading 34 digits (the largest-magnitude
    /// Decimal128 integer not exceeding it). Scaling past the finite range yields the
    /// signed infinity every arithmetic overflow yields; a zero carries the sign of the
    /// quotient it truncates.
    /// </summary>
    private static Decimal128 TowardZeroDecimal128(BigInteger integer, bool negativeZero)
    {
        var magnitude = BigInteger.Abs(integer);
        if (magnitude.IsZero)
            return negativeZero ? Decimal128.NegativeZero : Decimal128.Zero;

        // This oracle deliberately uses neither production digit counts nor its
        // bounded coefficient algorithm. Build the full integer and inspect its text.
        var digits = magnitude.ToString(CultureInfo.InvariantCulture).Length;
        // G-3 retains ordinary IEEE overflow, including the half-ulp threshold
        // between MaxValue and 1e6145 (the tie rounds up to infinity). Merely dropping
        // digits and scaling would incorrectly predict MaxValue in this narrow band.
        if (magnitude >= OverflowThreshold)
            return integer.Sign < 0 ? Decimal128.NegativeInfinity : Decimal128.PositiveInfinity;
        Decimal128 value;
        if (digits <= 34)
        {
            value = (Decimal128)(Int128)magnitude;
        }
        else
        {
            var dropped = digits - 34;
            value = Scaled(magnitude / BigInteger.Pow(10, dropped), dropped);
        }

        return integer.Sign < 0 ? -value : value;
    }

    // ── The deterministic boundary matrix ──────────────────────────────────

    /// <summary>
    /// Operand pairs constructed AROUND Decimal128 rounding boundaries. For a target
    /// quotient <c>n</c> with <c>d</c> digits, a divisor coefficient <c>cy</c> in the band
    /// <c>2·10^(34-d) &lt; cy &lt; 10^(35-d)</c> makes <c>(n·cy ∓ 1) / cy = n ∓ 1/cy</c>
    /// closer to <c>n</c> than half a unit in the 34th digit, so the IEEE quotient LANDS on
    /// the integer <c>n</c> from below (a crossing: the truncated quotient is <c>n - 1</c>)
    /// or from above (no crossing: it is <c>n</c>). Offsets of two units, an exact
    /// multiple, and a divisor below the band (where the quotient stays non-integral)
    /// surround every landing, and the operands are spelled at several quanta, including
    /// mixed ones and the subnormal floor. The second family crosses the
    /// consecutive-integer boundary: sparse exact quotients, an exact 35-digit quotient
    /// ending in 5 (a round-to-nearest tie that must still round TOWARD ZERO), quotients
    /// whose leading 34 digits must be kept, the range top, and an overflow.
    /// </summary>
    private static IEnumerable<(BigInteger Cx, int Ex, BigInteger Cy, int Ey, string Why)> BoundaryMatrix()
    {
        var limit = BigInteger.Pow(10, 34);
        int[] digitCounts = [1, 2, 3, 5, 9, 17, 25, 30, 33, 34];
        (int Ex, int Ey)[] quanta = [(0, 0), (-5, -5), (7, 0), (0, 3), (-6176, -6176)];

        foreach (var d in digitCounts)
        {
            var low = BigInteger.Pow(10, d - 1);
            var high = BigInteger.Pow(10, d) - 1;
            var targets = d == 1
                ? new BigInteger[] { 1, 7, 9 }
                : [low, low + 2, high, PiDigits(d)];
            var unit = BigInteger.Pow(10, 34 - d);
            var divisors = new List<BigInteger> { 3 * unit, 3 * unit + 1, 7 * unit, 2 * unit + 1, 10 * unit - 1 };
            if (unit >= 10)
                divisors.Add(3 * unit / 10); // below the band: the rounded quotient stays non-integral

            foreach (var n in targets)
            {
                foreach (var cy in divisors)
                {
                    foreach (var offset in new[] { -2, -1, 0, 1, 2 })
                    {
                        var cx = n * cy + offset;
                        if (cx < 1 || cx >= limit)
                            continue;

                        foreach (var (ex, ey) in quanta)
                            yield return (cx, ex, cy, ey, $"n={n} cy={cy} offset={offset}");
                    }
                }
            }
        }

        var nines = limit - 1;
        var pi = PiDigits(34);
        (BigInteger Cx, int Ex, BigInteger Cy, int Ey, string Why)[] beyond =
        [
            (1, 40, 1, 6, "1e40 / 1e6 = 1e34 exactly: the inclusive consecutive-integer boundary"),
            (1, 40, 1, 5, "1e40 / 1e5 = 1e35 exactly: a sparse quotient beyond the boundary"),
            (1, 34, 1, 0, "the inclusive boundary / 1"),
            (limit / 10 + 1, 1, 1, 0, "the first representable integer above 1e34"),
            (1, 40, 3, 0, "1e40 / 3: 40 threes, kept to 34"),
            (1, 40, 7, 0, "1e40 / 7: leading digits …428 must not round up to …429"),
            (2, 40, 3, 0, "2e40 / 3: 40 sixes, truncated (never …667)"),
            (1, 35, 7, 0, "1e35 / 7: the 35-digit …4285 keeps …428"),
            (1, 34, 7, 0, "1e34 / 7: the quotient is in-domain, and r * 7 rounds back to 1e34 (a non-fused product test is fooled)"),
            (nines, 1, 6, 0, "an exact 35-digit integer quotient ending in 5: toward zero, not ties-to-even"),
            (nines, 1, 7, 0, "35-digit inexact quotient"),
            (nines, 1, 3, 0, "exact sparse quotient 3333…3e1"),
            (nines, 10, 7, 0, "44-digit truncated quotient keeps its leading 34 digits"),
            (nines, 6111, 1, 0, "MaxValue / 1 is exact"),
            (nines, 6111, 3, 0, "MaxValue / 3: 6145-digit exact sparse quotient"),
            (1, 6144, 7, 0, "1e6144 / 7"),
            (nines, 6111, limit / 10 + 1, -33, "just below MaxValue: finite toward-zero result"),
            (nines, 6111, nines, -34, "exact quotient 1e6145: infinity is retained"),
            (1, -6176, nines, 6111, "minimum subnormal / maximum finite: underflowed zero"),
            (nines, 6111, 1, -6176, "maximum finite / minimum subnormal: largest exponent gap"),
            (pi, 20, pi + 3, -20, "quotient just below 1e40"),
            (pi, 0, 1, -30, "sparse dividend spread by a tiny divisor"),
            (5, 0, 1, -6176, "5 / 1e-6176 overflows to Infinity like every arithmetic overflow"),
            (7, -6176, 2, -6176, "subnormal operands, non-integral quotient"),
            (7, -6176, 7, -6176, "subnormal operands, exact quotient 1"),
        ];
        foreach (var row in beyond)
            yield return row;
    }

    /// <summary>The first <paramref name="digits"/> digits of π as an integer (a fixed, non-round target).</summary>
    private static BigInteger PiDigits(int digits)
        => BigInteger.Parse("3141592653589793238462643383279502884197"[..digits], CultureInfo.InvariantCulture);

    [Fact]
    public void BoundaryMatrix_HelperAndRemainder_MatchTheExactContract()
    {
        var failures = new List<string>();
        var checkedRows = 0;
        var landings = 0;
        foreach (var (cx, ex, cy, ey, why) in BoundaryMatrix())
        {
            foreach (var (sx, sy) in SignCombinations)
            {
                var x = Scaled(sx * cx, ex);
                var y = Scaled(sy * cy, ey);
                Assert.True(Decimal128.IsFinite(x) && Decimal128.IsFinite(y), $"operands must be representable: {why}");

                var (expectedQuotient, expectedRemainder) = ExactContract(sx * cx, ex, sy * cy, ey);
                var quotient = Decimal128Numerics.IntegerDivide(x, y);
                var remainder = x % y;
                if (Decimal128.IsInteger(x / y))
                    landings++;

                var integralQuantum = !Decimal128.IsFinite(quotient) || Decimal128.ILogB(Decimal128.GetQuantum(quotient)) >= 0;
                if (quotient != expectedQuotient || remainder != expectedRemainder || !integralQuantum
                    || Decimal128.IsNegative(quotient) != Decimal128.IsNegative(expectedQuotient)
                    || Decimal128.IsNegative(remainder) != Decimal128.IsNegative(expectedRemainder))
                {
                    failures.Add(
                        $"{Format(x)} div {Format(y)}: got {Format(quotient)} (quantum {Decimal128.ILogB(Decimal128.GetQuantum(quotient))}), "
                        + $"expected {Format(expectedQuotient)}; mod got {Format(remainder)}, expected {Format(expectedRemainder)} [{why}]");
                }

                checkedRows++;
            }
        }

        Assert.True(failures.Count == 0, $"{failures.Count} of {checkedRows} rows violated the contract:\n" + string.Join("\n", failures.Take(30)));
        Assert.True(checkedRows >= 3_000, $"The matrix degenerated: only {checkedRows} rows.");
        // The matrix must actually reach the ambiguous case the fast path cannot
        // decide — an IEEE quotient that is an integer — many times over.
        Assert.True(landings >= 500, $"Only {landings} rows had an integral rounded quotient.");
    }

    [Fact]
    public void BoundaryMatrix_SourceEvaluationAndPlannedLoop_AgreeWithTheHelper()
    {
        var failures = new List<string>();
        var checkedPrograms = 0;
        foreach (var (cx, ex, cy, ey, why) in BoundaryMatrix())
        {
            // Every evaluator-level program is a real parse; keep the family bounded
            // to the same-quantum rows (the helper matrix above covers every quantum).
            if (ex != ey || ex < -100)
                continue;

            foreach (var (sx, sy) in SignCombinations)
            {
                var x = Scaled(sx * cx, ex);
                var y = Scaled(sy * cy, ey);
                var (expectedQuotient, expectedRemainder) = ExactContract(sx * cx, ex, sy * cy, ey);
                var xText = Literal(sx * cx, ex);
                var yText = Literal(sy * cy, ey);

                var quotientDisplay = Display($"{xText} div {yText}");
                var remainderDisplay = Display($"{xText} mod {yText}");
                if (quotientDisplay != Format(expectedQuotient) || remainderDisplay != Format(expectedRemainder))
                {
                    failures.Add(
                        $"{xText} div {yText} displayed {quotientDisplay} (expected {Format(expectedQuotient)}); "
                        + $"mod displayed {remainderDisplay} (expected {Format(expectedRemainder)}) [{why}]");
                }

                // The planned loop arm must plan the division and agree with the
                // generic strategy on the same operands.
                var loop = $"S(v) = v div {yText}\nrepeat(S, 1, {xText})";
                var (generic, _) = RunCountedObserved(loop, enableLoopOptimization: false);
                var (planned, observed) = RunCountedObserved(loop, enableLoopOptimization: true);
                var genericNeutral = Neutral(generic);
                var plannedNeutral = Neutral(planned);
                var expectedNeutral = $"ok raw={SemanticExplorerHarness.Neutral(new Result.Atom(expectedQuotient))} n=1";
                if (genericNeutral != expectedNeutral || plannedNeutral != expectedNeutral || observed.OptimizedLoopHits != 1)
                {
                    failures.Add(
                        $"loop {loop.Replace("\n", " | ")}: generic {genericNeutral}, planned {plannedNeutral} "
                        + $"(hits {observed.OptimizedLoopHits}), expected {expectedNeutral} [{why}]");
                }

                checkedPrograms++;
            }
        }

        Assert.True(failures.Count == 0, $"{failures.Count} of {checkedPrograms} programs disagreed:\n" + string.Join("\n", failures.Take(30)));
        Assert.True(checkedPrograms >= 1_000, $"The program family degenerated: only {checkedPrograms} programs.");
    }

    private static string Neutral(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? "err " + SemanticExplorerHarness.ErrorCategory(result.Error)
            : $"ok raw={SemanticExplorerHarness.Neutral(result.Value.Value)} n={result.Value.EmittedCount}";

    [Fact]
    public void ArbitraryCoefficientsAndFullQuantumRange_MatchIndependentIntegerArithmetic()
    {
        var random = new Random(3009);
        BigInteger Coefficient()
        {
            var digits = new char[random.Next(1, 35)];
            digits[0] = (char)('1' + random.Next(9));
            for (var i = 1; i < digits.Length; i++)
                digits[i] = (char)('0' + random.Next(10));
            return BigInteger.Parse(digits, CultureInfo.InvariantCulture);
        }

        for (var i = 0; i < 512; i++)
        {
            var cx = Coefficient();
            var cy = Coefficient();
            // Half the cases cover the full quantum range; half concentrate on
            // precision/spacing transitions without constructing the landing matrix.
            var ex = i < 256 ? random.Next(-6176, 6112) : random.Next(-70, 71);
            var ey = i < 256 ? random.Next(-6176, 6112) : random.Next(-70, 71);
            foreach (var (sx, sy) in SignCombinations)
            {
                var x = Scaled(sx * cx, ex);
                var y = Scaled(sy * cy, ey);
                var expected = ExactContract(sx * cx, ex, sy * cy, ey);
                var actual = Decimal128Numerics.IntegerDivide(x, y);
                Assert.Equal(expected.Quotient, actual);
                Assert.Equal(Decimal128.IsNegative(expected.Quotient), Decimal128.IsNegative(actual));
                Assert.Equal(expected.Remainder, x % y);
            }
        }
    }

    [Theory]
    [InlineData(2, "000000")]
    [InlineData(753, "4993")]
    [InlineData(3847, "500")]
    [InlineData(7253, "999")]
    public void DiscardedDigits_AreDroppedTowardZero_ForEverySign(int divisor, string tail)
    {
        var dividend = BigInteger.Pow(10, 40);
        var truncated = dividend / divisor;
        var text = truncated.ToString(CultureInfo.InvariantCulture);
        Assert.Equal(tail, text[34..]);
        var expectedMagnitude = BigInteger.Parse(text[..34], CultureInfo.InvariantCulture)
            * BigInteger.Pow(10, tail.Length);
        foreach (var (sx, sy) in SignCombinations)
        {
            var actual = Decimal128Numerics.IntegerDivide(Scaled(sx, 40), sy * divisor);
            // Read the integral value back exactly; never use a rounded Decimal128
            // product to certify truncation or the div/mod identity.
            var actualInteger = BigInteger.Parse(Format(actual), CultureInfo.InvariantCulture);
            Assert.Equal(sx * sy * expectedMagnitude, actualInteger);
            Assert.True(BigInteger.Abs(actualInteger) <= truncated);
        }
    }

    [Fact]
    public void RoundedProduct_IsNotAnExactQuotientOracle()
    {
        var x = N("1e34");
        var rounded = x / 7;
        Assert.Equal(x, rounded * 7); // a false certificate for the pre-G-3 quotient
        var exact = BigInteger.Pow(10, 34) / 7;
        var actual = Decimal128Numerics.IntegerDivide(x, 7);
        Assert.NotEqual(rounded, actual);
        Assert.Equal(exact, BigInteger.Parse(Format(actual), CultureInfo.InvariantCulture));
        Assert.Equal(BigInteger.Pow(10, 34), 7 * exact + 4);
    }

    [Fact]
    public void RepresentableQuotient_DoesNotPromiseRoundedRecompositionIdentity()
    {
        const string x = "1000000000000000000000000000000005";
        const string y = "333333333333333333333333333333334.5";
        Assert.Equal("3", Display($"{x} div {y}"));
        Assert.Equal("1.5", Display($"{x} mod {y}"));
        // Exact arithmetic in tenths proves the mathematical identity; the
        // product rounds from ...003.5 to ...004, then +1.5 rounds to ...006.
        Assert.Equal(BigInteger.Parse(x) * 10, BigInteger.Parse(y.Replace(".", "")) * 3 + 15);
        Assert.Equal("1000000000000000000000000000000006", Display($"X = {x}\nY = {y}\nY * (X div Y) + (X mod Y)"));
        Assert.Equal("0", Display($"X = {x}\nY = {y}\nX == Y * (X div Y) + (X mod Y)"));
    }

    // ── The review's reproductions, both sides of the boundary, every sign ──

    [Theory]
    // The 34-digit failure: 8999…999 / 3 = 2999…999.6…, which IEEE rounds to 3e33.
    [InlineData("8999999999999999999999999999999999 div 3", "2999999999999999999999999999999999")]
    [InlineData("8999999999999999999999999999999999 mod 3", "2")]
    // The small-quotient failure: the rounded quotient is visibly 13.000…0, the exact one 12.999…
    [InlineData("Y = 3e32\nX = 13 * Y - 1\nX div Y", "12")]
    [InlineData("Y = 3e32\nX = 13 * Y - 1\nX mod Y", "299999999999999999999999999999999")]
    // The OTHER side of the boundary: the rounding lands DOWN on 12 and nothing may be adjusted.
    [InlineData("Y = 3e32\nX = 12 * Y + 1\nX div Y", "12")]
    [InlineData("Y = 3e32\nX = 12 * Y + 1\nX mod Y", "1")]
    // r * 7 rounds back to 1e34 exactly: an exactness test on a rounded product would be fooled.
    [InlineData("10000000000000000000000000000000000 div 7", "1428571428571428571428571428571428")]
    [InlineData("10000000000000000000000000000000000 mod 7", "4")]
    // The former Decimal128NumericsTests expectation: 2.999…994 truncates to 2, not 3.
    [InlineData("9999999999999999999999999999999998 div 3333333333333333333333333333333333", "2")]
    [InlineData("9999999999999999999999999999999998 mod 3333333333333333333333333333333333", "3333333333333333333333333333333332")]
    public void Reproductions_ReturnTheExactTruncatedQuotient(string source, string expectedDisplay)
    {
        Assert.Equal(expectedDisplay, Display(source));
        // Plain and counted evaluators agree (Observe throws on a disagreement).
        var observation = SemanticExplorerHarness.Observe("g3", source);
        Assert.Equal("ok", observation.Outcome);
        Assert.Equal(expectedDisplay, observation.Display);
    }

    [Theory]
    [InlineData("8999999999999999999999999999999999", "3", "2999999999999999999999999999999999", "2")]
    [InlineData("-8999999999999999999999999999999999", "3", "-2999999999999999999999999999999999", "-2")]
    [InlineData("8999999999999999999999999999999999", "-3", "-2999999999999999999999999999999999", "2")]
    [InlineData("-8999999999999999999999999999999999", "-3", "2999999999999999999999999999999999", "-2")]
    [InlineData("3899999999999999999999999999999999", "3e32", "12", "299999999999999999999999999999999")]
    [InlineData("-3899999999999999999999999999999999", "3e32", "-12", "-299999999999999999999999999999999")]
    [InlineData("3899999999999999999999999999999999", "-3e32", "-12", "299999999999999999999999999999999")]
    [InlineData("-3899999999999999999999999999999999", "-3e32", "12", "-299999999999999999999999999999999")]
    [InlineData("3600000000000000000000000000000001", "3e32", "12", "1")]
    [InlineData("-3600000000000000000000000000000001", "-3e32", "12", "-1")]
    public void EverySignCombination_TruncatesTowardZero_AndSatisfiesTheIdentity(
        string x, string y, string expectedQuotient, string expectedRemainder)
    {
        Assert.Equal(expectedQuotient, Display($"{x} div {y}"));
        Assert.Equal(expectedRemainder, Display($"{x} mod {y}"));
        // x == y * (x div y) + (x mod y), evaluated in KatLang: every intermediate
        // here is an exact 34-digit value, so the identity is observable in-language.
        Assert.Equal("1", Display($"X = {x}\nY = {y}\nX == Y * (X div Y) + (X mod Y)"));
        // Truncation is toward zero: the quotient never exceeds the true quotient in magnitude.
        Assert.Equal("1", Display($"X = {x}\nY = {y}\nQ = X div Y\nR = X / Y\nif(Q < 0, Q >= R, Q <= R)"));
    }

    [Theory]
    [InlineData("10 div 3", "3")]
    [InlineData("10 div 5", "2")]
    [InlineData("-7 div 2", "-3")]
    [InlineData("7 div -2", "-3")]
    [InlineData("-7 div -2", "3")]
    [InlineData("12.0 div 4", "3")]
    [InlineData("7.5 div 2.5", "3")]
    [InlineData("1 div 3", "0")]
    [InlineData("100 div 10", "10")]
    [InlineData("9999999999999999999999999999999999 div 1", "9999999999999999999999999999999999")]
    [InlineData("9999999999999999999999999999999999 div 9999999999999999999999999999999999", "1")]
    [InlineData("9999999999999999999999999999999999 div 3", "3333333333333333333333333333333333")]
    [InlineData("10000000000000000000000000000000000 div 3", "3333333333333333333333333333333333")]
    public void OrdinaryAndExactlyDivisibleOperands_AreUnchanged(string source, string expectedDisplay)
        => Assert.Equal(expectedDisplay, Display(source));

    // ── Digit extraction at the consecutive-integer boundary ────────────────

    [Theory]
    [InlineData("9999999999999999999999999999999999", "999999999999999999999999999999999", "9")]
    [InlineData("1234567890123456789012345678901234", "123456789012345678901234567890123", "4")]
    [InlineData("8999999999999999999999999999999999", "899999999999999999999999999999999", "9")]
    [InlineData("10000000000000000000000000000000000", "1000000000000000000000000000000000", "0")]
    [InlineData("-1234567890123456789012345678901234", "-123456789012345678901234567890123", "-4")]
    public void DigitExtraction_NearTheBoundary_StaysExact(string n, string expectedQuotient, string expectedRemainder)
    {
        Assert.Equal(expectedQuotient, Display($"{n} div 10"));
        Assert.Equal(expectedRemainder, Display($"{n} mod 10"));
    }

    [Theory]
    [InlineData("9999999999999999999999999999999999", 306)]
    [InlineData("8999999999999999999999999999999999", 305)]
    [InlineData("1234567890123456789012345678901234", 145)]
    public void DigitSumLoop_AgreesAcrossStrategies(string n, int expectedDigitSum)
    {
        var source =
            $"Step(v, s) = v div 10, s + v mod 10, v > 0\n" +
            $"R = while(Step, {n}, 0)\n" +
            "R:1";
        EvaluatorTestSupport.AssertEvalLoopModes(source, expectedDigitSum);
    }

    // ── Beyond the consecutive-integer domain ───────────────────────────────

    [Theory]
    // A sparse representable quotient is exact.
    [InlineData("1e40 div 1e6", "10000000000000000000000000000000000")]
    [InlineData("9999999999999999999999999999999999e10 div 3", "33333333333333333333333333333333330000000000")]
    // A quotient that needs more than 34 digits keeps its leading 34 digits — toward
    // zero, never rounded to nearest (`1e40 / 7` correctly rounds to …429e6).
    [InlineData("1e40 div 7", "1428571428571428571428571428571428000000")]
    [InlineData("1e35 div 7", "14285714285714285714285714285714280")]
    [InlineData("2e40 div 3", "6666666666666666666666666666666666000000")]
    [InlineData("-2e40 div 3", "-6666666666666666666666666666666666000000")]
    // An exact 35-digit integer ending in 5 is a round-to-nearest TIE; div still truncates.
    [InlineData("99999999999999999999999999999999990 div 6", "16666666666666666666666666666666660")]
    [InlineData("1e40 / 7", "1428571428571428571428571428571429000000")]
    public void BeyondTheConsecutiveIntegerDomain_RoundsTowardZero(string source, string expectedDisplay)
        => Assert.Equal(expectedDisplay, Display(source));

    [Fact]
    public void BeyondTheConsecutiveIntegerDomain_TheProductNeverExceedsTheDividend()
    {
        // Because div rounds toward zero and multiplication rounds monotonically,
        // (x div y) * y can never exceed x — the property the review's identity
        // reduces to once the quotient is no longer representable.
        Assert.Equal("1", Display("X = 1e40\n(X div 7) * 7 <= X"));
        Assert.Equal("1", Display("X = 2e40\n(X div 3) * 3 <= X"));
        Assert.Equal("1", Display("X = -2e40\n(X div 3) * 3 >= X"));
    }

    // ── Special values and the zero-divisor error are unchanged ────────────

    [Theory]
    [InlineData("(1e6144 * 10) div 3", "Infinity")]
    [InlineData("(1e6144 * 10) div -3", "-Infinity")]
    [InlineData("3 div (1e6144 * 10)", "0")]
    [InlineData("-3 div (1e6144 * 10)", "-0")]
    [InlineData("(1e6144 * 10) div (1e6144 * 10)", "NaN")]
    [InlineData("((-2) ^ 0.5) div 3", "NaN")]
    [InlineData("3 div ((-2) ^ 0.5)", "NaN")]
    [InlineData("5 div 1e-6176", "Infinity")]
    [InlineData("-5 div 1e-6176", "-Infinity")]
    [InlineData("1e6144 div 0.05", "Infinity")]
    [InlineData("1e-6176 div 3", "0")]
    [InlineData("-1e-6176 div 3", "-0")]
    [InlineData("1e-6176 div 3e-6176", "0")]
    [InlineData("7 div 8", "0")]
    [InlineData("-7 div 8", "-0")]
    [InlineData("7 div -8", "-0")]
    [InlineData("0 div -3", "-0")]
    [InlineData("-0 div 3", "-0")]
    [InlineData("0 div 3", "0")]
    public void SpecialValues_KeepTheOperatorContract(string source, string expectedDisplay)
        => Assert.Equal(expectedDisplay, Display(source));

    [Fact]
    public void Helper_SpecialValues_AreTheTruncatedIeeeQuotient()
    {
        Assert.True(Decimal128.IsNaN(Decimal128Numerics.IntegerDivide(Decimal128.NaN, 3)));
        Assert.True(Decimal128.IsNaN(Decimal128Numerics.IntegerDivide(3, Decimal128.NaN)));
        Assert.True(Decimal128.IsNaN(Decimal128Numerics.IntegerDivide(Decimal128.PositiveInfinity, Decimal128.NegativeInfinity)));
        Assert.Equal(Decimal128.PositiveInfinity, Decimal128Numerics.IntegerDivide(Decimal128.PositiveInfinity, 3));
        Assert.Equal(Decimal128.NegativeInfinity, Decimal128Numerics.IntegerDivide(Decimal128.PositiveInfinity, -3));
        var zero = Decimal128Numerics.IntegerDivide(3, Decimal128.PositiveInfinity);
        Assert.Equal(Decimal128.Zero, zero);
        Assert.False(Decimal128.IsNegative(zero));
        var negativeZero = Decimal128Numerics.IntegerDivide(-3, Decimal128.PositiveInfinity);
        Assert.Equal(Decimal128.Zero, negativeZero);
        Assert.True(Decimal128.IsNegative(negativeZero));
        // The helper is total: a zero divisor (which the evaluator rejects first)
        // follows the same IEEE rule.
        Assert.Equal(Decimal128.PositiveInfinity, Decimal128Numerics.IntegerDivide(3, Decimal128.Zero));
        Assert.True(Decimal128.IsNaN(Decimal128Numerics.IntegerDivide(Decimal128.Zero, Decimal128.Zero)));
    }

    [Fact]
    public void SpecialValueCrossProduct_PreservesIeeeValueSignAndZeroRepresentation()
    {
        Decimal128[] values = [Decimal128.NaN, Decimal128.PositiveInfinity, Decimal128.NegativeInfinity,
            Decimal128.Zero, Decimal128.NegativeZero, N("0e-6176"), N("-0e6111"),
            N("3"), N("-3"), Decimal128.Epsilon, -Decimal128.Epsilon, Decimal128.MaxValue];
        foreach (var x in values)
        foreach (var y in values)
        {
            var rounded = x / y;
            if (Decimal128.IsFinite(x) && Decimal128.IsFinite(y)
                && Decimal128.IsFinite(rounded) && rounded != Decimal128.Zero)
                continue;
            var expected = Decimal128.Truncate(rounded);
            var actual = Decimal128Numerics.IntegerDivide(x, y);
            Assert.Equal(expected, actual);
            Assert.Equal(Decimal128.IsNegative(expected), Decimal128.IsNegative(actual));
            if (Decimal128.IsFinite(actual))
            {
                Assert.True(Decimal128.HaveSameQuantum(expected, actual));
                Assert.Equal(Format(expected), Format(actual));
                Assert.InRange(Format(actual).Length, 1, 2); // only 0 or -0, never thousands of zeros
            }
        }
    }

    [Theory]
    [InlineData("5 div 0")]
    [InlineData("5 div -0")]
    [InlineData("5 div (1 - 1)")]
    [InlineData("5 div 1e-9999")]
    [InlineData("8999999999999999999999999999999999 div 0")]
    public void ZeroValuedDivisor_StaysTheSpecifiedErrorWithItsSpan(string source)
    {
        var plain = SourceProvenance.ParseValid(source).Evaluate();
        Assert.True(plain.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(plain.Error));
        Assert.Equal(KatLangErrorCode.DivisionByZero, plain.Error.Code);
        Assert.Equal(new SourceSpan(1, 1, 1, source.Length), Innermost(plain.Error).Span);

        var engine = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var publicError = Assert.Single(engine.Errors);
        Assert.Equal(KatLangErrorCode.DivisionByZero, publicError.Code);
        Assert.Equal(((int?)1, (int?)1, (int?)1, (int?)source.Length),
            (publicError.StartLine, publicError.StartColumn, publicError.EndLine, publicError.EndColumn));
    }

    // ── The planned numeric arm actually executes, and agrees ───────────────

    [Theory]
    [InlineData(false, "8999999999999999999999999999999999", "3", "2999999999999999999999999999999999")]
    [InlineData(true, "8999999999999999999999999999999999", "3", "2999999999999999999999999999999999")]
    [InlineData(false, "3899999999999999999999999999999999", "300000000000000000000000000000000", "12")]
    [InlineData(true, "3899999999999999999999999999999999", "300000000000000000000000000000000", "12")]
    [InlineData(false, "3600000000000000000000000000000001", "300000000000000000000000000000000", "12")]
    [InlineData(true, "3600000000000000000000000000000001", "300000000000000000000000000000000", "12")]
    [InlineData(false, "1e35", "7", "14285714285714285714285714285714280")]
    [InlineData(true, "1e35", "7", "14285714285714285714285714285714280")]
    [InlineData(false, "-8999999999999999999999999999999999", "3", "-2999999999999999999999999999999999")]
    [InlineData(true, "-8999999999999999999999999999999999", "3", "-2999999999999999999999999999999999")]
    public void PlannedNumericArm_ActuallyExecutesAndAgreesWithGeneric(bool useWhile, string x, string y, string expectedDisplay)
    {
        // `while` returns the state that entered the step whose continuation was
        // false, so a counter slot admits exactly one continuing iteration: the
        // quotient computed by the first step is the state the second step reads.
        var source = useWhile
            ? $"S(v, k) = v div {y}, k + 1, k < 1\nwhile(S, {x}, 0)"
            : $"S(v) = v div {y}\nrepeat(S, 1, {x})";
        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (planned, loop) = RunCountedObserved(source, enableLoopOptimization: true);
        Assert.False(generic.IsError);
        Assert.False(planned.IsError);
        var expected = useWhile ? $"ok raw=S[{expectedDisplay}, 1] n=2" : $"ok raw={expectedDisplay} n=1";
        Assert.Equal(expected, Neutral(generic));
        Assert.Equal(expected, Neutral(planned));

        // Outcome equality alone could pass if both executions became generic.
        Assert.Equal(1, loop.OptimizedLoopHits);
        var plan = Assert.Single(loop.LoopPlans);
        Assert.True(plan.Optimized);
        var division = Assert.Single(plan.Expressions, item => item.Role == "output" && item.Index == 0);
        Assert.True(division.Planned);
        Assert.StartsWith("IntegerDivide(StateSlot(v),", division.PlanSummary);
        Assert.Equal(useWhile ? 2 : 1, loop.LoopIterations);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
    }

    [Theory]
    [InlineData(false, "0")]
    [InlineData(true, "0")]
    [InlineData(false, "-0")]
    [InlineData(true, "1e-9999")]
    public void PlannedDivisionByZero_PreservesTheStructuredErrorAndSpan(bool useWhile, string divisor)
    {
        var expression = $"v div {divisor}";
        var source = useWhile
            ? $"S(v) = {expression}, 0\nwhile(S, 7)"
            : $"S(v) = {expression}\nrepeat(S, 1, 7)";
        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (planned, observed) = RunCountedObserved(source, enableLoopOptimization: true);
        Assert.True(generic.IsError);
        Assert.True(planned.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(planned.Error));
        Assert.Equal(new SourceSpan(1, 8, 1, 7 + expression.Length), Innermost(planned.Error).Span);
        Assert.Equal(DescribeErrorTree(generic.Error), DescribeErrorTree(planned.Error));
        Assert.Equal(1, observed.OptimizedLoopHits);
        Assert.Equal(0, observed.PlannedExpressionFallbacks);
        Assert.Equal(0, observed.GenericExpressionEvaluationsInsideOptimizedLoops);
    }

    [Fact]
    public void UnplannedDivisionExpression_UsesTheSameExactQuotient()
    {
        const string source = "S(v) = v div Math.Abs(-3)\nrepeat(S, 1, 8999999999999999999999999999999999)";
        // The Math dot-call is unsupported by the expression planner, forcing the
        // division expression through the generic evaluator inside the optimized loop.
        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (fallback, observed) = RunCountedObserved(source, enableLoopOptimization: true);
        Assert.Equal("ok raw=2999999999999999999999999999999999 n=1", Neutral(generic));
        Assert.Equal(Neutral(generic), Neutral(fallback));
        Assert.Equal(1, observed.OptimizedLoopHits);
        Assert.True(observed.GenericExpressionEvaluationsInsideOptimizedLoops > 0);
    }

    // ── Sync, counted, and genuinely suspending async agree ─────────────────

    [Theory]
    [InlineData("Z div 3", "2999999999999999999999999999999999")]
    [InlineData("Z mod 3", "2")]
    [InlineData("Z div -3", "-2999999999999999999999999999999999")]
    [InlineData("(Z + 1) div 3", "3000000000000000000000000000000000")]
    public async Task ExactQuotient_SurvivesSuspension(string expression, string expectedDisplay)
    {
        // Reading Z forces the async cache seam before the division executes.
        var source = $"Z = 8999999999999999999999999999999999\n7\n{expression}";
        var ast = Program(source);
        var plain = Evaluator.Run(ast);
        var counted = Evaluator.RunCountedObserved(ast, enableOptimizations: false).Result;
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var suspended = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(ast, cache));

        Assert.False(plain.IsError);
        Assert.False(counted.IsError);
        Assert.False(suspended.IsError);
        var expectedRaw = $"S[7, {expectedDisplay}]";
        Assert.Equal(expectedRaw, SemanticExplorerHarness.Neutral(plain.Value));
        Assert.Equal(expectedRaw, SemanticExplorerHarness.Neutral(counted.Value.Value));
        Assert.Equal(expectedRaw, SemanticExplorerHarness.Neutral(suspended.Value.Value));
        Assert.Equal(counted.Value.EmittedCount, suspended.Value.EmittedCount);
        Assert.True(cache.AsyncAccesses > 0);
        Assert.NotEmpty(cache.ThreadHops);
        Assert.Equal(0, cache.SyncAccesses);
    }

    [Fact]
    public async Task ZeroValuedDivisor_PreservesErrorAndSpanAfterSuspension()
    {
        const string expression = "Z div 0";
        var source = $"Z = 8999999999999999999999999999999999\n7\n{expression}";
        var ast = Program(source);
        var plain = Evaluator.Run(ast);
        var counted = Evaluator.RunCountedObserved(ast, enableOptimizations: false).Result;
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var suspended = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(ast, cache));

        Assert.True(plain.IsError);
        Assert.True(counted.IsError);
        Assert.True(suspended.IsError);
        foreach (var error in new[] { plain.Error, counted.Error, suspended.Error })
        {
            Assert.IsType<EvalError.DivByZero>(Innermost(error));
            Assert.Equal(KatLangErrorCode.DivisionByZero, error.Code);
            var diagnostic = KatLangError.FromEvalError(error);
            Assert.Equal(((int?)3, (int?)1, (int?)3, (int?)expression.Length),
                (diagnostic.StartLine, diagnostic.StartColumn, diagnostic.EndLine, diagnostic.EndColumn));
            Assert.Equal(DescribeErrorTree(plain.Error), DescribeErrorTree(error));
        }
        Assert.True(cache.AsyncAccesses > 0);
    }

    [Theory]
    [InlineData("Z div 3", "2999999999999999999999999999999999")]
    [InlineData("Z div 0", null)]
    public async Task Division_ResumesFromAnObservedIncompleteAsyncRun(string expression, string? expected)
    {
        var ast = Program($"Z = 8999999999999999999999999999999999\n{expression}");
        var cache = new HoldingAsyncZeroArgPropertyResultCache(holdAtAccess: 1);
        var pending = Evaluator.RunCountedAsync(ast, cache);
        try
        {
            await cache.Reached.WaitAsync(TimeSpan.FromSeconds(10));
            Assert.False(pending.IsCompleted);
        }
        finally
        {
            cache.Release();
        }
        var actual = await AsyncEvaluationHarness.Complete(pending);
        var generic = Evaluator.RunCountedObserved(ast, enableOptimizations: false).Result;
        Assert.Equal(Neutral(generic), Neutral(actual));
        if (expected is null)
        {
            Assert.True(actual.IsError);
            Assert.IsType<EvalError.DivByZero>(Innermost(actual.Error));
            Assert.Equal(DescribeErrorTree(generic.Error), DescribeErrorTree(actual.Error));
        }
        else
        {
            Assert.Equal($"ok raw={expected} n=1", Neutral(actual));
        }
    }

    // ── The fast-path predicate: both directions around every integer ────────

    [Fact]
    public void FastPath_NonIntegralRoundedQuotient_TruncatesExactly_OnBothSidesOfTheInteger()
    {
        // Below the crossing band (cy = 3e31 < 2e32) the rounded quotient stays
        // non-integral on both sides of 13, so the fast path decides; it must give
        // 12 below the integer and 13 above it.
        var y = N("3e31");
        Assert.Equal(N("12"), Decimal128Numerics.IntegerDivide(13 * y - Decimal128.One, y));
        Assert.Equal(N("13"), Decimal128Numerics.IntegerDivide(13 * y + Decimal128.One, y));
        Assert.False(Decimal128.IsInteger((13 * y - Decimal128.One) / y));
        Assert.False(Decimal128.IsInteger((13 * y + Decimal128.One) / y));

        // Inside the band (cy = 3e32) the rounded quotient IS the integer 13 from
        // below (a crossing) and 12 from above (no crossing): the exact decision
        // must adjust in exactly one direction.
        y = N("3e32");
        Assert.True(Decimal128.IsInteger((13 * y - Decimal128.One) / y));
        Assert.True(Decimal128.IsInteger((12 * y + Decimal128.One) / y));
        Assert.Equal(N("12"), Decimal128Numerics.IntegerDivide(13 * y - Decimal128.One, y));
        Assert.Equal(N("12"), Decimal128Numerics.IntegerDivide(12 * y + Decimal128.One, y));
        Assert.Equal(N("-12"), Decimal128Numerics.IntegerDivide(-(13 * y - Decimal128.One), y));
        Assert.Equal(N("-12"), Decimal128Numerics.IntegerDivide(12 * y + Decimal128.One, -y));
        Assert.Equal(N("12"), Decimal128Numerics.IntegerDivide(-(13 * y - Decimal128.One), -y));

        // The integral results carry an integral quantum: never `12.000…0`.
        Assert.Equal(0, Decimal128.ILogB(Decimal128.GetQuantum(Decimal128Numerics.IntegerDivide(13 * y - Decimal128.One, y))));
    }

    [Fact]
    public void ExactDivisionShortcut_KeepsTheIeeeQuotientBitForBit()
    {
        // Exactly divisible operands below 1e34 return the IEEE quotient re-quantized
        // by Truncate (the pre-G-3 result, bit-for-bit), including 34-digit ones.
        foreach (var (x, y) in new[] { ("12.0", "4"), ("100", "10"), ("9999999999999999999999999999999999", "1"), ("1e33", "1e-1"), ("1e40", "1e5"), ("6", "3") })
        {
            var expected = Decimal128.Truncate(N(x) / N(y));
            var actual = Decimal128Numerics.IntegerDivide(N(x), N(y));
            Assert.Equal(expected, actual);
            Assert.True(Decimal128.HaveSameQuantum(expected, actual), $"{x} div {y} changed its quantum");
        }

        // At or above 1e34 a divisible quotient need not be representable, so the
        // shortcut must not apply there: 1e40 / 1e6 is exact (and keeps its quantum),
        // while 3333333333333333333333333333333335 / 0.2 is the exact 35-digit integer
        // 16666666666666666666666666666666675 — divisible (`%` is zero), yet IEEE
        // rounds the tie UP to …6668e1 — and must come back truncated as …6667e1.
        Assert.True(Decimal128.HaveSameQuantum(N("1e40") / N("1e6"), Decimal128Numerics.IntegerDivide(N("1e40"), N("1e6"))));
        Assert.Equal(N("1e34"), Decimal128Numerics.IntegerDivide(N("1e40"), N("1e6")));

        var divisible = N("3333333333333333333333333333333335");
        var fifth = N("0.2");
        Assert.Equal(Decimal128.Zero, divisible % fifth);
        Assert.Equal(N("1666666666666666666666666666666668e1"), Decimal128.Truncate(divisible / fifth)); // the pre-G-3 rule
        Assert.Equal(N("1666666666666666666666666666666667e1"), Decimal128Numerics.IntegerDivide(divisible, fifth));
        Assert.Equal(N("-1666666666666666666666666666666667e1"), Decimal128Numerics.IntegerDivide(-divisible, fifth));
        // Below 1e34 the same shape is exact and unchanged: 333…35 / 2 = 166…67.5 → 166…67.
        Assert.Equal(N("1666666666666666666666666666666667"), Decimal128Numerics.IntegerDivide(divisible, N("2")));
    }
}
