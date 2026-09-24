using System.Globalization;
using System.Numerics;
using System.Text;

namespace KatLang.Tests;

/// <summary>
/// Numeric audit #6 (September 2026): <c>avg</c> is the EXACT total of its elements
/// divided by their count, rounded ONCE to 34 significant digits. It used to divide the
/// left-to-right Decimal128 sum, so a sum that rounded on the way produced a mean with no
/// correct digits — <c>avg((1, 1e34, -1e34))</c> was <c>0</c>, and <c>avg((1e34, 1, 1))</c>
/// was one unit low — while an OVERFLOWING sum already took the exact mean. The law pinned
/// here: for finite elements <c>avg</c> is the correctly rounded exact mean (so it cannot
/// depend on element order), and whenever every left-to-right addition was exact it is
/// still <c>sum(X) / count(X)</c> bit-for-bit, IEEE quantum and zero sign included.
///
/// <para>The oracle never consults Decimal128 arithmetic: the literals are parsed into
/// exact <see cref="BigInteger"/> coefficients, the rational mean is expanded by long
/// division to 60 significant digits with a sticky digit for any nonzero remainder, and
/// the runtime's correctly rounded text conversion rounds that expansion ONCE (the sticky
/// digit makes a truncated expansion round exactly as the full rational does, ties
/// included).</para>
/// </summary>
public class AverageExactMeanTests
{
    private const string Max = "9999999999999999999999999999999999e6111";

    // ── Oracle ─────────────────────────────────────────────────────────────

    private static (BigInteger Coefficient, int Exponent) ParseLiteral(string literal)
    {
        var negative = literal.StartsWith('-');
        var body = negative ? literal[1..] : literal;
        var exponent = 0;
        var e = body.IndexOf('e');
        if (e >= 0)
        {
            exponent = int.Parse(body[(e + 1)..], NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture);
            body = body[..e];
        }

        var point = body.IndexOf('.');
        if (point >= 0)
        {
            exponent -= body.Length - point - 1;
            body = body.Remove(point, 1);
        }

        var coefficient = BigInteger.Parse(body, CultureInfo.InvariantCulture);
        return (negative ? -coefficient : coefficient, exponent);
    }

    private static Decimal128 ExactMean(IReadOnlyList<string> literals)
    {
        var parsed = literals.Select(ParseLiteral).ToList();
        var minimumExponent = parsed.Min(p => p.Exponent);
        var sum = parsed.Aggregate(
            BigInteger.Zero,
            (total, p) => total + p.Coefficient * BigInteger.Pow(10, p.Exponent - minimumExponent));
        if (sum.IsZero)
            return Decimal128.Zero;

        var denominator = new BigInteger(literals.Count);
        var integerPart = BigInteger.DivRem(BigInteger.Abs(sum), denominator, out var remainder);
        var digits = new StringBuilder(integerPart.ToString(CultureInfo.InvariantCulture));
        var significant = integerPart.IsZero ? 0 : digits.Length;
        var fractionDigits = 0;
        while (!remainder.IsZero && significant < 60)
        {
            var digit = BigInteger.DivRem(remainder * 10, denominator, out remainder);
            digits.Append((char)('0' + (int)digit));
            fractionDigits++;
            if (significant > 0 || !digit.IsZero)
                significant++;
        }

        if (!remainder.IsZero)
        {
            digits.Append('1');
            fractionDigits++;
        }

        var text = (sum.Sign < 0 ? "-" : "") + digits + "e"
            + (minimumExponent - fractionDigits).ToString(CultureInfo.InvariantCulture);
        return Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);
    }

    // ── Helpers ────────────────────────────────────────────────────────────

    private static string Collection(IReadOnlyList<string> literals)
        => literals.Count == 1 ? literals[0] : "(" + string.Join(", ", literals) + ")";

    private static RunResult.Success RunValid(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));

    private static Decimal128 Atom(RunResult.Success success)
        => Assert.IsType<Result.Atom>(success.Value).Value;

    private static Decimal128 Avg(IReadOnlyList<string> literals)
        => Atom(RunValid($"avg({Collection(literals)})"));

    /// <summary>A deterministic corpus: mixed magnitudes, quanta, and signs, with cancelling pairs.</summary>
    private static List<string[]> GeneratedDatasets()
    {
        var random = new Random(0x6A76);
        var datasets = new List<string[]>();
        for (var i = 0; i < 400; i++)
        {
            var elements = new List<string>();
            var count = random.Next(1, 13);
            for (var j = 0; j < count; j++)
            {
                var digits = random.Next(1, 35);
                var coefficient = new StringBuilder();
                coefficient.Append((char)('1' + random.Next(9)));
                for (var d = 1; d < digits; d++)
                    coefficient.Append((char)('0' + random.Next(10)));
                var exponent = random.Next(5) switch
                {
                    0 => random.Next(-3, 4),
                    1 => random.Next(-40, 41),
                    2 => random.Next(-6176, 6111 - digits + 2),
                    _ => 0,
                };
                elements.Add((random.Next(2) == 0 ? "-" : "") + coefficient + "e" + exponent.ToString(CultureInfo.InvariantCulture));
            }

            if (count >= 2 && random.Next(4) == 0)
            {
                // A cancelling pair large enough to absorb the other elements on the way.
                var large = (1 + random.Next(9)).ToString(CultureInfo.InvariantCulture) + "e"
                    + random.Next(30, 61).ToString(CultureInfo.InvariantCulture);
                elements.Insert(random.Next(elements.Count + 1), large);
                elements.Insert(random.Next(elements.Count + 1), "-" + large);
            }

            datasets.Add([.. elements]);
        }

        return datasets;
    }

    // ── Reproductions ──────────────────────────────────────────────────────

    [Theory]
    // (1e34 + 2) / 3 is exactly 3333333333333333333333333333333334; the rounded running
    // sum 1e34 gave …333.
    [InlineData("avg((1e34, 1, 1))", "3333333333333333333333333333333334")]
    // The running sum absorbs 1 into 1e34 and then cancels to 0.
    [InlineData("avg((1, 1e34, -1e34))", "0.3333333333333333333333333333333333")]
    [InlineData("avg((1e34, -1e34, 1))", "0.3333333333333333333333333333333333")]
    [InlineData("avg((1, 1e34, -1e34, 0))", "0.25")]
    // The overflow rescue now carries the IEEE quantum of an exact quotient too.
    [InlineData($"avg(({Max}, {Max}, -{Max}, -{Max}, 4))", "0.8")]
    public void RoundedRunningSum_NoLongerDecidesTheMean(string source, string expectedDisplay)
    {
        var success = RunValid(source);
        Assert.Equal(expectedDisplay, success.ToDisplayString());
        Assert.Equal(Decimal128.Parse(expectedDisplay, CultureInfo.InvariantCulture), Atom(success));
    }

    [Fact]
    public void LeftToRightSum_KeepsItsDocumentedRounding()
    {
        // `sum` is still the left-to-right Decimal128 sum — the contrast the fix relies on.
        Assert.Equal("0", RunValid("sum((1, 1e34, -1e34))").ToDisplayString());
        Assert.Equal("1", RunValid("sum((1e34, -1e34, 1))").ToDisplayString());
    }

    // ── Laws ───────────────────────────────────────────────────────────────

    [Fact]
    public void FiniteMean_IsTheCorrectlyRoundedExactMean_AndOrderIndependent()
    {
        var datasets = GeneratedDatasets();
        for (var i = 0; i < datasets.Count; i++)
        {
            var dataset = datasets[i];
            var expected = ExactMean(dataset);
            var actual = Avg(dataset);
            Assert.True(
                expected.Equals(actual),
                $"dataset #{i} ({Collection(dataset)}): expected {expected}, got {actual}");

            var reversed = dataset.Reverse().ToArray();
            Assert.True(
                actual.Equals(Avg(reversed)),
                $"dataset #{i}: the mean depended on element order ({Collection(reversed)})");
        }
    }

    [Theory]
    [InlineData("1, 2")]
    [InlineData("1.0, 2.00")]
    [InlineData("0.1, 0.2, 0.3")]
    [InlineData("0.0, -0.00")]
    [InlineData("-0")]
    [InlineData("-0, -0")]
    [InlineData("100e1, 5")]
    [InlineData("5e-6176, 3e-6176")]
    [InlineData("1e6111, 1e6111")]
    // An exact sum at a coarser quantum (9999999999999999999999999999999999 + 1 is exactly
    // 1e34 at quantum 1) is not provably exact step by step, yet still the ordinary division.
    [InlineData("9999999999999999999999999999999999, 1, -5")]
    public void ExactLeftToRightSum_KeepsTheOrdinaryDivisionBitForBit(string elements)
    {
        var mean = Atom(RunValid($"avg(({elements}))"));
        var quotient = Atom(RunValid($"X = ({elements})\nsum(X) / count(X)"));
        Assert.Equal(quotient, mean);
        Assert.True(Decimal128.HaveSameQuantum(quotient, mean), $"quantum differs: {quotient} vs {mean}");
        Assert.Equal(Decimal128.IsNegative(quotient), Decimal128.IsNegative(mean));
    }

    [Theory]
    [InlineData("avg((1, sqrt(-1)))", "NaN")]
    [InlineData("avg((-ln(0), 1))", "Infinity")]
    [InlineData("avg((ln(0), 1e34, 1))", "-Infinity")]
    [InlineData("avg((-ln(0), ln(0)))", "NaN")]
    public void NonFiniteElements_KeepTheOrdinaryIeeeResult(string source, string expectedDisplay)
        => Assert.Equal(expectedDisplay, RunValid(source).ToDisplayString());

    [Theory]
    [InlineData("1, 1e34, -1e34")]
    [InlineData("1e34, 1, 1")]
    [InlineData("0.1, 0.2, 0.3")]
    public async Task EveryCallRoute_AgreesOnTheMean(string elements)
    {
        var direct = RunValid($"avg(({elements}))").ToDisplayString();
        Assert.Equal(direct, RunValid($"X = ({elements})\nX.avg").ToDisplayString());
        Assert.Equal(direct, RunValid($"X = ({elements})\navg(X)").ToDisplayString());
        Assert.Equal(direct, RunValid($"avg([{elements}])").ToDisplayString());

        var asynchronous = await NumericSemanticLawReviewTests.RunSuspending($"avg(({elements}))");
        Assert.Equal(direct, asynchronous.ToDisplayString());
    }
}
