using System.Globalization;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// <c>Math.RandomInt</c> uniformity: the sampler draws directly in the INTEGER
/// domain with modulo-rejection over uniform 128-bit draws
/// (<c>Evaluator.SampleUniformInteger</c>), never by scaling the fixed
/// 10^34-point <c>Math.Random</c> lattice — flooring a scaled fraction biases
/// every span that does not divide the lattice and cannot even reach every
/// integer of very large spans. The draw source is injected, so these tests
/// exercise the mapping and rejection logic DETERMINISTICALLY with scripted
/// draw sequences; the seeded statistical smoke test is deterministic and is
/// only a wiring sanity check, not the proof of uniformity.
/// </summary>
public class RandomIntSamplingTests
{
    private static Decimal128 N(string text)
        => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);

    private static (Func<UInt128> Source, Func<int> Remaining) Draws(params UInt128[] values)
    {
        var queue = new Queue<UInt128>(values);
        // Dequeue on an empty queue throws, so a sampler that draws MORE than the
        // script supplies fails the test loudly.
        return (() => queue.Dequeue(), () => queue.Count);
    }

    private static Decimal128 Sample(string start, string end, params UInt128[] draws)
    {
        var (source, remaining) = Draws(draws);
        var result = Evaluator.SampleUniformInteger(N(start), N(end), source);
        Assert.Equal(0, remaining());
        return result;
    }

    private static Decimal128 Sample(Decimal128 start, Decimal128 end, params UInt128[] draws)
    {
        var (source, remaining) = Draws(draws);
        var result = Evaluator.SampleUniformInteger(start, end, source);
        Assert.Equal(0, remaining());
        return result;
    }

    // ── Direct mapping: draw -> start + (draw mod span) ──────────────────────

    [Theory]
    [InlineData("1", "7", 0uL, "1")]     // dice: draw 0 -> start
    [InlineData("1", "7", 5uL, "6")]     // draw span-1 -> end-1
    [InlineData("1", "7", 6uL, "1")]     // draw span wraps to start
    [InlineData("-3", "3", 0uL, "-3")]   // negative-to-positive span
    [InlineData("-3", "3", 5uL, "2")]
    [InlineData("0", "10", 7uL, "7")]
    public void AcceptedDraws_MapByModuloFromStart(string start, string end, ulong draw, string expected)
        => Assert.Equal(N(expected), Sample(start, end, (UInt128)draw));

    [Fact]
    public void SmallSpan_ConsecutiveDraws_CycleUniformlyThroughEveryValue()
    {
        // Exhaustive aligned window: draws 0..24 over span 5 hit each of the five
        // values exactly five times, in cycling order — the mapping has no
        // preferred residue.
        var counts = new Dictionary<Decimal128, int>();
        for (var draw = 0; draw < 25; draw++)
        {
            var value = Sample("10", "15", (UInt128)draw);
            counts[value] = counts.GetValueOrDefault(value) + 1;
            Assert.Equal(N((10 + (draw % 5)).ToString(CultureInfo.InvariantCulture)), value);
        }

        Assert.Equal(5, counts.Count);
        Assert.All(counts.Values, static count => Assert.Equal(5, count));
    }

    // ── Rejection: spans that do not divide 2^128 ────────────────────────────
    // 2^128 ≡ 1 (mod 3), so for span 3 exactly ONE top draw (2^128 - 1 =
    // UInt128.MaxValue) is rejected; 2^128 ≡ 4 (mod 6), so for span 6 the top
    // FOUR draws are rejected. Everything below the cutoff is accepted and the
    // accepted count is an exact multiple of the span — that is what removes
    // the modulo bias.

    [Theory]
    [InlineData(1uL, 0uL)]
    [InlineData(2uL, 0uL)]
    [InlineData(3uL, 1uL)]
    [InlineData(5uL, 1uL)]
    [InlineData(6uL, 4uL)]
    [InlineData(10uL, 6uL)]
    [InlineData(257uL, 1uL)]
    public void RepresentativeSpans_HaveTheExactTwoToThe128RejectionCutoff(
        ulong spanValue, ulong expectedRejectedCount)
    {
        // Independent BigInteger arithmetic explicitly represents 2^128 and proves
        // both the rejected-state count and divisibility of the accepted set.
        var sourceStateCount = BigInteger.One << 128;
        var spanBig = new BigInteger(spanValue);
        Assert.Equal(new BigInteger(expectedRejectedCount), sourceStateCount % spanBig);
        Assert.Equal(BigInteger.Zero, (sourceStateCount - expectedRejectedCount) % spanBig);

        var cutoff = UInt128.MaxValue - expectedRejectedCount;
        Assert.Equal(
            (Decimal128)(spanValue - 1),
            Sample(Decimal128.Zero, (Decimal128)spanValue, cutoff));

        if (expectedRejectedCount == 0)
            return;

        // Every top state above the cutoff is rejected. Feeding all of them before
        // raw zero also forces a multi-rejection chain for spans 6 and 10.
        var draws = Enumerable.Range(0, (int)expectedRejectedCount)
            .Select(index => UInt128.MaxValue - (UInt128)index)
            .Append(UInt128.Zero)
            .ToArray();
        Assert.Equal(Decimal128.Zero, Sample(Decimal128.Zero, (Decimal128)spanValue, draws));
    }

    [Fact]
    public void PowerOfTwoSpan_NeverRejects()
    {
        // span 2^64 divides 2^128 exactly: even the maximum draw is accepted, and
        // (2^128 - 1) mod 2^64 = 2^64 - 1 -> end-1.
        var span = (UInt128)ulong.MaxValue + 1;
        var start = Decimal128.Zero;
        var end = (Decimal128)((Int128)span);
        var (source, remaining) = Draws(UInt128.MaxValue);
        var result = Evaluator.SampleUniformInteger(start, end, source);
        Assert.Equal(0, remaining());
        Assert.Equal((Decimal128)((Int128)span - 1), result);
    }

    // ── The exact consecutive-integer boundary ───────────────────────────────

    [Fact]
    public void NearBoundarySpans_ProduceExactlyRepresentableIntegers()
    {
        Assert.Equal(N("9999999999999999999999999999999998"), Sample("1e34 - 2", "1e34", (UInt128)0));
        Assert.Equal(N("9999999999999999999999999999999999"), Sample("1e34 - 2", "1e34", (UInt128)1));
    }

    [Fact]
    public void FullSupportedHalfOpenDomain_ReachesLowerBoundUpperAdjacentAndZero()
    {
        // Half-open span = 2e34; draw 0 -> -1e34, draw span-1 -> the greatest
        // INCLUDED value 1e34 - 1 (34 nines). The exclusive +1e34 bound itself
        // is intentionally not an outcome. Under
        // the old scaled-lattice design a span of 2e34 had only 10^34 reachable
        // points — half the integers could NEVER occur.
        Assert.Equal(N("-1e34"), Sample("-1e34", "1e34", (UInt128)0));

        var span = (UInt128)((Int128)N("1e34") - (Int128)N("-1e34"));
        Assert.Equal(N("9999999999999999999999999999999999"), Sample("-1e34", "1e34", span - 1));
        Assert.Equal(Decimal128.Zero, Sample("-1e34", "1e34", (UInt128)(Int128)N("1e34")));
    }

    [Fact]
    public void FullSupportedDomain_UsesTheExactLargeSpanRejectionCutoff()
    {
        var start = N("-1e34");
        var end = N("1e34");
        var span = (UInt128)((Int128)end - (Int128)start);
        var rejectedCount = (UInt128)((BigInteger.One << 128) % BigInteger.CreateChecked(span));
        Assert.NotEqual(UInt128.Zero, rejectedCount);

        var cutoff = UInt128.MaxValue - rejectedCount;
        Assert.Equal(end - Decimal128.One, Sample(start, end, cutoff));
        Assert.Equal(start, Sample(start, end, cutoff + UInt128.One, UInt128.Zero));
    }

    [Fact]
    public void ExactIntegerBoundary_IsConsecutiveOnlyThroughOneE34()
    {
        Assert.Equal(N("1000000000000000000000000000000001"), N("1e33") + Decimal128.One);
        Assert.Equal(N("-1000000000000000000000000000000001"), N("-1e33") - Decimal128.One);

        Assert.NotEqual(N("1e34"), N("1e34") - Decimal128.One);
        Assert.Equal(N("1e34"), N("1e34") + Decimal128.One);
        Assert.NotEqual(N("-1e34"), N("-1e34") + Decimal128.One);
        Assert.Equal(N("-1e34"), N("-1e34") - Decimal128.One);
    }

    private static Decimal128 Sample(string startExpr, string endExpr, UInt128 draw)
    {
        var start = startExpr.Contains(' ') ? EvalConstant(startExpr) : N(startExpr);
        var end = endExpr.Contains(' ') ? EvalConstant(endExpr) : N(endExpr);
        var (source, remaining) = Draws(draw);
        var result = Evaluator.SampleUniformInteger(start, end, source);
        Assert.Equal(0, remaining());
        return result;
    }

    private static Decimal128 EvalConstant(string expression)
    {
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(expression).Root));
        Assert.False(result.IsError);
        return Assert.Single(result.Value);
    }

    // ── Domain validation and production wiring through the language surface ─

    [Theory]
    [InlineData("Math.RandomInt(2e34, 3e34)")]
    [InlineData("Math.RandomInt(0 - 3e34, 0)")]
    [InlineData("Math.RandomInt(0, 1e34 + 1e34)")]
    public void BoundsBeyondTheExactIntegerDomain_AreRejected(string source)
    {
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var illegal = Assert.IsType<EvalError.IllegalInEval>(error);
        Assert.Contains("must not exceed 1e34 in magnitude", illegal.Reason);
    }

    [Fact]
    public void BoundsAtTheExactIntegerBoundary_AreAccepted()
    {
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid("Math.RandomInt(1e34 - 1, 1e34)").Root));
        Assert.False(result.IsError);
        // Span 1: the only possible value, independent of the draw.
        Assert.Equal(N("9999999999999999999999999999999999"), Assert.Single(result.Value));
    }

    [Fact]
    public void NegativeLowerBoundAtTheExactIntegerBoundary_IsAccepted()
    {
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid("Math.RandomInt(0 - 1e34, (0 - 1e34) + 1)").Root));
        Assert.False(result.IsError);
        Assert.Equal(N("-1e34"), Assert.Single(result.Value));
    }

    [Theory]
    [InlineData("Math.RandomInt(Math.Sqrt(-1), 2)")]
    [InlineData("Math.RandomInt(0, 9e6144 * 10)")]
    [InlineData("Math.RandomInt(0 - 9e6144 * 10, 0)")]
    public void NonFiniteBounds_AreRejectedAsNonWholeNumbers(string source)
    {
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var illegal = Assert.IsType<EvalError.IllegalInEval>(error);
        Assert.Contains("bounds must be whole numbers", illegal.Reason);
    }

    [Fact]
    public void SignedZeroLowerBound_IsAcceptedAndProducesOrdinaryZeroForAUnitSpan()
    {
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid("Math.RandomInt(-0, 1)").Root));
        Assert.False(result.IsError);
        Assert.Equal(Decimal128.Zero, Assert.Single(result.Value));
    }

    [Fact]
    public void SeededSampler_HasStableBroadDistributionAcrossRepresentativeSpans()
    {
        foreach (var span in new[] { 3, 5, 6, 10, 17, 257 })
        {
            const int expectedPerBucket = 400;
            var source = new DeterministicUInt128Source(0xa0761d6478bd642fUL ^ (ulong)span);
            var counts = new int[span];
            for (var i = 0; i < span * expectedPerBucket; i++)
            {
                var value = Evaluator.SampleUniformInteger(Decimal128.Zero, (Decimal128)span, source.Next);
                counts[(int)value]++;
            }

            Assert.All(counts, count => Assert.True(count > 0));

            double chiSquare = 0;
            foreach (var count in counts)
            {
                var difference = count - expectedPerBucket;
                chiSquare += (double)(difference * difference) / expectedPerBucket;
            }

            // Fixed seed and a deliberately generous ~3x-degrees-of-freedom cap:
            // a gross mapping/wiring defect fails, while mathematical uniformity is
            // established by the exact cutoff tests rather than this finite sample.
            Assert.True(
                chiSquare < Math.Max(20, span * 3),
                $"span {span}: chi-square {chiSquare.ToString(CultureInfo.InvariantCulture)}");
        }
    }

    private sealed class DeterministicUInt128Source(ulong seed)
    {
        private ulong state = seed;

        public UInt128 Next()
            => ((UInt128)NextUInt64() << 64) | NextUInt64();

        private ulong NextUInt64()
        {
            state += 0x9e3779b97f4a7c15UL;
            var value = state;
            value = (value ^ (value >> 30)) * 0xbf58476d1ce4e5b9UL;
            value = (value ^ (value >> 27)) * 0x94d049bb133111ebUL;
            return value ^ (value >> 31);
        }
    }
}
