using System.Globalization;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Deterministic coverage for the exact 10^34-point fraction lattice used by
/// <c>Math.Random</c>. The injected bounded source exercises the same production
/// composition helper without depending on <see cref="Random.Shared"/> luck.
/// </summary>
public class RandomFractionSamplingTests
{
    private const long ComponentBound = 100_000_000_000_000_000;

    private static Decimal128 N(string text)
        => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);

    private static Decimal128 Sample(params long[] components)
    {
        var queue = new Queue<long>(components);
        var result = Evaluator.SampleRandomUnitFraction(maxExclusive =>
        {
            Assert.Equal(ComponentBound, maxExclusive);
            return queue.Dequeue();
        });
        Assert.Empty(queue);
        return result;
    }

    [Fact]
    public void NullComponentSource_IsRejected()
        => Assert.Throws<ArgumentNullException>(() => Evaluator.SampleRandomUnitFraction(null!));

    [Theory]
    [InlineData(-1, 0)]
    [InlineData(ComponentBound, 0)]
    [InlineData(0, -1)]
    [InlineData(0, ComponentBound)]
    public void ComponentSource_MustHonorEachRequestedHalfOpenBound(long high, long low)
        => Assert.Throws<InvalidOperationException>(() => Sample(high, low));

    [Theory]
    [InlineData(0, 0, "0")]
    [InlineData(0, 1, "1e-34")]
    [InlineData(1, 0, "1e-17")]
    [InlineData(ComponentBound - 1, ComponentBound - 1, "0.9999999999999999999999999999999999")]
    public void ComponentEndpoints_ComposeToTheExactExpectedFraction(
        long high, long low, string expected)
        => Assert.Equal(N(expected), Sample(high, low));

    [Fact]
    public void UnitFractionEndpoints_AreZeroInclusiveAndOneExclusive()
    {
        var minimum = Sample(0, 0);
        var maximum = Sample(ComponentBound - 1, ComponentBound - 1);

        Assert.Equal(Decimal128.Zero, minimum);
        Assert.True(maximum < Decimal128.One);
        Assert.Equal(N("1e-34"), Decimal128.One - maximum);
    }

    [Fact]
    public void LowComponent_ChangesDigitsBeyondTheHighComponentAndDoublePrecision()
    {
        var highOnly = Sample(ComponentBound - 1, 0);
        var withLowestLowDigit = Sample(ComponentBound - 1, 1);

        // A binary64/NextDouble-style path cannot retain a 1e-34 change near 1.
        Assert.NotEqual(highOnly, withLowestLowDigit);
        Assert.Equal(N("1e-34"), withLowestLowDigit - highOnly);
    }

    [Theory]
    [InlineData("2", "6", "0", "2")]
    [InlineData("2", "6", "0.25", "3")]
    [InlineData("2", "6", "0.5", "4")]
    [InlineData("-7", "5", "0.75", "2")]
    public void UnitFractionScaling_MapsIntoTheRequestedRange(
        string start,
        string end,
        string unitFraction,
        string expected)
        => Assert.Equal(
            N(expected),
            Evaluator.ScaleRandomUnitFractionToHalfOpenRange(
                N(start), N(end), N(unitFraction)));

    [Fact]
    public void UnitFractionScaling_RoundsAnAccidentalUpperEndpointBackToStart()
    {
        // The production source is one-exclusive. This guard protects the
        // half-open contract even if Decimal128 range scaling rounds upward.
        Assert.Equal(
            N("2"),
            Evaluator.ScaleRandomUnitFractionToHalfOpenRange(N("2"), N("6"), Decimal128.One));
    }

    [Fact]
    public void ProductionUInt128Source_IsNotStuckAtZero()
    {
        var draws = Enumerable.Range(0, 16).Select(_ => Evaluator.NextRandomUInt128()).ToArray();
        Assert.Contains(draws, draw => draw != UInt128.Zero);
    }

    [Fact]
    public void SeededFractions_HaveBroadStableCoverageAndMeanNearOneHalf()
    {
        const int sampleCount = 100_000;
        const int binCount = 20;
        var source = new DeterministicBoundedInt64Source(0x4d595df4d0f33173UL);
        var bins = new int[binCount];
        var highComponents = new HashSet<Int128>();
        var lowComponents = new HashSet<Int128>();
        var scale = Decimal128.ScaleB(Decimal128.One, 34);
        Decimal128 sum = Decimal128.Zero;

        for (var i = 0; i < sampleCount; i++)
        {
            var value = Evaluator.SampleRandomUnitFraction(source.Next);
            Assert.True(value >= Decimal128.Zero && value < Decimal128.One);

            sum += value;
            bins[(int)Decimal128.Floor(value * binCount)]++;

            var latticeInteger = (Int128)(value * scale);
            highComponents.Add(latticeInteger / ComponentBound);
            lowComponents.Add(latticeInteger % ComponentBound);
        }

        // Fixed seed, deliberately generous thresholds: this is a smoke test for
        // gross composition/wiring mistakes, not the proof of uniformity. The
        // bijective hi/lo construction and bounded-source contracts provide that.
        Assert.All(bins, count => Assert.InRange(count, 4_500, 5_500));
        Assert.True(Decimal128.Abs((sum / sampleCount) - N("0.5")) < N("0.01"));
        Assert.True(highComponents.Count > 99_000);
        Assert.True(lowComponents.Count > 99_000);
    }

    /// <summary>
    /// Stable SplitMix64 byte source plus exact bounded rejection. This test-only
    /// generator is deterministic across runtime versions and never uses binary
    /// floating-point scaling.
    /// </summary>
    private sealed class DeterministicBoundedInt64Source(ulong seed)
    {
        private ulong state = seed;

        public long Next(long maxExclusive)
        {
            var span = (ulong)maxExclusive;
            var rejectedCount = (ulong.MaxValue % span) + 1;
            if (rejectedCount == span)
                rejectedCount = 0;

            ulong draw;
            do
            {
                draw = NextUInt64();
            }
            while (rejectedCount != 0 && draw > ulong.MaxValue - rejectedCount);

            return (long)(draw % span);
        }

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
