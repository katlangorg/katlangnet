using System.Numerics;
using KatLang.Evaluation;

namespace KatLang.Tests.Randomness;

/// <summary>
/// The exact internal stream contract of <c>docs/design/seeded-randomness-2026-09.md</c>,
/// pinned against oracles the production code had no hand in: published SplitMix64
/// known-answer data, an independent BigInteger derivation, and the test-side
/// <see cref="ReferenceSplitMix64"/> re-implementation. Nothing here obtains an
/// expected value by running the production <see cref="RandomSource"/> family.
/// </summary>
public class RandomSourceTests
{
    // ── SplitMix64 known-answer vectors ───────────────────────────────────────
    //
    // Provenance. Seed 0 is the canonical published output of Vigna's splitmix64.c
    // (the first five words — E220A8397B1DCDAF, 6E789E6AA1B965F4, 06C45D188009454F,
    // F88BB8A8724C81EC, 1B39896A51A8749B — are the reference vectors reproduced by
    // the xoshiro/xoroshiro test suites and the rand_xoshiro crate documentation).
    // Every seed below was ALSO derived by an independent BigInteger PowerShell
    // script (state and products masked to 2^64 explicitly, never by CLR wrap-around),
    // which reproduced the published seed-0 words exactly — so the same script's
    // outputs for the remaining seeds are trusted by that anchor. The constants were
    // typed in from that script's output, not captured from SplitMix64RandomSource.

    public static TheoryData<long, ulong[]> KnownAnswerVectors => new()
    {
        {
            0L,
            [0xE220A8397B1DCDAFUL, 0x6E789E6AA1B965F4UL, 0x06C45D188009454FUL, 0xF88BB8A8724C81ECUL, 0x1B39896A51A8749BUL, 0x53CB9F0C747EA2EAUL]
        },
        {
            1L,
            [0x910A2DEC89025CC1UL, 0xBEEB8DA1658EEC67UL, 0xF893A2EEFB32555EUL, 0x71C18690EE42C90BUL, 0x71BB54D8D101B5B9UL, 0xC34D0BFF90150280UL]
        },
        {
            -1L,
            [0xE4D971771B652C20UL, 0xE99FF867DBF682C9UL, 0x382FF84CB27281E9UL, 0x6D1DB36CCBA982D2UL, 0xB4A0472E578069AEUL, 0xD31DADBDA438BB33UL]
        },
        {
            long.MinValue,
            [0x481EC0A212A9F3DBUL, 0xC46FA638A6309012UL, 0x61A685FFC80A8140UL, 0x592E268383E356F9UL, 0x0C8881EE746884D3UL, 0x4D7E6A268A67C5FFUL]
        },
        {
            long.MaxValue,
            [0x2A67D7552E039EA7UL, 0xF20C01408082F947UL, 0xEC159351AF424190UL, 0x2020319894995BFBUL, 0x532168FD38C3F6CBUL, 0x1CD287CC27FEE113UL]
        },
    };

    [Theory]
    [MemberData(nameof(KnownAnswerVectors))]
    public void SplitMix64_ProducesThePublishedKnownAnswerWords(long seed, ulong[] expected)
    {
        var source = RandomSourceFactory.Create(seed, ThrowingEntropy);

        var actual = new ulong[expected.Length];
        for (var i = 0; i < actual.Length; i++)
            actual[i] = source.NextUInt64();

        Assert.Equal(expected, actual);
    }

    [Theory]
    [MemberData(nameof(KnownAnswerVectors))]
    public void KnownAnswerVectors_AgreeWithTheTestSideReferenceImplementation(long seed, ulong[] expected)
    {
        // Independent second oracle for the same constants: the test-side SplitMix64.
        var reference = new ReferenceSplitMix64(ReferenceSplitMix64.StateOf(seed));
        foreach (var word in expected)
            Assert.Equal(word, reference.Next());
    }

    [Theory]
    [InlineData(2L)]
    [InlineData(-2L)]
    [InlineData(42L)]
    [InlineData(-9_000_000_000L)]
    [InlineData(0x7F00_0000_0000_0001L)]
    public void SplitMix64_MatchesTheReferenceStream_ForFurtherSeeds(long seed)
    {
        var production = RandomSourceFactory.Create(seed, ThrowingEntropy);
        var reference = new ReferenceSplitMix64(ReferenceSplitMix64.StateOf(seed));

        for (var i = 0; i < 256; i++)
            Assert.Equal(reference.Next(), production.NextUInt64());
    }

    // ── Seed → state ───────────────────────────────────────────────────────────

    [Fact]
    public void SeedBitPattern_IsTheInitialState_NeverFoldedOrTruncated()
    {
        // Seed -1 has the bit pattern 0xFFFF_FFFF_FFFF_FFFF; folding, |seed|, or an int
        // truncation would all land on a different stream than the pinned -1 vector.
        // The stream started explicitly at state ulong.MaxValue must equal it.
        var fromSeed = RandomSourceFactory.Create(-1L, ThrowingEntropy);
        var fromState = new SplitMix64RandomSource(ulong.MaxValue);
        for (var i = 0; i < 8; i++)
            Assert.Equal(fromState.NextUInt64(), fromSeed.NextUInt64());
    }

    [Fact]
    public void NegativeAndPositiveSeedsOfTheSameMagnitude_NameDifferentStreams()
    {
        var negative = RandomSourceFactory.Create(-5L, ThrowingEntropy);
        var positive = RandomSourceFactory.Create(5L, ThrowingEntropy);

        Assert.NotEqual(negative.NextUInt64(), positive.NextUInt64());
    }

    [Fact]
    public void ExtremeSeeds_AreValidAndDistinct()
    {
        var first = RandomSourceFactory.Create(long.MinValue, ThrowingEntropy).NextUInt64();
        var second = RandomSourceFactory.Create(long.MaxValue, ThrowingEntropy).NextUInt64();
        var zero = RandomSourceFactory.Create(0L, ThrowingEntropy).NextUInt64();

        Assert.NotEqual(first, second);
        Assert.NotEqual(first, zero);
        Assert.NotEqual(second, zero);
    }

    // ── 128-bit composition ────────────────────────────────────────────────────

    [Fact]
    public void NextUInt128_ComposesTheFirstWordAsTheHighHalf()
    {
        var source = new ScriptedWordSource(0x0123_4567_89AB_CDEFUL, 0xFEDC_BA98_7654_3210UL);

        var value = source.NextUInt128();

        Assert.Equal(new UInt128(0x0123_4567_89AB_CDEFUL, 0xFEDC_BA98_7654_3210UL), value);
        Assert.Equal(0, source.Remaining);
    }

    [Fact]
    public void NextUInt128_OverTheSeededStream_IsHiThenLoOfConsecutiveWords()
    {
        // Seed 0: words 1 and 2 of the published vector form the first 128-bit draw.
        var source = RandomSourceFactory.Create(0L, ThrowingEntropy);
        Assert.Equal(new UInt128(0xE220A8397B1DCDAFUL, 0x6E789E6AA1B965F4UL), source.NextUInt128());
        Assert.Equal(new UInt128(0x06C45D188009454FUL, 0xF88BB8A8724C81ECUL), source.NextUInt128());
    }

    // ── Bounded rejection ──────────────────────────────────────────────────────

    private static readonly BigInteger TwoPow64 = BigInteger.One << 64;

    /// <summary>Largest ACCEPTED raw word for a bound, from an explicit 2^64.</summary>
    private static ulong CutoffOf(long bound)
        => (ulong)(TwoPow64 - (TwoPow64 % bound) - 1);

    [Theory]
    [InlineData(3L)]
    [InlineData(6L)]
    [InlineData(10L)]
    [InlineData(257L)]
    [InlineData(100_000_000_000_000_000L)] // the Math.Random component bound, 2^64 mod 1e17 = 46744073709551616
    [InlineData(long.MaxValue)]            // 2^64 mod (2^63 - 1) = 2
    public void NextInt64Below_RejectsExactlyTheTopIncompleteCycle(long bound)
    {
        var cutoff = CutoffOf(bound);
        var rejectedCount = (ulong)(TwoPow64 % bound);
        Assert.NotEqual(0UL, rejectedCount);
        Assert.Equal(ulong.MaxValue - rejectedCount, cutoff);

        // The largest accepted word is accepted (and maps by modulo)...
        var accepted = new ScriptedWordSource(cutoff);
        Assert.Equal((long)(cutoff % (ulong)bound), accepted.NextInt64Below(bound));
        Assert.Equal(0, accepted.Remaining);

        // ...and every word above it is rejected until an accepted one arrives.
        var rejectedWords = new List<ulong> { cutoff + 1, ulong.MaxValue };
        var rejectingThenSeven = new ScriptedWordSource(rejectedWords.Append(7UL));
        Assert.Equal(7 % bound, rejectingThenSeven.NextInt64Below(bound));
        Assert.Equal(0, rejectingThenSeven.Remaining);
    }

    [Theory]
    [InlineData(1L)]
    [InlineData(2L)]
    [InlineData(1L << 32)]
    [InlineData(1L << 62)]
    public void NextInt64Below_NeverRejectsForBoundsDividingTwoToThe64(long bound)
    {
        Assert.Equal(BigInteger.Zero, TwoPow64 % bound);

        var source = new ScriptedWordSource(ulong.MaxValue, 0UL);
        Assert.Equal((long)(ulong.MaxValue % (ulong)bound), source.NextInt64Below(bound));
        Assert.Equal(0L, source.NextInt64Below(bound));
        Assert.Equal(0, source.Remaining);
    }

    [Fact]
    public void NextInt64Below_BoundOne_ConsumesExactlyOneWordAndReturnsZero()
    {
        // Consumption is part of the stream contract: skipping the draw for a unit
        // bound would shift every later value.
        var source = new ScriptedWordSource(0xDEAD_BEEFUL, 0x1234UL);

        Assert.Equal(0L, source.NextInt64Below(1));
        Assert.Equal(1, source.Remaining);
        Assert.Equal(0x1234UL, source.NextUInt64());
    }

    [Theory]
    [InlineData(0L)]
    [InlineData(-1L)]
    [InlineData(long.MinValue)]
    public void NextInt64Below_InvalidBound_ThrowsBeforeConsumingAnyWord(long bound)
    {
        var source = new ScriptedWordSource(1UL, 2UL);

        Assert.Throws<ArgumentOutOfRangeException>(() => source.NextInt64Below(bound));
        Assert.Equal(2, source.Remaining);
    }

    [Fact]
    public void NextInt64Below_OverTheSeededStream_MatchesTheReferenceSampler()
    {
        var production = RandomSourceFactory.Create(12345L, ThrowingEntropy);
        var reference = new ReferenceSplitMix64(ReferenceSplitMix64.StateOf(12345L));

        foreach (var bound in new[] { 1L, 3L, 6L, 1000L, 100_000_000_000_000_000L, long.MaxValue, 1L << 40 })
        {
            for (var i = 0; i < 64; i++)
                Assert.Equal(ReferenceRandomOracle.BoundedInt64(reference, bound), production.NextInt64Below(bound));
        }
    }

    // ── Factory / entropy seam ────────────────────────────────────────────────

    [Fact]
    public void FractionRejections_KeepHighBeforeLow_AndLeaveTheNextDrawAtTheExpectedWord()
    {
        const long bound = 100_000_000_000_000_000;
        var source = new ScriptedWordSource(
            ulong.MaxValue, CutoffOf(bound) + 1, 17UL,
            ulong.MaxValue, 23UL,
            0x0123_4567_89AB_CDEFUL, 0xFEDC_BA98_7654_3210UL);

        // Two rejected high words, then one rejected low word. The accepted
        // lattice integer is exactly 17 * 10^17 + 23, scaled by 10^-34.
        var fraction = Evaluator.SampleRandomUnitFraction(source);
        Assert.Equal(SeededRun.D("1.700000000000000023E-16"), fraction);
        Assert.Equal(2, source.Remaining);
        Assert.Equal(new UInt128(0x0123_4567_89AB_CDEFUL, 0xFEDC_BA98_7654_3210UL), source.NextUInt128());
        Assert.Equal(0, source.Remaining);
    }

    [Fact]
    public void SuppliedSeed_BypassesTheEntropyProvider()
    {
        var consulted = 0;
        var source = RandomSourceFactory.Create(7L, () => { consulted++; return 99UL; });

        source.NextUInt64();
        Assert.Equal(0, consulted);
        Assert.Equal(new ReferenceSplitMix64(7UL).Next(), RandomSourceFactory.Create(7L, ThrowingEntropy).NextUInt64());
    }

    [Fact]
    public void UnseededCreation_ConsultsTheEntropyProviderExactlyOnce_AndUsesItsBitsAsTheInitialState()
    {
        const ulong scriptedEntropy = 0xC0FF_EE00_1234_5678UL;
        var consulted = 0;
        var source = RandomSourceFactory.Create(null, () => { consulted++; return scriptedEntropy; });

        Assert.Equal(1, consulted);

        // The scripted bits are the SplitMix64 initial state exactly: the stream equals
        // the reference stream started at that state (which is also the seed
        // unchecked((long)scriptedEntropy) would select).
        var reference = new ReferenceSplitMix64(scriptedEntropy);
        for (var i = 0; i < 16; i++)
            Assert.Equal(reference.Next(), source.NextUInt64());

        Assert.Equal(1, consulted);
    }

    [Fact]
    public void Factory_RejectsANullEntropyProvider_EvenWhenASeedWouldBypassIt()
    {
        Assert.Throws<ArgumentNullException>(() => RandomSourceFactory.Create(null, null!));
        Assert.Throws<ArgumentNullException>(() => RandomSourceFactory.Create(1L, null!));
    }

    [Fact]
    public void ProductionEntropy_IsNotAFixedDefault()
    {
        // The ONE coarse unseeded sanity check: sixteen entropy acquisitions cannot all
        // agree unless the provider is stuck (2^-960 by chance).
        var samples = Enumerable.Range(0, 16).Select(_ => RandomSourceFactory.AcquireProductionEntropy()).ToArray();
        Assert.True(samples.Distinct().Count() > 1, "Random.Shared-backed entropy returned one constant value.");
    }

    // ── Helpers ────────────────────────────────────────────────────────────────

    private static readonly Func<ulong> ThrowingEntropy =
        () => throw new InvalidOperationException("A seeded source must never consult entropy.");

    /// <summary>
    /// Scripts the RAW seam only: the production bounded and 128-bit derivations run
    /// unchanged over the scripted words, so what is under test is exactly how many
    /// words they consume and how they combine them.
    /// </summary>
    private sealed class ScriptedWordSource(IEnumerable<ulong> words) : RandomSource
    {
        private readonly Queue<ulong> _words = new(words);

        public ScriptedWordSource(params ulong[] words) : this((IEnumerable<ulong>)words) { }

        public int Remaining => _words.Count;

        public override ulong NextUInt64() => _words.Dequeue();
    }
}
