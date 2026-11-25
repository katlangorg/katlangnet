using System.Globalization;
using System.Numerics;
using KatLang.Evaluation;

namespace KatLang.Tests.Randomness;

/// <summary>
/// Test-side, INDEPENDENT re-derivation of KatLang's documented random contract
/// (<c>docs/design/seeded-randomness-2026-09.md</c>): the SplitMix64 word stream, the
/// 64-bit bounded rejection sampler, the 128-bit composition, the 10^34-lattice unit
/// fraction, the half-open scaling, and the 128-bit integer rejection sampler. Nothing
/// here calls the production <see cref="RandomSource"/> family or the evaluator's
/// sampling helpers: the arithmetic is written from the specification with
/// <see cref="BigInteger"/> (2^64 and 2^128 are represented explicitly rather than
/// computed by wrap-around), so a seeded evaluator result can be cross-checked
/// against an expectation the implementation had no hand in producing.
/// </summary>
internal sealed class ReferenceSplitMix64(ulong state)
{
    private ulong _state = state;

    /// <summary>The seed → initial-state map of the contract: the plain bit cast.</summary>
    public static ulong StateOf(long seed) => unchecked((ulong)seed);

    /// <summary>
    /// One SplitMix64 output (Vigna, <c>splitmix64.c</c>): advance by the golden-ratio
    /// increment FIRST, then mix the advanced state.
    /// </summary>
    public ulong Next()
    {
        unchecked
        {
            _state += 0x9E3779B97F4A7C15UL;
            var z = _state;
            z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
            z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
            return z ^ (z >> 31);
        }
    }
}

/// <summary>
/// A <see cref="RandomSource"/> whose EVERY seam is the reference derivation: raw words
/// from <see cref="ReferenceSplitMix64"/>, bounded draws and 128-bit composition from
/// <see cref="ReferenceRandomOracle"/>. Handing it to the production samplers exercises
/// their composition over independently produced inputs.
/// </summary>
internal sealed class ReferenceRandomSource(ulong state) : RandomSource
{
    private readonly ReferenceSplitMix64 _words = new(state);

    public override ulong NextUInt64() => _words.Next();

    public override UInt128 NextUInt128() => ReferenceRandomOracle.ComposeUInt128(_words);

    public override long NextInt64Below(long maxExclusive) => ReferenceRandomOracle.BoundedInt64(_words, maxExclusive);
}

internal static class ReferenceRandomOracle
{
    private static readonly BigInteger TwoPow64 = BigInteger.One << 64;
    private static readonly BigInteger TwoPow128 = BigInteger.One << 128;
    private static readonly BigInteger ComponentBound = BigInteger.Pow(10, 17);

    /// <summary>
    /// Uniform <c>[0, maxExclusive)</c>: reject every raw word in the top incomplete
    /// cycle — the highest <c>2^64 mod bound</c> values — then reduce modulo the bound.
    /// The cutoff is computed with an explicit 2^64, independently of the production
    /// <c>(ulong.MaxValue % bound) + 1</c> formulation.
    /// </summary>
    public static long BoundedInt64(ReferenceSplitMix64 words, long maxExclusive)
    {
        Assert.True(maxExclusive > 0);
        var bound = new BigInteger(maxExclusive);
        var rejectedCount = TwoPow64 % bound;
        var firstRejected = TwoPow64 - rejectedCount;

        while (true)
        {
            var draw = new BigInteger(words.Next());
            if (draw < firstRejected)
                return (long)(draw % bound);
        }
    }

    /// <summary>Two raw words; the first drawn is the HIGH half.</summary>
    public static UInt128 ComposeUInt128(ReferenceSplitMix64 words)
    {
        var hi = words.Next();
        var lo = words.Next();
        return new UInt128(hi, lo);
    }

    /// <summary>
    /// Uniform <c>[0, span)</c> over 128-bit draws with the same top-cycle rejection,
    /// the cutoff computed with an explicit 2^128.
    /// </summary>
    public static BigInteger UniformBelow(ReferenceSplitMix64 words, BigInteger span)
    {
        Assert.True(span > 0);
        var rejectedCount = TwoPow128 % span;
        var firstRejected = TwoPow128 - rejectedCount;

        while (true)
        {
            var draw = (BigInteger)ComposeUInt128(words);
            if (draw < firstRejected)
                return draw % span;
        }
    }

    /// <summary>
    /// The unit fraction of one <c>Math.Random</c> call: HIGH component, then LOW, each
    /// an exact bounded 17-digit draw; the lattice integer <c>high * 10^17 + low</c>
    /// times <c>10^-34</c>, formed here by parsing the exact decimal text rather than
    /// by the production's Decimal128 multiply-add.
    /// </summary>
    public static Decimal128 UnitFraction(ReferenceSplitMix64 words)
    {
        var high = new BigInteger(BoundedInt64(words, 100_000_000_000_000_000));
        var low = new BigInteger(BoundedInt64(words, 100_000_000_000_000_000));
        var lattice = (high * ComponentBound) + low;
        return Decimal128.Parse(
            lattice.ToString(CultureInfo.InvariantCulture) + "E-34",
            NumberStyles.Float,
            CultureInfo.InvariantCulture);
    }

    /// <summary>
    /// One <c>Math.Random(start, end)</c> result: the documented half-open scaling
    /// <c>start + fraction * (end - start)</c> in Decimal128, an accidental upper
    /// endpoint folding back to <c>start</c>.
    /// </summary>
    public static Decimal128 Random(ReferenceSplitMix64 words, Decimal128 start, Decimal128 end)
    {
        var scaled = start + (UnitFraction(words) * (end - start));
        return scaled >= end ? start : scaled;
    }

    /// <summary>One <c>Math.RandomInt(start, end)</c> result over the exact integer span.</summary>
    public static Decimal128 RandomInt(ReferenceSplitMix64 words, BigInteger start, BigInteger end)
    {
        var value = start + UniformBelow(words, end - start);
        return Decimal128.Parse(value.ToString(CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture);
    }
}
