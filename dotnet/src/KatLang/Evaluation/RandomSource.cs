using System.Buffers.Binary;

namespace KatLang.Evaluation;

/// <summary>
/// One evaluation run's stream of random words — the ONLY randomness the evaluator
/// consumes (<c>Math.Random</c> / <c>random</c> and <c>Math.RandomInt</c> /
/// <c>randomInt</c> share it in evaluation order). Owned by the run's
/// <see cref="EvaluationBudget"/>, so every copied <c>EvalCtx</c> reaches the same
/// stream and no nested call, callback, loop frame, or async resumption can reset
/// or duplicate it. Never static, never shared between runs, never locked: evaluator
/// access is sequential within one run (an async continuation may resume on another
/// thread, but never concurrently with the same run).
///
/// <para><see cref="NextUInt64"/> is the raw primitive; the bounded and 128-bit
/// derivations below are the ONE way those wider draws are composed, so their
/// consumption of raw words is part of the reproducible-stream contract
/// (<c>docs/design/seeded-randomness-2026-09.md</c>). They are virtual only so tests
/// can script each seam independently — the production source is the sealed
/// <see cref="SplitMix64RandomSource"/>, which inherits these derivations unchanged.</para>
/// </summary>
internal abstract class RandomSource
{
    /// <summary>The next raw 64-bit word of the stream.</summary>
    public abstract ulong NextUInt64();

    /// <summary>
    /// The next 128-bit word: two raw words, the FIRST drawn becoming the high half
    /// (<c>(hi &lt;&lt; 64) | lo</c>). The order is pinned — reversing it changes every
    /// seeded <c>Math.RandomInt</c> result.
    /// </summary>
    public virtual UInt128 NextUInt128()
    {
        var hi = NextUInt64();
        var lo = NextUInt64();
        return ((UInt128)hi << 64) | lo;
    }

    /// <summary>
    /// A uniform value in <c>[0, maxExclusive)</c> by REJECTION of the top incomplete
    /// cycle of the 64-bit range followed by modulo — never plain modulo, which biases
    /// every bound that does not divide 2^64. The count of rejected top draws is
    /// <c>2^64 mod bound</c> (computed as <c>(ulong.MaxValue % bound) + 1</c>, folded
    /// to zero when the bound divides 2^64 exactly); a draw above
    /// <c>ulong.MaxValue - rejected</c> is discarded and redrawn. Every accepted call
    /// consumes at least one raw word — a bound of 1 still consumes exactly one and
    /// returns 0 — because consumption is part of the reproducible-stream contract.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">
    /// <paramref name="maxExclusive"/> is not positive. Thrown BEFORE any word is
    /// consumed.
    /// </exception>
    public virtual long NextInt64Below(long maxExclusive)
    {
        if (maxExclusive <= 0)
        {
            throw new ArgumentOutOfRangeException(
                nameof(maxExclusive), maxExclusive, "The exclusive bound must be positive.");
        }

        var bound = (ulong)maxExclusive;
        var rejected = (ulong.MaxValue % bound) + 1;
        if (rejected == bound)
            rejected = 0;

        ulong draw;
        do
        {
            draw = NextUInt64();
        }
        while (rejected != 0 && draw > ulong.MaxValue - rejected);

        return (long)(draw % bound);
    }
}

/// <summary>
/// KatLang's production generator: SplitMix64 exactly as published by Vigna
/// (<c>splitmix64.c</c>) — the state is advanced by <c>0x9E3779B97F4A7C15</c> BEFORE
/// mixing, and the output is the advanced state mixed by
/// <c>z ^= z &gt;&gt; 30; z *= 0xBF58476D1CE4E5B9; z ^= z &gt;&gt; 27; z *= 0x94D049BB133111EB;
/// z ^= z &gt;&gt; 31</c>. A host seed becomes the initial state by the plain bit cast
/// <c>unchecked((ulong)seed)</c> — no folding, hashing, or truncation — so every
/// <see cref="long"/> names a distinct stream and <c>-5</c> and <c>5</c> differ.
/// The stream is reproducible for a given KatLang version across platforms; it is
/// NOT cryptographically secure and its exact values may change between KatLang
/// versions when the generator, the samplers, or evaluation order deliberately change.
/// </summary>
internal sealed class SplitMix64RandomSource : RandomSource
{
    private const ulong Increment = 0x9E3779B97F4A7C15UL;
    private const ulong Mixer1 = 0xBF58476D1CE4E5B9UL;
    private const ulong Mixer2 = 0x94D049BB133111EBUL;

    private ulong _state;

    /// <summary>Starts the stream at <paramref name="state"/> — the seed's bit pattern, or fresh entropy.</summary>
    public SplitMix64RandomSource(ulong state)
        => _state = state;

    public override ulong NextUInt64()
    {
        unchecked
        {
            _state += Increment;
            var z = _state;
            z = (z ^ (z >> 30)) * Mixer1;
            z = (z ^ (z >> 27)) * Mixer2;
            return z ^ (z >> 31);
        }
    }
}

/// <summary>
/// The ONE construction seam for a run's <see cref="RandomSource"/>: a supplied seed
/// selects that seed's stream and never consults entropy; an absent seed draws the
/// initial state from the supplied entropy provider exactly once. The provider is a
/// plain parameter — there is no static, thread-local, ambient, or settable default —
/// so a test scripts entropy by passing its own provider and production passes
/// <see cref="AcquireProductionEntropy"/>.
/// </summary>
internal static class RandomSourceFactory
{
    /// <summary>Production entropy provider, held once so budget construction allocates no delegate.</summary>
    internal static readonly Func<ulong> ProductionEntropy = AcquireProductionEntropy;

    internal static RandomSource Create(long? seed, Func<ulong> entropyProvider)
    {
        ArgumentNullException.ThrowIfNull(entropyProvider);
        return new SplitMix64RandomSource(seed is { } value ? unchecked((ulong)value) : entropyProvider());
    }

    /// <summary>
    /// Eight bytes from the runtime's shared generator, read as one little-endian 64-bit
    /// state. <see cref="Random.NextBytes(Span{byte})"/> rather than
    /// <see cref="Random.NextInt64()"/>: the latter never returns the full 64-bit domain,
    /// and an unseeded run should be able to start at any of the 2^64 states a seed can
    /// name. This is the ONLY place the evaluator touches <see cref="Random.Shared"/>;
    /// every later draw comes from the run's own SplitMix64 stream.
    /// </summary>
    internal static ulong AcquireProductionEntropy()
    {
        Span<byte> bytes = stackalloc byte[8];
        Random.Shared.NextBytes(bytes);
        return BinaryPrimitives.ReadUInt64LittleEndian(bytes);
    }
}
