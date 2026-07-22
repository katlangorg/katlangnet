using System.Collections.Immutable;

namespace KatLang.ParserFuzz;

/// <summary>
/// Deterministic fuzz-byte decoder for the metamorphic target.
///
/// <para>Every dimension is selected from a small fixed TABLE by a reduced byte, so the
/// decoder is total (any byte string, including the empty one, maps to a valid parameter
/// point), allocates a constant amount, and can never be made to build a large collection by
/// an integer encoded in the input. Missing bytes read as zero, which is why a short or
/// malformed input still yields a valid compact case rather than being discarded.</para>
///
/// <para>The result is NORMALIZED: dimensions the selected limit mode does not use are
/// forced to their canonical index, so distinct byte strings that mean the same case decode
/// to one canonical parameter point and <c>Decode(Encode(p)) == p</c> holds.</para>
/// </summary>
internal static class MetamorphicDecoder
{
    // The tables are IMMUTABLE, not just readonly: the harness must have no static mutable
    // state at all, so nothing — not even a test — can retune a dimension for a later run.

    /// <summary>Phase 1 has exactly one trusted relation family.</summary>
    internal static readonly ImmutableArray<MetamorphicFamily> FamilyTable =
        [MetamorphicFamily.DottedCollectionCall];

    /// <summary>
    /// The <c>stop</c> bounds used for <c>range(1, stop)</c>. KatLang's range is INCLUSIVE
    /// and counts downward when <c>start &gt; stop</c>, so it always yields at least one
    /// element: there is no empty range, <c>range(1, 1)</c> (one item) is the smallest form,
    /// and <c>range(1, 0)</c> is the descending two-item case — the nearest thing to "N = 0".
    /// Negative stops cover the descending direction. The largest entry keeps Phase 1's
    /// generated collections small.
    /// </summary>
    internal static readonly ImmutableArray<int> RangeStopTable = [1, 0, 2, 3, 5, 8, -1, -3, 16, 33, 64, 100];

    internal static readonly ImmutableArray<MetamorphicLimitMode> LimitModeTable =
    [
        MetamorphicLimitMode.Default,
        MetamorphicLimitMode.CumulativeItems,
        MetamorphicLimitMode.PerCollectionItems,
        MetamorphicLimitMode.Both,
    ];

    /// <summary>Offsets from the template's expected total: just below, exactly at, just above, clear.</summary>
    internal static readonly ImmutableArray<int> OffsetTable = [-1, 0, 1, 4];

    /// <summary>Index of the canonical value used for a dimension the limit mode does not use.</summary>
    private const int UnusedOffsetIndex = 1;   // OffsetTable[1] == 0

    /// <summary>Largest collection cardinality any Phase 1 parameter point may generate.</summary>
    internal const int MaxPhase1Cardinality = 128;

    /// <summary>
    /// Maps arbitrary fuzz bytes to one normalized parameter point. Total and pure: the same
    /// bytes always produce the same result, and no input is rejected here — template
    /// preconditions, not decoding, decide whether a case is comparable.
    /// </summary>
    internal static MetamorphicParameters Decode(ReadOnlySpan<byte> input)
    {
        var familyIndex = Select(input, 0, FamilyTable.Length);
        var rangeStopIndex = Select(input, 1, RangeStopTable.Length);
        var limitModeIndex = Select(input, 2, LimitModeTable.Length);
        var cumulativeOffsetIndex = Select(input, 3, OffsetTable.Length);
        var perCollectionOffsetIndex = Select(input, 4, OffsetTable.Length);
        var optimizeIndex = Select(input, 5, 2);

        // Normalize unused dimensions so equivalent byte strings share one canonical case.
        var mode = LimitModeTable[limitModeIndex];
        if (mode is MetamorphicLimitMode.Default or MetamorphicLimitMode.PerCollectionItems)
            cumulativeOffsetIndex = UnusedOffsetIndex;
        if (mode is MetamorphicLimitMode.Default or MetamorphicLimitMode.CumulativeItems)
            perCollectionOffsetIndex = UnusedOffsetIndex;

        return new MetamorphicParameters(
            familyIndex, rangeStopIndex, limitModeIndex,
            cumulativeOffsetIndex, perCollectionOffsetIndex, optimizeIndex);
    }

    /// <summary>
    /// Reduces byte <paramref name="position"/> (zero when absent) into <c>[0, count)</c>.
    /// Checked arithmetic throughout; <paramref name="count"/> is a table length, never a
    /// value taken from the input.
    /// </summary>
    private static int Select(ReadOnlySpan<byte> input, int position, int count)
    {
        ArgumentOutOfRangeException.ThrowIfLessThan(count, 1);
        var raw = position < input.Length ? input[position] : (byte)0;
        return checked(raw % count);
    }
}
