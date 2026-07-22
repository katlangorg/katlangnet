using System.Collections.Immutable;

namespace KatLang.ParserFuzz;

/// <summary>
/// Deterministic fuzz-byte decoder for the metamorphic target.
///
/// <para>Every dimension is selected from a small fixed TABLE by a reduced byte, so the
/// decoder is total (any byte string, including the empty one, maps to a valid parameter
/// point), allocates a constant amount, and can never be made to build a large collection by
/// an integer encoded in the input. Missing bytes read as zero, which is why a short or
/// malformed input still yields a valid compact case rather than being discarded. It reads
/// only a bounded prefix — at most <see cref="MaxPayloadLength"/> bytes — however long the
/// input is.</para>
///
/// <para><b>Version-zero compatibility.</b> A payload of
/// <see cref="MetamorphicParameters.CommonPayloadLength"/> bytes or fewer always resolves to
/// the Phase 1 family with the Phase 1 tables. Phase 1's family table had a single entry, so
/// byte 0 could not select anything else; forcing the family for short payloads reproduces
/// that exactly. Every tracked Phase 1 seed and every six-byte payload therefore decodes to
/// precisely the case it decoded to before.</para>
///
/// <para>The result is NORMALIZED: dimensions the selected limit mode or family does not use
/// are forced to their canonical index, so distinct byte strings that mean the same case
/// decode to one canonical parameter point and <c>Decode(Encode(p)) == p</c> holds.</para>
/// </summary>
internal static class MetamorphicDecoder
{
    // The tables are IMMUTABLE, not just readonly: the harness must have no static mutable
    // state at all, so nothing — not even a test — can retune a dimension for a later run.

    /// <summary>Registered families in payload order; index 0 is frozen as the Phase 1 family.</summary>
    internal static readonly ImmutableArray<MetamorphicFamily> FamilyTable =
        [.. MetamorphicFamilyRegistry.All.Select(static definition => definition.Family)];

    /// <summary>
    /// The <c>stop</c> bounds used by the Phase 1 family's <c>range(1, stop)</c>. KatLang's
    /// range is INCLUSIVE and counts downward when <c>start &gt; stop</c>, so it always yields
    /// at least one element: there is no empty range, <c>range(1, 1)</c> (one item) is the
    /// smallest form, and <c>range(1, 0)</c> is the descending two-item case. FROZEN: changing
    /// this table would change what an existing six-byte payload means.
    /// </summary>
    internal static readonly ImmutableArray<int> RangeStopTable = [1, 0, 2, 3, 5, 8, -1, -3, 16, 33, 64, 100];

    /// <summary>Offsets from a measured total: just below, exactly at, just above, clear. FROZEN.</summary>
    internal static readonly ImmutableArray<int> OffsetTable = [-1, 0, 1, 4];

    /// <summary>Index of the canonical value used for a dimension the limit mode does not use.</summary>
    private const int UnusedOffsetIndex = 1;   // OffsetTable[1] == 0

    /// <summary>Largest collection cardinality any Phase 1 parameter point may generate.</summary>
    internal const int MaxPhase1Cardinality = 128;

    /// <summary>Bytes the decoder will ever read, regardless of input length.</summary>
    internal static readonly int MaxPayloadLength =
        MetamorphicParameters.CommonPayloadLength + MetamorphicParameters.MaxExtraDimensions;

    /// <summary>
    /// Maps arbitrary fuzz bytes to one normalized parameter point. Total and pure: the same
    /// bytes always produce the same result, and no input is rejected here — template
    /// preconditions, not decoding, decide whether a case is comparable.
    /// </summary>
    internal static MetamorphicParameters Decode(ReadOnlySpan<byte> input)
    {
        // Version zero: six bytes or fewer means the Phase 1 family, byte 0 ignored.
        var familyIndex = input.Length <= MetamorphicParameters.CommonPayloadLength
            ? 0
            : Select(input, 0, FamilyTable.Length);

        var definition = MetamorphicFamilyRegistry.Get(FamilyTable[familyIndex]);

        // Byte 1 belongs to the Phase 1 family; every other family normalizes it away.
        var legacyRangeStopIndex = definition.UsesLegacyRangeStop ? Select(input, 1, RangeStopTable.Length) : 0;

        var limitModeIndex = Select(input, 2, definition.SupportedLimitModes.Length);
        var primaryOffsetIndex = Select(input, 3, OffsetTable.Length);
        var secondaryOffsetIndex = Select(input, 4, OffsetTable.Length);
        var optimizeIndex = definition.SupportsOptimizerPolicy ? Select(input, 5, 2) : 0;

        // Normalize the offsets the selected mode does not use, so equivalent byte strings
        // share one canonical case. Modes 0-3 keep exactly the Phase 1 rule.
        var mode = definition.SupportedLimitModes[limitModeIndex];
        if (!UsesPrimaryOffset(mode)) primaryOffsetIndex = UnusedOffsetIndex;
        if (!UsesSecondaryOffset(mode)) secondaryOffsetIndex = UnusedOffsetIndex;

        var parameters = new MetamorphicParameters(
            familyIndex, legacyRangeStopIndex, limitModeIndex,
            primaryOffsetIndex, secondaryOffsetIndex, optimizeIndex);

        for (var i = 0; i < definition.ExtraDimensionCount; i++)
        {
            parameters = parameters.WithExtra(
                i,
                Select(input, MetamorphicParameters.CommonPayloadLength + i, definition.ExtraDimensionSizes[i]));
        }

        // Family-specific refinement: a dimension whose legal range depends on another
        // dimension (a builtin's suffix-variant count, a consumer's callback arity) is reduced
        // here rather than by a coarser per-byte modulus, so the canonical form is unique.
        return definition.Normalize(parameters);
    }

    /// <summary>True when <paramref name="mode"/> configures a limit from the PRIMARY offset byte.</summary>
    internal static bool UsesPrimaryOffset(MetamorphicLimitMode mode) => mode
        is MetamorphicLimitMode.CumulativeItems
        or MetamorphicLimitMode.Both
        or MetamorphicLimitMode.CumulativeStrings;

    /// <summary>True when <paramref name="mode"/> configures a limit from the SECONDARY offset byte.</summary>
    internal static bool UsesSecondaryOffset(MetamorphicLimitMode mode) => mode
        is MetamorphicLimitMode.PerCollectionItems
        or MetamorphicLimitMode.Both
        or MetamorphicLimitMode.PerStringLength;

    /// <summary>
    /// Reduces byte <paramref name="position"/> (zero when absent) into <c>[0, count)</c>.
    /// Checked arithmetic throughout; <paramref name="count"/> is a table length, never a
    /// value taken from the input.
    /// </summary>
    internal static int Select(ReadOnlySpan<byte> input, int position, int count)
    {
        ArgumentOutOfRangeException.ThrowIfLessThan(count, 1);
        var raw = position < input.Length ? input[position] : (byte)0;
        return checked(raw % count);
    }
}
