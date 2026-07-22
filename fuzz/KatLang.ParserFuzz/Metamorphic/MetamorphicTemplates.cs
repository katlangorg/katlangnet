using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// Trusted templates: the only place a metamorphic pair is created.
///
/// <para>A template owns an EQUIVALENCE ARGUMENT, not a rewriting. Each registered family
/// CONSTRUCTS both members from the same parameters, so the comparison is trustworthy without
/// any semantic analysis of the generated text. This type owns the shared entry points —
/// parameter validation, registry dispatch, and the Phase 1 family — while each Phase 2 family
/// lives in its own template alongside the argument that justifies it.</para>
/// </summary>
internal static class MetamorphicTemplates
{
    /// <summary>
    /// Items <c>range(1, stop)</c> materializes. KatLang's range is inclusive and counts
    /// downward when <c>start &gt; stop</c>, so the cardinality is the inclusive distance
    /// from 1 and is never zero.
    /// </summary>
    internal static long RangeCardinality(int rangeStop)
        => checked(Math.Abs((long)rangeStop - 1L) + 1L);

    /// <summary>Instantiates the template selected by <paramref name="parameters"/>.</summary>
    internal static MetamorphicCase Build(MetamorphicParameters parameters)
    {
        // Only decoder output is a legal input here: every index must already name a table
        // entry, so a hand-built parameter point fails loudly instead of silently reading
        // past a table or fabricating an untrusted pair.
        EnsureDecoderProduced(parameters);
        return MetamorphicFamilyRegistry.Get(parameters.Family).Build(parameters);
    }

    private static void EnsureDecoderProduced(MetamorphicParameters parameters)
    {
        Check(parameters.FamilyIndex, MetamorphicDecoder.FamilyTable.Length, "relation family");

        var definition = MetamorphicFamilyRegistry.Get(MetamorphicDecoder.FamilyTable[parameters.FamilyIndex]);
        Check(parameters.LimitModeIndex, definition.SupportedLimitModes.Length, "limit mode");
        Check(parameters.PrimaryOffsetIndex, MetamorphicDecoder.OffsetTable.Length, "primary offset");
        Check(parameters.SecondaryOffsetIndex, MetamorphicDecoder.OffsetTable.Length, "secondary offset");
        Check(parameters.OptimizeIndex, 2, "optimizer policy");

        Check(
            parameters.LegacyRangeStopIndex,
            definition.UsesLegacyRangeStop ? MetamorphicDecoder.RangeStopTable.Length : 1,
            "range stop");

        for (var i = 0; i < MetamorphicParameters.MaxExtraDimensions; i++)
        {
            var size = i < definition.ExtraDimensionCount ? definition.ExtraDimensionSizes[i] : 1;
            Check(parameters.Extra(i), size, $"appended dimension {i.ToString(CultureInfo.InvariantCulture)}");
        }

        static void Check(int index, int tableLength, string dimension)
        {
            if ((uint)index >= (uint)tableLength)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(parameters), index,
                    $"The {dimension} index is outside its table; metamorphic parameters must come from MetamorphicDecoder.Decode.");
            }
        }
    }

    // ── Phase 1 family: count(range(1, N)) against range(1, N).count ────────────

    internal static MetamorphicPrecondition ValidateRangeCount(MetamorphicParameters parameters)
    {
        var cardinality = RangeCardinality(parameters.RangeStop);

        if (cardinality < 1)
            return MetamorphicPrecondition.Rejected("non-positive-cardinality");

        if (cardinality > MetamorphicDecoder.MaxPhase1Cardinality)
            return MetamorphicPrecondition.Rejected("cardinality-above-phase1-bound");

        return MetamorphicPrecondition.Ok;
    }

    internal static MetamorphicCase BuildRangeCount(MetamorphicParameters parameters)
    {
        var stop = parameters.RangeStop;
        var cardinality = RangeCardinality(stop);
        var stopText = stop.ToString(CultureInfo.InvariantCulture);

        var left = $"Output = count(range(1, {stopText}))";
        var right = $"Output = range(1, {stopText}).count";

        return MetamorphicCaseFactory.Create(
            parameters,
            left,
            right,
            ValidateRangeCount(parameters),
            $"range(1, {stopText}) materializes {cardinality.ToString(CultureInfo.InvariantCulture)} item slot(s)");
    }

    // ── Parameter-space enumeration for the deterministic tests ─────────────────

    /// <summary>
    /// Every normalized parameter point of the Phase 1 family — the compatibility surface, so
    /// it stays exhaustive.
    /// </summary>
    internal static IEnumerable<MetamorphicParameters> EnumerateLegacyParameters()
    {
        var seen = new HashSet<MetamorphicParameters>();
        var modes = MetamorphicFamilyRegistry.Get(MetamorphicFamily.DottedCollectionCall).SupportedLimitModes.Length;

        for (var stop = 0; stop < MetamorphicDecoder.RangeStopTable.Length; stop++)
        for (var mode = 0; mode < modes; mode++)
        for (var primary = 0; primary < MetamorphicDecoder.OffsetTable.Length; primary++)
        for (var secondary = 0; secondary < MetamorphicDecoder.OffsetTable.Length; secondary++)
        for (var optimize = 0; optimize < 2; optimize++)
        {
            var parameters = MetamorphicDecoder.Decode(
                [0, (byte)stop, (byte)mode, (byte)primary, (byte)secondary, (byte)optimize]);
            if (seen.Add(parameters)) yield return parameters;
        }
    }

    /// <summary>
    /// A reviewed STRATIFIED sweep over every registered family. The full Cartesian product of
    /// Phase 2's dimensions is in the millions and mostly redundant, so the sweep crosses each
    /// family's own dimensions exhaustively under the default policy, then crosses every
    /// execution policy against a few representative points of that family.
    ///
    /// <para><b>The offset byte is a family dimension for some families.</b> Under most limit
    /// modes the primary offset only moves a budget around the template's measured total, so
    /// stratum 1 fixes it and stratum 2 varies it as part of the execution policy. Under
    /// <see cref="MetamorphicLimitMode.FamilyDerived"/> it is not a policy knob at all — it is the
    /// SIGNED BOUNDARY OFFSET, and its sign selects which law the case declares. Fixing it there
    /// would leave the exact boundary-failure relation unreachable from this sweep no matter how
    /// many other dimensions were crossed, so stratum 1 crosses it wherever the stratum-1 mode
    /// reads it. Points whose law ignores the offset are collapsed by the family's own normalizer
    /// and deduplicated here, so this costs only the cases that genuinely differ.</para>
    /// </summary>
    internal static IEnumerable<MetamorphicParameters> EnumerateStratifiedParameters()
    {
        var seen = new HashSet<MetamorphicParameters>();

        foreach (var parameters in EnumerateLegacyParameters())
        {
            if (seen.Add(parameters)) yield return parameters;
        }

        for (var familyIndex = 1; familyIndex < MetamorphicDecoder.FamilyTable.Length; familyIndex++)
        {
            var definition = MetamorphicFamilyRegistry.Get(MetamorphicDecoder.FamilyTable[familyIndex]);

            // Stratum 1: the family's own dimensions, exhaustively, under the default policy —
            // including the offset byte where that mode makes it one of them.
            var offsets = MetamorphicDecoder.UsesPrimaryOffset(definition.SupportedLimitModes[0])
                ? MetamorphicDecoder.OffsetTable.Length
                : 1;

            foreach (var extras in CrossExtras(definition))
            for (var primary = 0; primary < offsets; primary++)
            {
                var parameters = DecodeWith(
                    familyIndex, mode: 0, primary: offsets == 1 ? 1 : primary,
                    secondary: 1, optimize: 0, extras);
                if (seen.Add(parameters)) yield return parameters;
            }

            // Stratum 2: every execution policy against a few representative family points.
            foreach (var extras in RepresentativeExtras(definition))
            for (var mode = 0; mode < definition.SupportedLimitModes.Length; mode++)
            for (var primary = 0; primary < MetamorphicDecoder.OffsetTable.Length; primary++)
            for (var secondary = 0; secondary < MetamorphicDecoder.OffsetTable.Length; secondary++)
            for (var optimize = 0; optimize < 2; optimize++)
            {
                var parameters = DecodeWith(familyIndex, mode, primary, secondary, optimize, extras);
                if (seen.Add(parameters)) yield return parameters;
            }
        }
    }

    private static MetamorphicParameters DecodeWith(
        int familyIndex, int mode, int primary, int secondary, int optimize, IReadOnlyList<int> extras)
    {
        var payload = new byte[MetamorphicParameters.CommonPayloadLength + extras.Count];
        payload[0] = (byte)familyIndex;
        payload[2] = (byte)mode;
        payload[3] = (byte)primary;
        payload[4] = (byte)secondary;
        payload[5] = (byte)optimize;
        for (var i = 0; i < extras.Count; i++)
            payload[MetamorphicParameters.CommonPayloadLength + i] = (byte)extras[i];
        return MetamorphicDecoder.Decode(payload);
    }

    private static IEnumerable<IReadOnlyList<int>> CrossExtras(MetamorphicFamilyDefinition definition)
    {
        var counts = definition.ExtraDimensionSizes;
        if (counts.Length == 0)
        {
            yield return [];
            yield break;
        }

        var indices = new int[counts.Length];
        while (true)
        {
            yield return (int[])indices.Clone();

            var position = counts.Length - 1;
            while (position >= 0)
            {
                indices[position]++;
                if (indices[position] < counts[position]) break;
                indices[position] = 0;
                position--;
            }

            if (position < 0) yield break;
        }
    }

    private static IEnumerable<IReadOnlyList<int>> RepresentativeExtras(MetamorphicFamilyDefinition definition)
    {
        var counts = definition.ExtraDimensionSizes;
        if (counts.Length == 0)
        {
            yield return [];
            yield break;
        }

        // Three points per family: the first entry of every dimension, the middle, and the last.
        foreach (var pick in new Func<int, int>[] { static _ => 0, static n => n / 2, static n => n - 1 })
            yield return counts.Select(pick).ToArray();
    }
}
