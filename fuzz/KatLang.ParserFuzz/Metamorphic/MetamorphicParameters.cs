using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>Which evaluation limits a case configures around the template's measured totals.</summary>
internal enum MetamorphicLimitMode
{
    /// <summary>No explicit limits: the default policy applies to both members.</summary>
    Default,

    /// <summary>Primary offset configures the cumulative per-run item budget (<c>MaxMaterializedItems</c>).</summary>
    CumulativeItems,

    /// <summary>Secondary offset configures the single-collection ceiling (<c>MaxCollectionItems</c>).</summary>
    PerCollectionItems,

    /// <summary>Both item budgets, independently offset.</summary>
    Both,

    /// <summary>Primary offset configures the cumulative string budget (<c>MaxMaterializedStringChars</c>).</summary>
    CumulativeStrings,

    /// <summary>Secondary offset configures the single-string ceiling (<c>MaxStringLength</c>).</summary>
    PerStringLength,

    /// <summary>Every budget configured explicitly and comfortably above what the pair needs.</summary>
    Generous,

    /// <summary>
    /// The FAMILY owns both sides' limits.
    ///
    /// <para>Declared by the Phase 3 budget-law family, whose whole subject is placing one
    /// resource dimension at a derived boundary — a limit the shared
    /// <see cref="MetamorphicLimitPolicy.Derive"/> policy cannot express, because it varies
    /// per side and per law. The PRIMARY offset byte keeps a meaning here: it is the signed
    /// boundary offset applied to the right member. Laws that do not sweep a boundary collapse
    /// it in their own normalizer, so no two payloads build the same case.</para>
    /// </summary>
    FamilyDerived,
}

/// <summary>
/// The decoded, compact, fully replayable description of one metamorphic case.
///
/// <para>Every field is a small table INDEX rather than a raw number, so no value taken from
/// fuzz input can select an expensive computation or an allocation proportional to an encoded
/// integer.</para>
///
/// <para><b>Payload layout.</b> Bytes 0-5 are the COMMON prefix and keep the exact meaning
/// they had in Phase 1:</para>
/// <code>
/// 0  relation family          (see the compatibility rule below)
/// 1  legacy range stop        (used only by the Phase 1 family; normalized away for others)
/// 2  limit mode               (indexed into the FAMILY's supported modes)
/// 3  primary limit offset     (relative to the measured total the mode configures)
/// 4  secondary limit offset   (relative to the measured total the mode configures)
/// 5  optimizer policy
/// 6+ family-specific dimensions, APPENDED — never an overload of an existing byte
/// </code>
///
/// <para><b>Backward compatibility.</b> A payload of <see cref="CommonPayloadLength"/> bytes or
/// fewer is a version-zero payload and always decodes to the Phase 1 family with the Phase 1
/// tables, exactly as before — byte 0 is ignored there, mirroring Phase 1's single-entry family
/// table. Reaching any Phase 2 family requires a seventh byte, so no tracked Phase 1 seed and no
/// six-byte payload can change meaning.</para>
/// </summary>
internal readonly record struct MetamorphicParameters(
    int FamilyIndex,
    int LegacyRangeStopIndex,
    int LimitModeIndex,
    int PrimaryOffsetIndex,
    int SecondaryOffsetIndex,
    int OptimizeIndex,
    int Extra0 = 0,
    int Extra1 = 0,
    int Extra2 = 0,
    int Extra3 = 0)
{
    /// <summary>Bytes in the common prefix; also the largest version-zero payload.</summary>
    public const int CommonPayloadLength = 6;

    /// <summary>Largest number of appended family-specific dimensions.</summary>
    public const int MaxExtraDimensions = 4;

    /// <summary>Bytes one encoded parameter point occupies for its family.</summary>
    public int EncodedLength => CommonPayloadLength + Definition.ExtraDimensionCount;

    public MetamorphicFamily Family => MetamorphicDecoder.FamilyTable[FamilyIndex];

    public MetamorphicFamilyDefinition Definition => MetamorphicFamilyRegistry.Get(Family);

    /// <summary>The <c>stop</c> bound of the Phase 1 family's generated <c>range(1, stop)</c>.</summary>
    public int RangeStop => MetamorphicDecoder.RangeStopTable[LegacyRangeStopIndex];

    public MetamorphicLimitMode LimitMode => Definition.SupportedLimitModes[LimitModeIndex];

    /// <summary>Signed offset applied to the measured total for the mode's primary limit.</summary>
    public int PrimaryOffset => MetamorphicDecoder.OffsetTable[PrimaryOffsetIndex];

    /// <summary>Signed offset applied to the measured total for the mode's secondary limit.</summary>
    public int SecondaryOffset => MetamorphicDecoder.OffsetTable[SecondaryOffsetIndex];

    public bool EnableOptimizations => OptimizeIndex == 0;

    /// <summary>Reads appended dimension <paramref name="index"/> (0-based over bytes 6+).</summary>
    public int Extra(int index) => index switch
    {
        0 => Extra0,
        1 => Extra1,
        2 => Extra2,
        3 => Extra3,
        _ => throw new ArgumentOutOfRangeException(nameof(index), index, "Only four appended dimensions exist."),
    };

    /// <summary>Returns a copy with appended dimension <paramref name="index"/> replaced.</summary>
    public MetamorphicParameters WithExtra(int index, int value) => index switch
    {
        0 => this with { Extra0 = value },
        1 => this with { Extra1 = value },
        2 => this with { Extra2 = value },
        3 => this with { Extra3 = value },
        _ => throw new ArgumentOutOfRangeException(nameof(index), index, "Only four appended dimensions exist."),
    };

    /// <summary>Canonical encoding; <c>Decode(Encode(p)) == p</c> for any decoded p.</summary>
    public byte[] Encode()
    {
        var extras = Definition.ExtraDimensionCount;
        var bytes = new byte[CommonPayloadLength + extras];
        bytes[0] = (byte)FamilyIndex;
        bytes[1] = (byte)LegacyRangeStopIndex;
        bytes[2] = (byte)LimitModeIndex;
        bytes[3] = (byte)PrimaryOffsetIndex;
        bytes[4] = (byte)SecondaryOffsetIndex;
        bytes[5] = (byte)OptimizeIndex;
        for (var i = 0; i < extras; i++)
            bytes[CommonPayloadLength + i] = (byte)Extra(i);
        return bytes;
    }

    /// <summary>Lowercase, space-separated hex of <see cref="Encode"/> — the seed payload form.</summary>
    public string ToHex() => string.Join(" ", Encode().Select(b => b.ToString("x2", CultureInfo.InvariantCulture)));

    /// <summary>Stable, machine-independent one-line summary used in reports and fingerprints.</summary>
    public override string ToString()
    {
        var definition = Definition;
        var text =
            $"family={definition.Id} limitMode={LimitMode} primaryOffset={Signed(PrimaryOffset)} " +
            $"secondaryOffset={Signed(SecondaryOffset)} optimize={(EnableOptimizations ? "on" : "off")}";

        if (definition.UsesLegacyRangeStop)
            text += $" rangeStop={RangeStop.ToString(CultureInfo.InvariantCulture)}";

        var variant = definition.DescribeVariant(this);
        return variant.Length == 0 ? text : text + " " + variant;
    }

    private static string Signed(int value)
        => (value >= 0 ? "+" : "") + value.ToString(CultureInfo.InvariantCulture);
}
