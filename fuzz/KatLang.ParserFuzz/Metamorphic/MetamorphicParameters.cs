using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>Which evaluation limits a case configures around the template's expected total.</summary>
internal enum MetamorphicLimitMode
{
    /// <summary>No explicit limits: the default policy applies to both members.</summary>
    Default,

    /// <summary>Only the cumulative per-run item budget (<c>MaxMaterializedItems</c>).</summary>
    CumulativeItems,

    /// <summary>Only the single-collection ceiling (<c>MaxCollectionItems</c>).</summary>
    PerCollectionItems,

    /// <summary>Both budgets, independently offset from the expected total.</summary>
    Both,
}

/// <summary>
/// The decoded, compact, fully replayable description of one metamorphic case. Every field
/// is a small table INDEX rather than a raw number, so no value taken from fuzz input can
/// select an expensive computation or an allocation proportional to an encoded integer.
///
/// <para>Six bytes, one per field, each byte holding the (already reduced) table index. The
/// encoding is the replay payload: a seed stores these bytes and nothing else, and both
/// sources are regenerated deterministically from them.</para>
/// </summary>
internal readonly record struct MetamorphicParameters(
    int FamilyIndex,
    int RangeStopIndex,
    int LimitModeIndex,
    int CumulativeOffsetIndex,
    int PerCollectionOffsetIndex,
    int OptimizeIndex)
{
    /// <summary>Number of bytes one encoded parameter point occupies.</summary>
    public const int EncodedLength = 6;

    public MetamorphicFamily Family => MetamorphicDecoder.FamilyTable[FamilyIndex];

    /// <summary>The <c>stop</c> bound of the generated <c>range(1, stop)</c>.</summary>
    public int RangeStop => MetamorphicDecoder.RangeStopTable[RangeStopIndex];

    public MetamorphicLimitMode LimitMode => MetamorphicDecoder.LimitModeTable[LimitModeIndex];

    /// <summary>Signed offset applied to the expected total for the cumulative budget.</summary>
    public int CumulativeOffset => MetamorphicDecoder.OffsetTable[CumulativeOffsetIndex];

    /// <summary>Signed offset applied to the expected total for the per-collection ceiling.</summary>
    public int PerCollectionOffset => MetamorphicDecoder.OffsetTable[PerCollectionOffsetIndex];

    public bool EnableOptimizations => OptimizeIndex == 0;

    /// <summary>Canonical six-byte encoding; <c>Decode(Encode(p)) == p</c> for any decoded p.</summary>
    public byte[] Encode() =>
    [
        (byte)FamilyIndex,
        (byte)RangeStopIndex,
        (byte)LimitModeIndex,
        (byte)CumulativeOffsetIndex,
        (byte)PerCollectionOffsetIndex,
        (byte)OptimizeIndex,
    ];

    /// <summary>Lowercase, space-separated hex of <see cref="Encode"/> — the seed payload form.</summary>
    public string ToHex() => string.Join(" ", Encode().Select(b => b.ToString("x2", CultureInfo.InvariantCulture)));

    /// <summary>Stable, machine-independent one-line summary used in reports and fingerprints.</summary>
    public override string ToString() =>
        $"family={MetamorphicCase.FamilyIdOf(Family)} rangeStop={RangeStop.ToString(CultureInfo.InvariantCulture)} " +
        $"limitMode={LimitMode} cumulativeOffset={Signed(CumulativeOffset)} " +
        $"perCollectionOffset={Signed(PerCollectionOffset)} optimize={(EnableOptimizations ? "on" : "off")}";

    private static string Signed(int value) =>
        (value >= 0 ? "+" : "") + value.ToString(CultureInfo.InvariantCulture);
}
