namespace KatLang.Tests;

using SettlementShare = PropertyExposureResolver.SettlementShare;
using SummaryScope = PropertyExposureResolver.SummaryScope;

/// <summary>
/// Settlement-share keys for store-level tests (<see cref="ExposureSettlementShareTests"/>,
/// <see cref="ExposureSettlementFootprintTests"/>). Production builds every key from a pending reference
/// (charged at its id-independent <see cref="SummaryReference.StableContentKeyLength"/>) or from a seed, so it has
/// no constructor that takes free text: one would let a reference's key be charged at its text length, which
/// depends on the ids this process has issued.
/// </summary>
internal static class SettlementShareTestKeys
{
    /// <summary>A key whose content is text holding no process-wide id, charged at its length.</summary>
    public static SettlementShare.Key TextKey(string content, SummaryScope level, BoundOwnerSet? bound)
        => new(content, level, bound, content.Length);
}
