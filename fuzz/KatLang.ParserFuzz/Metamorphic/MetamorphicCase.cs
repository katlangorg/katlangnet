using System.Globalization;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Relation families. A family names ONE trusted template plus the equivalence argument
/// that justifies comparing the pair it generates. Adding a family means adding a template
/// whose construction guarantees the declared relation — never a textual rewriting of an
/// arbitrary mutated program.
/// </summary>
internal enum MetamorphicFamily
{
    /// <summary>
    /// Phase 1: the dotted collection call versus its ordinary receiver-first spelling
    /// (<c>count(range(1, N))</c> vs <c>range(1, N).count</c>). The dotted form is not an
    /// optimization of the ordinary form, it IS the ordinary form — <c>A.F(B)</c> means
    /// <c>F(A, B)</c> — so semantic AND exact operational equality are both justified.
    /// </summary>
    DottedCollectionCall,
}

/// <summary>The declared LANGUAGE-SEMANTIC relation between the two members of a pair.</summary>
internal enum MetamorphicSemanticRelation
{
    /// <summary>
    /// Both members produce the same stable semantic observation: success/failure, neutral
    /// structural value, emitted count, innermost stable error category and — where the
    /// payload is a machine-independent number — its structured payload.
    /// </summary>
    SemanticEqual,
}

/// <summary>The declared OPERATIONAL relation between the two members of a pair.</summary>
internal enum MetamorphicOperationalRelation
{
    /// <summary>
    /// Exact equality of materialized collection-item slots and materialized string UTF-16
    /// units, plus the same relevant resource-limit verdict. Deliberately NOT every counter:
    /// evaluation steps and peak dynamic depth are recorded for diagnostics only, because
    /// the repository's established contract for this pair
    /// (<c>OperationalMetamorphicTests.DottedAndOrdinaryForms_ChargeExactlyTheSameWork</c>)
    /// asserts materialization equality and not a shared step definition.
    /// </summary>
    ExactMaterializationEqual,
}

/// <summary>
/// Whether the template's own construction preconditions hold for one decoded parameter
/// point. A failed precondition is a REJECTED case, never a mismatch: the pair is not
/// compared at all, and the reason is reported.
/// </summary>
internal sealed record MetamorphicPrecondition(bool Satisfied, string Reason)
{
    public static readonly MetamorphicPrecondition Ok = new(true, "ok");

    public static MetamorphicPrecondition Rejected(string reason) => new(false, reason);
}

/// <summary>
/// One metamorphic testcase: a trusted template instantiation plus the execution policy and
/// the declared relations under which its two members must agree.
///
/// <para>This is deliberately not "one arbitrary source file". Equivalence is guaranteed by
/// how <see cref="LeftSource"/> and <see cref="RightSource"/> were CONSTRUCTED, so the
/// comparison is trustworthy without any semantic analysis of the generated text.</para>
///
/// <para>Harness-internal; nothing here is public API.</para>
/// </summary>
internal sealed record MetamorphicCase(
    MetamorphicFamily Family,
    MetamorphicParameters Parameters,
    string LeftSource,
    string RightSource,
    MetamorphicSemanticRelation SemanticRelation,
    MetamorphicOperationalRelation OperationalRelation,
    EvaluationLimits? Limits,
    bool EnableOptimizations,
    MetamorphicPrecondition Precondition,
    bool LeanRepresentable,
    string Description)
{
    /// <summary>
    /// Item slots the template expects the generated collection to materialize. Template
    /// knowledge used by the deterministic tests and by the limit derivation; the fuzz
    /// target itself never asserts it, so the campaign stays purely metamorphic rather
    /// than becoming an oracle comparison.
    /// </summary>
    public long ExpectedItemTotal { get; init; }

    /// <summary>Stable, machine-independent rendering of the effective limits.</summary>
    public string LimitsText => DescribeLimits(Limits);

    /// <summary>Family identifier used in seeds, reports, and fingerprints.</summary>
    public string FamilyId => FamilyIdOf(Family);

    internal static string FamilyIdOf(MetamorphicFamily family) => family switch
    {
        MetamorphicFamily.DottedCollectionCall => "dotted-collection-call",
        _ => family.ToString(),
    };

    internal static bool TryParseFamilyId(string text, out MetamorphicFamily family)
    {
        foreach (var candidate in Enum.GetValues<MetamorphicFamily>())
        {
            if (string.Equals(FamilyIdOf(candidate), text, StringComparison.Ordinal))
            {
                family = candidate;
                return true;
            }
        }

        family = default;
        return false;
    }

    internal static string DescribeLimits(EvaluationLimits? limits)
    {
        if (limits is null) return "default";

        var parts = new List<string>(2);
        if (limits.MaxMaterializedItems is { } cumulative)
            parts.Add("maxMaterializedItems=" + cumulative.ToString(CultureInfo.InvariantCulture));
        if (limits.MaxCollectionItems is { } perCollection)
            parts.Add("maxCollectionItems=" + perCollection.ToString(CultureInfo.InvariantCulture));
        return parts.Count == 0 ? "explicit(none)" : string.Join(",", parts);
    }
}
