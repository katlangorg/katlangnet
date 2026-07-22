using System.Globalization;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Trusted templates: the only place a metamorphic pair is created.
///
/// <para>A template owns an EQUIVALENCE ARGUMENT, not a rewriting. Phase 1's single family
/// instantiates the two spellings of one call — <c>count(range(1, N))</c> and
/// <c>range(1, N).count</c> — which are equivalent because KatLang defines the dotted form
/// as the ordinary receiver-first call (<c>A.F(B)</c> means <c>F(A, B)</c>, and for the fixed
/// collection builtins the receiver fills the single <c>collection</c> parameter). The pair is
/// therefore expected to agree on semantics AND on the work it charges, which is why the
/// operational relation may be exact equality rather than an inequality.</para>
///
/// <para>The template also knows the cardinality it asks the language to build, which is how
/// resource limits can be placed exactly on, just below, and just above the boundary. That
/// knowledge is used to DERIVE limits and by the deterministic tests; the fuzz target never
/// asserts it, so the campaign stays a pair comparison rather than an oracle comparison.</para>
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

    /// <summary>Every normalized parameter point Phase 1's decoder can produce.</summary>
    internal static IEnumerable<MetamorphicParameters> EnumerateAllParameters()
    {
        var seen = new HashSet<MetamorphicParameters>();
        for (var family = 0; family < MetamorphicDecoder.FamilyTable.Length; family++)
        for (var stop = 0; stop < MetamorphicDecoder.RangeStopTable.Length; stop++)
        for (var mode = 0; mode < MetamorphicDecoder.LimitModeTable.Length; mode++)
        for (var cumulative = 0; cumulative < MetamorphicDecoder.OffsetTable.Length; cumulative++)
        for (var perCollection = 0; perCollection < MetamorphicDecoder.OffsetTable.Length; perCollection++)
        for (var optimize = 0; optimize < 2; optimize++)
        {
            var parameters = MetamorphicDecoder.Decode(
                [(byte)family, (byte)stop, (byte)mode, (byte)cumulative, (byte)perCollection, (byte)optimize]);
            if (seen.Add(parameters)) yield return parameters;
        }
    }

    /// <summary>Instantiates the template selected by <paramref name="parameters"/>.</summary>
    internal static MetamorphicCase Build(MetamorphicParameters parameters)
    {
        // Only decoder output is a legal input here: every index must already name a table
        // entry, so a hand-built parameter point fails loudly instead of silently reading
        // past a table or fabricating an untrusted pair.
        EnsureDecoderProduced(parameters);

        return parameters.Family switch
        {
            MetamorphicFamily.DottedCollectionCall => BuildDottedCollectionCall(parameters),
            _ => throw new ArgumentOutOfRangeException(
                nameof(parameters), parameters.Family, "No template is registered for this relation family."),
        };
    }

    private static void EnsureDecoderProduced(MetamorphicParameters parameters)
    {
        Check(parameters.FamilyIndex, MetamorphicDecoder.FamilyTable.Length, "relation family");
        Check(parameters.RangeStopIndex, MetamorphicDecoder.RangeStopTable.Length, "range stop");
        Check(parameters.LimitModeIndex, MetamorphicDecoder.LimitModeTable.Length, "limit mode");
        Check(parameters.CumulativeOffsetIndex, MetamorphicDecoder.OffsetTable.Length, "cumulative offset");
        Check(parameters.PerCollectionOffsetIndex, MetamorphicDecoder.OffsetTable.Length, "per-collection offset");
        Check(parameters.OptimizeIndex, 2, "optimizer policy");

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

    private static MetamorphicCase BuildDottedCollectionCall(MetamorphicParameters parameters)
    {
        var stop = parameters.RangeStop;
        var cardinality = RangeCardinality(stop);
        var stopText = stop.ToString(CultureInfo.InvariantCulture);

        var left = $"Output = count(range(1, {stopText}))";
        var right = $"Output = range(1, {stopText}).count";

        var (limits, limitsNote) = DeriveLimits(parameters, cardinality);
        var precondition = CheckPreconditions(parameters, cardinality, left, right);

        var description =
            $"{MetamorphicCase.FamilyIdOf(parameters.Family)}: range(1, {stopText}) materializes " +
            $"{cardinality.ToString(CultureInfo.InvariantCulture)} item slot(s); " +
            $"limits {MetamorphicCase.DescribeLimits(limits)}{limitsNote}; " +
            $"optimizations {(parameters.EnableOptimizations ? "on" : "off")}";

        return new MetamorphicCase(
            Family: parameters.Family,
            Parameters: parameters,
            LeftSource: left,
            RightSource: right,
            SemanticRelation: MetamorphicSemanticRelation.SemanticEqual,
            OperationalRelation: MetamorphicOperationalRelation.ExactMaterializationEqual,
            Limits: limits,
            EnableOptimizations: parameters.EnableOptimizations,
            Precondition: precondition,
            // Both members are ordinary KatLang programs whose SEMANTICS Lean models, so either
            // one could be checked against the Lean differential corpus. The RELATION cannot:
            // Lean models an unbounded evaluator with no notion of work. See fuzz/README.md.
            LeanRepresentable: true,
            Description: description)
        {
            ExpectedItemTotal = cardinality,
        };
    }

    /// <summary>
    /// Places the configured budgets relative to the template's expected total. Both KatLang
    /// limits reject values below 1, so an offset that would ask for 0 is clamped up and the
    /// clamp is reported rather than silently applied — a "one below" case at cardinality 1
    /// really is an "exactly at" case.
    /// </summary>
    private static (EvaluationLimits? Limits, string Note) DeriveLimits(
        MetamorphicParameters parameters, long cardinality)
    {
        if (parameters.LimitMode == MetamorphicLimitMode.Default)
            return (null, "");

        var clamped = false;
        long? cumulative = null;
        int? perCollection = null;

        if (parameters.LimitMode is MetamorphicLimitMode.CumulativeItems or MetamorphicLimitMode.Both)
            cumulative = Place(cardinality, parameters.CumulativeOffset, ref clamped);

        if (parameters.LimitMode is MetamorphicLimitMode.PerCollectionItems or MetamorphicLimitMode.Both)
            perCollection = (int)Place(cardinality, parameters.PerCollectionOffset, ref clamped);

        var limits = new EvaluationLimits
        {
            MaxMaterializedItems = cumulative,
            MaxCollectionItems = perCollection,
        };

        return (limits, clamped ? " (offset clamped to the minimum legal limit)" : "");

        static long Place(long total, int offset, ref bool clamped)
        {
            var requested = checked(total + offset);
            if (requested >= 1) return requested;
            clamped = true;
            return 1;
        }
    }

    /// <summary>
    /// Template preconditions. They are expected to hold by construction; checking them
    /// anyway keeps a future template's generation bug visible as a counted REJECTION with a
    /// reason instead of surfacing as a false mismatch.
    /// </summary>
    private static MetamorphicPrecondition CheckPreconditions(
        MetamorphicParameters parameters, long cardinality, string left, string right)
    {
        if (!MetamorphicDecoder.FamilyTable.Contains(parameters.Family))
            return MetamorphicPrecondition.Rejected("unregistered-family");

        if (cardinality < 1)
            return MetamorphicPrecondition.Rejected("non-positive-cardinality");

        if (cardinality > MetamorphicDecoder.MaxPhase1Cardinality)
            return MetamorphicPrecondition.Rejected("cardinality-above-phase1-bound");

        if (left.Length == 0 || right.Length == 0)
            return MetamorphicPrecondition.Rejected("empty-generated-source");

        if (string.Equals(left, right, StringComparison.Ordinal))
            return MetamorphicPrecondition.Rejected("identical-pair-members");

        if (!right.Contains(".count", StringComparison.Ordinal))
            return MetamorphicPrecondition.Rejected("right-member-is-not-the-dotted-form");

        return MetamorphicPrecondition.Ok;
    }
}
