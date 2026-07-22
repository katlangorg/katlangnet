using System.Collections.Immutable;
using System.Globalization;
using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>
/// One reviewed cached-versus-rebuilt shape: the VALUE a zero-argument property binds, and the
/// USE that consumes it (<c>$</c> stands for the property name).
/// </summary>
/// <param name="RequiresReuseEvidence">
/// False only where the program cannot reach a second access — a property whose evaluation fails
/// stops the run at the first use. Such a template still pins a real contract (an erroring
/// property is not stored, and both forms agree on the error), so it is kept and says so instead
/// of being silently dropped.
/// </param>
/// <param name="TrailingRow">An extra final output row, used to place an error AFTER real reuse.</param>
internal sealed record MetamorphicCacheSource(
    string Id,
    string Value,
    string Use,
    bool RequiresReuseEvidence = true,
    string TrailingRow = "");

/// <summary>
/// Phase 3 Group B — a program that REUSES one zero-argument property against a rebuilt form
/// that constructs the same value independently for every use.
///
/// <code>
/// left (cached)    MmA = range(1, 6)                 right (rebuilt)  MmA1 = range(1, 6)
///                  Output = MmA.count, MmA.count                      MmA2 = range(1, 6)
///                                                                     Output = MmA1.count, MmA2.count
/// </code>
///
/// <para><b>Equivalence argument.</b> KatLang is pure, so binding one property and using it twice
/// and binding two properties to the same expression compute the same values. The two forms are
/// generated from ONE (value, use) pair and one reuse count, so they cannot drift: the rebuilt
/// side is the cached side with the single binding replicated and each use pointed at its own
/// copy. Property binding and call boundaries are identical on both sides — the rebuilt form is
/// deliberately NOT an inlined expression, because inlining would remove the property-access
/// machinery from one side and make the comparison about something else.</para>
///
/// <para><b>Cache evidence.</b> The per-run zero-argument property cache is the thing under test,
/// so the case is only admitted when the run PROVES it: the cached side must record at least
/// <c>uses - 1</c> hits, and the rebuilt side must record none at all. Distinct property names
/// have distinct binding identities, so the rebuilt side cannot accidentally share an entry —
/// and the evidence gate turns that from an argument into a measurement.</para>
///
/// <para><b>Directional work.</b> The cache exists to do less, so the relation is
/// <see cref="MetamorphicOperationalRelation.WorkNeverIncreases"/>: the cached side may charge
/// fewer materialized items, fewer string units, and fewer steps, but never more. Equality would
/// forbid caching; the inequality still catches a cache that costs more than it saves.</para>
///
/// <para><b>Why cumulative budgets are rejected.</b> The cached form legitimately materializes
/// less, so a cumulative budget derived from its measurement is below what the rebuilt form
/// needs. The two sides would then stop at different points — a true difference in execution
/// policy, not a defect — so those modes are rejected by name (the same treatment Phase 2 gives
/// fused chains) rather than compared. Per-OBJECT ceilings are kept: both forms build the same
/// individual collections and strings, so those boundaries genuinely coincide.</para>
/// </summary>
internal static class MetamorphicCacheTemplate
{
    private const int SourceDimension = 0;
    private const int ReuseDimension = 1;
    private const int OrderDimension = 2;

    private const string Property = MetamorphicTables.NamePrefix + "A";
    private const string Placeholder = "$";

    /// <summary>How many times the value is used. Both counts exercise a real reuse.</summary>
    internal static readonly ImmutableArray<int> ReuseCounts = [2, 3];

    /// <summary>Execution orders this family generates.</summary>
    internal static readonly ImmutableArray<MetamorphicExecutionOrder> Orders =
        [MetamorphicExecutionOrder.LeftFirst, MetamorphicExecutionOrder.RightFirst];

    /// <summary>Reviewed (value, use) pairs spanning every value kind the cache can hold.</summary>
    internal static readonly ImmutableArray<MetamorphicCacheSource> Sources =
    [
        new("cached-atom", "7", Placeholder),
        new("cached-string", "'abcd'", Placeholder),
        new("cached-list", "[1, 2, 3]", Placeholder + ".count"),
        new("cached-sequence", "(1, 2, 3)", Placeholder + ".count"),
        new("cached-empty-list", "[]", Placeholder + ".count"),
        new("cached-empty-sequence", "()", Placeholder + ".count"),
        new("cached-nested-collection", "[[1, 2], [3, 4]]", Placeholder + ".count"),
        new("cached-list-of-sequences", "[(1, 2), (3, 4)]", Placeholder + ".first"),
        new("cached-string-list", "['abc', 'de']", Placeholder + ".count"),
        new("cached-mixed-collection", "[1, 'ab', [2, 3]]", Placeholder + ".count"),
        // MEASURED, not assumed: a bare property reference in an ordinary call ARGUMENT position
        // records no zero-argument property cache request at all, while the SAME property used as
        // a dotted receiver does (see the two entries below). Both forms produce identical values;
        // the difference is purely a missed reuse, and the repository documents the cache as
        // something property-style access "may" use rather than must. The template is kept — the
        // pair is still a valid cached-versus-rebuilt comparison — but it does not claim reuse it
        // demonstrably does not get. Pinned by
        // MetamorphicPhase3FamilyTests.ArgumentPositionPropertyReference_DoesNotConsultTheCache.
        new("argument-position-property", "range(1, 6)", "sum(" + Placeholder + ")", RequiresReuseEvidence: false),
        new("cached-receiver-sum", "range(1, 6)", Placeholder + ".sum"),
        new("cached-dotted-receiver", "range(1, 6)", Placeholder + ".take(2)"),
        new("cached-callback-input", "[1, 2, 3]", Placeholder + ".map(" + MetamorphicTables.DoubleCallback + ")"),
        new("cached-filter-chain", "range(1, 8)", Placeholder + ".filter(" + MetamorphicTables.BigCallback + ").count"),
        new("cached-multi-output-property", "1, 2, 3", Placeholder),
        new("cached-string-projection", "range(1, 4)", Placeholder + ".count.string"),
        // Reuse happens first, then the run fails: proves an error later in the program does not
        // retroactively change what the cache already served.
        new("error-after-reuse", "range(1, 4)", Placeholder + ".count", TrailingRow: "min([])"),
        // The property itself fails, so no second access is ever reached. Kept because "an
        // erroring property is not stored and both forms report the same error" is a real
        // contract, and the template says so rather than claiming reuse it cannot have.
        new("erroring-property", "min([])", Placeholder, RequiresReuseEvidence: false),
    ];

    internal static int SourceCount => Sources.Length;

    /// <summary>Limit modes this family generates, including the ones it rejects by name.</summary>
    internal static readonly ImmutableArray<MetamorphicLimitMode> LimitModes =
    [
        MetamorphicLimitMode.Default,
        MetamorphicLimitMode.PerCollectionItems,
        MetamorphicLimitMode.PerStringLength,
        MetamorphicLimitMode.Generous,
        MetamorphicLimitMode.CumulativeItems,
        MetamorphicLimitMode.CumulativeStrings,
    ];

    internal static MetamorphicCacheSource SourceOf(MetamorphicParameters parameters)
        => Sources[parameters.Extra(SourceDimension)];

    internal static int ReuseCountOf(MetamorphicParameters parameters)
        => ReuseCounts[parameters.Extra(ReuseDimension)];

    internal static MetamorphicExecutionOrder OrderOf(MetamorphicParameters parameters)
        => Orders[parameters.Extra(OrderDimension)];

    internal static MetamorphicParameters Normalize(MetamorphicParameters parameters) => parameters;

    internal static MetamorphicPrecondition Validate(MetamorphicParameters parameters)
    {
        // A cumulative budget placed at the CACHED side's measurement is below what the rebuilt
        // side legitimately needs, so the two forms would stop at different points for a reason
        // that is not a defect. Rejected by name and counted, never compared.
        if (parameters.LimitMode is MetamorphicLimitMode.CumulativeItems
            or MetamorphicLimitMode.Both
            or MetamorphicLimitMode.CumulativeStrings)
        {
            return MetamorphicPrecondition.Rejected("rebuilt-form-does-not-share-the-cumulative-budget");
        }

        var source = SourceOf(parameters);
        if (!source.Use.Contains(Placeholder, StringComparison.Ordinal))
            return MetamorphicPrecondition.Rejected("cache-use-does-not-consume-the-property");

        return ReuseCountOf(parameters) < 2
            ? MetamorphicPrecondition.Rejected("cache-reuse-count-below-two")
            : MetamorphicPrecondition.Ok;
    }

    internal static string DescribeVariant(MetamorphicParameters parameters)
    {
        var source = SourceOf(parameters);
        return $"cacheSource={source.Id} uses={ReuseCountOf(parameters).ToString(CultureInfo.InvariantCulture)} " +
               $"reuseEvidence={(source.RequiresReuseEvidence ? "required" : "not-reachable")} " +
               $"order={OrderOf(parameters)}";
    }

    internal static MetamorphicCase Build(MetamorphicParameters parameters)
    {
        var source = SourceOf(parameters);
        var uses = ReuseCountOf(parameters);

        var cached = BuildCached(source, uses);
        var rebuilt = BuildRebuilt(source, uses);

        var testCase = MetamorphicCaseFactory.Create(
            parameters,
            cached,
            rebuilt,
            Validate(parameters),
            $"cached property '{source.Id}' used {uses.ToString(CultureInfo.InvariantCulture)} time(s) " +
            "against the independently rebuilt form");

        return testCase with
        {
            ExecutionOrder = OrderOf(parameters),
            LeftEvidence = source.RequiresReuseEvidence
                ? new MetamorphicSideEvidence(MinimumCacheHits: uses - 1)
                : MetamorphicSideEvidence.None,
            // Distinct property names have distinct binding identities, so the rebuilt side must
            // never serve one from cache. This is the "no accidental sharing" check.
            RightEvidence = new MetamorphicSideEvidence(MaximumCacheHits: 0),
        };
    }

    private static string BuildCached(MetamorphicCacheSource source, int uses)
    {
        var text = new StringBuilder();
        AppendPreamble(text, source);
        text.Append(Property).Append(" = ").Append(source.Value).Append('\n');
        text.Append("Output = ").Append(
            string.Join(", ", Enumerable.Repeat(Apply(source.Use, Property), uses)));
        AppendTrailingRow(text, source);
        return text.ToString();
    }

    private static string BuildRebuilt(MetamorphicCacheSource source, int uses)
    {
        var text = new StringBuilder();
        AppendPreamble(text, source);

        var names = new string[uses];
        for (var i = 0; i < uses; i++)
        {
            names[i] = Property + (i + 1).ToString(CultureInfo.InvariantCulture);
            text.Append(names[i]).Append(" = ").Append(source.Value).Append('\n');
        }

        text.Append("Output = ").Append(string.Join(", ", names.Select(name => Apply(source.Use, name))));
        AppendTrailingRow(text, source);
        return text.ToString();
    }

    private static void AppendPreamble(StringBuilder text, MetamorphicCacheSource source)
    {
        if (source.Use.Contains(MetamorphicTables.NamePrefix, StringComparison.Ordinal))
            text.Append(MetamorphicTables.CallbackPreamble);
    }

    private static void AppendTrailingRow(StringBuilder text, MetamorphicCacheSource source)
    {
        if (source.TrailingRow.Length > 0) text.Append(", ").Append(source.TrailingRow);
    }

    private static string Apply(string use, string name) => use.Replace(Placeholder, name, StringComparison.Ordinal);
}
