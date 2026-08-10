using System.Collections.Immutable;
using System.Globalization;
using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>One link in a trusted dotted chain: a registered builtin plus its written suffix.</summary>
internal sealed record MetamorphicChainLink(string Builtin, string Suffix = "")
{
    /// <summary>The dotted spelling of this link applied to whatever precedes it.</summary>
    public string Dotted => Suffix.Length == 0 ? "." + Builtin : $".{Builtin}({Suffix})";

    /// <summary>The ordinary spelling of this link wrapping <paramref name="inner"/>.</summary>
    public string Ordinary(string inner)
        => Suffix.Length == 0 ? $"{Builtin}({inner})" : $"{Builtin}({inner}, {Suffix})";
}

/// <summary>
/// Group C — a bounded dotted chain against the nested ordinary call built STRUCTURALLY from
/// the same link list.
///
/// <code>
/// MmR.map(MmDouble).count      vs      count(map(MmR, MmDouble))
/// </code>
///
/// <para><b>Equivalence argument.</b> Each link is one application of the Group A rewrite, and
/// the two forms are generated from ONE ordered list of links: the dotted form appends
/// <c>.F(suffix)</c> per link, the ordinary form wraps <c>F(inner, suffix)</c> per link. The
/// ordinary equivalent is never recovered by reparsing or rewriting dotted source text, so the
/// pair cannot drift.</para>
///
/// <para>Chains are bounded to <see cref="MaxChainLength"/> links, every link must name a
/// registered trusted builtin, and structural member access is excluded by construction (every
/// member is a prelude builtin applied to a value).</para>
/// </summary>
internal static class MetamorphicChainTemplate
{
    private const int ChainDimension = 0;
    private const int ReceiverDimension = 1;

    private const string R = MetamorphicTables.ReceiverProperty;

    /// <summary>Phase 2 keeps chains short; nothing here is longer.</summary>
    internal const int MaxChainLength = 3;

    private static readonly string Double = MetamorphicTables.DoubleCallback;
    private static readonly string Big = MetamorphicTables.BigCallback;
    private static readonly string Add = MetamorphicTables.AddCallback;

    /// <summary>Reviewed chains. Each is a fixed link list, never assembled from fuzz bytes.</summary>
    internal static readonly ImmutableArray<ImmutableArray<MetamorphicChainLink>> Chains =
    [
        [new("map", Double), new("count")],
        [new("take", "2"), new("distinct")],
        [new("filter", Big), new("count")],
        [new("map", Double), new("sum")],
        [new("order"), new("last")],
        [new("distinct"), new("count")],
        [new("take", "2"), new("distinct"), new("count")],
        [new("filter", Big), new("map", Double), new("count")],
        [new("order"), new("skip", "1"), new("sum")],
        [new("map", Double), new("distinct"), new("count")],
        [new("map", Double), new("reduce", Add + ", 0")],
        [new("atoms"), new("count")],
    ];

    internal static int ChainCount => Chains.Length;

    internal static ImmutableArray<MetamorphicChainLink> ChainOf(MetamorphicParameters parameters)
        => Chains[parameters.Extra(ChainDimension)];

    internal static MetamorphicValueShape ReceiverOf(MetamorphicParameters parameters)
        => MetamorphicTables.ReceiverShapes[parameters.Extra(ReceiverDimension)];

    internal static MetamorphicParameters Normalize(MetamorphicParameters parameters) => parameters;

    /// <summary>
    /// The dotted spelling of a chain is the one the sequence-pipeline optimizer can FUSE; the
    /// nested ordinary form is not. Fusion is documented to materialize less while still
    /// enforcing the same single-collection boundary, so equality is claimed only where fusion
    /// cannot apply, and the weaker directional relation only where it can.
    ///
    /// <para>Eligibility is the EFFECTIVE runtime condition, not the optimizer flag alone:
    /// <see cref="MetamorphicLimitPolicy.SequencePipelineFusionCanApply"/> also accounts for the
    /// configured string, step, and cumulative-item budgets that switch the
    /// sequence-pipeline optimizer off. Keying on the flag alone would give away
    /// detection strength for free — those limit modes run unfused and do agree
    /// exactly, so they get the exact relation.</para>
    ///
    /// <para>Measured on the committed chain table: with fusion ineligible the two forms agree
    /// exactly on all 144 chain/receiver pairs; with fusion eligible the dotted form charged less
    /// on 5 of them (<c>filter &gt; count</c>) and never more.</para>
    /// </summary>
    internal static MetamorphicOperationalRelation SelectOperationalRelation(
        MetamorphicParameters parameters, EvaluationLimits? limits)
        => MetamorphicLimitPolicy.SequencePipelineFusionCanApply(parameters.EnableOptimizations, limits)
            ? MetamorphicOperationalRelation.MaterializationNeverIncreases
            : MetamorphicOperationalRelation.ExactMaterializationEqual;

    internal static MetamorphicPrecondition Validate(MetamorphicParameters parameters)
    {
        var chain = ChainOf(parameters);

        if (chain.Length is < 2 or > MaxChainLength)
            return MetamorphicPrecondition.Rejected("chain-length-out-of-bounds");

        // The cumulative-item modes need no rejection anymore: a CONFIGURED cumulative
        // materialization budget forces the generic sequence paths in the runtime
        // (Evaluator.CreateRootCtx, mirrored by
        // MetamorphicLimitPolicy.SequencePipelineFusionCanApply), so both spellings run
        // unfused and charge the budget identically — the divergence the former
        // "fused-chain-does-not-share-the-cumulative-item-budget" rejection guarded is
        // structurally impossible now. (Pinned by
        // MetamorphicPhase2FamilyTests.ChainCumulativeModes_AreAcceptedWhenTheirBudgetDisablesFusion.)

        foreach (var link in chain)
        {
            // Every link must be extension-style-call eligible: a registered trusted builtin.
            if (!MetamorphicTables.Builtins.Any(builtin => builtin.Name == link.Builtin))
                return MetamorphicPrecondition.Rejected("chain-link-is-not-a-registered-builtin");
        }

        var receiver = ReceiverOf(parameters);
        if (receiver.Source.StartsWith('(') && receiver.Source.Contains('=', StringComparison.Ordinal))
            return MetamorphicPrecondition.Rejected("block-valued-receiver-resolves-structurally");

        return MetamorphicPrecondition.Ok;
    }

    internal static string DescribeVariant(MetamorphicParameters parameters)
    {
        var chain = ChainOf(parameters);
        return $"chain={string.Join(">", chain.Select(link => link.Builtin))} " +
               $"chainLength={chain.Length.ToString(CultureInfo.InvariantCulture)} " +
               $"receiver={ReceiverOf(parameters).Id}";
    }

    internal static MetamorphicCase Build(MetamorphicParameters parameters)
    {
        var chain = ChainOf(parameters);
        var receiver = ReceiverOf(parameters);

        var preamble = new StringBuilder();
        if (chain.Any(link => link.Suffix.Contains(MetamorphicTables.NamePrefix, StringComparison.Ordinal)))
            preamble.Append(MetamorphicTables.CallbackPreamble);
        preamble.Append(R).Append(" = ").Append(receiver.Source).Append('\n');

        // Both forms come from the SAME ordered link list.
        var ordinary = R;
        foreach (var link in chain) ordinary = link.Ordinary(ordinary);

        var dotted = new StringBuilder(R);
        foreach (var link in chain) dotted.Append(link.Dotted);

        return MetamorphicCaseFactory.Create(
            parameters,
            $"{preamble}{ordinary}",
            $"{preamble}{dotted}",
            Validate(parameters),
            $"{chain.Length.ToString(CultureInfo.InvariantCulture)}-link chain " +
            $"{string.Join(" > ", chain.Select(link => link.Builtin))} on receiver {receiver.Id}");
    }
}
