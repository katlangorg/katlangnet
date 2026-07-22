using System.Collections.Immutable;

namespace KatLang.ParserFuzz;

/// <summary>One reviewed program shape used to compare two runtime entry points.</summary>
/// <param name="Parses">
/// False for the deliberately malformed template. A surface that consumes an already-parsed root
/// can never see such a program, so pairing it there is a REJECTED case rather than a comparison
/// of an outcome one side cannot have.
/// </param>
internal sealed record MetamorphicEntryPointSource(string Id, string Source, bool Parses = true);

/// <summary>One reviewed pair of surfaces, plus the argument for comparing them.</summary>
internal sealed record MetamorphicSurfacePair(string Id, MetamorphicSurface Left, MetamorphicSurface Right)
{
    /// <summary>Facets both surfaces project — everything this pair is actually compared on.</summary>
    public MetamorphicFacets Shared =>
        MetamorphicSurfaces.Get(Left).Facets & MetamorphicSurfaces.Get(Right).Facets;

    /// <summary>True when at least one side consumes an already-parsed root.</summary>
    public bool NeedsParsableSource =>
        MetamorphicSurfaces.Get(Left).RequiresParsableSource || MetamorphicSurfaces.Get(Right).RequiresParsableSource;
}

/// <summary>
/// Phase 3 Group C — ONE trusted source executed through TWO runtime entry points.
///
/// <para><b>Equivalence argument.</b> Again there is nothing to rewrite: both members are the
/// same source text. What varies is the surface, and the claim is that KatLang's entry points are
/// different PROJECTIONS of one evaluation rather than different evaluations. The comparison is
/// therefore made on the intersection of what the two surfaces can actually report — never on a
/// field one of them does not have, which would pass on two absences.</para>
///
/// <para><b>What each surface can honestly report</b> is declared once, in
/// <see cref="MetamorphicSurfaces"/>, and was read off the production signatures rather than
/// assumed: <c>Evaluator.Run</c> returns a value with no emitted count; <c>RunFlat</c> returns the
/// host-atom projection and no structural value; the engine's public <c>KatLangError</c> keeps a
/// formatted message and a span rather than the structured <c>EvalError</c>, so engine surfaces
/// claim the outcome but not the error kind; and only <c>RunCountedObserved</c> hands back a
/// budget, so every pair involving another surface declares
/// <see cref="MetamorphicOperationalRelation.NotCompared"/> instead of comparing two zeroes.</para>
///
/// <para><b>Fresh state, shared configuration.</b> Every invocation re-parses, allocates its own
/// budget, and allocates its own zero-argument property cache, while the immutable
/// <see cref="EvaluationLimits"/> and <see cref="RunOptions"/> instances are reused across both
/// sides. The execution-order dimension runs the pair both ways round, so a surface that only
/// agrees when it goes first would be reported rather than hidden.</para>
///
/// <para><b>Rendering.</b> <c>EvaluateToString</c> is NOT <c>Run(...).ToDisplayString()</c> for a
/// successful program — it returns space-joined host atoms — so rendered text is compared exactly
/// where the two surfaces produced the same projection (every failure, and every same-surface
/// repeat) and the strict length bound is checked on both sides always. Asserting blanket string
/// equality would assert something the runtime never promised.</para>
///
/// <para><b>Limits are held at the default or comfortably generous.</b> Resource FAILURE coverage
/// comes from source templates that exceed the always-on ceilings on their own, not from tightening
/// a budget: the engine surfaces additionally bound the host-atom projection by the per-collection
/// ceiling (<c>KatLangEngine.Run</c>, <c>Evaluator.RunFlat</c>) while <c>RunCounted</c> does not, so
/// a tightened per-collection budget would compare two genuinely different contracts. The
/// budget-law family is where limits vary.</para>
/// </summary>
internal static class MetamorphicEntryPointTemplate
{
    private const int SourceDimension = 0;
    private const int PairDimension = 1;
    private const int OrderDimension = 2;

    private const string F = MetamorphicTables.NamePrefix + "F";
    private const string A = MetamorphicTables.NamePrefix + "A";

    /// <summary>Reviewed program shapes: successes of every value kind, and every failure channel.</summary>
    internal static readonly ImmutableArray<MetamorphicEntryPointSource> Sources =
    [
        new("scalar-success", "Output = 1 + 2"),
        new("collection-success", "Output = range(1, 5)"),
        new("list-success", "Output = [1, [2, 3]]"),
        new("sequence-success", "Output = (1, 2, 3)"),
        new("multiple-rows", "Output = 1, 2, 3"),
        new("empty-sequence", "Output = ()"),
        new("empty-list", "Output = []"),
        new("string-success", "Output = 'abc'"),
        new("mixed-rows", "Output = [1, 'ab', [2, 3]], (4, 5)"),
        new("top-level-property", "DisplayDecimals = 2\nOutput = 1.5"),
        new("evaluator-failure", "Output = min([])"),
        new("arity-failure", $"{F}(a, b) = a + b\nOutput = {F}(1)"),
        new("resource-failure-collection", "Output = range(1, 200000).count"),
        new("resource-failure-depth", $"{F}(0) = 0\n{F}(n) = {F}(n - 1)\nOutput = {F}(200)"),
        new("no-program-output", $"{A} = 1"),
        new("parse-failure", "Output = 1 ; 2", Parses: false),
    ];

    internal static int SourceCount => Sources.Length;

    /// <summary>
    /// Reviewed surface pairs. Every entry's intersection is more than the bare outcome, which the
    /// static constructor enforces so a vacuous pair can never be registered.
    /// </summary>
    internal static readonly ImmutableArray<MetamorphicSurfacePair> Pairs =
    [
        new("observed-vs-counted",
            MetamorphicSurface.EvaluatorRunCountedObserved, MetamorphicSurface.EvaluatorRunCounted),
        new("counted-vs-plain",
            MetamorphicSurface.EvaluatorRunCounted, MetamorphicSurface.EvaluatorRun),
        new("counted-vs-top-level-property",
            MetamorphicSurface.EvaluatorRunCounted, MetamorphicSurface.EvaluatorRunCountedWithTopLevelProperty),
        new("flat-vs-engine-atoms",
            MetamorphicSurface.EvaluatorRunFlat, MetamorphicSurface.EngineEvaluateToAtoms),
        new("flat-vs-engine-run",
            MetamorphicSurface.EvaluatorRunFlat, MetamorphicSurface.EngineRun),
        new("counted-vs-engine-run",
            MetamorphicSurface.EvaluatorRunCounted, MetamorphicSurface.EngineRun),
        new("engine-run-vs-engine-string",
            MetamorphicSurface.EngineRun, MetamorphicSurface.EngineEvaluateToString),
        new("engine-atoms-vs-engine-run",
            MetamorphicSurface.EngineEvaluateToAtoms, MetamorphicSurface.EngineRun),
    ];

    internal static int PairCount => Pairs.Length;

    /// <summary>Execution orders this family generates.</summary>
    internal static readonly ImmutableArray<MetamorphicExecutionOrder> Orders =
        [MetamorphicExecutionOrder.LeftFirst, MetamorphicExecutionOrder.RightFirst];

    /// <summary>Limit modes this family generates; see the type doc for why they are only these two.</summary>
    internal static readonly ImmutableArray<MetamorphicLimitMode> LimitModes =
        [MetamorphicLimitMode.Default, MetamorphicLimitMode.Generous];

    static MetamorphicEntryPointTemplate()
    {
        var ids = new HashSet<string>(StringComparer.Ordinal);
        foreach (var pair in Pairs)
        {
            if (!ids.Add(pair.Id))
                throw new MetamorphicHarnessException($"Duplicate surface pair id '{pair.Id}'.");

            if (pair.Shared == MetamorphicFacets.Outcome)
            {
                throw new MetamorphicHarnessException(
                    $"Surface pair '{pair.Id}' shares only the outcome facet, so comparing it would be vacuous.");
            }
        }

        var sourceIds = new HashSet<string>(StringComparer.Ordinal);
        foreach (var source in Sources)
        {
            if (!sourceIds.Add(source.Id))
                throw new MetamorphicHarnessException($"Duplicate entry-point source id '{source.Id}'.");
        }
    }

    internal static MetamorphicEntryPointSource SourceOf(MetamorphicParameters parameters)
        => Sources[parameters.Extra(SourceDimension)];

    internal static MetamorphicSurfacePair PairOf(MetamorphicParameters parameters)
        => Pairs[parameters.Extra(PairDimension)];

    internal static MetamorphicExecutionOrder OrderOf(MetamorphicParameters parameters)
        => Orders[parameters.Extra(OrderDimension)];

    internal static MetamorphicParameters Normalize(MetamorphicParameters parameters) => parameters;

    internal static MetamorphicPrecondition Validate(MetamorphicParameters parameters)
    {
        var source = SourceOf(parameters);
        var pair = PairOf(parameters);

        if (!source.Parses && pair.NeedsParsableSource)
            return MetamorphicPrecondition.Rejected("surface-pair-requires-a-parsable-source");

        if (pair.Shared == MetamorphicFacets.Outcome)
            return MetamorphicPrecondition.Rejected("surface-pair-shares-only-the-outcome");

        return MetamorphicPrecondition.Ok;
    }

    /// <summary>
    /// Counters are only claimed when BOTH surfaces hand back a budget, which is exactly the
    /// observed-vs-observed case. Every other pair declares no operational relation rather than
    /// comparing a real measurement against a structural zero.
    /// </summary>
    internal static MetamorphicOperationalRelation SelectOperationalRelation(
        MetamorphicParameters parameters, EvaluationLimits? limits)
    {
        var pair = PairOf(parameters);
        return pair.Shared.HasFlag(MetamorphicFacets.OperationalCounters)
            ? MetamorphicOperationalRelation.IdenticalWork
            : MetamorphicOperationalRelation.NotCompared;
    }

    internal static string DescribeVariant(MetamorphicParameters parameters)
    {
        var pair = PairOf(parameters);
        return $"entryPointSource={SourceOf(parameters).Id} pair={pair.Id} " +
               $"leftSurface={MetamorphicSurfaces.Get(pair.Left).Id} " +
               $"rightSurface={MetamorphicSurfaces.Get(pair.Right).Id} " +
               // The flags enum renders with ", " separators; the fingerprint uses spaces as its
               // own delimiter, so the shared-facet set is written without them.
               $"sharedFacets={pair.Shared.ToString().Replace(", ", "+", StringComparison.Ordinal)} " +
               $"order={OrderOf(parameters)}";
    }

    internal static MetamorphicCase Build(MetamorphicParameters parameters)
    {
        var source = SourceOf(parameters);
        var pair = PairOf(parameters);

        var testCase = MetamorphicCaseFactory.Create(
            parameters,
            source.Source,
            source.Source,
            Validate(parameters),
            $"entry-point source '{source.Id}' through {pair.Id}");

        // Every surface but the observed evaluator entry point runs the production optimizer
        // policy, so the pair is generated with optimizations ON and byte 5 is normalized away by
        // the registry (SupportsOptimizerPolicy: false).
        return testCase with
        {
            LeftProfile = new MetamorphicExecutionProfile(pair.Left, testCase.Limits, EnableOptimizations: true),
            RightProfile = new MetamorphicExecutionProfile(pair.Right, testCase.Limits, EnableOptimizations: true),
            ExecutionOrder = OrderOf(parameters),
        };
    }
}
