using System.Collections.Immutable;
using System.Globalization;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>One deterministic resource dimension a budget law may exercise.</summary>
internal enum MetamorphicResourceDimension
{
    /// <summary>Simultaneously active dynamic invocations (<c>MaxDepth</c>).</summary>
    Depth,

    /// <summary>Cumulative semantic work (<c>MaxSteps</c>).</summary>
    Steps,

    /// <summary>Immediate item slots in ONE materialized collection (<c>MaxCollectionItems</c>).</summary>
    PerCollectionItems,

    /// <summary>Item slots materialized across the whole run (<c>MaxMaterializedItems</c>).</summary>
    CumulativeItems,

    /// <summary>UTF-16 units in ONE language string (<c>MaxStringLength</c>).</summary>
    PerStringLength,

    /// <summary>UTF-16 units materialized across the whole run (<c>MaxMaterializedStringChars</c>).</summary>
    CumulativeStringChars,

    /// <summary>UTF-16 units ONE rendered display string may return (<c>MaxDisplayLength</c>).</summary>
    DisplayLength,
}

/// <summary>How a dimension's boundary is obtained.</summary>
internal enum MetamorphicBoundarySource
{
    /// <summary>Read straight off the run's own budget — exact by construction.</summary>
    MeasuredCounter,

    /// <summary>Read off the rendered text the engine returned.</summary>
    MeasuredRendering,

    /// <summary>Found by a bounded, deterministic search, then VERIFIED below/at/above.</summary>
    BoundedSearch,
}

/// <summary>
/// Why a boundary derivation stopped where it did.
///
/// <para>This is the classification the deterministic full-interval tests read. It is
/// deliberately separate from the REASON text: the reason is the harness-visible rejection
/// string, which is part of the campaign's reporting surface and must not drift, while this
/// says which of the search's documented terminating conditions was reached.</para>
/// </summary>
internal enum MetamorphicBoundaryStopReason
{
    /// <summary>A first success was found strictly above the interval's lower bound.</summary>
    Found,

    /// <summary>
    /// The interval's LOWER BOUND already succeeds, so there is no failing neighbour and no
    /// transition to locate. The value is still reported, and <c>Derive</c> rejects it because a
    /// boundary law needs a legal "one below" case.
    /// </summary>
    LowerBoundAlreadySucceeds,

    /// <summary>No probed limit inside the interval succeeded, including the ceiling itself.</summary>
    NoSuccessInInterval,

    /// <summary>The fixed probe budget ran out before the interval was resolved.</summary>
    ProbeBudgetExhausted,

    /// <summary>The measurement run itself could not be observed (a template precondition).</summary>
    Unobservable,

    /// <summary>The measured counter or rendering shows the source never touches this dimension.</summary>
    DimensionNotExercised,
}

/// <summary>
/// The CLOSED interval a bounded search may probe for one dimension, exposed so the
/// deterministic tests can sweep exactly what the search can reach — no wider, no narrower.
/// </summary>
internal readonly record struct MetamorphicBoundaryInterval(
    MetamorphicResourceDimension Dimension, string Id, long Low, long High)
{
    /// <summary>Limit values in the interval, inclusive of both ends.</summary>
    public long Count => checked(High - Low + 1);

    public override string ToString()
        => $"{Id}[{Low.ToString(CultureInfo.InvariantCulture)}..{High.ToString(CultureInfo.InvariantCulture)}]";
}

/// <summary>
/// Everything the harness knows about one resource dimension, declared as data.
///
/// <para><b>Baseline vs value.</b> A boundary is only meaningful if it was derived under the
/// SAME execution policy the boundary runs use. Two dimensions need care there: configuring any
/// step budget switches the loop optimizer off, and configuring either string budget switches
/// the sequence-pipeline optimizer off (<c>Evaluator.CreateRootCtx</c>). So those dimensions
/// measure under a deliberately generous limit of their OWN kind rather than under the default
/// policy — the measurement then describes the same execution the sweep will run, and only one
/// limit ever varies.</para>
/// </summary>
internal sealed record MetamorphicResourceDimensionDefinition(
    MetamorphicResourceDimension Dimension,
    string Id,
    MetamorphicBoundarySource BoundarySource,
    long MinimumLegalLimit,
    long SearchCeiling,
    string ExpectedResourceKind,
    MetamorphicBoundaryStop Stop,
    MetamorphicSurface Surface,
    EvaluationLimits? Baseline,
    Func<long, EvaluationLimits> WithValue)
{
    /// <summary>The smallest boundary that leaves room for a one-below case.</summary>
    public long SmallestUsableBoundary => checked(MinimumLegalLimit + 1);
}

/// <summary>
/// Derives the exact limit at which one trusted source stops fitting in one resource dimension.
///
/// <para><b>Measured wherever possible.</b> Four of the seven dimensions are read straight off
/// the run's own <c>EvaluationBudget</c>, which makes them exact rather than estimated: a run
/// that charged <c>S</c> steps succeeds at <c>MaxSteps = S</c> and fails at <c>S - 1</c>, and a
/// run that reserved <c>M</c> item slots succeeds at <c>MaxMaterializedItems = M</c> and fails at
/// <c>M - 1</c> on its LAST reservation (both budgets check before moving any counter, so a
/// rejected reservation leaves the total untouched).</para>
///
/// <para><b>Bounded search only where nothing counts it.</b> The two per-object ceilings —
/// largest single collection, longest single string — are not accumulated anywhere, so they are
/// found by a deterministic exponential-then-binary probe over a fixed, small ceiling with a
/// fixed probe budget. The search ASSUMES success is monotone in the limit; it never asserts it.
/// Whatever it finds is then verified by the below/at/above executions the law performs, so a
/// violation of monotonicity surfaces as a mismatch rather than as a silently wrong boundary.
/// Nothing here allocates from an encoded integer, and no unbounded search is ever performed.</para>
/// </summary>
internal static class MetamorphicBoundaryPolicy
{
    /// <summary>Step budget the step dimension measures under — high enough never to bind.</summary>
    internal const long StepProbeCeiling = 100_000;

    /// <summary>Cumulative string budget the string dimension measures under.</summary>
    internal const long StringProbeCeiling = 100_000;

    /// <summary>Largest per-collection / per-string limit the bounded search will probe.</summary>
    internal const long SearchCeilingItems = 4_096;

    /// <summary>Probes one bounded search may perform. Exceeding it is a rejection, never a hang.</summary>
    internal const int MaxSearchProbes = 32;

    private static readonly ImmutableArray<MetamorphicResourceDimensionDefinition> Definitions =
    [
        new(MetamorphicResourceDimension.Depth, "depth",
            MetamorphicBoundarySource.MeasuredCounter,
            MinimumLegalLimit: 1, SearchCeiling: EvaluationLimits.MaxSupportedDepth,
            ExpectedResourceKind: nameof(EvalError.EvaluationDepthExceeded),
            MetamorphicBoundaryStop.ResourceError,
            MetamorphicSurface.EvaluatorRunCountedObserved,
            Baseline: null,
            WithValue: static value => new EvaluationLimits { MaxDepth = ToDepth(value) }),

        new(MetamorphicResourceDimension.Steps, "steps",
            MetamorphicBoundarySource.MeasuredCounter,
            MinimumLegalLimit: 1, SearchCeiling: StepProbeCeiling,
            ExpectedResourceKind: nameof(EvalError.EvaluationStepLimitExceeded),
            MetamorphicBoundaryStop.ResourceError,
            MetamorphicSurface.EvaluatorRunCountedObserved,
            // A configured step budget switches the loop optimizer off, so the measurement must
            // carry one too or it would describe a different execution than the sweep.
            Baseline: new EvaluationLimits { MaxSteps = StepProbeCeiling },
            WithValue: static value => new EvaluationLimits { MaxSteps = value }),

        new(MetamorphicResourceDimension.PerCollectionItems, "per-collection-items",
            MetamorphicBoundarySource.BoundedSearch,
            MinimumLegalLimit: 1, SearchCeiling: SearchCeilingItems,
            ExpectedResourceKind: nameof(EvalError.CollectionSizeLimitExceeded),
            MetamorphicBoundaryStop.ResourceError,
            MetamorphicSurface.EvaluatorRunCountedObserved,
            Baseline: null,
            WithValue: static value => new EvaluationLimits { MaxCollectionItems = ToCollection(value) }),

        new(MetamorphicResourceDimension.CumulativeItems, "cumulative-items",
            MetamorphicBoundarySource.MeasuredCounter,
            MinimumLegalLimit: 1, SearchCeiling: SearchCeilingItems,
            ExpectedResourceKind: nameof(EvalError.MaterializationLimitExceeded),
            MetamorphicBoundaryStop.ResourceError,
            MetamorphicSurface.EvaluatorRunCountedObserved,
            Baseline: null,
            WithValue: static value => new EvaluationLimits { MaxMaterializedItems = value }),

        new(MetamorphicResourceDimension.PerStringLength, "per-string-length",
            MetamorphicBoundarySource.BoundedSearch,
            MinimumLegalLimit: 0, SearchCeiling: SearchCeilingItems,
            ExpectedResourceKind: nameof(EvalError.StringSizeLimitExceeded),
            MetamorphicBoundaryStop.ResourceError,
            MetamorphicSurface.EvaluatorRunCountedObserved,
            // Either string budget switches the sequence-pipeline optimizer off; measure with one.
            Baseline: new EvaluationLimits { MaxStringLength = EvaluationLimits.MaxSupportedStringLength },
            WithValue: static value => new EvaluationLimits { MaxStringLength = ToStringLimit(value) }),

        new(MetamorphicResourceDimension.CumulativeStringChars, "cumulative-string-chars",
            MetamorphicBoundarySource.MeasuredCounter,
            MinimumLegalLimit: 0, SearchCeiling: StringProbeCeiling,
            ExpectedResourceKind: nameof(EvalError.StringMaterializationLimitExceeded),
            MetamorphicBoundaryStop.ResourceError,
            MetamorphicSurface.EvaluatorRunCountedObserved,
            Baseline: new EvaluationLimits { MaxMaterializedStringChars = StringProbeCeiling },
            WithValue: static value => new EvaluationLimits { MaxMaterializedStringChars = value }),

        new(MetamorphicResourceDimension.DisplayLength, "display-length",
            MetamorphicBoundarySource.MeasuredRendering,
            MinimumLegalLimit: 0, SearchCeiling: EvaluationLimits.MaxSupportedDisplayLength,
            // Display length is a host RENDERING policy: the run still succeeds and the bounded
            // writer returns a complete overflow indication, so there is no evaluation error.
            ExpectedResourceKind: nameof(EvalError.DisplayLengthLimitExceeded),
            MetamorphicBoundaryStop.RenderingTruncation,
            MetamorphicSurface.EngineRun,
            Baseline: null,
            WithValue: static value => new EvaluationLimits { MaxDisplayLength = ToDisplay(value) }),
    ];

    static MetamorphicBoundaryPolicy()
    {
        if (Definitions.Length != Enum.GetValues<MetamorphicResourceDimension>().Length)
            throw new MetamorphicHarnessException("Every resource dimension needs a registered definition.");

        var ids = new HashSet<string>(StringComparer.Ordinal);
        foreach (var definition in Definitions)
        {
            if (!ids.Add(definition.Id))
                throw new MetamorphicHarnessException($"Duplicate resource dimension id '{definition.Id}'.");
        }
    }

    internal static ImmutableArray<MetamorphicResourceDimensionDefinition> All => Definitions;

    internal static MetamorphicResourceDimensionDefinition Get(MetamorphicResourceDimension dimension)
    {
        foreach (var definition in Definitions)
        {
            if (definition.Dimension == dimension) return definition;
        }

        throw new ArgumentOutOfRangeException(nameof(dimension), dimension, "No definition is registered for this dimension.");
    }

    /// <summary>
    /// The derived boundary, or the reason no usable one exists for this source.
    ///
    /// <para><see cref="Reason"/> is the campaign-visible rejection text and must stay stable;
    /// <see cref="Stop"/> is the structured classification the deterministic tests assert on, and
    /// <see cref="Probes"/> is how many EXECUTIONS the derivation cost, which is what bounds it.</para>
    /// </summary>
    internal readonly record struct Boundary(
        bool Found,
        long Value,
        string Reason,
        MetamorphicBoundaryStopReason Stop = MetamorphicBoundaryStopReason.Found,
        int Probes = 0)
    {
        internal static Boundary At(long value, int probes = 0)
            => new(true, value, "ok", MetamorphicBoundaryStopReason.Found, probes);

        /// <summary>A first success that sits ON the interval's lower bound: no failing neighbour.</summary>
        internal static Boundary AtLowerBound(long value, int probes)
            => new(true, value, "ok", MetamorphicBoundaryStopReason.LowerBoundAlreadySucceeds, probes);

        internal static Boundary Unusable(string reason, MetamorphicBoundaryStopReason stop, int probes = 0)
            => new(false, 0, reason, stop, probes);
    }

    /// <summary>
    /// Derives the smallest limit at which <paramref name="source"/> still fits in
    /// <paramref name="dimension"/>. Returns an unusable boundary — a REJECTION reason, never a
    /// mismatch — when the source does not exercise the dimension at all, when the boundary is
    /// too small to have a legal "one below" neighbour, or when the bounded search did not find
    /// one inside its ceiling.
    /// </summary>
    internal static Boundary Derive(string source, MetamorphicResourceDimension dimension)
    {
        var definition = Get(dimension);

        var boundary = definition.BoundarySource switch
        {
            MetamorphicBoundarySource.MeasuredCounter => MeasureCounter(source, definition),
            MetamorphicBoundarySource.MeasuredRendering => MeasureRendering(source, definition),
            MetamorphicBoundarySource.BoundedSearch => Search(source, definition),
            _ => Boundary.Unusable("unknown-boundary-source", MetamorphicBoundaryStopReason.Unobservable),
        };

        if (!boundary.Found) return boundary;

        // A boundary law needs a LEGAL one-below neighbour. A first success that sits on the
        // interval's lower bound has none, which the search already classified.
        return boundary.Value < definition.SmallestUsableBoundary
            ? boundary with
            {
                Found = false,
                Value = 0,
                Reason = $"{definition.Id}-boundary-below-smallest-usable-limit",
                Stop = MetamorphicBoundaryStopReason.LowerBoundAlreadySucceeds,
            }
            : boundary;
    }

    /// <summary>
    /// The closed interval a bounded search may probe. The deterministic full-interval
    /// monotonicity test sweeps EXACTLY this, so the law it proves covers everything the search
    /// could ever return.
    /// </summary>
    internal static MetamorphicBoundaryInterval IntervalOf(MetamorphicResourceDimension dimension)
    {
        var definition = Get(dimension);
        return new MetamorphicBoundaryInterval(
            dimension, definition.Id, definition.MinimumLegalLimit, definition.SearchCeiling);
    }

    /// <summary>Every dimension whose boundary comes from a bounded search rather than a measurement.</summary>
    internal static IEnumerable<MetamorphicResourceDimensionDefinition> SearchedDimensions
        => Definitions.Where(static definition => definition.BoundarySource == MetamorphicBoundarySource.BoundedSearch);

    /// <summary>Limits placing <paramref name="dimension"/> at <paramref name="value"/>.</summary>
    internal static EvaluationLimits LimitsAt(MetamorphicResourceDimension dimension, long value)
        => Get(dimension).WithValue(value);

    /// <summary>
    /// Limits that are comfortably ABOVE what a run needs in one dimension while keeping every
    /// other policy identical to the dimension's baseline — the in-budget-neutrality partner of
    /// <see cref="LimitsAt"/>.
    /// </summary>
    internal static EvaluationLimits GenerousLimits(MetamorphicResourceDimension dimension, long boundary)
    {
        var definition = Get(dimension);
        var generous = checked(boundary + (boundary < 1_000 ? 1_000 : boundary));
        return definition.WithValue(generous > definition.SearchCeiling ? definition.SearchCeiling : generous);
    }

    private static Boundary MeasureCounter(string source, MetamorphicResourceDimensionDefinition definition)
    {
        if (!Observe(source, definition, definition.Baseline, out var observation, out var reason))
            return Boundary.Unusable(reason, MetamorphicBoundaryStopReason.Unobservable, 1);

        if (observation.Semantic.Outcome != "ok")
            return Boundary.Unusable(
                $"{definition.Id}-baseline-run-did-not-succeed", MetamorphicBoundaryStopReason.Unobservable, 1);

        var measured = definition.Dimension switch
        {
            MetamorphicResourceDimension.Depth => observation.PeakDynamicDepth,
            MetamorphicResourceDimension.Steps => observation.EvaluationSteps,
            MetamorphicResourceDimension.CumulativeItems => observation.MaterializedItems,
            MetamorphicResourceDimension.CumulativeStringChars => observation.MaterializedStringChars,
            _ => throw new MetamorphicHarnessException(
                $"{definition.Id} is not a measured-counter dimension."),
        };

        return measured <= 0
            ? Boundary.Unusable(
                $"{definition.Id}-not-exercised-by-this-source",
                MetamorphicBoundaryStopReason.DimensionNotExercised, 1)
            : Boundary.At(measured, 1);
    }

    private static Boundary MeasureRendering(string source, MetamorphicResourceDimensionDefinition definition)
    {
        if (!Observe(source, definition, definition.Baseline, out var observation, out var reason))
            return Boundary.Unusable(reason, MetamorphicBoundaryStopReason.Unobservable, 1);

        if (observation.Projection is not { RenderedText: { } text })
            return Boundary.Unusable(
                $"{definition.Id}-surface-rendered-nothing", MetamorphicBoundaryStopReason.Unobservable, 1);

        return text.Length <= 0
            ? Boundary.Unusable(
                $"{definition.Id}-not-exercised-by-this-source",
                MetamorphicBoundaryStopReason.DimensionNotExercised, 1)
            : Boundary.At(text.Length, 1);
    }

    /// <summary>
    /// Deterministic exponential-then-binary probe for the FIRST limit inside
    /// <see cref="IntervalOf"/> at which the source succeeds.
    ///
    /// <para>Bounded four ways: by the interval's explicit ceiling, by
    /// <see cref="MaxSearchProbes"/> EXECUTIONS, by checked arithmetic on every candidate, and by
    /// only ever varying ONE limit away from the dimension's baseline. Every terminating condition
    /// is classified rather than collapsed into one "not found": a lower bound that already
    /// succeeds, an interval with no success in it, and an exhausted probe budget are three
    /// different facts about the template, and the deterministic tests assert which one
    /// occurred.</para>
    ///
    /// <para>The search ASSUMES success is monotone in the limit; it never asserts it. That
    /// assumption is discharged separately and exhaustively by
    /// <c>MetamorphicPhase3FamilyTests.SearchedBoundaries_AreMonotoneAcrossTheirCompleteInterval</c>,
    /// which sweeps every value of this interval for every registered template and both optimizer
    /// policies.</para>
    /// </summary>
    private static Boundary Search(string source, MetamorphicResourceDimensionDefinition definition)
    {
        var interval = IntervalOf(definition.Dimension);
        var probes = 0;

        // Anything at or below `low` is known to FAIL; `high` is the first known success.
        var low = checked(interval.Low - 1);
        long high = -1;

        for (var candidate = Math.Max(interval.Low, 1); candidate <= interval.High; candidate = checked(candidate * 2))
        {
            if (++probes > MaxSearchProbes) return ProbeBudget(definition, probes);
            if (SucceedsAt(source, definition, candidate)) { high = candidate; break; }
            low = candidate;
        }

        if (high < 0)
        {
            // The ceiling itself may be the first success when doubling overshot it.
            if (++probes > MaxSearchProbes) return ProbeBudget(definition, probes);
            if (!SucceedsAt(source, definition, interval.High))
            {
                return Boundary.Unusable(
                    $"{definition.Id}-no-success-below-search-ceiling",
                    MetamorphicBoundaryStopReason.NoSuccessInInterval,
                    probes);
            }

            high = interval.High;
        }

        while (checked(high - low) > 1)
        {
            if (++probes > MaxSearchProbes) return ProbeBudget(definition, probes);
            var middle = checked(low + ((high - low) / 2));
            if (SucceedsAt(source, definition, middle)) high = middle;
            else low = middle;
        }

        // The interval's lower bound may itself already succeed, in which case there is no failing
        // neighbour and no transition was located. Say so; Derive turns it into a rejection.
        return high <= interval.Low ? Boundary.AtLowerBound(high, probes) : Boundary.At(high, probes);
    }

    private static Boundary ProbeBudget(MetamorphicResourceDimensionDefinition definition, int probes)
        => Boundary.Unusable(
            $"{definition.Id}-search-probe-budget", MetamorphicBoundaryStopReason.ProbeBudgetExhausted, probes);

    /// <summary>
    /// The ONE success predicate. The bounded search and the deterministic full-interval
    /// monotonicity test both call this, so the test can never prove a law about a different
    /// notion of "fits" than the search uses.
    /// </summary>
    internal static bool SucceedsAt(
        string source,
        MetamorphicResourceDimensionDefinition definition,
        long value,
        bool enableOptimizations = true)
        => TryObserveAt(source, definition, value, out var observation, enableOptimizations)
            && observation.Semantic.Outcome == "ok";

    /// <summary>
    /// Runs <paramref name="source"/> at exactly one limit value of one dimension, through the
    /// dimension's own surface, and hands back what it produced. Shared by the search predicate
    /// and by the deterministic tests so both observe identically.
    /// </summary>
    internal static bool TryObserveAt(
        string source,
        MetamorphicResourceDimensionDefinition definition,
        long value,
        out MetamorphicOperationalObservation observation,
        bool enableOptimizations = true)
        => Observe(source, definition, definition.WithValue(value), out observation, out _, enableOptimizations);

    private static bool Observe(
        string source,
        MetamorphicResourceDimensionDefinition definition,
        EvaluationLimits? limits,
        out MetamorphicOperationalObservation observation,
        out string reason,
        bool enableOptimizations = true)
    {
        var profile = new MetamorphicExecutionProfile(definition.Surface, limits, enableOptimizations);
        if (MetamorphicSurfaces.TryObserve(
                source, profile, MetamorphicExecutor.OptionsFor(profile), collectEvidence: false, out observation, out var why))
        {
            reason = "ok";
            return true;
        }

        reason = $"{definition.Id}-baseline-{why}";
        return false;
    }

    private static int ToDepth(long value)
        => value >= EvaluationLimits.MaxSupportedDepth ? EvaluationLimits.MaxSupportedDepth : (int)value;

    private static int ToCollection(long value)
        => value >= EvaluationLimits.MaxSupportedCollectionItems
            ? EvaluationLimits.MaxSupportedCollectionItems
            : (int)value;

    private static int ToStringLimit(long value)
        => value >= EvaluationLimits.MaxSupportedStringLength ? EvaluationLimits.MaxSupportedStringLength : (int)value;

    private static int ToDisplay(long value)
        => value >= EvaluationLimits.MaxSupportedDisplayLength ? EvaluationLimits.MaxSupportedDisplayLength : (int)value;

    /// <summary>Stable text for reports and fingerprints.</summary>
    internal static string Describe(MetamorphicResourceDimension dimension, long boundary)
        => Get(dimension).Id + "@" + boundary.ToString(CultureInfo.InvariantCulture);
}
