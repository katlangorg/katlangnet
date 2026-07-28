using System.Collections.Immutable;
using System.Globalization;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>The resource-budget laws Phase 3 tests. Each one fixes what the two members are.</summary>
internal enum MetamorphicBudgetLaw
{
    /// <summary>
    /// Laws 1 and 2 together: the left member runs AT the derived boundary and the right member
    /// at boundary + offset. A negative offset is the exact failure law (one below must stop with
    /// the dimension's own resource error), a non-negative one is monotonic success (a larger
    /// effective limit must still succeed, with the same result).
    /// </summary>
    BoundarySweep,

    /// <summary>
    /// Law 3: the dimension's baseline policy against limits comfortably above what the run
    /// needs. A limit that never binds must not change the result, the emitted count, or the work.
    /// </summary>
    InBudgetNeutral,

    /// <summary>
    /// Law 4: a control run, then a run that FAILS its reservation, then the control run again.
    /// The failing run must leave nothing behind.
    /// </summary>
    FailedReservationStability,

    /// <summary>
    /// Law 6: one immutable limits/options instance reused across independent runs — sequential
    /// with unrelated runs interleaved, or a bounded deterministic set of parallel runs.
    /// </summary>
    RunIsolation,

    /// <summary>
    /// Law 5: two TRUSTED EQUIVALENT FORMS (Phase 1/2 families) executed at the same derived
    /// boundary. Applied only to pairs whose declared operational relation is exact — never to a
    /// fused chain, whose materialization relation is directional by design.
    /// </summary>
    EquivalentFormBoundaryParity,
}

/// <summary>Which isolation shape a <see cref="MetamorphicBudgetLaw.RunIsolation"/> case uses.</summary>
internal enum MetamorphicIsolationMode
{
    /// <summary>Sequential: unrelated runs are interposed between the two observations.</summary>
    Sequential,

    /// <summary>A bounded, deterministic number of parallel observations sharing one options instance.</summary>
    BoundedParallel,
}

/// <summary>One compact program a budget law places limits around.</summary>
internal sealed record MetamorphicBudgetSource(string Id, string Source);

/// <summary>
/// One trusted equivalent-form pair from Phases 1 and 2, plus whether its declared relation is
/// exact enough to claim the WORK dimensions (steps and depth) share a boundary.
/// </summary>
/// <param name="SharesWorkBoundary">
/// True only for the user-defined extension call, where both spellings resolve to one and the
/// same invocation. A dotted BUILTIN link charges one extra step and one extra depth level than
/// its ordinary spelling — the repository documents this and Phase 2's relation deliberately
/// excludes those counters — so such a pair may only sweep the materialization and rendering
/// dimensions.
/// </param>
internal sealed record MetamorphicEquivalentForms(
    string Id, string Left, string Right, bool SharesWorkBoundary);

/// <summary>
/// Phase 3 Group D — the resource-budget laws.
///
/// <para><b>These are not arbitrary limit sweeps.</b> Every case knows which resource it
/// exercises and where that dimension's boundary came from
/// (<see cref="MetamorphicBoundaryPolicy"/>): four dimensions are read straight off the run's own
/// budget, two are found by a bounded deterministic probe, and the rendered-length one is measured
/// from the text the engine returned. Exactly ONE limit ever varies between the two members; every
/// other policy — including the optimizer-eligibility consequences of configuring a step or string
/// budget — is held constant by the dimension's own baseline.</para>
///
/// <para><b>Stack sufficiency is deliberately absent.</b> The host-stack backstop can only stop a
/// run EARLIER than the deterministic depth limit and is machine-dependent, so it is never used as
/// a boundary: a case that hits it is rejected by the executor with its own reason rather than
/// compared. The depth dimension tests the deterministic <c>MaxDepth</c> limit only.</para>
///
/// <para><b>Nothing here allocates from an encoded integer.</b> Sources are fixed compact
/// programs, the boundary offsets come from the frozen four-entry offset table, and the bounded
/// search has a fixed ceiling and a fixed probe budget.</para>
/// </summary>
internal static class MetamorphicBudgetLawTemplate
{
    private const int SourceDimension = 0;
    private const int LawDimension = 1;
    private const int ResourceDimension = 2;
    private const int IsolationDimension = 3;

    private const string F = MetamorphicTables.NamePrefix + "F";
    private const string V = MetamorphicTables.ReceiverProperty;
    private const string Double = MetamorphicTables.DoubleCallback;
    private const string Big = MetamorphicTables.BigCallback;

    /// <summary>Compact programs, each exercising several resource dimensions at small sizes.</summary>
    internal static readonly ImmutableArray<MetamorphicBudgetSource> Sources =
    [
        new("range-count", "Output = range(1, 12).count"),
        new("list-literal", $"{V} = [1, 2, 3, 4, 5]\nOutput = {V}.count"),
        new("string-rows", "Output = 'abcd', 'ef'"),
        new("string-projection", "Output = range(1, 4).count.string"),
        new("direct-recursion", $"{F}(0) = 0\n{F}(n) = {F}(n - 1)\nOutput = {F}(5)"),
        new("counted-loop", $"{V}Step = x + 1\nOutput = {V}Step.repeat(6, 0)"),
        new("map-pipeline", $"{Double}(x) = x * 2\nOutput = range(1, 6).map({Double})"),
        new("filter-count-pipeline", $"{Big}(x) = x > 2\nOutput = range(1, 9).filter({Big}).count"),
        new("nested-structures", "Output = [[1, 2], [3, 4]], (5, 6)"),
        new("mixed-collection", $"{V} = [1, 'ab', [2, 3]]\nOutput = {V}.count, {V}"),
        new("exact-collected-list", $"{F}(items...) = items\nOutput = {F}(1, 2, 3, 4)"),
    ];

    internal static int SourceCount => Sources.Length;

    /// <summary>
    /// Trusted equivalent forms from Phases 1 and 2, used by
    /// <see cref="MetamorphicBudgetLaw.EquivalentFormBoundaryParity"/>. Fused chains are
    /// deliberately absent: their materialization relation is directional, so requiring a shared
    /// boundary would contradict the relation Phase 2 established.
    /// </summary>
    internal static readonly ImmutableArray<MetamorphicEquivalentForms> Forms =
    [
        new("ordinary-vs-dotted-count",
            "Output = count(range(1, 10))", "Output = range(1, 10).count", SharesWorkBoundary: false),
        new("ordinary-vs-dotted-sum",
            "Output = sum(range(1, 6))", "Output = range(1, 6).sum", SharesWorkBoundary: false),
        new("ordinary-vs-dotted-take",
            "Output = take([1, 2, 3, 4], 2)", "Output = [1, 2, 3, 4].take(2)", SharesWorkBoundary: false),
        new("ordinary-vs-dotted-strings",
            "Output = count(['abc', 'de'])", "Output = ['abc', 'de'].count", SharesWorkBoundary: false),
        new("user-extension-ordinary-vs-dotted",
            $"{F}(r, a) = take(r, a)\n{V} = [1, 2, 3, 4]\nOutput = {F}({V}, 2)",
            $"{F}(r, a) = take(r, a)\n{V} = [1, 2, 3, 4]\nOutput = {V}.{F}(2)",
            SharesWorkBoundary: true),
        new("builtin-callback-vs-wrapper",
            $"{V} = [[1, 2], [3]]\nOutput = {V}.map(count)",
            $"{V} = [[1, 2], [3]]\n{MetamorphicTables.WrapperFunction}(a) = a.count\n" +
            $"Output = {V}.map({MetamorphicTables.WrapperFunction})",
            SharesWorkBoundary: false),
    ];

    internal static int FormCount => Forms.Length;

    /// <summary>
    /// Every program a boundary can be derived for, in payload order: the plain sources plus BOTH
    /// members of each equivalent-form pair.
    ///
    /// <para><c>Build</c> only ever derives from the left member, but the equivalent-form law then
    /// runs the right member at that same limit — so the boundary law's monotonicity obligation
    /// covers both members, and this is the set the deterministic full-interval sweep validates.</para>
    /// </summary>
    internal static readonly ImmutableArray<MetamorphicBudgetSource> BoundaryTemplates =
    [
        .. Sources,
        .. Forms.SelectMany(static form => new[]
        {
            new MetamorphicBudgetSource(form.Id + "/left", form.Left),
            new MetamorphicBudgetSource(form.Id + "/right", form.Right),
        }),
    ];

    internal static readonly ImmutableArray<MetamorphicBudgetLaw> Laws =
    [
        MetamorphicBudgetLaw.BoundarySweep,
        MetamorphicBudgetLaw.InBudgetNeutral,
        MetamorphicBudgetLaw.FailedReservationStability,
        MetamorphicBudgetLaw.RunIsolation,
        MetamorphicBudgetLaw.EquivalentFormBoundaryParity,
    ];

    internal static readonly ImmutableArray<MetamorphicIsolationMode> IsolationModes =
        [MetamorphicIsolationMode.Sequential, MetamorphicIsolationMode.BoundedParallel];

    /// <summary>Resource dimensions in payload order.</summary>
    internal static ImmutableArray<MetamorphicResourceDimensionDefinition> Dimensions
        => MetamorphicBoundaryPolicy.All;

    /// <summary>The one limit mode this family uses: it derives both sides' limits itself.</summary>
    internal static readonly ImmutableArray<MetamorphicLimitMode> LimitModes =
        [MetamorphicLimitMode.FamilyDerived];

    static MetamorphicBudgetLawTemplate()
    {
        if (Forms.Length > Sources.Length)
        {
            throw new MetamorphicHarnessException(
                "The equivalent-form table shares the source dimension and must not be larger than it.");
        }

        var ids = new HashSet<string>(StringComparer.Ordinal);
        foreach (var source in Sources)
        {
            if (!ids.Add(source.Id))
                throw new MetamorphicHarnessException($"Duplicate budget-law source id '{source.Id}'.");
        }

        foreach (var form in Forms)
        {
            if (!ids.Add(form.Id))
                throw new MetamorphicHarnessException($"Duplicate budget-law form id '{form.Id}'.");
        }
    }

    internal static MetamorphicBudgetLaw LawOf(MetamorphicParameters parameters)
        => Laws[parameters.Extra(LawDimension)];

    internal static MetamorphicBudgetSource SourceOf(MetamorphicParameters parameters)
        => Sources[parameters.Extra(SourceDimension)];

    internal static MetamorphicEquivalentForms FormsOf(MetamorphicParameters parameters)
        => Forms[parameters.Extra(SourceDimension) % Forms.Length];

    internal static MetamorphicResourceDimensionDefinition DimensionOf(MetamorphicParameters parameters)
        => Dimensions[parameters.Extra(ResourceDimension)];

    internal static MetamorphicIsolationMode IsolationOf(MetamorphicParameters parameters)
        => IsolationModes[parameters.Extra(IsolationDimension)];

    /// <summary>The signed offset applied to the derived boundary for the RIGHT member.</summary>
    internal static int BoundaryOffset(MetamorphicParameters parameters) => parameters.PrimaryOffset;

    /// <summary>
    /// Collapses the dimensions a law does not use, so distinct payloads cannot build the same
    /// case under different fingerprints. Idempotent, which <c>Decode(Encode(p)) == p</c> needs.
    /// </summary>
    internal static MetamorphicParameters Normalize(MetamorphicParameters parameters)
    {
        var law = LawOf(parameters);

        // Only the boundary laws read the offset byte.
        if (law is not (MetamorphicBudgetLaw.BoundarySweep or MetamorphicBudgetLaw.EquivalentFormBoundaryParity))
            parameters = parameters with { PrimaryOffsetIndex = CanonicalOffsetIndex };

        // Only the isolation law reads the isolation byte.
        if (law != MetamorphicBudgetLaw.RunIsolation)
            parameters = parameters.WithExtra(IsolationDimension, 0);

        // The equivalent-form law indexes a SHORTER table through the shared source byte.
        if (law == MetamorphicBudgetLaw.EquivalentFormBoundaryParity)
            parameters = parameters.WithExtra(SourceDimension, checked(parameters.Extra(SourceDimension) % Forms.Length));

        return parameters;
    }

    /// <summary>Index of the zero offset in the frozen offset table.</summary>
    private const int CanonicalOffsetIndex = 1;

    internal static MetamorphicPrecondition Validate(MetamorphicParameters parameters)
    {
        var law = LawOf(parameters);
        var dimension = DimensionOf(parameters);

        // Failed-RESERVATION stability needs a run that genuinely fails. The rendered-output limit
        // is a host rendering policy rather than an evaluation budget: below the boundary the run
        // still succeeds and the bounded writer returns a complete overflow indication, so there
        // is no reservation to fail and nothing for a later run to recover from.
        if (law == MetamorphicBudgetLaw.FailedReservationStability
            && dimension.Stop != MetamorphicBoundaryStop.ResourceError)
        {
            return MetamorphicPrecondition.Rejected("display-limit-does-not-fail-a-reservation");
        }

        if (law != MetamorphicBudgetLaw.EquivalentFormBoundaryParity)
            return MetamorphicPrecondition.Ok;

        var forms = FormsOf(parameters);
        var isWorkDimension = dimension.Dimension is MetamorphicResourceDimension.Depth or MetamorphicResourceDimension.Steps;
        return isWorkDimension && !forms.SharesWorkBoundary
            ? MetamorphicPrecondition.Rejected("equivalent-forms-do-not-share-a-work-boundary")
            : MetamorphicPrecondition.Ok;
    }

    internal static string DescribeVariant(MetamorphicParameters parameters)
    {
        var law = LawOf(parameters);
        var dimension = DimensionOf(parameters);
        var subject = law == MetamorphicBudgetLaw.EquivalentFormBoundaryParity
            ? FormsOf(parameters).Id
            : SourceOf(parameters).Id;

        var text = $"law={law} budgetSource={subject} resource={dimension.Id} " +
                   $"boundarySource={dimension.BoundarySource}";

        if (law is MetamorphicBudgetLaw.BoundarySweep or MetamorphicBudgetLaw.EquivalentFormBoundaryParity)
            text += " boundaryOffset=" + Signed(BoundaryOffset(parameters));
        if (law == MetamorphicBudgetLaw.RunIsolation)
            text += " isolation=" + IsolationOf(parameters);

        return text;
    }

    internal static MetamorphicCase Build(MetamorphicParameters parameters)
    {
        var law = LawOf(parameters);
        var dimension = DimensionOf(parameters);
        var precondition = Validate(parameters);

        var (leftSource, rightSource, subject) = law == MetamorphicBudgetLaw.EquivalentFormBoundaryParity
            ? (FormsOf(parameters).Left, FormsOf(parameters).Right, FormsOf(parameters).Id)
            : (SourceOf(parameters).Source, SourceOf(parameters).Source, SourceOf(parameters).Id);

        var testCase = MetamorphicCaseFactory.Create(
            parameters, leftSource, rightSource, precondition,
            $"budget law {law} on '{subject}' over {dimension.Id}");

        if (!precondition.Satisfied) return testCase;

        // The boundary is derived from the LEFT member under the dimension's own baseline, so the
        // measurement describes the same execution policy the sweep will run under.
        var boundary = MetamorphicBoundaryPolicy.Derive(leftSource, dimension.Dimension);
        if (!boundary.Found)
            return testCase with { Precondition = MetamorphicPrecondition.Rejected(boundary.Reason) };

        return law switch
        {
            MetamorphicBudgetLaw.BoundarySweep => BuildBoundarySweep(parameters, testCase, dimension, boundary.Value),
            MetamorphicBudgetLaw.EquivalentFormBoundaryParity =>
                BuildEquivalentFormParity(parameters, testCase, dimension, boundary.Value),
            MetamorphicBudgetLaw.InBudgetNeutral => BuildInBudgetNeutral(testCase, dimension, boundary.Value),
            MetamorphicBudgetLaw.FailedReservationStability =>
                BuildFailedReservationStability(testCase, dimension, boundary.Value),
            MetamorphicBudgetLaw.RunIsolation => BuildRunIsolation(parameters, testCase, dimension, boundary.Value),
            _ => throw new MetamorphicHarnessException($"No builder is implemented for budget law {law}."),
        };
    }

    private static MetamorphicCase BuildBoundarySweep(
        MetamorphicParameters parameters,
        MetamorphicCase testCase,
        MetamorphicResourceDimensionDefinition dimension,
        long boundary)
    {
        var offset = BoundaryOffset(parameters);
        var rightValue = checked(boundary + offset);

        var left = new MetamorphicExecutionProfile(
            dimension.Surface, MetamorphicBoundaryPolicy.LimitsAt(dimension.Dimension, boundary), EnableOptimizations: true);
        var right = new MetamorphicExecutionProfile(
            dimension.Surface, MetamorphicBoundaryPolicy.LimitsAt(dimension.Dimension, rightValue), EnableOptimizations: true);

        return testCase with
        {
            LeftProfile = left,
            RightProfile = right,
            // A negative offset is the exact FAILURE law; a non-negative one is monotonic success.
            SemanticRelation = offset < 0
                ? MetamorphicSemanticRelation.SameResourceBoundary
                : MetamorphicSemanticRelation.MonotonicSuccess,
            // Below the boundary the right member aborts, so its counters are a partial prefix.
            // At or above it, a limit that does not bind must not change the work either.
            OperationalRelation = offset < 0
                ? MetamorphicOperationalRelation.NotCompared
                : MetamorphicOperationalRelation.IdenticalWork,
            BoundaryStop = offset < 0 ? dimension.Stop : MetamorphicBoundaryStop.None,
            ExpectedResourceKind = dimension.ExpectedResourceKind,
            CollectEvidence = offset >= 0,
            Description = testCase.Description +
                $"; boundary {MetamorphicBoundaryPolicy.Describe(dimension.Dimension, boundary)}" +
                $", right at {rightValue.ToString(CultureInfo.InvariantCulture)}",
        };
    }

    private static MetamorphicCase BuildEquivalentFormParity(
        MetamorphicParameters parameters,
        MetamorphicCase testCase,
        MetamorphicResourceDimensionDefinition dimension,
        long boundary)
    {
        // BOTH forms run at the SAME limit. The claim is that two trusted equivalent forms cross
        // the same deterministic boundary — at the boundary both succeed, below it both fail with
        // the same structured resource error and the same payload.
        var value = checked(boundary + BoundaryOffset(parameters));
        var limits = MetamorphicBoundaryPolicy.LimitsAt(dimension.Dimension, value);
        var profile = new MetamorphicExecutionProfile(dimension.Surface, limits, EnableOptimizations: true);

        return testCase with
        {
            LeftProfile = profile,
            RightProfile = profile,
            SemanticRelation = MetamorphicSemanticRelation.SemanticEqual,
            OperationalRelation = MetamorphicOperationalRelation.ExactMaterializationEqual,
            Description = testCase.Description +
                $"; both forms at {MetamorphicBoundaryPolicy.Describe(dimension.Dimension, value)}",
        };
    }

    private static MetamorphicCase BuildInBudgetNeutral(
        MetamorphicCase testCase,
        MetamorphicResourceDimensionDefinition dimension,
        long boundary)
    {
        // The dimension's BASELINE is the default policy wherever configuring the dimension does
        // not change optimizer eligibility, and a deliberately non-binding limit of the same kind
        // where it does (steps and strings). Either way both members run the same execution
        // policy and differ only in a limit that cannot bind.
        var left = new MetamorphicExecutionProfile(dimension.Surface, dimension.Baseline, EnableOptimizations: true);
        var right = new MetamorphicExecutionProfile(
            dimension.Surface, MetamorphicBoundaryPolicy.GenerousLimits(dimension.Dimension, boundary),
            EnableOptimizations: true);

        return testCase with
        {
            LeftProfile = left,
            RightProfile = right,
            SemanticRelation = MetamorphicSemanticRelation.SemanticEqual,
            OperationalRelation = MetamorphicOperationalRelation.IdenticalWork,
            // Identical work includes identical optimizer evidence, which is how this law proves
            // the generous limit did not quietly switch an optimizer off.
            CollectEvidence = true,
            Description = testCase.Description + "; baseline policy against a comfortably generous limit",
        };
    }

    private static MetamorphicCase BuildFailedReservationStability(
        MetamorphicCase testCase,
        MetamorphicResourceDimensionDefinition dimension,
        long boundary)
    {
        var profile = new MetamorphicExecutionProfile(
            dimension.Surface, MetamorphicBoundaryPolicy.GenerousLimits(dimension.Dimension, boundary),
            EnableOptimizations: true);

        return testCase with
        {
            LeftProfile = profile,
            RightProfile = profile,
            RunPlan = MetamorphicRunPlan.AfterFailedRun,
            InterferenceSource = testCase.LeftSource,
            // One below the boundary, so the interposed run genuinely fails the reservation this
            // dimension guards — the executor rejects the case if it does not.
            InterferenceLimits = MetamorphicBoundaryPolicy.LimitsAt(dimension.Dimension, checked(boundary - 1)),
            SemanticRelation = MetamorphicSemanticRelation.IndependentRunStable,
            OperationalRelation = MetamorphicOperationalRelation.IdenticalWork,
            CollectEvidence = true,
            Description = testCase.Description +
                $"; control run repeated after a run that fails at {(boundary - 1).ToString(CultureInfo.InvariantCulture)}",
        };
    }

    private static MetamorphicCase BuildRunIsolation(
        MetamorphicParameters parameters,
        MetamorphicCase testCase,
        MetamorphicResourceDimensionDefinition dimension,
        long boundary)
    {
        var mode = IsolationOf(parameters);
        var profile = new MetamorphicExecutionProfile(
            dimension.Surface, MetamorphicBoundaryPolicy.GenerousLimits(dimension.Dimension, boundary),
            EnableOptimizations: true);

        return testCase with
        {
            LeftProfile = profile,
            RightProfile = profile,
            RunPlan = mode == MetamorphicIsolationMode.Sequential
                ? MetamorphicRunPlan.AfterInterleavedRuns
                : MetamorphicRunPlan.BoundedParallel,
            SemanticRelation = MetamorphicSemanticRelation.IndependentRunStable,
            OperationalRelation = MetamorphicOperationalRelation.IdenticalWork,
            CollectEvidence = true,
            Description = testCase.Description + $"; {mode} isolation over one shared limits instance",
        };
    }

    private static string Signed(int value)
        => (value >= 0 ? "+" : "") + value.ToString(CultureInfo.InvariantCulture);
}
