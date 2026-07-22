using System.Globalization;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Relation families. A family names ONE trusted template plus the equivalence argument
/// that justifies comparing the pair it generates. Adding a family means adding a template
/// whose construction guarantees the declared relation — never a textual rewriting of an
/// arbitrary mutated program.
///
/// <para>Enum values are a compatibility surface: the Phase 1 family must stay registry index
/// 0, because a version-zero payload resolves there.</para>
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

    /// <summary>
    /// Phase 2 Group A: <c>F(receiver, suffix...)</c> against <c>receiver.F(suffix...)</c> over
    /// the trusted collection builtins and every receiver value kind.
    /// </summary>
    DottedCollectionBuiltin,

    /// <summary>
    /// Phase 2 Group B: the same rewrite for a USER-defined function, where the receiver
    /// expression's single evaluation is the operationally visible property.
    /// </summary>
    UserExtensionCall,

    /// <summary>
    /// Phase 2 Group C: a bounded dotted chain against the nested ordinary call the template
    /// builds structurally from the same link list.
    /// </summary>
    DottedChain,

    /// <summary>
    /// Phase 2 Group D: a direct builtin callback against a user wrapper with a provably
    /// equivalent callback projection.
    /// </summary>
    BuiltinCallbackWrapper,

    /// <summary>
    /// Phase 3 Group A: ONE trusted source executed twice, once with the optimizers enabled and
    /// once with them disabled. Admitted only when the optimized run is PROVEN to have taken the
    /// intended optimizer path.
    /// </summary>
    OptimizerGenericParity,

    /// <summary>
    /// Phase 3 Group B: a program that reuses one zero-argument property against a rebuilt form
    /// that constructs the same value independently for each use.
    /// </summary>
    CachedPropertyReuse,

    /// <summary>
    /// Phase 3 Group C: ONE trusted source executed through two runtime entry points, compared
    /// on the intersection of what those surfaces can actually project.
    /// </summary>
    EntryPointParity,

    /// <summary>
    /// Phase 3 Group D: resource-budget laws — boundary sweeps, in-budget neutrality,
    /// failed-reservation stability, and sequential/parallel run isolation.
    /// </summary>
    BudgetLaw,
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

    /// <summary>
    /// The two members agree on every facet BOTH of their surfaces actually project
    /// (<see cref="MetamorphicFacets"/>): outcome always, plus structured error, neutral value,
    /// emitted count, host atoms, and rendered text wherever both sides report them. Declared for
    /// entry-point parity, where demanding <see cref="SemanticEqual"/> would compare fields one
    /// surface cannot produce and silently pass on <c>null == null</c>.
    /// </summary>
    SameStructuredOutcome,

    /// <summary>
    /// One-directional: IF the left member succeeded, the right member — running the same source
    /// at a larger effective limit — must also succeed and agree on every shared facet. A left
    /// member that did not succeed places no obligation on the right, which is exactly what makes
    /// this a monotonicity law rather than an equality.
    /// </summary>
    MonotonicSuccess,

    /// <summary>
    /// The exact boundary law: the left member (at the derived boundary) must succeed, and the
    /// right member (one unit below it) must stop in the way the case DECLARED — with the
    /// dimension's structured resource error, or, for the rendering dimension, with a bounded
    /// truncated rendering. Both the required stop kind and the expected resource error live on
    /// the case, so the comparator reads data rather than special-casing a dimension.
    /// </summary>
    SameResourceBoundary,

    /// <summary>
    /// Both members are INDEPENDENT executions that must be indistinguishable: same semantics,
    /// same projections, same counters, same optimizer and cache evidence. Declared for
    /// failed-reservation stability and for sequential/bounded-parallel run isolation, where any
    /// difference at all means run state leaked.
    /// </summary>
    IndependentRunStable,
}

/// <summary>
/// The declared OPERATIONAL relation between the two members of a pair.
///
/// <para><b>Every operational relation below carries one qualification.</b> Operational counters
/// are compared only when BOTH executions complete. When either side stops at a structured
/// resource limit, semantic outcome, resource-limit kind, and structured payload remain
/// comparable, but partial work counters are not: an aborted run's counters are the prefix
/// recorded at the abort point, and two equivalent forms may legitimately have done different
/// preparatory work before reaching the same limit. Ordinary (non-resource) semantic failures are
/// NOT exempt — their counters are compared exactly like a successful run's. The gate is
/// <see cref="MetamorphicComparator.WorkIsComparable"/>.</para>
///
/// <para>A relation is additionally skipped when either surface does not project operational
/// counters at all (<see cref="MetamorphicFacets.OperationalCounters"/>), which is the normal
/// case for entry-point parity: only <c>Evaluator.RunCountedObserved</c> hands back a budget.</para>
/// </summary>
internal enum MetamorphicOperationalRelation
{
    /// <summary>
    /// Exact equality of materialized collection-item slots and materialized string UTF-16
    /// units, plus the same relevant resource-limit verdict. Deliberately NOT every counter:
    /// evaluation steps and peak dynamic depth are recorded for diagnostics only, because the
    /// two forms may legitimately differ in invocation accounting (a dotted zero-argument link
    /// charges one step and one depth level; a user wrapper adds a whole invocation).
    /// </summary>
    ExactMaterializationEqual,

    /// <summary>
    /// Everything <see cref="ExactMaterializationEqual"/> requires PLUS exact equality of
    /// evaluation steps and peak dynamic depth. Declared only where the repository already
    /// establishes that contract — currently the user-defined extension call, whose two
    /// spellings resolve to one and the same user invocation
    /// (<c>OperationalMetamorphicTests.UserExtensionCall_ChargesTheSameInBothForms</c>).
    /// </summary>
    ExactObservedWorkEqual,

    /// <summary>
    /// The RIGHT member never materializes MORE than the left. Declared where the right form is
    /// eligible for sequence-pipeline FUSION and the left form is not: a fused pipeline that
    /// materializes nothing legitimately charges less, and demanding equality would forbid the
    /// fusion the runtime documents. The inequality still catches the failure mode that matters —
    /// a dotted form doing MORE work than its ordinary equivalent, which is exactly how the
    /// duplicate dotted-receiver materialization defect presented.
    ///
    /// <para>Declared only where fusion is EFFECTIVELY eligible
    /// (<see cref="MetamorphicLimitPolicy.SequencePipelineFusionCanApply"/>: the optimizer flag
    /// plus the string and step budgets that switch the sequence-pipeline optimizer off).
    /// Measured: wherever fusion is ineligible the two forms agree exactly on all 144
    /// chain/receiver pairs, so those policies keep the exact check.</para>
    /// </summary>
    MaterializationNeverIncreases,

    /// <summary>
    /// Everything <see cref="MaterializationNeverIncreases"/> requires PLUS "the left member
    /// never charges more evaluation STEPS than the right".
    ///
    /// <para>Declared where the left member is permitted to do strictly less TOTAL work than an
    /// otherwise identical right member: an optimized run against the generic run of the same
    /// source, and a cached-property run against the rebuilt form that constructs the same value
    /// independently. Peak dynamic depth is deliberately NOT part of it — an optimized loop plan
    /// can legitimately reach a different nesting profile than the generic interpreter, so the
    /// depth is recorded and reported but never a failure condition.</para>
    /// </summary>
    WorkNeverIncreases,

    /// <summary>
    /// The two members did EXACTLY the same amount of work: materialized items, materialized
    /// string units, evaluation steps, and peak dynamic depth all equal. Declared for in-budget
    /// neutrality (a limit generous enough never to bind must not change what a run does) and for
    /// run isolation (an independent repeat of one run must charge identically).
    /// </summary>
    IdenticalWork,

    /// <summary>
    /// No operational claim at all. Declared where at least one surface cannot report counters —
    /// entry-point parity across surfaces that do not hand back a budget — so the case is a
    /// purely semantic comparison and says so rather than pretending equality.
    /// </summary>
    NotCompared,
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

/// <summary>How the executor should sequence the two observations of one case.</summary>
internal enum MetamorphicRunPlan
{
    /// <summary>Left once, then right once. The Phase 1/2 plan and the Phase 3 default.</summary>
    Sequential,

    /// <summary>
    /// Left once (the control), then a deliberately FAILING run of the case's interference
    /// source, then right. Proves a failed reservation cannot corrupt a later independent run.
    /// </summary>
    AfterFailedRun,

    /// <summary>
    /// Left once, then several unrelated runs, then right — the A/B/A shape applied to a whole
    /// declared relation rather than to the executor's internal sampling check.
    /// </summary>
    AfterInterleavedRuns,

    /// <summary>
    /// Left once, then a bounded, deterministic number of observations of the right member taken
    /// from DISTINCT coexisting threads that share one immutable limits/options instance. Every
    /// thread must produce the same observation; the first that differs (by index, never by
    /// completion order) becomes the reported right member, so a leak is a mismatch rather than a
    /// flaky pass.
    ///
    /// <para>The threads enter the evaluator in index order rather than overlapping: coverage
    /// instrumentation keeps one process-wide "previous location" slot, so overlapping evaluations
    /// make the fuzzing engine's feedback a function of the thread schedule instead of the input.
    /// <see cref="MetamorphicExecutor"/> documents the measurement behind that. Genuinely
    /// simultaneous execution is covered by the deterministic tests, which run uninstrumented.</para>
    /// </summary>
    BoundedParallel,
}

/// <summary>
/// Which member the executor observes FIRST.
///
/// <para>The two members are still reported as left and right whichever order they ran in, so
/// swapping the order swaps nothing about the declared relation — it only changes which
/// execution had a completely clean process behind it. Every relation in this harness must hold
/// under both orders; a relation that only holds one way is a state leak.</para>
/// </summary>
internal enum MetamorphicExecutionOrder
{
    /// <summary>Left is observed first. The Phase 1/2 order.</summary>
    LeftFirst,

    /// <summary>Right is observed first.</summary>
    RightFirst,
}

/// <summary>How the right member of a boundary case is required to stop.</summary>
internal enum MetamorphicBoundaryStop
{
    /// <summary>Not a boundary case.</summary>
    None,

    /// <summary>The right member must fail with the case's declared structured resource error.</summary>
    ResourceError,

    /// <summary>
    /// The right member must still complete, but its RENDERING must be bounded by the lower
    /// display limit and therefore differ from the left member's full text. Display length is a
    /// host rendering policy, not an evaluation budget, so it stops differently by design.
    /// </summary>
    RenderingTruncation,
}

/// <summary>
/// One side's execution policy: which entry point runs it, under which limits, with which
/// optimizer policy. Phase 1 and Phase 2 give both sides the same profile; Phase 3's families
/// are exactly the ones that vary it.
/// </summary>
internal sealed record MetamorphicExecutionProfile(
    MetamorphicSurface Surface,
    EvaluationLimits? Limits,
    bool EnableOptimizations)
{
    /// <summary>The Phase 1/2 profile: the observed evaluator entry point.</summary>
    internal static MetamorphicExecutionProfile Observed(EvaluationLimits? limits, bool enableOptimizations)
        => new(MetamorphicSurface.EvaluatorRunCountedObserved, limits, enableOptimizations);

    public string SurfaceId => MetamorphicSurfaces.Get(Surface).Id;

    public string LimitsText => MetamorphicCase.DescribeLimits(Limits);

    public override string ToString()
        => $"{SurfaceId}/{LimitsText}/optimizer={(EnableOptimizations ? "on" : "off")}";
}

/// <summary>
/// What one side's run must be PROVEN to have done before the case may be compared.
///
/// <para>This is the optimizer-hit and cache-hit evidence gate. A case that claims to compare an
/// optimized execution against a generic one is only admissible if the optimized run really
/// selected an optimizer path and the generic run really did not; a case that claims to compare
/// cached reuse against independent rebuilding is only admissible if the cached side recorded
/// hits and the rebuilt side did not. A requirement that does not hold makes the case REJECTED
/// with a named reason — never a mismatch, because nothing about the language was disproved.</para>
/// </summary>
internal sealed record MetamorphicSideEvidence(
    MetamorphicOptimizerPath RequiredPaths = MetamorphicOptimizerPath.None,
    MetamorphicOptimizerPath ForbiddenPaths = MetamorphicOptimizerPath.None,
    int? MinimumCacheHits = null,
    int? MaximumCacheHits = null)
{
    /// <summary>No evidence requirement — the Phase 1/2 default.</summary>
    internal static readonly MetamorphicSideEvidence None = new();

    public bool IsEmpty =>
        RequiredPaths == MetamorphicOptimizerPath.None
        && ForbiddenPaths == MetamorphicOptimizerPath.None
        && MinimumCacheHits is null
        && MaximumCacheHits is null;

    /// <summary>The rejection reason, or <c>null</c> when this side's evidence satisfies the claim.</summary>
    internal string? Unsatisfied(MetamorphicOperationalObservation observation, string side)
    {
        if (IsEmpty) return null;

        if (RequiredPaths != MetamorphicOptimizerPath.None || ForbiddenPaths != MetamorphicOptimizerPath.None)
        {
            if (observation.OptimizerEvidence is not { } optimizer)
                return $"{side}-optimizer-evidence-unavailable";
            if ((optimizer.Paths & RequiredPaths) != RequiredPaths)
                return $"{side}-optimizer-path-not-exercised";
            if ((optimizer.Paths & ForbiddenPaths) != MetamorphicOptimizerPath.None)
                return $"{side}-optimizer-path-unexpectedly-exercised";
        }

        if (MinimumCacheHits is null && MaximumCacheHits is null) return null;

        if (observation.CacheEvidence is not { } cache)
            return $"{side}-cache-evidence-unavailable";
        if (MinimumCacheHits is { } minimum && cache.Hits < minimum)
            return $"{side}-cache-reuse-not-observed";
        if (MaximumCacheHits is { } maximum && cache.Hits > maximum)
            return $"{side}-cache-reuse-unexpectedly-observed";

        return null;
    }
}

/// <summary>
/// One metamorphic testcase: a trusted template instantiation plus the execution policy and
/// the declared relations under which its two members must agree.
///
/// <para>This is deliberately not "one arbitrary source file". Equivalence is guaranteed by
/// how <see cref="LeftSource"/> and <see cref="RightSource"/> were CONSTRUCTED, so the
/// comparison is trustworthy without any semantic analysis of the generated text.</para>
///
/// <para>The declared <see cref="OperationalRelation"/> applies only when both executions
/// COMPLETE; see <see cref="MetamorphicOperationalRelation"/> for the resource-abort
/// qualification every operational relation carries.</para>
///
/// <para>Every Phase 3 addition below is an <c>init</c> property with its Phase 1/2 value as the
/// default, so a case built by a Phase 1 or Phase 2 template is exactly the case it always was:
/// both sides observed through <c>Evaluator.RunCountedObserved</c> under one shared limits
/// instance and one shared optimizer policy, run sequentially, with no evidence requirement.</para>
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
    /// Item slots the template expects the generated collection to materialize, MEASURED from
    /// the left member's own run-scoped budget rather than modelled analytically. Used to place
    /// limits on, just below, and just above the real boundary, and by the deterministic tests;
    /// the fuzz target itself never asserts it, so the campaign stays a pair comparison rather
    /// than an oracle comparison.
    /// </summary>
    public long ExpectedItemTotal { get; init; }

    /// <summary>String UTF-16 units the left member was measured to materialize.</summary>
    public long ExpectedStringTotal { get; init; }

    /// <summary>The left member's execution policy. Defaults to the Phase 1/2 shared policy.</summary>
    public MetamorphicExecutionProfile LeftProfile { get; init; }
        = MetamorphicExecutionProfile.Observed(Limits, EnableOptimizations);

    /// <summary>The right member's execution policy. Defaults to the Phase 1/2 shared policy.</summary>
    public MetamorphicExecutionProfile RightProfile { get; init; }
        = MetamorphicExecutionProfile.Observed(Limits, EnableOptimizations);

    /// <summary>How the executor sequences the two observations.</summary>
    public MetamorphicRunPlan RunPlan { get; init; } = MetamorphicRunPlan.Sequential;

    /// <summary>Which member is observed first. Every relation must hold under both orders.</summary>
    public MetamorphicExecutionOrder ExecutionOrder { get; init; } = MetamorphicExecutionOrder.LeftFirst;

    /// <summary>
    /// The program a non-sequential run plan executes BETWEEN the two observations: a run that
    /// must fail its reservation (<see cref="MetamorphicRunPlan.AfterFailedRun"/>) or an
    /// unrelated program (<see cref="MetamorphicRunPlan.AfterInterleavedRuns"/>).
    /// </summary>
    public string? InterferenceSource { get; init; }

    /// <summary>Limits the interference run uses; <c>null</c> means the right member's limits.</summary>
    public EvaluationLimits? InterferenceLimits { get; init; }

    /// <summary>
    /// Forces optimizer and cache evidence to be collected even when neither side REQUIRES it —
    /// used by the laws that compare the two runs' execution paths rather than gating on them.
    /// </summary>
    public bool CollectEvidence { get; init; }

    /// <summary>Evidence the left member's run must show before the pair may be compared.</summary>
    public MetamorphicSideEvidence LeftEvidence { get; init; } = MetamorphicSideEvidence.None;

    /// <summary>Evidence the right member's run must show before the pair may be compared.</summary>
    public MetamorphicSideEvidence RightEvidence { get; init; } = MetamorphicSideEvidence.None;

    /// <summary>How a boundary case's right member is required to stop.</summary>
    public MetamorphicBoundaryStop BoundaryStop { get; init; } = MetamorphicBoundaryStop.None;

    /// <summary>
    /// The structured error kind a <see cref="MetamorphicBoundaryStop.ResourceError"/> case
    /// requires, as the innermost <c>EvalError</c> type name.
    /// </summary>
    public string? ExpectedResourceKind { get; init; }

    /// <summary>Stable, machine-independent rendering of the effective limits.</summary>
    public string LimitsText => DescribeLimits(Limits);

    /// <summary>Family identifier used in seeds, reports, and fingerprints.</summary>
    public string FamilyId => FamilyIdOf(Family);

    /// <summary>The registry entry backing this case.</summary>
    public MetamorphicFamilyDefinition Definition => MetamorphicFamilyRegistry.Get(Family);

    /// <summary>True when either side needs optimizer or cache evidence collected.</summary>
    public bool CollectsEvidence => CollectEvidence || !LeftEvidence.IsEmpty || !RightEvidence.IsEmpty;

    internal static string FamilyIdOf(MetamorphicFamily family) => MetamorphicFamilyRegistry.Get(family).Id;

    internal static bool TryParseFamilyId(string text, out MetamorphicFamily family)
    {
        if (MetamorphicFamilyRegistry.TryGetById(text, out var definition))
        {
            family = definition.Family;
            return true;
        }

        family = default;
        return false;
    }

    internal static string DescribeLimits(EvaluationLimits? limits)
    {
        if (limits is null) return "default";

        var parts = new List<string>(8);
        if (limits.MaxDepth is { } depth)
            parts.Add("maxDepth=" + depth.ToString(CultureInfo.InvariantCulture));
        if (limits.MaxSteps is { } steps)
            parts.Add("maxSteps=" + steps.ToString(CultureInfo.InvariantCulture));
        if (limits.MaxMaterializedItems is { } cumulative)
            parts.Add("maxMaterializedItems=" + cumulative.ToString(CultureInfo.InvariantCulture));
        if (limits.MaxCollectionItems is { } perCollection)
            parts.Add("maxCollectionItems=" + perCollection.ToString(CultureInfo.InvariantCulture));
        if (limits.MaxMaterializedStringChars is { } cumulativeStrings)
            parts.Add("maxMaterializedStringChars=" + cumulativeStrings.ToString(CultureInfo.InvariantCulture));
        if (limits.MaxStringLength is { } perString)
            parts.Add("maxStringLength=" + perString.ToString(CultureInfo.InvariantCulture));
        if (limits.MaxDisplayLength is { } display)
            parts.Add("maxDisplayLength=" + display.ToString(CultureInfo.InvariantCulture));
        return parts.Count == 0 ? "explicit(none)" : string.Join(",", parts);
    }
}
