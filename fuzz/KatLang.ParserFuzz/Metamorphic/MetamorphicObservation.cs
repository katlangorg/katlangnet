using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// Which observations one runtime surface actually PROJECTS.
///
/// <para>Phase 1 and Phase 2 only ever used <see cref="Observed"/> — everything
/// <c>Evaluator.RunCountedObserved</c> hands back. Phase 3 compares different entry points
/// against each other, and those genuinely differ in what they can report: <c>Evaluator.Run</c>
/// returns a value with no emitted count, <c>RunFlat</c> returns host atoms with no structural
/// value, a formatter returns rendered text and nothing else, and only
/// <c>RunCountedObserved</c> hands back the run's budget.</para>
///
/// <para>A pair is compared on the INTERSECTION of what both sides project. That is what keeps
/// entry-point parity honest: a facet neither surface can report is not silently "equal", it is
/// recorded as not compared, and a family that would end up comparing nothing but the outcome is
/// rejected by its own precondition rather than passing vacuously.</para>
/// </summary>
[Flags]
internal enum MetamorphicFacets
{
    None = 0,

    /// <summary>Success or failure. Every surface projects this.</summary>
    Outcome = 1 << 0,

    /// <summary>Innermost structured error kind, its stable payload, its strict field detail, and the resource verdict.</summary>
    StructuredError = 1 << 1,

    /// <summary>The structural value: legacy neutral text, the value itself, and its kl-struct-v1 identity.</summary>
    Structure = 1 << 2,

    /// <summary>The root emitted count.</summary>
    EmittedCount = 1 << 3,

    /// <summary>The host-atom projection (list boundaries opened).</summary>
    HostAtoms = 1 << 4,

    /// <summary>Rendered display text, together with the projection that produced it.</summary>
    RenderedText = 1 << 5,

    /// <summary>The run's own budget counters.</summary>
    OperationalCounters = 1 << 6,

    /// <summary>The engine's top-level property channel (<c>DisplayDecimals</c>).</summary>
    TopLevelProperty = 1 << 7,

    /// <summary>What <c>Evaluator.RunCountedObserved</c> projects — the Phase 1/2 default.</summary>
    Observed = Outcome | StructuredError | Structure | EmittedCount | OperationalCounters,
}

/// <summary>
/// LANGUAGE-SEMANTIC identity of one run: the class of observation the Lean differential
/// corpus compares, plus the host-policy flag that keeps a resource-limit failure
/// distinguishable from an ordinary language-semantic failure.
///
/// <para><b>Structural identity (SEM-2A).</b> <see cref="Structure"/> is the LEGACY neutral text,
/// kept byte-for-byte because FORMAL-06 and the semantic explorer pin it, but it is not injective
/// (strings are written between unescaped quotes). A surface that hands back a value therefore
/// also records the value itself (<see cref="Value"/>, compared with
/// <see cref="Result.ValueComparer"/> — the in-process authority) and its versioned durable
/// identity (<see cref="StructuralIdentity"/>, <c>kl-struct-v1</c>). Only a completed run's
/// ordinary value is retained: run results never contain a call reference, and no plan, cell,
/// budget or cache is reachable from a <see cref="Result"/>.</para>
///
/// <para><b>Strict error detail (SEM-2A).</b> A surface that hands back the structured
/// <c>EvalError</c> also records its innermost Q-67 fields (<see cref="ErrorDetail"/>), which a
/// case declaring <see cref="MetamorphicErrorPolicy.StrictSameSource"/> compares. The legacy
/// <see cref="ErrorPayload"/> keeps its cross-source meaning.</para>
///
/// <para>Equality is hand-written so that two observations of equal VALUES are equal records
/// (<see cref="Result"/> record equality compares item lists by reference); every other member
/// compares exactly as the generated equality did.</para>
/// </summary>
internal sealed record MetamorphicSemanticObservation(
    string Outcome,             // "ok" | "err"
    string? Structure,          // legacy neutral structural value (ok only)
    int? EmittedCount,          // root emitted count (ok only)
    string? ErrorCategory,      // innermost structured error kind (err only)
    string? ErrorPayload,       // stable numeric payload where supported (err only)
    bool IsResourceLimit)       // host resource policy, never a language-semantic fact
{
    /// <summary>The completed value itself (ok only, when the surface hands one back).</summary>
    public Result? Value { get; init; }

    /// <summary>The value's <c>kl-struct-v1</c> durable identity (whenever <see cref="Value"/> is set).</summary>
    public string? StructuralIdentity { get; init; }

    /// <summary>Innermost structured error fields (err only, when the surface hands back an <c>EvalError</c>).</summary>
    public MetamorphicErrorDetail? ErrorDetail { get; init; }

    /// <summary>A legacy-only record, retained for compatibility; insufficient for structural comparison.</summary>
    public static MetamorphicSemanticObservation Success(string structure, int emittedCount)
        => new("ok", structure, emittedCount, null, null, false);

    /// <summary>A legacy-only failure: category and payload, no structured detail.</summary>
    public static MetamorphicSemanticObservation Failure(string category, string? payload, bool isResourceLimit)
        => new("err", null, null, category, payload, isResourceLimit);

    /// <summary>
    /// A success observed from the value itself: typed value and durable identity together, plus
    /// the legacy text unless it exceeds <see cref="MetamorphicValue.MaxObservedNeutralLength"/>
    /// (a path-exponential shared value), in which case <see cref="Structure"/> is <c>null</c>.
    /// </summary>
    public static MetamorphicSemanticObservation OfValue(Result value, int? emittedCount)
        => new("ok", MetamorphicValue.NeutralWithin(value, MetamorphicValue.MaxObservedNeutralLength), emittedCount, null, null, false)
        {
            Value = value,
            StructuralIdentity = MetamorphicStructuralIdentity.Encode(value),
        };

    /// <summary>A failure observed from the structured error: legacy fields plus its strict detail.</summary>
    public static MetamorphicSemanticObservation OfError(EvalError error)
        => new("err", null, null,
            MetamorphicValue.ErrorCategory(error), MetamorphicValue.ErrorPayload(error), error.IsResourceLimit)
        {
            ErrorDetail = MetamorphicErrorDetail.Observe(error),
        };

    public bool Equals(MetamorphicSemanticObservation? other)
        => other is not null
            && string.Equals(Outcome, other.Outcome, StringComparison.Ordinal)
            && string.Equals(Structure, other.Structure, StringComparison.Ordinal)
            && EmittedCount == other.EmittedCount
            && string.Equals(ErrorCategory, other.ErrorCategory, StringComparison.Ordinal)
            && string.Equals(ErrorPayload, other.ErrorPayload, StringComparison.Ordinal)
            && IsResourceLimit == other.IsResourceLimit
            && string.Equals(StructuralIdentity, other.StructuralIdentity, StringComparison.Ordinal)
            && Equals(ErrorDetail, other.ErrorDetail)
            && (Value is null
                ? other.Value is null
                : other.Value is not null && Result.ValueComparer.Equals(Value, other.Value));

    public override int GetHashCode()
        => HashCode.Combine(
            HashCode.Combine(Outcome, Structure, EmittedCount, ErrorCategory, ErrorPayload, IsResourceLimit),
            StructuralIdentity, ErrorDetail, Value is null);

    /// <summary>
    /// A surface that reports only WHETHER the run failed: the engine's public error type keeps
    /// a formatted message and a span, not the structured <c>EvalError</c>, so nothing more
    /// specific than the outcome can honestly be claimed for it.
    /// </summary>
    public static MetamorphicSemanticObservation OutcomeOnly(bool failed)
        => new(failed ? "err" : "ok", null, null, null, null, false);

    public override string ToString() => Outcome == "ok"
        ? $"ok value={MetamorphicStructuralIdentity.PreviewText(Structure)} emitted={EmittedCount?.ToString(CultureInfo.InvariantCulture) ?? "-"}"
            + (StructuralIdentity is null ? "" : " identity=" + MetamorphicStructuralIdentity.Preview(StructuralIdentity))
        : $"err kind={ErrorCategory ?? "-"} payload={ErrorPayload ?? "-"} resourceLimit={(IsResourceLimit ? "yes" : "no")}"
            + (ErrorDetail is null ? "" : " detail=" + ErrorDetail);
}

/// <summary>
/// The extra projections a non-default entry point produces. Every field is a stable, machine
/// independent TEXT encoding, so two observations can be compared and fingerprinted without
/// holding on to evaluator values.
/// </summary>
/// <param name="RenderedProjection">
/// Which rendering the surface returned — the canonical structured display, or none. Rendered
/// text is compared exactly where the two surfaces produced the SAME projection, so a surface
/// that renders a different projection can never be held to another's text; the length bound is
/// checked on every side regardless.
/// </param>
internal sealed record MetamorphicSurfaceProjection(
    string? HostAtoms,
    string? RenderedText,
    string RenderedProjection,
    int RenderedLimit,
    string? TopLevelProperty)
{
    internal const string StructuredDisplay = "structured-display";
    internal const string NoRendering = "none";

    /// <summary>UTF-16 units the surface actually returned, or -1 when it rendered nothing.</summary>
    public int RenderedLength => RenderedText?.Length ?? -1;
}

/// <summary>
/// OPERATIONAL counters one run charged, read from the run's own
/// <see cref="KatLang.Evaluation.EvaluationBudget"/>. These are C# implementation
/// observations: they may be compared between C# executions and are never compared with
/// Lean, which models an unbounded evaluator with no notion of work.
///
/// <para><see cref="EvaluationSteps"/> and <see cref="PeakDynamicDepth"/> are carried for
/// DIAGNOSTICS only under the Phase 1 relation, because the repository's established contract
/// for the dotted/ordinary pair asserts materialization equality and does not claim the two
/// forms share one definition of a "step". Relations that DO claim them say so explicitly.</para>
///
/// <para>The Phase 3 fields are all <c>init</c> properties with Phase 1/2 defaults, so an
/// observation taken through the original path is byte-for-byte the record it always was and
/// replay equality is unchanged.</para>
/// </summary>
internal sealed record MetamorphicOperationalObservation(
    MetamorphicSemanticObservation Semantic,
    long EvaluationSteps,
    long MaterializedItems,
    long MaterializedStringChars,
    int PeakDynamicDepth,
    string OptimizerPolicy)
{
    /// <summary>What this surface could report. Defaults to the Phase 1/2 observed set.</summary>
    public MetamorphicFacets Facets { get; init; } = MetamorphicFacets.Observed;

    /// <summary>Stable identifier of the entry point that produced this observation.</summary>
    public string Surface { get; init; } = MetamorphicSurfaces.DefaultSurfaceId;

    /// <summary>Host atoms, rendered text, and the top-level property channel, when projected.</summary>
    public MetamorphicSurfaceProjection? Projection { get; init; }

    /// <summary>Which optimizer path the run took, when a diagnostics channel was attached.</summary>
    public MetamorphicOptimizerEvidence? OptimizerEvidence { get; init; }

    /// <summary>The run's zero-argument property cache profile, when one was attached.</summary>
    public MetamorphicCacheEvidence? CacheEvidence { get; init; }

    // NOTE: the effective LIMITS are deliberately NOT part of an observation. An observation
    // records what a run produced and charged; the policy it ran under belongs to the case's
    // execution profile, which is where the fingerprint and the diagnostics read it from. Keeping
    // it here would make two observations of the same program unequal merely because they were
    // budgeted differently, which is exactly the comparison in-budget neutrality has to make.

    public override string ToString()
    {
        var text =
            $"{Semantic} | surface={Surface} facets={Facets} " +
            $"steps={EvaluationSteps.ToString(CultureInfo.InvariantCulture)} " +
            $"materializedItems={MaterializedItems.ToString(CultureInfo.InvariantCulture)} " +
            $"materializedStringChars={MaterializedStringChars.ToString(CultureInfo.InvariantCulture)} " +
            $"peakDepth={PeakDynamicDepth.ToString(CultureInfo.InvariantCulture)} optimizer={OptimizerPolicy}";

        if (Projection is { } projection)
        {
            text +=
                $" | rendered={projection.RenderedProjection}" +
                $"({projection.RenderedLength.ToString(CultureInfo.InvariantCulture)}" +
                $"/{projection.RenderedLimit.ToString(CultureInfo.InvariantCulture)})" +
                $" atoms={projection.HostAtoms ?? "-"}";
        }

        if (OptimizerEvidence is { } optimizer) text += " | optimizer:" + optimizer;
        if (CacheEvidence is { } cache) text += " | cache:" + cache;
        return text;
    }
}
