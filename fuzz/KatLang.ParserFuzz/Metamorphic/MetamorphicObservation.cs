using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// Which observations one runtime surface actually PROJECTS.
///
/// <para>Phase 1 and Phase 2 only ever used <see cref="Observed"/> — everything
/// <c>Evaluator.RunCountedObserved</c> hands back. Phase 3 compares different entry points
/// against each other, and those genuinely differ in what they can report: <c>Evaluator.Run</c>
/// returns a value with no emitted count, <c>RunFlat</c> returns host atoms with no structural
/// value, <c>KatLangEngine.EvaluateToString</c> returns rendered text and nothing else, and only
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

    /// <summary>Innermost structured error kind, its stable payload, and the resource verdict.</summary>
    StructuredError = 1 << 1,

    /// <summary>The neutral structural value.</summary>
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
/// </summary>
internal sealed record MetamorphicSemanticObservation(
    string Outcome,             // "ok" | "err"
    string? Structure,          // neutral structural value (ok only)
    int? EmittedCount,          // root emitted count (ok only)
    string? ErrorCategory,      // innermost structured error kind (err only)
    string? ErrorPayload,       // stable numeric payload where supported (err only)
    bool IsResourceLimit)       // host resource policy, never a language-semantic fact
{
    public static MetamorphicSemanticObservation Success(string structure, int emittedCount)
        => new("ok", structure, emittedCount, null, null, false);

    public static MetamorphicSemanticObservation Failure(string category, string? payload, bool isResourceLimit)
        => new("err", null, null, category, payload, isResourceLimit);

    /// <summary>
    /// A surface that reports only WHETHER the run failed: the engine's public error type keeps
    /// a formatted message and a span, not the structured <c>EvalError</c>, so nothing more
    /// specific than the outcome can honestly be claimed for it.
    /// </summary>
    public static MetamorphicSemanticObservation OutcomeOnly(bool failed)
        => new(failed ? "err" : "ok", null, null, null, null, false);

    public override string ToString() => Outcome == "ok"
        ? $"ok value={Structure ?? "-"} emitted={EmittedCount?.ToString(CultureInfo.InvariantCulture) ?? "-"}"
        : $"err kind={ErrorCategory ?? "-"} payload={ErrorPayload ?? "-"} resourceLimit={(IsResourceLimit ? "yes" : "no")}";
}

/// <summary>
/// The extra projections a non-default entry point produces. Every field is a stable, machine
/// independent TEXT encoding, so two observations can be compared and fingerprinted without
/// holding on to evaluator values.
/// </summary>
/// <param name="RenderedProjection">
/// Which rendering the surface returned. This matters because
/// <c>KatLangEngine.EvaluateToString</c> is documented to return SPACE-JOINED HOST ATOMS on
/// success and the structured diagnostic rendering otherwise, so it does not equal
/// <c>Run(...).ToDisplayString()</c> for a successful program. Rendered text is therefore
/// compared exactly where the two surfaces produced the SAME projection, and the length bound
/// is checked on every side regardless.
/// </param>
internal sealed record MetamorphicSurfaceProjection(
    string? HostAtoms,
    string? RenderedText,
    string RenderedProjection,
    int RenderedLimit,
    string? TopLevelProperty)
{
    internal const string StructuredDisplay = "structured-display";
    internal const string JoinedAtoms = "joined-atoms";
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
