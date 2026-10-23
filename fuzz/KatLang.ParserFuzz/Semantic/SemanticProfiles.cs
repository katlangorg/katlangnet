using System.Collections.Immutable;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// One SEM-2B execution profile: a registered <see cref="MetamorphicSurface"/> (the ONE adapter per
/// entry point), its optimizer policy where the surface has one, the host fixture mode, the
/// cancellation schedule, and the run order. Every execution gets fresh run state: a fresh parse,
/// budget, property cache and host fixture; only the immutable limits instance is shared.
/// </summary>
internal sealed record SemanticProfile(
    string Id,
    MetamorphicSurface Surface,
    bool EnableOptimizations,
    bool GatedHost,
    int? CancelAtSuspension,
    bool AfterInterleavedRun,
    string Description)
{
    public MetamorphicExecutionProfile ExecutionProfile
        => new(Surface, SemanticProfiles.Limits, EnableOptimizations);

    public MetamorphicSurfaceDefinition Definition => MetamorphicSurfaces.Get(Surface);

    public bool IsCancellation => CancelAtSuspension is not null;

    /// <summary>A fresh host fixture for ONE run of this profile.</summary>
    public MetamorphicHostFixture NewFixture() => GatedHost
        ? MetamorphicHostFixture.Gated(CancelAtSuspension)
        : MetamorphicHostFixture.Synchronous();

    /// <summary>Stable description for descriptors: surface, optimizer, limits, fixture, schedule, run order.</summary>
    public string Describe()
        => $"{Id}: surface={Definition.Id} optimizer={(Definition.SupportsOptimizerPolicy ? (EnableOptimizations ? "on" : "off") : Definition.IsAsynchronous && !Definition.UsesFrontEndPipeline ? "twin-pinned-off" : "production-default")} "
            + $"limits={MetamorphicCase.DescribeLimits(SemanticProfiles.Limits)} effectiveLimits={SemanticProfiles.EffectiveLimitsText} host={MetamorphicHostFixture.FixtureId} "
            + $"schedule={(GatedHost ? (CancelAtSuspension is { } k ? "cancel-at-suspension-" + k : MetamorphicHostFixture.ReleaseInOrderSchedule) : "synchronous")} "
            + $"order={(AfterInterleavedRun ? "after-interleaved-run" : "fresh")}";
}

/// <summary>A declared comparison between two profiles of ONE source.</summary>
internal sealed record SemanticProfilePair(
    string Left,
    string Right,
    MetamorphicSemanticRelation SemanticRelation,
    MetamorphicOperationalRelation OperationalRelation,
    string Justification)
{
    public string Id => "parity:" + Left + "~" + Right;
}

/// <summary>
/// The deliberate, small SEM-2B profile matrix and its declared comparisons.
///
/// <para><b>Unsupported combinations</b> (documented, never reported as covered): the asynchronous
/// twin pins both optimizers off, so there is no "async optimized" profile — its optimizer flag is
/// not a policy; the engine entry points take no optimizer switch, so they are never reported as
/// "optimizer disabled"; the async-capable property cache keeps no statistics, so asynchronous
/// profiles claim no cache evidence; the engine's public error keeps no structured
/// <c>EvalError</c>, so engine profiles compare outcome, failure stage, value, count, atoms and
/// rendering, never error kinds.</para>
/// </summary>
internal static class SemanticProfiles
{
    internal const string SyncGeneric = "sync-generic";
    internal const string SyncOptimized = "sync-optimized";
    internal const string AsyncTwin = "async-twin";
    internal const string EngineRun = "engine-run";
    internal const string EngineRunAsync = "engine-run-async";
    internal const string SyncOptimizedRerun = "sync-optimized-rerun";
    internal const string AsyncTwinCancel = "async-twin-cancel-1";
    internal const string EngineRunAsyncCancel = "engine-run-async-cancel-1";

    /// <summary>Deterministic limits: the production defaults (generated programs terminate by construction).</summary>
    internal static readonly EvaluationLimits? Limits = null;

    // Persist the effective policy too: "default" alone would silently change a replay's
    // configuration if a later build changed a production default or hard ceiling.
    internal static string EffectiveLimitsText
    {
        get
        {
            var limits = Limits ?? EvaluationLimits.Default;
            return FormattableString.Invariant($"depth:{limits.EffectiveMaxDepth},ast:{limits.EffectiveMaxAstDepth},steps:{limits.EffectiveMaxSteps?.ToString(System.Globalization.CultureInfo.InvariantCulture) ?? "unlimited"},collection:{limits.EffectiveMaxCollectionItems},items:{limits.EffectiveMaxMaterializedItems?.ToString(System.Globalization.CultureInfo.InvariantCulture) ?? "unlimited"},string:{limits.EffectiveMaxStringLength},chars:{limits.EffectiveMaxMaterializedStringChars?.ToString(System.Globalization.CultureInfo.InvariantCulture) ?? "unlimited"},display:{limits.EffectiveMaxDisplayLength}");
        }
    }

    internal static readonly ImmutableArray<SemanticProfile> All =
    [
        new(SyncGeneric, MetamorphicSurface.EvaluatorRunCountedObserved, false, false, null, false,
            "observed synchronous evaluator, both optimizers off"),
        new(SyncOptimized, MetamorphicSurface.EvaluatorRunCountedObserved, true, false, null, false,
            "observed synchronous evaluator, both optimizers on"),
        new(AsyncTwin, MetamorphicSurface.EvaluatorRunCountedObservedAsync, false, true, null, false,
            "observed asynchronous twin, gated host (genuine suspension at every wait)"),
        new(EngineRun, MetamorphicSurface.EngineRun, true, false, null, false,
            "public KatLangEngine.Run (production optimizer default)"),
        new(EngineRunAsync, MetamorphicSurface.EngineRunAsync, true, true, null, false,
            "public KatLangEngine.RunAsync, gated host"),
        new(SyncOptimizedRerun, MetamorphicSurface.EvaluatorRunCountedObserved, true, false, null, true,
            "sync-optimized again after an unrelated run, reusing the immutable limits instance"),
        new(AsyncTwinCancel, MetamorphicSurface.EvaluatorRunCountedObservedAsync, false, true, 1, false,
            "asynchronous twin cancelled at its first witnessed suspension"),
        new(EngineRunAsyncCancel, MetamorphicSurface.EngineRunAsync, true, true, 1, false,
            "public RunAsync cancelled at its first witnessed suspension"),
    ];

    /// <summary>Declared profile comparisons, applied whenever a case runs both profiles.</summary>
    internal static readonly ImmutableArray<SemanticProfilePair> Pairs =
    [
        new(SyncGeneric, SyncOptimized, MetamorphicSemanticRelation.SameStructuredOutcome,
            MetamorphicOperationalRelation.ExactObservedWorkEqual,
            "one source, generic vs optimized strategy: strategy-neutral budgets (Q-09b)"),
        new(SyncOptimized, AsyncTwin, MetamorphicSemanticRelation.SameStructuredOutcome,
            MetamorphicOperationalRelation.NotCompared,
            "sync vs asynchronous twin: equal semantics; no operational claim across strategies here"),
        new(SyncOptimized, EngineRun, MetamorphicSemanticRelation.SameStructuredOutcome,
            MetamorphicOperationalRelation.NotCompared,
            "evaluator vs public engine: shared facets only (engine keeps no structured error)"),
        new(EngineRun, EngineRunAsync, MetamorphicSemanticRelation.SameStructuredOutcome,
            MetamorphicOperationalRelation.NotCompared,
            "public sync vs public async: shared facets including atoms and rendering"),
        new(SyncOptimized, SyncOptimizedRerun, MetamorphicSemanticRelation.IndependentRunStable,
            MetamorphicOperationalRelation.IdenticalWork,
            "fresh-run isolation: an interleaved unrelated run and reused configuration change nothing"),
    ];

    internal static SemanticProfile Get(string id)
        => All.FirstOrDefault(p => string.Equals(p.Id, id, StringComparison.Ordinal))
            ?? throw new MetamorphicHarnessException($"Unknown SEM-2B profile '{id}'.");

    internal static bool TryGet(string id, out SemanticProfile profile)
    {
        profile = All.FirstOrDefault(p => string.Equals(p.Id, id, StringComparison.Ordinal))!;
        return profile is not null;
    }

    internal static IEnumerable<string> RelationsFor(SemanticCase semanticCase)
    {
        foreach (var pair in Pairs.Where(p => semanticCase.Profiles.Contains(p.Left) && semanticCase.Profiles.Contains(p.Right)))
            yield return $"{pair.Id}: semantic={pair.SemanticRelation}; operational={pair.OperationalRelation}; errors=StrictSameSource";
        foreach (var member in semanticCase.Members.Skip(1))
            yield return $"relation:{member.Role}: profile={SyncOptimized}; semantic=SemanticEqual; operational=NotCompared; errors=Normalized";
        if (semanticCase.Profiles.Contains(AsyncTwinCancel) && semanticCase.Profiles.Contains(EngineRunAsyncCancel))
            yield return $"parity:{AsyncTwinCancel}~{EngineRunAsyncCancel}: cancellation-and-exact-events";
    }
}
