using System.Collections.Immutable;
using System.Globalization;
using KatLang;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.ParserFuzz;

/// <summary>One runtime entry point the harness can execute a program through.</summary>
internal enum MetamorphicSurface
{
    /// <summary>
    /// <c>Evaluator.RunCountedObserved</c> — the Phase 1/2 surface. The only one that hands
    /// back the run's own <c>EvaluationBudget</c>, so the only one with operational counters.
    /// </summary>
    EvaluatorRunCountedObserved,

    /// <summary><c>Evaluator.RunCounted</c> — counted result, no budget.</summary>
    EvaluatorRunCounted,

    /// <summary><c>Evaluator.Run</c> — a plain value, with no emitted count at all.</summary>
    EvaluatorRun,

    /// <summary><c>Evaluator.RunFlat</c> — the host-atom projection only.</summary>
    EvaluatorRunFlat,

    /// <summary><c>Evaluator.RunCountedWithTopLevelProperty</c> — counted result plus the property channel.</summary>
    EvaluatorRunCountedWithTopLevelProperty,

    /// <summary><c>KatLangEngine.Run</c> — the public façade: front end, top-level property, host atoms, rendering.</summary>
    EngineRun,

    /// <summary><c>KatLangEngine.EvaluateToAtoms</c> — host atoms, throwing on failure.</summary>
    EngineEvaluateToAtoms,

    /// <summary><c>OutputFormatters.Exact.Format(KatLangEngine.Run(...))</c> — the canonical rendered text.</summary>
    EngineExactFormatter,

    /// <summary>
    /// <c>Evaluator.RunCountedObservedAsync</c> with an async-capable property cache, so the run takes
    /// the asynchronous twin family (SEM-2B). Hands back the run's budget like the synchronous
    /// observed surface, but it has NO optimizer policy: the twin path pins both optimizers off.
    /// Genuine suspension is evidence only when an asynchronous <see cref="MetamorphicHostFixture"/>
    /// witnesses it; without one the twin runs but never suspends.
    /// </summary>
    EvaluatorRunCountedObservedAsync,

    /// <summary><c>KatLangEngine.RunAsync</c> — the public asynchronous façade (SEM-2B).</summary>
    EngineRunAsync,
}

/// <summary>Everything the harness knows about one entry point, declared rather than inferred.</summary>
/// <param name="RequiresParsableSource">
/// True when the surface consumes an already-parsed root, so a program the front end rejects can
/// never reach it and must be a REJECTED case rather than a failure outcome. The engine surfaces
/// take source text and report a parse failure as an ordinary outcome.
/// </param>
/// <param name="SupportsOptimizerPolicy">
/// True when the surface lets the caller choose the optimizer policy. Only the observed
/// evaluator entry point does; every other surface runs the production default, so a pair that
/// mixes them may only be generated with optimizations ON.
/// </param>
internal sealed record MetamorphicSurfaceDefinition(
    MetamorphicSurface Surface,
    string Id,
    MetamorphicFacets Facets,
    bool RequiresParsableSource,
    bool SupportsOptimizerPolicy,
    bool UsesFrontEndPipeline)
{
    /// <summary>
    /// True when the adapter can run a program against a <see cref="MetamorphicHostFixture"/>'s host
    /// operations (SEM-2B). A surface without it refuses a fixture rather than silently dropping it.
    /// </summary>
    public bool SupportsHostFixture { get; init; }

    /// <summary>True when the adapter is an ASYNCHRONOUS entry point that a gated fixture can suspend.</summary>
    public bool IsAsynchronous { get; init; }
}

/// <summary>
/// The registered runtime surfaces and the adapters that project each one onto ONE neutral
/// observation.
///
/// <para><b>Adapters never invent a facet.</b> Each surface declares exactly what it can report
/// (<see cref="MetamorphicSurfaceDefinition.Facets"/>) and a pair is compared on the intersection
/// of the two declarations, so "these two entry points agree" never quietly means "neither could
/// tell". <c>Evaluator.Run</c> really does not produce an emitted count, and the engine's public
/// <c>KatLangError</c> really does keep only a formatted message and a span rather than the
/// structured <c>EvalError</c>, so those surfaces do not claim the corresponding facets.</para>
///
/// <para><b>Every invocation gets fresh mutable state.</b> A fresh parse, a fresh budget, and a
/// fresh zero-argument property cache per call. The immutable <see cref="EvaluationLimits"/> and
/// <see cref="RunOptions"/> instances are deliberately SHARED and reused across invocations,
/// because "a reused configuration object carries no run state" is one of the properties this
/// layer exists to exercise.</para>
/// </summary>
internal static class MetamorphicSurfaces
{
    /// <summary>Stable id of the Phase 1/2 surface, and the default on every observation.</summary>
    internal const string DefaultSurfaceId = "evaluator-run-counted-observed";

    private static readonly ImmutableArray<MetamorphicSurfaceDefinition> Definitions =
    [
        new(MetamorphicSurface.EvaluatorRunCountedObserved, DefaultSurfaceId,
            MetamorphicFacets.Observed,
            RequiresParsableSource: true, SupportsOptimizerPolicy: true, UsesFrontEndPipeline: false)
        {
            SupportsHostFixture = true,
        },

        new(MetamorphicSurface.EvaluatorRunCounted, "evaluator-run-counted",
            MetamorphicFacets.Outcome | MetamorphicFacets.StructuredError
            | MetamorphicFacets.Structure | MetamorphicFacets.EmittedCount,
            RequiresParsableSource: true, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: false),

        new(MetamorphicSurface.EvaluatorRun, "evaluator-run",
            MetamorphicFacets.Outcome | MetamorphicFacets.StructuredError | MetamorphicFacets.Structure,
            RequiresParsableSource: true, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: false),

        new(MetamorphicSurface.EvaluatorRunFlat, "evaluator-run-flat",
            MetamorphicFacets.Outcome | MetamorphicFacets.StructuredError | MetamorphicFacets.HostAtoms,
            RequiresParsableSource: true, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: false),

        new(MetamorphicSurface.EvaluatorRunCountedWithTopLevelProperty, "evaluator-run-counted-with-top-level-property",
            MetamorphicFacets.Outcome | MetamorphicFacets.StructuredError | MetamorphicFacets.Structure
            | MetamorphicFacets.EmittedCount | MetamorphicFacets.TopLevelProperty,
            RequiresParsableSource: true, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: false),

        new(MetamorphicSurface.EngineRun, "engine-run",
            MetamorphicFacets.Outcome | MetamorphicFacets.Structure | MetamorphicFacets.EmittedCount
            | MetamorphicFacets.HostAtoms | MetamorphicFacets.RenderedText,
            RequiresParsableSource: false, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: true)
        {
            SupportsHostFixture = true,
        },

        new(MetamorphicSurface.EngineEvaluateToAtoms, "engine-evaluate-to-atoms",
            MetamorphicFacets.Outcome | MetamorphicFacets.HostAtoms,
            RequiresParsableSource: false, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: true),

        new(MetamorphicSurface.EngineExactFormatter, "engine-exact-formatter",
            MetamorphicFacets.Outcome | MetamorphicFacets.Structure | MetamorphicFacets.EmittedCount
            | MetamorphicFacets.HostAtoms | MetamorphicFacets.RenderedText,
            RequiresParsableSource: false, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: true),

        new(MetamorphicSurface.EvaluatorRunCountedObservedAsync, "evaluator-run-counted-observed-async",
            MetamorphicFacets.Observed,
            RequiresParsableSource: true, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: false)
        {
            SupportsHostFixture = true,
            IsAsynchronous = true,
        },

        new(MetamorphicSurface.EngineRunAsync, "engine-run-async",
            MetamorphicFacets.Outcome | MetamorphicFacets.Structure | MetamorphicFacets.EmittedCount
            | MetamorphicFacets.HostAtoms | MetamorphicFacets.RenderedText,
            RequiresParsableSource: false, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: true)
        {
            SupportsHostFixture = true,
            IsAsynchronous = true,
        },
    ];

    static MetamorphicSurfaces()
    {
        var ids = new HashSet<string>(StringComparer.Ordinal);
        foreach (var definition in Definitions)
        {
            if (!ids.Add(definition.Id))
                throw new MetamorphicHarnessException($"Duplicate metamorphic surface id '{definition.Id}'.");
            if (!definition.Facets.HasFlag(MetamorphicFacets.Outcome))
                throw new MetamorphicHarnessException($"Surface '{definition.Id}' must project the outcome facet.");
        }

        if (Definitions.Length != Enum.GetValues<MetamorphicSurface>().Length)
            throw new MetamorphicHarnessException("Every MetamorphicSurface value needs a registered definition.");
    }

    internal static ImmutableArray<MetamorphicSurfaceDefinition> All => Definitions;

    internal static MetamorphicSurfaceDefinition Get(MetamorphicSurface surface)
    {
        foreach (var definition in Definitions)
        {
            if (definition.Surface == surface) return definition;
        }

        throw new ArgumentOutOfRangeException(nameof(surface), surface, "No adapter is registered for this surface.");
    }

    /// <summary>
    /// Runs <paramref name="source"/> through one surface with fresh mutable state and projects
    /// the result onto a neutral observation.
    ///
    /// <para>Returns <c>false</c> only when the surface REQUIRES a parsable source and the front
    /// end rejected it — that is a template precondition failure, never a mismatch. Every
    /// unexpected exception escapes, so the fuzzing engine still records it as a crash.</para>
    /// </summary>
    internal static bool TryObserve(
        string source,
        MetamorphicExecutionProfile profile,
        RunOptions options,
        bool collectEvidence,
        out MetamorphicOperationalObservation observation,
        out string reason)
        => TryObserve(source, profile, options, collectEvidence, host: null, out observation, out reason);

    /// <summary>
    /// <see cref="TryObserve(string, MetamorphicExecutionProfile, RunOptions, bool, out MetamorphicOperationalObservation, out string)"/>
    /// against one run's <see cref="MetamorphicHostFixture"/> (SEM-2B): the program is parsed and run
    /// with the fixture's host operations, and an asynchronous surface is driven through the fixture's
    /// suspension gate. The fixture belongs to this ONE observation. A surface that cannot carry host
    /// operations refuses the fixture with a harness exception rather than silently running without it.
    /// </summary>
    internal static bool TryObserve(
        string source,
        MetamorphicExecutionProfile profile,
        RunOptions options,
        bool collectEvidence,
        MetamorphicHostFixture? host,
        out MetamorphicOperationalObservation observation,
        out string reason)
    {
        ArgumentNullException.ThrowIfNull(source);
        ArgumentNullException.ThrowIfNull(profile);
        ArgumentNullException.ThrowIfNull(options);

        var definition = Get(profile.Surface);
        observation = null!;
        reason = "ok";

        if (host is not null && !definition.SupportsHostFixture)
            throw new MetamorphicHarnessException($"Surface '{definition.Id}' cannot run against a host fixture.");
        if (host is { Asynchronous: true } && !definition.IsAsynchronous)
            throw new MetamorphicHarnessException($"Surface '{definition.Id}' is synchronous; a gated host fixture needs an asynchronous surface.");
        if (host is not null)
            options = new RunOptions { EvaluationLimits = options.EvaluationLimits, HostOperations = host.Operations };

        return definition.Surface switch
        {
            MetamorphicSurface.EvaluatorRunCountedObserved =>
                ObserveRunCountedObserved(source, profile, definition, collectEvidence, host, ref observation, ref reason),
            MetamorphicSurface.EvaluatorRunCountedObservedAsync =>
                ObserveRunCountedObservedAsync(source, profile, definition, collectEvidence, host, ref observation, ref reason),
            MetamorphicSurface.EngineRunAsync =>
                ObserveEngineRunAsync(source, profile, definition, options, host, ref observation),
            MetamorphicSurface.EvaluatorRunCounted =>
                ObserveRunCounted(source, profile, definition, ref observation, ref reason),
            MetamorphicSurface.EvaluatorRun =>
                ObserveRun(source, profile, definition, ref observation, ref reason),
            MetamorphicSurface.EvaluatorRunFlat =>
                ObserveRunFlat(source, profile, definition, ref observation, ref reason),
            MetamorphicSurface.EvaluatorRunCountedWithTopLevelProperty =>
                ObserveRunCountedWithTopLevelProperty(source, profile, definition, ref observation, ref reason),
            MetamorphicSurface.EngineRun =>
                ObserveEngineRun(source, profile, definition, options, ref observation),
            MetamorphicSurface.EngineEvaluateToAtoms =>
                ObserveEngineEvaluateToAtoms(source, profile, definition, options, ref observation),
            MetamorphicSurface.EngineExactFormatter =>
                ObserveEngineExactFormatter(source, profile, definition, options, ref observation),
            _ => throw new MetamorphicHarnessException($"No adapter is implemented for surface {definition.Surface}."),
        };
    }

    // ── Evaluator surfaces ──────────────────────────────────────────────────

    private static bool ObserveRunCountedObserved(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        bool collectEvidence,
        MetamorphicHostFixture? host,
        ref MetamorphicOperationalObservation observation,
        ref string reason)
    {
        if (!TryParse(source, host, ref reason, out var block)) return false;

        var cache = new RunScopedZeroArgPropertyResultCache();
        var loopDiagnostics = collectEvidence ? new LoopOptimizationDiagnostics() : null;
        var sequenceDiagnostics = collectEvidence ? new SequencePipelineDiagnostics() : null;

        var (result, budget) = Evaluator.RunCountedObserved(
            block, profile.Limits, profile.EnableOptimizations, cache, loopDiagnostics, sequenceDiagnostics,
            hostOperations: host?.Operations);

        observation = ObservedFrom(result, budget, profile, definition, loopDiagnostics, sequenceDiagnostics,
            collectEvidence ? MetamorphicCacheEvidence.From(cache.GetSnapshot()) : null);
        return true;
    }

    /// <summary>
    /// The asynchronous twin of <see cref="ObserveRunCountedObserved"/> (SEM-2B). An async-capable
    /// property cache routes the run through the twin family (whose preparation pins both
    /// optimizers off, so the profile's optimizer flag is not a policy here); a gated host fixture
    /// drives it through genuine suspensions. That cache keeps no statistics, so no cache evidence
    /// is claimed.
    /// </summary>
    private static bool ObserveRunCountedObservedAsync(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        bool collectEvidence,
        MetamorphicHostFixture? host,
        ref MetamorphicOperationalObservation observation,
        ref string reason)
    {
        if (!TryParse(source, host, ref reason, out var block)) return false;

        var cache = new RunScopedAsyncZeroArgPropertyResultCache();
        var loopDiagnostics = collectEvidence ? new LoopOptimizationDiagnostics() : null;
        var sequenceDiagnostics = collectEvidence ? new SequencePipelineDiagnostics() : null;

        Task<(EvalResult<Evaluator.CountedResult> Result, KatLang.Evaluation.EvaluationBudget Budget)> Start(CancellationToken token)
            => Evaluator.RunCountedObservedAsync(
                block, profile.Limits, cache, loopDiagnostics, sequenceDiagnostics,
                hostOperations: host?.Operations, cancellationToken: token).AsTask();

        var (result, budget) = host is { Asynchronous: true }
            ? host.Drive(Start, MetamorphicHostFixture.DefaultWatchdog)
            : Start(CancellationToken.None).GetAwaiter().GetResult();

        observation = ObservedFrom(result, budget, profile, definition, loopDiagnostics, sequenceDiagnostics, cacheEvidence: null)
            with { OptimizerPolicy = "twin" };
        return true;
    }

    /// <summary>The shared projection of one observed run (sync or async) onto its neutral observation.</summary>
    private static MetamorphicOperationalObservation ObservedFrom(
        EvalResult<Evaluator.CountedResult> result,
        KatLang.Evaluation.EvaluationBudget budget,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        LoopOptimizationDiagnostics? loopDiagnostics,
        SequencePipelineDiagnostics? sequenceDiagnostics,
        MetamorphicCacheEvidence? cacheEvidence)
    {
        // Snapshot the run's own counters BEFORE encoding anything, so no later read can be
        // mistaken for work the run performed.
        var steps = budget.ConsumedSteps;
        var materializedItems = budget.MaterializedItems;
        var materializedStringChars = budget.MaterializedStringChars;
        var peakDepth = budget.PeakDepth;

        var semantic = SemanticOf(result.IsError, result.IsError ? result.Error : null,
            result.IsError ? null : result.Value.Value, result.IsError ? null : result.Value.EmittedCount);

        // Purity: encoding the outcome must not have charged the run it describes.
        if (budget.ConsumedSteps != steps
            || budget.MaterializedItems != materializedItems
            || budget.MaterializedStringChars != materializedStringChars
            || budget.PeakDepth != peakDepth)
        {
            throw new MetamorphicHarnessException(
                "Observing a completed run changed its budget counters; the operational observation is not a pure read.");
        }

        return new MetamorphicOperationalObservation(
            semantic, steps, materializedItems, materializedStringChars, peakDepth,
            profile.EnableOptimizations ? "on" : "off")
        {
            Facets = definition.Facets,
            Surface = definition.Id,

            OptimizerEvidence = loopDiagnostics is not null && sequenceDiagnostics is not null
                ? MetamorphicOptimizerEvidence.From(loopDiagnostics.GetSnapshot(), sequenceDiagnostics.GetSnapshot())
                : null,
            CacheEvidence = cacheEvidence,
        };
    }

    private static bool ObserveRunCounted(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        ref MetamorphicOperationalObservation observation,
        ref string reason)
    {
        if (!TryParse(source, ref reason, out var block)) return false;

        var result = Evaluator.RunCounted(block, new RunScopedZeroArgPropertyResultCache(), profile.Limits);
        observation = Bare(
            SemanticOf(result.IsError, result.IsError ? result.Error : null,
                result.IsError ? null : result.Value.Value, result.IsError ? null : result.Value.EmittedCount),
            profile, definition);
        return true;
    }

    private static bool ObserveRun(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        ref MetamorphicOperationalObservation observation,
        ref string reason)
    {
        if (!TryParse(source, ref reason, out var block)) return false;

        var result = Evaluator.Run(block, profile.Limits);
        observation = Bare(
            SemanticOf(result.IsError, result.IsError ? result.Error : null,
                result.IsError ? null : result.Value, emittedCount: null),
            profile, definition);
        return true;
    }

    private static bool ObserveRunFlat(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        ref MetamorphicOperationalObservation observation,
        ref string reason)
    {
        if (!TryParse(source, ref reason, out var block)) return false;

        var result = Evaluator.RunFlat(block, profile.Limits);
        var semantic = SemanticOf(result.IsError, result.IsError ? result.Error : null, value: null, emittedCount: null);
        observation = Bare(semantic, profile, definition) with
        {
            Projection = new MetamorphicSurfaceProjection(
                result.IsError ? null : MetamorphicValue.HostAtoms(result.Value),
                RenderedText: null,
                MetamorphicSurfaceProjection.NoRendering,
                RenderedLimit: -1,
                TopLevelProperty: null),
        };
        return true;
    }

    private static bool ObserveRunCountedWithTopLevelProperty(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        ref MetamorphicOperationalObservation observation,
        ref string reason)
    {
        if (!TryParse(source, ref reason, out var block)) return false;

        var result = Evaluator.RunCountedWithTopLevelProperty(
            block, EngineTopLevelPropertyName, new RunScopedZeroArgPropertyResultCache(), profile.Limits);

        var semantic = SemanticOf(
            result.IsError, result.IsError ? result.Error : null,
            result.IsError ? null : result.Value.Output.Value,
            result.IsError ? null : result.Value.Output.EmittedCount);

        // The property channel is compared as text, so it carries the injective, ValueComparer-
        // canonical identity rather than the legacy neutral text (which can collide, SEM-2A).
        var property = result.IsError || result.Value.TopLevelProperty is not { } counted
            ? "absent"
            : MetamorphicStructuralIdentity.Encode(counted.Value) + "#" + counted.EmittedCount.ToString(CultureInfo.InvariantCulture);

        observation = Bare(semantic, profile, definition) with
        {
            Projection = new MetamorphicSurfaceProjection(
                HostAtoms: null, RenderedText: null,
                MetamorphicSurfaceProjection.NoRendering, RenderedLimit: -1, TopLevelProperty: property),
        };
        return true;
    }

    // ── Engine surfaces ─────────────────────────────────────────────────────

    private static bool ObserveEngineRun(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        RunOptions options,
        ref MetamorphicOperationalObservation observation)
    {
        var run = KatLangEngine.Run(source, options);
        var rendered = run.ToDisplayString();

        observation = FromEngineRun(run, rendered, MetamorphicSurfaceProjection.StructuredDisplay, profile, definition);
        return true;
    }

    private static bool ObserveEngineEvaluateToAtoms(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        RunOptions options,
        ref MetamorphicOperationalObservation observation)
    {
        string? atoms;
        bool failed;
        try
        {
            atoms = MetamorphicValue.HostAtoms(KatLangEngine.EvaluateToAtoms(source, options));
            failed = false;
        }
        catch (KatLangException)
        {
            // The documented failure channel of this surface. It carries formatted diagnostics
            // rather than structured errors, so nothing beyond the outcome is claimed.
            atoms = null;
            failed = true;
        }

        observation = Bare(MetamorphicSemanticObservation.OutcomeOnly(failed), profile, definition) with
        {
            Projection = new MetamorphicSurfaceProjection(
                atoms, RenderedText: null,
                MetamorphicSurfaceProjection.NoRendering, RenderedLimit: -1, TopLevelProperty: null),
        };
        return true;
    }

    /// <summary>
    /// The canonical <c>exact</c> output formatter over an engine run.
    ///
    /// <para>This adapter performs TWO independent invocations of the engine with the same
    /// shared immutable <see cref="RunOptions"/>: the first run is rendered by the formatter for
    /// the text, and the second supplies the structured outcome recorded beside it. That is
    /// deliberate rather than incidental — the second invocation is exactly the "independent
    /// runs reusing one options object agree" property, so a formatter text that disagreed with
    /// <c>Run(...).ToDisplayString()</c> of an equal run is reported rather than hidden.</para>
    /// </summary>
    private static bool ObserveEngineExactFormatter(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        RunOptions options,
        ref MetamorphicOperationalObservation observation)
    {
        var text = KatLang.Formatting.OutputFormatters.Exact.Format(KatLangEngine.Run(source, options));
        var run = KatLangEngine.Run(source, options);

        observation = FromEngineRun(run, text, MetamorphicSurfaceProjection.StructuredDisplay, profile, definition);
        return true;
    }

    /// <summary>
    /// <c>KatLangEngine.RunAsync</c> (SEM-2B). With a gated fixture the run is driven through its
    /// suspensions and the fixture's cancellation schedule reaches the run through
    /// <see cref="RunOptions.EvaluationCancellationToken"/>; without one it is simply awaited.
    /// </summary>
    private static bool ObserveEngineRunAsync(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        RunOptions options,
        MetamorphicHostFixture? host,
        ref MetamorphicOperationalObservation observation)
    {
        Task<RunResult> Start(CancellationToken token)
            => KatLangEngine.RunAsync(source, new RunOptions
            {
                EvaluationLimits = options.EvaluationLimits,
                HostOperations = options.HostOperations,
                EvaluationCancellationToken = token,
            });

        var run = host is { Asynchronous: true }
            ? host.Drive(Start, MetamorphicHostFixture.DefaultWatchdog)
            : KatLangEngine.RunAsync(source, options).GetAwaiter().GetResult();

        observation = FromEngineRun(run, run.ToDisplayString(), MetamorphicSurfaceProjection.StructuredDisplay, profile, definition);
        return true;
    }

    /// <summary>The engine's top-level property channel name, mirrored for the evaluator surface.</summary>
    private const string EngineTopLevelPropertyName = "DisplayDecimals";

    private static MetamorphicOperationalObservation FromEngineRun(
        RunResult run,
        string renderedText,
        string renderedProjection,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition)
    {
        var success = run as RunResult.Success;
        var semantic = success is null
            ? MetamorphicSemanticObservation.OutcomeOnly(failed: true)
            : MetamorphicSemanticObservation.OfValue(success.Value, success.EmittedCount);

        return Bare(semantic, profile, definition) with
        {
            Projection = new MetamorphicSurfaceProjection(
                success is null ? null : MetamorphicValue.HostAtoms(success.Atoms),
                renderedText,
                renderedProjection,
                (profile.Limits ?? EvaluationLimits.Default).EffectiveMaxDisplayLength,
                TopLevelProperty: null),
            FailureStage = run switch
            {
                RunResult.Success => null,
                RunResult.ParseFailure => MetamorphicOperationalObservation.FrontEndFailureStage,
                RunResult.EvalFailure => MetamorphicOperationalObservation.EvaluationFailureStage,
                _ => "other:" + run.GetType().Name,
            },
        };
    }

    // ── Shared helpers ──────────────────────────────────────────────────────

    private static bool TryParse(string source, ref string reason, out Expr.AlgorithmExpr block)
        => TryParse(source, host: null, ref reason, out block);

    /// <summary>Parses with the fixture's host operations in scope, exactly as the engine would.</summary>
    private static bool TryParse(string source, MetamorphicHostFixture? host, ref string reason, out Expr.AlgorithmExpr block)
    {
        var parsed = host is null
            ? Parser.Parse(source)
            : Parser.Parse(source, new RunOptions { HostOperations = host.Operations });
        if (parsed.HasErrors)
        {
            block = null!;
            reason = "parse-error";
            return false;
        }

        block = new Expr.AlgorithmExpr(parsed.Root);
        return true;
    }

    private static MetamorphicSemanticObservation SemanticOf(
        bool isError, EvalError? error, Result? value, int? emittedCount)
        => isError
            ? MetamorphicSemanticObservation.OfError(error!)
            : value is null
                ? new MetamorphicSemanticObservation("ok", null, emittedCount, null, null, false)
                : MetamorphicSemanticObservation.OfValue(value, emittedCount);

    /// <summary>An observation with no operational counters — every surface but the observed one.</summary>
    private static MetamorphicOperationalObservation Bare(
        MetamorphicSemanticObservation semantic,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition)
        => new(semantic, 0, 0, 0, 0, profile.EnableOptimizations ? "on" : "off")
        {
            Facets = definition.Facets,
            Surface = definition.Id,

        };
}
