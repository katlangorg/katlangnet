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

    /// <summary><c>KatLangEngine.EvaluateToString</c> — rendered text.</summary>
    EngineEvaluateToString,
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
    bool UsesFrontEndPipeline);

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
            RequiresParsableSource: true, SupportsOptimizerPolicy: true, UsesFrontEndPipeline: false),

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
            RequiresParsableSource: false, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: true),

        new(MetamorphicSurface.EngineEvaluateToAtoms, "engine-evaluate-to-atoms",
            MetamorphicFacets.Outcome | MetamorphicFacets.HostAtoms,
            RequiresParsableSource: false, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: true),

        new(MetamorphicSurface.EngineEvaluateToString, "engine-evaluate-to-string",
            MetamorphicFacets.Outcome | MetamorphicFacets.Structure | MetamorphicFacets.EmittedCount
            | MetamorphicFacets.HostAtoms | MetamorphicFacets.RenderedText,
            RequiresParsableSource: false, SupportsOptimizerPolicy: false, UsesFrontEndPipeline: true),
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
    {
        ArgumentNullException.ThrowIfNull(source);
        ArgumentNullException.ThrowIfNull(profile);
        ArgumentNullException.ThrowIfNull(options);

        var definition = Get(profile.Surface);
        observation = null!;
        reason = "ok";

        return definition.Surface switch
        {
            MetamorphicSurface.EvaluatorRunCountedObserved =>
                ObserveRunCountedObserved(source, profile, definition, collectEvidence, ref observation, ref reason),
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
            MetamorphicSurface.EngineEvaluateToString =>
                ObserveEngineEvaluateToString(source, profile, definition, options, ref observation),
            _ => throw new MetamorphicHarnessException($"No adapter is implemented for surface {definition.Surface}."),
        };
    }

    // ── Evaluator surfaces ──────────────────────────────────────────────────

    private static bool ObserveRunCountedObserved(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        bool collectEvidence,
        ref MetamorphicOperationalObservation observation,
        ref string reason)
    {
        if (!TryParse(source, ref reason, out var block)) return false;

        var cache = new RunScopedZeroArgPropertyResultCache();
        var loopDiagnostics = collectEvidence ? new LoopOptimizationDiagnostics() : null;
        var sequenceDiagnostics = collectEvidence ? new SequencePipelineDiagnostics() : null;

        var (result, budget) = Evaluator.RunCountedObserved(
            block, profile.Limits, profile.EnableOptimizations, cache, loopDiagnostics, sequenceDiagnostics);

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

        observation = new MetamorphicOperationalObservation(
            semantic, steps, materializedItems, materializedStringChars, peakDepth,
            profile.EnableOptimizations ? "on" : "off")
        {
            Facets = definition.Facets,
            Surface = definition.Id,

            OptimizerEvidence = loopDiagnostics is not null && sequenceDiagnostics is not null
                ? MetamorphicOptimizerEvidence.From(loopDiagnostics.GetSnapshot(), sequenceDiagnostics.GetSnapshot())
                : null,
            CacheEvidence = collectEvidence ? MetamorphicCacheEvidence.From(cache.GetSnapshot()) : null,
        };
        return true;
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

        var property = result.IsError || result.Value.TopLevelProperty is not { } counted
            ? "absent"
            : MetamorphicValue.Neutral(counted.Value) + "#" + counted.EmittedCount.ToString(CultureInfo.InvariantCulture);

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
    /// <c>KatLangEngine.EvaluateToString</c>.
    ///
    /// <para>This adapter performs TWO independent invocations of the engine with the same
    /// shared immutable <see cref="RunOptions"/>: <c>EvaluateToString</c> for the text it
    /// returns, and <c>Run</c> for the structured outcome the text surface does not expose. That
    /// is deliberate rather than incidental — the second invocation is exactly the
    /// "independent runs reusing one options object agree" property, and without it the
    /// rendered text could not be attributed to a projection at all.</para>
    ///
    /// <para><b>The projection matters.</b> <c>EvaluateToString</c> returns SPACE-JOINED HOST
    /// ATOMS on success and the structured diagnostic rendering otherwise, so it is NOT equal to
    /// <c>Run(...).ToDisplayString()</c> for a successful program. Recording which projection
    /// produced the text lets the comparator require exact text equality precisely where the two
    /// surfaces really do render the same thing, instead of asserting a false relation.</para>
    /// </summary>
    private static bool ObserveEngineEvaluateToString(
        string source,
        MetamorphicExecutionProfile profile,
        MetamorphicSurfaceDefinition definition,
        RunOptions options,
        ref MetamorphicOperationalObservation observation)
    {
        var text = KatLangEngine.EvaluateToString(source, options);
        var run = KatLangEngine.Run(source, options);

        var projection = run is RunResult.Success
            ? MetamorphicSurfaceProjection.JoinedAtoms
            : MetamorphicSurfaceProjection.StructuredDisplay;

        observation = FromEngineRun(run, text, projection, profile, definition);
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
            : new MetamorphicSemanticObservation(
                "ok", MetamorphicValue.Neutral(success.Value), success.EmittedCount, null, null, false);

        return Bare(semantic, profile, definition) with
        {
            Projection = new MetamorphicSurfaceProjection(
                success is null ? null : MetamorphicValue.HostAtoms(success.Atoms),
                renderedText,
                renderedProjection,
                (profile.Limits ?? EvaluationLimits.Default).EffectiveMaxDisplayLength,
                TopLevelProperty: null),
        };
    }

    // ── Shared helpers ──────────────────────────────────────────────────────

    private static bool TryParse(string source, ref string reason, out Expr.Block block)
    {
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
        {
            block = null!;
            reason = "parse-error";
            return false;
        }

        block = new Expr.Block(parsed.Root);
        return true;
    }

    private static MetamorphicSemanticObservation SemanticOf(
        bool isError, EvalError? error, Result? value, int? emittedCount)
        => isError
            ? MetamorphicSemanticObservation.Failure(
                MetamorphicValue.ErrorCategory(error!), MetamorphicValue.ErrorPayload(error!), error!.IsResourceLimit)
            : new MetamorphicSemanticObservation(
                "ok", value is null ? null : MetamorphicValue.Neutral(value), emittedCount, null, null, false);

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
