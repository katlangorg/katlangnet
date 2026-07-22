using System.Globalization;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.ParserFuzz;

/// <summary>
/// Which execution paths one run's optimizers actually took.
///
/// <para>Phase 3's optimizer-versus-generic family must not classify a case as
/// "optimizer versus generic" unless the optimized run genuinely exercised the intended
/// optimizer path. Proving that an outer WRAPPER ran is not enough: <c>LoopExecutions</c>
/// increments for every loop, optimized or not, so a template whose loop shape falls back is
/// still counted there. These flags distinguish the cases the runtime itself distinguishes.</para>
/// </summary>
[Flags]
internal enum MetamorphicOptimizerPath
{
    None = 0,

    /// <summary>An optimized loop plan was SELECTED and entered (<c>OptimizedLoopHits</c>).</summary>
    OptimizedLoopSelected = 1 << 0,

    /// <summary>At least one PLANNED expression executed inside an optimized loop.</summary>
    PlannedExpressionExecuted = 1 << 1,

    /// <summary>An optimized-loop attempt fell back to the generic loop.</summary>
    LoopFallbackExecuted = 1 << 2,

    /// <summary>
    /// A loop ran, the optimizer DECLINED it, and the generic loop executed instead. Requires an
    /// actual recorded fallback, so this is never confused with a loop that returned before the
    /// optimizer was consulted at all.
    /// </summary>
    GenericLoopExecuted = 1 << 3,

    /// <summary>A sequence pipeline was FUSED (filter/count or direct range).</summary>
    FusedPipelineExecuted = 1 << 4,

    /// <summary>A sequence-pipeline fusion attempt fell back.</summary>
    PipelineFallbackExecuted = 1 << 5,

    /// <summary>A generic expression was evaluated inside an otherwise optimized loop.</summary>
    GenericExpressionInsideOptimizedLoop = 1 << 6,

    /// <summary>
    /// A loop ran and returned WITHOUT the optimizer ever being consulted — the zero-iteration
    /// short circuit in <c>RepeatLoopCounted</c>, which returns the initial state before the
    /// optimizer flag, the shape check, or the state-slot check are reached.
    ///
    /// <para>Kept distinct from <see cref="GenericLoopExecuted"/> deliberately. Both have no
    /// optimized-loop hit, but only one of them represents "the optimizer looked and declined";
    /// collapsing them would let a template claim it exercised a fallback it never reached.</para>
    /// </summary>
    LoopShortCircuited = 1 << 7,
}

/// <summary>
/// A stable, machine-independent summary of one run's optimizer diagnostics.
///
/// <para>Counts only: no plan identities, no hash codes, no addresses, no timings. Nothing here
/// is a comparison oracle — the evidence decides whether a case is ADMISSIBLE (did the optimized
/// side really optimize?) and is reported in the fingerprint, while the relations themselves are
/// still compared on semantics and budget counters.</para>
/// </summary>
internal sealed record MetamorphicOptimizerEvidence(
    MetamorphicOptimizerPath Paths,
    long OptimizedLoopHits,
    long OptimizedLoopFallbacks,
    long LoopExecutions,
    long PlannedExpressionHits,
    long PlannedExpressionFallbacks,
    long FusionHits,
    long FusionFallbacks)
{
    /// <summary>The evidence of a run that had no diagnostics channel attached.</summary>
    public static readonly MetamorphicOptimizerEvidence Unobserved =
        new(MetamorphicOptimizerPath.None, 0, 0, 0, 0, 0, 0, 0);

    /// <summary>True when SOME optimizer genuinely selected a specialized path.</summary>
    public bool OptimizerSelected =>
        Paths.HasFlag(MetamorphicOptimizerPath.OptimizedLoopSelected)
        || Paths.HasFlag(MetamorphicOptimizerPath.FusedPipelineExecuted);

    /// <summary>True when nothing optimized ran — the fully generic execution.</summary>
    public bool FullyGeneric => !OptimizerSelected;

    /// <summary>Stable feature text for the fingerprint.</summary>
    public string Feature => Paths == MetamorphicOptimizerPath.None ? "none" : Paths.ToString().Replace(", ", "+", StringComparison.Ordinal);

    internal static MetamorphicOptimizerEvidence From(
        LoopOptimizationDiagnosticsSnapshot loops, SequencePipelineDiagnosticsSnapshot pipelines)
    {
        var fusionHits = loopSafeAdd(pipelines.FilterCountFusionHits, pipelines.DirectRangeFusionHits);
        var fusionFallbacks = loopSafeAdd(pipelines.FilterCountFusionFallbacks, pipelines.DirectRangeFusionFallbacks);

        var paths = MetamorphicOptimizerPath.None;
        if (loops.OptimizedLoopHits > 0) paths |= MetamorphicOptimizerPath.OptimizedLoopSelected;
        if (loops.PlannedExpressionHits > 0) paths |= MetamorphicOptimizerPath.PlannedExpressionExecuted;
        if (loops.OptimizedLoopFallbacks > 0) paths |= MetamorphicOptimizerPath.LoopFallbackExecuted;
        if (loops.LoopExecutions > 0 && loops.OptimizedLoopHits == 0)
        {
            // A recorded fallback means the optimizer was consulted and declined; none means the
            // loop returned before it was ever reached.
            paths |= loops.OptimizedLoopFallbacks > 0
                ? MetamorphicOptimizerPath.GenericLoopExecuted
                : MetamorphicOptimizerPath.LoopShortCircuited;
        }
        if (loops.GenericExpressionEvaluationsInsideOptimizedLoops > 0)
            paths |= MetamorphicOptimizerPath.GenericExpressionInsideOptimizedLoop;
        if (fusionHits > 0) paths |= MetamorphicOptimizerPath.FusedPipelineExecuted;
        if (fusionFallbacks > 0) paths |= MetamorphicOptimizerPath.PipelineFallbackExecuted;

        return new MetamorphicOptimizerEvidence(
            paths,
            loops.OptimizedLoopHits,
            loops.OptimizedLoopFallbacks,
            loops.LoopExecutions,
            loops.PlannedExpressionHits,
            loops.PlannedExpressionFallbacks,
            fusionHits,
            fusionFallbacks);

        static long loopSafeAdd(long a, long b) => checked(a + b);
    }

    public override string ToString() =>
        $"{Feature} loopHits={OptimizedLoopHits.ToString(CultureInfo.InvariantCulture)} " +
        $"loopFallbacks={OptimizedLoopFallbacks.ToString(CultureInfo.InvariantCulture)} " +
        $"loops={LoopExecutions.ToString(CultureInfo.InvariantCulture)} " +
        $"plannedExpr={PlannedExpressionHits.ToString(CultureInfo.InvariantCulture)} " +
        $"fusion={FusionHits.ToString(CultureInfo.InvariantCulture)}/" +
        $"{FusionFallbacks.ToString(CultureInfo.InvariantCulture)}";
}

/// <summary>
/// One run's zero-argument property cache profile, read from the run-scoped cache the executor
/// created for that run alone.
///
/// <para>This is the CACHE-HIT EVIDENCE Phase 3's cached-versus-rebuilt family needs: a template
/// only claims "this side reuses a cached property" if the run really recorded hits, and the
/// rebuilt side only claims independence if it recorded none. Counts only, so the evidence is
/// identical on every machine.</para>
/// </summary>
internal sealed record MetamorphicCacheEvidence(
    int Requests, int Hits, int Misses, int Stores, int DistinctKeys)
{
    /// <summary>The profile of a run whose cache was not observed.</summary>
    public static readonly MetamorphicCacheEvidence Unobserved = new(0, 0, 0, 0, 0);

    internal static MetamorphicCacheEvidence From(ZeroArgPropertyResultCacheSnapshot snapshot)
        => new(snapshot.TotalRequests, snapshot.Hits, snapshot.Misses, snapshot.Stores, snapshot.DistinctKeysCreated);

    /// <summary>Stable feature text for the fingerprint.</summary>
    public string Feature =>
        $"h{Hits.ToString(CultureInfo.InvariantCulture)}" +
        $"m{Misses.ToString(CultureInfo.InvariantCulture)}" +
        $"s{Stores.ToString(CultureInfo.InvariantCulture)}";

    public override string ToString() =>
        $"requests={Requests.ToString(CultureInfo.InvariantCulture)} " +
        $"hits={Hits.ToString(CultureInfo.InvariantCulture)} " +
        $"misses={Misses.ToString(CultureInfo.InvariantCulture)} " +
        $"stores={Stores.ToString(CultureInfo.InvariantCulture)} " +
        $"keys={DistinctKeys.ToString(CultureInfo.InvariantCulture)}";
}
