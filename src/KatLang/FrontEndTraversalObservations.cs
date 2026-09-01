namespace KatLang;

/// <summary>
/// Passive, pass-scoped observer of front-end AST traversal work. One instance belongs to ONE
/// measured front-end invocation and is passed explicitly through the internal observation
/// overloads (<c>ParameterDetector.DetectPrevalidated</c>, <c>ImplicitArgumentResolver.ResolvePrevalidated</c>,
/// <c>PropertyExposureResolver.Resolve</c>, <c>PropertyDependencyGraphBuilder.BuildDependencyOrder</c> /
/// <c>.BuildSummaries</c>, <c>ModuleLoader.TraversalObservations</c>), so it records the structural
/// work its own pass performs. It is never static and never ambient: the production paths carry no
/// observer and record nothing, so a count can never leak across operations, runs, or threads.
/// (The resolver and exposure passes forward their observer into the one builder channel each
/// consumes.)
///
/// <para>Internal and excluded from every public API; the counts are C# implementation
/// observations with no semantic meaning, used only by the front-end shared-AST-graph (DAG)
/// complexity regressions. A fresh instance starts at zero by construction, so no reset logic
/// exists or is required.</para>
///
/// <para>This is the same operation-scoped observation shape as
/// <see cref="ValueTraversalObservations"/> (value walks) and
/// <see cref="PatternComparisonObservations"/> (parser/clause-family comparisons): created by the
/// measuring caller, mutated only through <c>Record*</c> methods, and read afterwards.</para>
///
/// <para><b>What one count means.</b> Every counter records node-body EXPANSIONS of the named
/// traversal: one increment per structurally recursive node whose children were actually walked.
/// Childless leaves record nothing, and a node reached again through a second shared reference is
/// served from that walk's reference-identity memo without re-expansion, so for ONE walk each
/// count stays bounded by the number of distinct reachable recursive nodes — never the number of
/// expanded tree paths. Memo lifetimes are per constant-context walk region (see each pass), so
/// the same node expanded under two genuinely different contexts records once per context. The
/// one deliberately wider memo is the builder's completed algorithm-summary memo
/// (<c>PropertyDependencyGraphBuilder.SummaryMemo</c>), which spans one whole exposure
/// resolution — see <see cref="DependencyAlgorithmSummaryComputations"/>.</para>
/// </summary>
internal sealed class FrontEndTraversalObservations
{
    /// <summary>Free-name collection expansions (<c>ParameterDetector.CollectFreeParams</c>).</summary>
    public long DetectorCollectExpansions { get; private set; }

    internal void RecordDetectorCollectExpansion()
        => DetectorCollectExpansions = checked(DetectorCollectExpansions + 1);

    /// <summary>
    /// Rewrite expansions of the detector's four rewriting walks
    /// (<c>RewriteParams</c>, <c>RewriteBinderRefs</c>, <c>ProcessExpr</c>, <c>ProcessOpenExpr</c>).
    /// </summary>
    public long DetectorRewriteExpansions { get; private set; }

    internal void RecordDetectorRewriteExpansion()
        => DetectorRewriteExpansions = checked(DetectorRewriteExpansions + 1);

    /// <summary>Diagnostic-span search expansions (<c>ParameterDetector.FindResolveSpan</c>).</summary>
    public long DetectorSpanSearchExpansions { get; private set; }

    internal void RecordDetectorSpanSearchExpansion()
        => DetectorSpanSearchExpansions = checked(DetectorSpanSearchExpansions + 1);

    /// <summary>Implicit-dependency collection expansions (<c>ImplicitArgumentResolver.CollectImplicitDeps</c>).</summary>
    public long ResolverCollectExpansions { get; private set; }

    internal void RecordResolverCollectExpansion()
        => ResolverCollectExpansions = checked(ResolverCollectExpansions + 1);

    /// <summary>
    /// Rewrite expansions of the resolver's rewriting walks
    /// (<c>RewriteImplicitCalls</c>, <c>ProcessExprNested</c>, <c>ProcessOpenExpr</c>).
    /// </summary>
    public long ResolverRewriteExpansions { get; private set; }

    internal void RecordResolverRewriteExpansion()
        => ResolverRewriteExpansions = checked(ResolverRewriteExpansions + 1);

    /// <summary>Exposure rewrite expansions (<c>PropertyExposureResolver.RewriteExpr</c>).</summary>
    public long ExposureRewriteExpansions { get; private set; }

    internal void RecordExposureRewriteExpansion()
        => ExposureRewriteExpansions = checked(ExposureRewriteExpansions + 1);

    /// <summary>Summary-seed expansions (<c>PropertyDependencyGraphBuilder.CollectSummarySeed</c>, expression level).</summary>
    public long DependencySeedExpansions { get; private set; }

    internal void RecordDependencySeedExpansion()
        => DependencySeedExpansions = checked(DependencySeedExpansions + 1);

    /// <summary>
    /// Completed algorithm-level summary computations in the builder's summary channel
    /// (<c>PropertyDependencyGraphBuilder.CollectSharedAlgorithmSummarySeed</c> misses of the
    /// completed-summary memo). Unlike the per-node expansion counters, one count means ONE
    /// whole-algorithm summary computed and admitted; a reach served from the memo records
    /// nothing, so an observed analysis is bounded by the DISTINCT algorithm nodes it
    /// summarizes per memo lifetime — for the exposure resolver, once per resolution rather
    /// than once per ancestor nesting level (M17).
    /// </summary>
    public long DependencyAlgorithmSummaryComputations { get; private set; }

    internal void RecordDependencyAlgorithmSummaryComputation()
        => DependencyAlgorithmSummaryComputations = checked(DependencyAlgorithmSummaryComputations + 1);

    /// <summary>Sibling-dependency expansions (<c>PropertyDependencyGraphBuilder.CollectSiblingDependencyIndices</c>).</summary>
    public long DependencySiblingExpansions { get; private set; }

    internal void RecordDependencySiblingExpansion()
        => DependencySiblingExpansions = checked(DependencySiblingExpansions + 1);

    /// <summary>
    /// Rewrite expansions of the module loader's traversal (synchronous walk and async twins
    /// together — the twins mirror the same walk, so one counter keeps their accounting united).
    /// </summary>
    public long LoaderWalkExpansions { get; private set; }

    internal void RecordLoaderWalkExpansion()
        => LoaderWalkExpansions = checked(LoaderWalkExpansions + 1);

    /// <summary>Load-bearing pre-scan expansions (<c>ModuleLoader</c>'s <c>LoadBearingMarker</c>).</summary>
    public long LoaderMarkerExpansions { get; private set; }

    internal void RecordLoaderMarkerExpansion()
        => LoaderMarkerExpansions = checked(LoaderMarkerExpansions + 1);
}

/// <summary>
/// Shared classification of expression nodes whose children can recursively multiply traversal
/// paths. Analysis walks and rewrites that return childless leaves unchanged can skip memo entries
/// for the excluded variants. A rewrite that can REPLACE a leaf (for example Resolve to Param/Call)
/// must still memoize that leaf to preserve input sharing; its wrapper owns that decision. This
/// list deliberately does not participate in the fail-loud variant-exhaustiveness contract of the
/// traversal switches themselves.
/// </summary>
internal static class AstTraversalDagSafety
{
    internal static bool HasTraversableExprChildren(Expr expr)
        => expr is not (Expr.Num or Expr.StringLiteral or Expr.EmptySequence
            or Expr.NativeCall or Expr.Param or Expr.Resolve);
}
