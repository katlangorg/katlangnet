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

    /// <summary>
    /// Conditional branch-body REGIONS the detector processed (<c>ParameterDetector.ProcessConditionalBranchBody</c>
    /// misses of the run's branch-body region memo). One count means one branch body elaborated under one
    /// semantic region — parent scope, binder names, captured names, reporting mode; a body reached again
    /// under the same region (a second family sharing it, a second path to its family) records nothing, so
    /// the count is bounded by distinct (body, region) pairs, never by traversal paths (M4).
    /// </summary>
    public long DetectorBranchBodyRegionExpansions { get; private set; }

    internal void RecordDetectorBranchBodyRegionExpansion()
        => DetectorBranchBodyRegionExpansions = checked(DetectorBranchBodyRegionExpansions + 1);

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

    /// <summary>
    /// Conditional branch-body REGIONS the resolver processed (<c>ImplicitArgumentResolver.ProcessAlgorithm</c>
    /// misses of the run's algorithm region memo for bodies rewritten under a closed branch pattern): one
    /// count per branch body rewritten under one semantic region — the signature snapshot of its free
    /// reference names, the closed binder specification, and the reporting mode (M4).
    /// </summary>
    public long ResolverBranchBodyRegionExpansions { get; private set; }

    internal void RecordResolverBranchBodyRegionExpansion()
        => ResolverBranchBodyRegionExpansions = checked(ResolverBranchBodyRegionExpansions + 1);

    /// <summary>
    /// Nested user-algorithm REGIONS the resolver processed outside any branch pattern — property values,
    /// block literals, open targets (<c>ImplicitArgumentResolver.ProcessAlgorithm</c> misses of the same
    /// memo): one count per algorithm body rewritten under one semantic region — the signature snapshot
    /// of its free reference names and the reporting mode. A property value shared by several
    /// properties or reached through several paths under one snapshot records once (M4).
    /// </summary>
    public long ResolverAlgorithmRegionExpansions { get; private set; }

    internal void RecordResolverAlgorithmRegionExpansion()
        => ResolverAlgorithmRegionExpansions = checked(ResolverAlgorithmRegionExpansions + 1);

    /// <summary>Exposure rewrite expansions (<c>PropertyExposureResolver.RewriteExpr</c>).</summary>
    public long ExposureRewriteExpansions { get; private set; }

    internal void RecordExposureRewriteExpansion()
        => ExposureRewriteExpansions = checked(ExposureRewriteExpansions + 1);

    /// <summary>
    /// User-algorithm regions the exposure pass processed (<c>PropertyExposureResolver.ProcessUserAlgorithm</c>
    /// entries): one count per distinct algorithm body classified under one visible-summary context —
    /// property values, block literals, and conditional branch bodies alike (M4).
    /// </summary>
    public long ExposureAlgorithmExpansions { get; private set; }

    internal void RecordExposureAlgorithmExpansion()
        => ExposureAlgorithmExpansions = checked(ExposureAlgorithmExpansions + 1);

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

    /// <summary>
    /// Completed conditional BRANCH-BODY summary computations in the builder's summary channel
    /// (<c>PropertyDependencyGraphBuilder.CollectBranchBodySummarySeed</c> misses of the
    /// completed branch-body memo, keyed by body reference and binder-name set). Like
    /// <see cref="DependencyAlgorithmSummaryComputations"/>, one count means one whole body
    /// summarized under one binder context; a body shared by several families with the same
    /// binders is summarized once per memo lifetime (M4).
    /// </summary>
    public long DependencyBranchBodySummaryComputations { get; private set; }

    internal void RecordDependencyBranchBodySummaryComputation()
        => DependencyBranchBodySummaryComputations = checked(DependencyBranchBodySummaryComputations + 1);

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

    // ── Semantic model construction (editor) ──────────────────────────────────

    /// <summary>
    /// Expression visits of the semantic model builder (<c>SemanticModelBuilder</c>'s value-position and
    /// open-position expression walks): one count per expression node analyzed under one scope frame. A
    /// node reached again in the same frame — through a second DAG path — is served from the frame's
    /// visit memo and records nothing, so the count is bounded by distinct (node, frame) pairs (M4).
    /// </summary>
    public long SemanticModelExpressionVisits { get; private set; }

    internal void RecordSemanticModelExpressionVisit()
        => SemanticModelExpressionVisits = checked(SemanticModelExpressionVisits + 1);

    /// <summary>
    /// Algorithm visits of the semantic model builder: one count per algorithm node analyzed under one
    /// parent scope frame and one extra-parameter table (a conditional branch's binder symbols, or none).
    /// A shared algorithm reached again under the same frame and table records nothing.
    /// </summary>
    public long SemanticModelAlgorithmVisits { get; private set; }

    internal void RecordSemanticModelAlgorithmVisit()
        => SemanticModelAlgorithmVisits = checked(SemanticModelAlgorithmVisits + 1);

    // ── Elaborated scope-lookup work (M18) ────────────────────────────────────
    // Unlike the traversal counters above, these record LOOKUP work performed by
    // ElaboratedScopeLookup over one observed front-end pass: chain levels
    // visited, linear property-name comparisons, per-level acceleration-index
    // constructions, open-target resolutions, and parent-walk root discoveries.
    // They flow through the observed pass's ElaboratedPropertyScope chain (the
    // chain root carries the observer), so like every other counter they are
    // pass-scoped, passive, and absent from production paths.

    /// <summary>Scope-chain levels visited by direct (ownership-first) name queries.</summary>
    public long LookupLevelVisits { get; private set; }

    internal void RecordLookupLevelVisit()
        => LookupLevelVisits = checked(LookupLevelVisits + 1);

    /// <summary>
    /// Property-name equality comparisons performed by LINEAR scans of a scope
    /// level's property list or an open provider's member list. Index-served
    /// lookups record nothing here (dictionary probes are not linear scans), so
    /// this is the counter that exposes quadratic wide-scope lookup work.
    /// </summary>
    public long LookupPropertyComparisons { get; private set; }

    internal void RecordLookupPropertyComparisons(int count)
        => LookupPropertyComparisons = checked(LookupPropertyComparisons + count);

    /// <summary>Per-level property-name index constructions (at most one per queried level).</summary>
    public long LookupNameIndexBuilds { get; private set; }

    internal void RecordLookupNameIndexBuild()
        => LookupNameIndexBuilds = checked(LookupNameIndexBuilds + 1);

    /// <summary>
    /// Open-target resolutions performed for opened-name matching (one per written
    /// open target examined for providers; dotted targets resolve through their own
    /// nested steps without extra counts here).
    /// </summary>
    public long LookupOpenTargetResolutions { get; private set; }

    internal void RecordLookupOpenTargetResolution()
        => LookupOpenTargetResolutions = checked(LookupOpenTargetResolutions + 1);

    /// <summary>Per-provider exported-member index constructions (at most one per consulted provider).</summary>
    public long LookupOpenMemberIndexBuilds { get; private set; }

    internal void RecordLookupOpenMemberIndexBuild()
        => LookupOpenMemberIndexBuilds = checked(LookupOpenMemberIndexBuilds + 1);

    /// <summary>
    /// Chain-root discoveries performed by WALKING parent links. The cached
    /// per-chain root reference discovers the root at construction time without
    /// a walk, so an accelerated pass records zero.
    /// </summary>
    public long LookupRootDiscoveryWalks { get; private set; }

    internal void RecordLookupRootDiscoveryWalk()
        => LookupRootDiscoveryWalks = checked(LookupRootDiscoveryWalks + 1);
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
