namespace KatLang;

/// <summary>
/// Passive, pass-scoped observer of front-end AST traversal work. One instance belongs to ONE
/// measured front-end invocation and is passed explicitly through the internal observation
/// overloads (<c>ParameterDetector.DetectPrevalidated</c>, <c>ImplicitArgumentResolver.ResolvePrevalidated</c>,
/// <c>PropertyExposureResolver.Resolve</c>, <c>PropertyDependencyGraphBuilder.BuildDependencyOrder</c> /
/// <c>.BuildSummaries</c>, <c>ModuleLoader.TraversalObservations</c>,
/// <c>LoadElaborationGuard.CreateUnavailableDiagnostics</c>), so it records the structural
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
/// <para><b>What one count means.</b> The per-pass recursive expansion counters record node-body
/// EXPANSIONS of the named traversal: one increment per recursive node whose children were walked.
/// Childless leaves record nothing, and a node reached again through a second shared reference is
/// served from that walk's reference-identity memo without re-expansion, so for ONE walk each
/// count stays bounded by the number of distinct reachable recursive nodes — never the number of
/// expanded tree paths. Memo lifetimes are per constant-context walk region (see each pass), so
/// the same node expanded under two genuinely different contexts records once per context. The
/// one deliberately wider memo is the builder's completed algorithm-summary memo
/// (<c>PropertyDependencyGraphBuilder.SummaryMemo</c>), which spans one whole exposure
/// resolution — see <see cref="DependencyAlgorithmSummaryComputations"/>. Other counters below
/// measure regions, lookups, or base-walker work as their individual summaries specify. In
/// particular, base-walker expression dispatch counts include leaves, and declaration visits
/// count list iterations rather than distinct nodes.</para>
/// </summary>
internal sealed class FrontEndTraversalObservations
{
    /// <summary>Visible bindings probed while building or updating resolver region footprints.</summary>
    public long ResolverSnapshotBindingProbes { get; private set; }

    internal void RecordResolverSnapshotBindingProbe()
        => ResolverSnapshotBindingProbes = checked(ResolverSnapshotBindingProbes + 1);

    /// <summary>Summary entries contributed by branch regions to their family's accumulator.</summary>
    public long BranchSummaryContributionEntries { get; private set; }

    internal void RecordBranchSummaryContribution(int entries)
        => BranchSummaryContributionEntries = checked(BranchSummaryContributionEntries + entries);

    /// <summary>Free-name collection expansions (<c>ParameterDetector.CollectFreeParams</c>).</summary>
    public long DetectorCollectExpansions { get; private set; }

    internal void RecordDetectorCollectExpansion()
        => DetectorCollectExpansions = checked(DetectorCollectExpansions + 1);

    /// <summary>
    /// Rewrite expansions of the detector's three rewriting walks
    /// (<c>RewriteParams</c>, <c>ProcessExpr</c>, <c>ProcessOpenExpr</c>).
    /// </summary>
    public long DetectorRewriteExpansions { get; private set; }

    internal void RecordDetectorRewriteExpansion()
        => DetectorRewriteExpansions = checked(DetectorRewriteExpansions + 1);

    /// <summary>Diagnostic-span search expansions (<c>ParameterDetector.FindFirstResolveSpans</c>).</summary>
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
    /// Closed-list forwarding verdicts the resolver COMPUTED (<c>ImplicitArgumentResolver.MissingClosedListForwardingNames</c>
    /// behind the region memo <c>ResolverWalkMemos.MissingForwardingNames</c>): one count per callee pattern
    /// list judged under one region's rewrite context. The gate and the blocked-forwarding report of every
    /// further reference to that callee in the region are served from the memo and record nothing, so the
    /// count is bounded by distinct (callee, region) pairs, never by the number of references.
    /// </summary>
    public long ResolverForwardingVerdicts { get; private set; }

    internal void RecordResolverForwardingVerdict()
        => ResolverForwardingVerdicts = checked(ResolverForwardingVerdicts + 1);

    /// <summary>
    /// Lifted references the resolver rewrote into synthesized implicit calls — one count per call
    /// EDGE (<c>ImplicitArgumentResolver.RewriteBareReference</c> and <c>LiftBareBuiltinDotCall</c>):
    /// every lifted reference keeps its own call node, which carries its source span and its
    /// origin entry (FE-2).
    /// </summary>
    public long ImplicitCallsSynthesized { get; private set; }

    internal void RecordImplicitCallSynthesized()
        => ImplicitCallsSynthesized = checked(ImplicitCallsSynthesized + 1);

    /// <summary>
    /// Synthesized implicit-argument BUNDLES the resolver built (<c>ResolverWalkMemos.ImplicitArguments</c>):
    /// one per callee parameter-pattern list per rewrite region, however many lifted references to that
    /// callee the region rewrites — they all share the one bundle (FE-2). Before the sharing, every
    /// reference built its own, so K references to a callable of L parameters built K bundles of L slots.
    /// </summary>
    public long ImplicitArgumentBundlesBuilt { get; private set; }

    /// <summary>Top-level argument slots of the bundles counted by <see cref="ImplicitArgumentBundlesBuilt"/>.</summary>
    public long ImplicitArgumentSlotsBuilt { get; private set; }

    internal void RecordImplicitArgumentBundleBuilt(int slots)
    {
        ImplicitArgumentBundlesBuilt = checked(ImplicitArgumentBundlesBuilt + 1);
        ImplicitArgumentSlotsBuilt = checked(ImplicitArgumentSlotsBuilt + slots);
    }

    // ── Shared implicit-signature templates (FE-3) ───────────────────────────
    //
    // K owners that each lift the same L-wide callee hold K × L LOGICAL (owner, slot) bindings. These
    // counters measure the PHYSICAL representation built for them: a template is built once per
    // distinct lifted signature, an owner instance costs its own head, and only an owner whose own
    // names reorder the lifted ones materializes a signature of its own.

    /// <summary>
    /// Flat signature TEMPLATES a resolution interned (<c>ImplicitSignatureTemplateInterner.InternFlat</c>):
    /// one per distinct lifted signature content, however many owners lift it.
    /// </summary>
    public long SignatureTemplatesBuilt { get; private set; }

    /// <summary>Top-level pattern slots of the templates counted by <see cref="SignatureTemplatesBuilt"/>.</summary>
    public long SignatureTemplateSlotsBuilt { get; private set; }

    internal void RecordSignatureTemplateBuilt(int slots)
    {
        SignatureTemplatesBuilt = checked(SignatureTemplatesBuilt + 1);
        SignatureTemplateSlotsBuilt = checked(SignatureTemplateSlotsBuilt + slots);
    }

    /// <summary>
    /// Owners given a lifted signature through a shared template (<c>ImplicitArgumentResolver.LiftSignature</c>):
    /// the template itself for an owner with no own parameter, or its own head composed over the template.
    /// </summary>
    public long OwnerSignatureInstances { get; private set; }

    /// <summary>Owner-local head slots copied by <see cref="OwnerSignatureInstances"/> (never the shared tail).</summary>
    public long OwnerSignatureHeadSlots { get; private set; }

    internal void RecordOwnerSignatureInstance(int headSlots)
    {
        OwnerSignatureInstances = checked(OwnerSignatureInstances + 1);
        OwnerSignatureHeadSlots = checked(OwnerSignatureHeadSlots + headSlots);
    }

    /// <summary>
    /// Owners whose own parameter names meet their lifted ones, so their signature order is genuinely
    /// their own and is merged per owner (<c>ImplicitArgumentResolver.LiftSignature</c>).
    /// </summary>
    public long OwnerSignaturesMaterialized { get; private set; }

    /// <summary>Top-level slots of the signatures counted by <see cref="OwnerSignaturesMaterialized"/>.</summary>
    public long OwnerSignatureMaterializedSlots { get; private set; }

    internal void RecordOwnerSignatureMaterialized(int slots)
    {
        OwnerSignaturesMaterialized = checked(OwnerSignaturesMaterialized + 1);
        OwnerSignatureMaterializedSlots = checked(OwnerSignatureMaterializedSlots + slots);
    }

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

    /// <summary>
    /// Visible-parameter contexts the collision validator interned by their name-set CONTENT key
    /// (<c>ParameterPropertyCollisionValidator.ContextId</c>): one count per bindings instance, whose key
    /// text is hashed exactly once. Every node visit under that instance compares an integer context id,
    /// so the count is bounded by the contexts the walk extends, never by the nodes it visits (hashing the
    /// key — every name in scope — at each node made a P-parameter body quadratic).
    /// </summary>
    public long CollisionContextInterns { get; private set; }

    internal void RecordCollisionContextIntern()
        => CollisionContextInterns = checked(CollisionContextInterns + 1);

    // ── Semantic-context work (FE-1) ──────────────────────────────────────────
    //
    // A scope that sees W names and contains K nested scopes must not cost K × W: each context is
    // built once and EXTENDED by what it adds. These counters measure the W-sized work itself, so
    // a regression that copies, re-sorts, or re-materializes a wide context per child multiplies
    // them by the children while the expansion counters above stay unchanged.

    /// <summary>
    /// Names fed into canonical name-set construction (<see cref="NameSetInterner.With"/>): the
    /// content identity of a semantic-region context — a detector branch body's captured names, a
    /// collision validator's visible parameter names, a sibling walk's shadow names — is extended by
    /// the names a context introduces, so the count is bounded by those introductions, never by
    /// nested scopes × names in scope.
    /// </summary>
    public long ContextNamesCanonicalized { get; private set; }

    internal void RecordContextNameCanonicalized()
        => ContextNamesCanonicalized = checked(ContextNamesCanonicalized + 1);

    /// <summary>
    /// Entries written into PERSISTENT context maps — the resolver's visible signature map, the
    /// detector's parameter-ownership map, the collision validator's declaration bindings — when a
    /// context is extended or updated. An inherited entry is shared, never copied, so the count is
    /// bounded by the declarations each context adds, never by nested scopes × visible names.
    /// </summary>
    public long ContextEntriesWritten { get; private set; }

    internal void RecordContextEntryWritten()
        => ContextEntriesWritten = checked(ContextEntriesWritten + 1);

    /// <summary>
    /// Shared implicit-signature templates added to a persistent context as ONE layer instead of one
    /// entry per name (FE-3) — the detector's parameter-ownership map and the collision validator's
    /// declaration bindings: an owner whose completed signature is an L-wide shared template costs one
    /// layer, never L <see cref="ContextEntriesWritten"/>.
    /// </summary>
    public long ContextTemplateLayers { get; private set; }

    internal void RecordContextTemplateLayer()
        => ContextTemplateLayers = checked(ContextTemplateLayers + 1);

    /// <summary>
    /// Owner parameter names materialized by the summary and exposure passes: one owner's
    /// parameter-name set is built once per resolution and shared by every property summary,
    /// fixed-point iteration, and requirement lookup at that owner — never once per property.
    /// </summary>
    public long OwnerParameterNamesMaterialized { get; private set; }

    internal void RecordOwnerParameterNamesMaterialized(int count)
        => OwnerParameterNamesMaterialized = checked(OwnerParameterNamesMaterialized + count);

    /// <summary>
    /// Names examined while qualifying or stripping a summary seed's required ancestor parameters
    /// against one owner's names: the SMALLER of the seed's requirements and the owner's name set is
    /// scanned, so a narrow seed under a wide owner costs its own size, never the owner's width.
    /// </summary>
    public long SummaryQualificationProbes { get; private set; }

    /// <summary>Actual name probes in shared summary residual checks, including work before memo hits.</summary>
    public long SummaryResidualNameProbes { get; private set; }

    internal void RecordSummaryResidualNameProbe()
        => SummaryResidualNameProbes = checked(SummaryResidualNameProbes + 1);

    internal void RecordSummaryQualificationProbe()
        => SummaryQualificationProbes = checked(SummaryQualificationProbes + 1);

    /// <summary>
    /// Branch-pair steps a canonical name-set union or difference actually computed
    /// (<see cref="NameSetInterner.Union(CanonicalNameSet, CanonicalNameSet)"/>,
    /// <see cref="NameSetInterner.Except(CanonicalNameSet, CanonicalNameSet)"/>); a pair already
    /// combined is answered from the interner's memo. Combining a context with another that differs
    /// from an already combined one by a few names therefore costs the paths those names touch,
    /// never the width of the sets.
    /// </summary>
    public long NameSetOperationSteps { get; private set; }

    internal void RecordNameSetOperationStep()
        => NameSetOperationSteps = checked(NameSetOperationSteps + 1);

    /// <summary>
    /// Candidate names a near-miss suggestion query compared against its unresolved name
    /// (<see cref="SuggestionQuery.Evaluate"/>). A promotion captures only the canonical candidate
    /// context; the comparison runs when a diagnostic actually renders the suggestion, so a valid
    /// program that never renders one records none, however many names it promotes.
    /// </summary>
    public long SuggestionCandidatesExamined { get; private set; }

    internal void RecordSuggestionCandidateExamined()
        => SuggestionCandidatesExamined = checked(SuggestionCandidatesExamined + 1);

    /// <summary>Exposure rewrite expansions (<c>PropertyExposureResolver.RewriteExpr</c>).</summary>
    public long ExposureRewriteExpansions { get; private set; }

    internal void RecordExposureRewriteExpansion()
        => ExposureRewriteExpansions = checked(ExposureRewriteExpansions + 1);

    /// <summary>
    /// Call and dot-call argument BUNDLES the exposure pass rewrote (<c>PropertyExposureResolver.RewriteArgumentBundle</c>):
    /// one count per distinct bundle per region. A bundle shared by several call edges — implicit lifting's
    /// synthesized arguments (FE-2) — rewrites once and stays shared.
    /// </summary>
    public long ExposureArgumentBundleRewrites { get; private set; }

    internal void RecordExposureArgumentBundleRewrite()
        => ExposureArgumentBundleRewrites = checked(ExposureArgumentBundleRewrites + 1);

    /// <summary>
    /// User-algorithm regions the exposure pass processed (<c>PropertyExposureResolver.ProcessUserAlgorithm</c>
    /// entries): one count per distinct algorithm body classified under one visible-summary context —
    /// property values, block literals, and conditional branch bodies alike (M4).
    /// </summary>
    public long ExposureAlgorithmExpansions { get; private set; }

    internal void RecordExposureAlgorithmExpansion()
        => ExposureAlgorithmExpansions = checked(ExposureAlgorithmExpansions + 1);

    // ── FE-4a: required-ancestor sets (PropertyExposureResolver) ──────────────
    // The logical relation "property P requires ancestor input A" can hold K × W times while the
    // representation stays O(K + W): these count the REPRESENTATION work — canonical-set
    // construction and combination, level evaluations, and output lists materialized — never the
    // logical memberships themselves.

    /// <summary>
    /// Worklist evaluations of the exposure level fixed point: one per evaluation of one
    /// property's requirement equation. Bounded by the properties plus the re-evaluations their
    /// changing dependencies cause — never iterations × properties.
    /// </summary>
    public long RequiredAncestorLevelEvaluations { get; private set; }

    internal void RecordRequiredAncestorLevelEvaluation()
        => RequiredAncestorLevelEvaluations = checked(RequiredAncestorLevelEvaluations + 1);

    /// <summary>
    /// Owner-qualified requirement elements fed into canonical-set construction (each costs one
    /// key lookup). A property whose set equals a sibling's shares it without canonicalizing again.
    /// </summary>
    public long RequiredAncestorElementsCanonicalized { get; private set; }

    internal void RecordRequiredAncestorElementCanonicalized()
        => RequiredAncestorElementsCanonicalized = checked(RequiredAncestorElementsCanonicalized + 1);

    /// <summary>Canonical requirement-set branch pairs combined by union or difference (memo misses).</summary>
    public long RequiredAncestorSetOperationSteps { get; private set; }

    internal void RecordRequiredAncestorSetOperationStep()
        => RequiredAncestorSetOperationSteps = checked(RequiredAncestorSetOperationSteps + 1);

    /// <summary>
    /// Top-level open/path/visible-name requirement resolutions COMPUTED (memo misses of the
    /// level solver's validated resolution memo): K properties reading one opened or navigated
    /// member resolve it once while the summaries it read stand.
    /// </summary>
    public long RequiredAncestorResolutionComputations { get; private set; }

    internal void RecordRequiredAncestorResolutionComputation()
        => RequiredAncestorResolutionComputations = checked(RequiredAncestorResolutionComputations + 1);

    /// <summary>
    /// Distinct output lists materialized (<see cref="Property.RequiredAncestorParameters"/> name
    /// lists and internal capture-requirement lists): one per distinct content per run, however
    /// many properties share it.
    /// </summary>
    public long RequiredAncestorListsMaterialized { get; private set; }

    /// <summary>Entries in the lists counted by <see cref="RequiredAncestorListsMaterialized"/> — the physical output storage.</summary>
    public long RequiredAncestorListEntriesMaterialized { get; private set; }

    internal void RecordRequiredAncestorListMaterialized(int entries)
    {
        RequiredAncestorListsMaterialized = checked(RequiredAncestorListsMaterialized + 1);
        RequiredAncestorListEntriesMaterialized = checked(RequiredAncestorListEntriesMaterialized + entries);
    }

    /// <summary>
    /// Persistent base lists built (one per distinct base a derived list extends) and their entries —
    /// the O(W) a family of overlapping requirement sets pays once.
    /// </summary>
    public long RequiredAncestorPersistentBases { get; private set; }

    /// <summary>Entries of the persistent base lists counted by <see cref="RequiredAncestorPersistentBases"/>.</summary>
    public long RequiredAncestorPersistentBaseEntries { get; private set; }

    internal void RecordRequiredAncestorPersistentBase(int entries)
    {
        RequiredAncestorPersistentBases = checked(RequiredAncestorPersistentBases + 1);
        RequiredAncestorPersistentBaseEntries = checked(RequiredAncestorPersistentBaseEntries + entries);
    }

    /// <summary>
    /// Lists DERIVED from a persistent base by their difference, and the difference entries inserted —
    /// a derived list stores only those (sharing every other node with its base).
    /// </summary>
    public long RequiredAncestorListsDerived { get; private set; }

    /// <summary>Difference entries inserted into the lists counted by <see cref="RequiredAncestorListsDerived"/>.</summary>
    public long RequiredAncestorDerivedEntries { get; private set; }

    internal void RecordRequiredAncestorListDerived(int deltaEntries)
    {
        RequiredAncestorListsDerived = checked(RequiredAncestorListsDerived + 1);
        RequiredAncestorDerivedEntries = checked(RequiredAncestorDerivedEntries + deltaEntries);
    }

    /// <summary>
    /// Worklist evaluations of the summary channel's member fixed point
    /// (<c>PropertyDependencyGraphBuilder.CollectAlgorithmSummary</c>): one per evaluation of one
    /// member's seed equation, bounded by members plus dependency-driven re-evaluations.
    /// </summary>
    public long SummaryMemberEvaluations { get; private set; }

    /// <summary>Changed exposure summaries notifying an equation that read them.</summary>
    public long RequiredAncestorReaderNotifications { get; private set; }

    internal void RecordRequiredAncestorReaderNotification()
        => RequiredAncestorReaderNotifications = checked(RequiredAncestorReaderNotifications + 1);

    /// <summary>Changed member seeds notifying an equation that read them.</summary>
    public long SummaryMemberReaderNotifications { get; private set; }

    internal void RecordSummaryMemberReaderNotification()
        => SummaryMemberReaderNotifications = checked(SummaryMemberReaderNotifications + 1);

    internal void RecordSummaryMemberEvaluation()
        => SummaryMemberEvaluations = checked(SummaryMemberEvaluations + 1);

    /// <summary>
    /// Member-seed evaluations that ran a full level expansion (neither an alias of one sibling's
    /// seed nor a validated reuse of an equal-content expansion) — each copies its seed's content.
    /// </summary>
    public long SummaryMemberExpansions { get; private set; }

    internal void RecordSummaryMemberExpansion()
        => SummaryMemberExpansions = checked(SummaryMemberExpansions + 1);

    /// <summary>Summary-seed expansions (<c>PropertyDependencyGraphBuilder.CollectSummarySeed</c>, expression level).</summary>
    public long DependencySeedExpansions { get; private set; }

    internal void RecordDependencySeedExpansion()
        => DependencySeedExpansions = checked(DependencySeedExpansions + 1);

    /// <summary>
    /// Call and dot-call argument-bundle summaries the summary channel COMPUTED
    /// (<c>PropertyDependencyGraphBuilder.CompletedArgumentBundleSeed</c> memo misses): one per distinct
    /// bundle per summary region. A synthesized bundle shared by K lifted call edges (FE-2) is summarized
    /// once, and its completed seed is absorbed by reference rather than copied into each edge's seed.
    /// </summary>
    public long DependencyArgumentBundleSummaries { get; private set; }

    internal void RecordDependencyArgumentBundleSummary()
        => DependencyArgumentBundleSummaries = checked(DependencyArgumentBundleSummaries + 1);

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

    // ── Shared AstWalker base traversal (walker-class passes) ─────────────────
    // These record what the BASE AstWalker examines during ONE observed walk of a
    // walker carrying the observer (AstWalker.TraversalObservations — today the
    // load-elaboration guard). Unlike the per-pass expansion counters above, the
    // declaration counter records every ELEMENT of an algorithm's explicit parameter
    // list the per-declaration loop examines, once per algorithm that lists it: the
    // work a rescan of an intentionally SHARED list performs, which a per-node
    // expansion count alone hides (K2-R2).

    /// <summary>Algorithm bodies the base walker expanded (user and conditional algorithms).</summary>
    public long WalkerAlgorithmExpansions { get; private set; }

    internal void RecordWalkerAlgorithmExpansion()
        => WalkerAlgorithmExpansions = checked(WalkerAlgorithmExpansions + 1);

    /// <summary>Expression nodes the base walker dispatched (<c>AstWalker.VisitExpr</c> entries).</summary>
    public long WalkerExpressionExpansions { get; private set; }

    /// <summary>
    /// Call and dot-call argument SLOTS the base walker dispatched (<c>AstWalker.VisitCallArguments</c>),
    /// memo hits included. A library walker visits a bundle shared by several call nodes — implicit
    /// lifting's synthesized arguments (FE-2) — once per context, so K lifted references to a callable of
    /// L parameters dispatch L slots, never K × L.
    /// </summary>
    public long WalkerCallArgumentSlots { get; private set; }

    internal void RecordWalkerCallArgumentSlots(int slots)
        => WalkerCallArgumentSlots = checked(WalkerCallArgumentSlots + slots);

    /// <summary>
    /// Child edges the structural preflight enumerated (<c>AstStructuralPreflight.Check</c>), memoized
    /// revisits included. A call's argument bundle is ONE child, so a bundle shared by K calls (FE-2)
    /// costs K edges plus its own slots once.
    /// </summary>
    public long StructuralPreflightEdges { get; private set; }

    internal void RecordStructuralPreflightEdge()
        => StructuralPreflightEdges = checked(StructuralPreflightEdges + 1);

    internal void RecordWalkerExpressionExpansion()
        => WalkerExpressionExpansions = checked(WalkerExpressionExpansions + 1);

    /// <summary>
    /// Explicit parameter declarations the base walker's per-declaration loop examined. A
    /// walker that opts out (<c>VisitsExplicitParameterDeclarations => false</c>) records
    /// zero; a walker that keeps the loop records one per declaration PER ALGORITHM that
    /// lists it — for the N synthetic helpers of a wide assignment deconstruction, which
    /// share one N-declaration list, that is N² for a walk that needs none of them.
    /// </summary>
    public long WalkerParameterDeclarationVisits { get; private set; }

    internal void RecordWalkerParameterDeclarationVisit()
        => WalkerParameterDeclarationVisits = checked(WalkerParameterDeclarationVisits + 1);

    /// <summary>
    /// Sum of the recorded base-walker work: user/conditional algorithm expansions, expression
    /// dispatches (including leaves), and parameter-declaration iterations. This is not an
    /// instruction count: subclass-only work and other metadata loops are not instrumented.
    /// </summary>
    public long WalkerSteps
        => checked(WalkerAlgorithmExpansions + WalkerExpressionExpansions + WalkerParameterDeclarationVisits);

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
    /// Call and dot-call argument SLOTS the semantic model builder dispatched, memo hits included: one
    /// analysis per (argument bundle, frame, region), so a bundle shared by K lifted call nodes (FE-2)
    /// dispatches its slots once, never K times.
    /// </summary>
    public long SemanticModelCallArgumentSlots { get; private set; }

    internal void RecordSemanticModelCallArgumentSlots(int slots)
        => SemanticModelCallArgumentSlots = checked(SemanticModelCallArgumentSlots + slots);

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
/// is deliberately a NEGATIVE list (a variant not named here is treated as having children), so
/// a new variant errs toward memoization; classifying it is a performance decision, not part of
/// the compiler-checked exhaustiveness of the traversal switches themselves.
/// </summary>
internal static class AstTraversalDagSafety
{
    internal static bool HasTraversableExprChildren(Expr expr)
        => expr is not (Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence
            or Expr.NativeCall or Expr.Param or Expr.Resolve);
}
