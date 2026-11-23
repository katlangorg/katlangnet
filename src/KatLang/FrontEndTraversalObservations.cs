namespace KatLang;

/// <summary>
/// Passive, pass-scoped observer of front-end AST traversal work. One instance belongs to ONE
/// measured front-end invocation and is passed explicitly through the internal observation
/// overloads (<c>ParameterDetector.DetectPrevalidated</c>, <c>ImplicitArgumentResolver.ResolvePrevalidated</c>,
/// <c>PropertyExposureResolver.Resolve</c>, <c>PropertyDependencyGraphBuilder.BuildSummaries</c>,
/// <c>ModuleLoader.TraversalObservations</c>,
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
/// <para>Every public numeric counter is also read by reflection in
/// <c>FrontEndCancellationCheckpointTests</c> to detect work after cancellation and route differences;
/// absence of a named reader alone does not make a counter unused.</para>
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
    // Diagnostic-only phase boundaries; absent on production invocations. Besides the in-pass stages
    // (completed-publication, retarget-and-seal, analysis-region-reuse, and a deferred unit's
    // deferred-freeze) it receives each elaboration pass's begin and end under a FrontEndPassStage
    // name (PassBoundary).
    internal Action<string, bool>? StageObserver { get; set; }

    /// <summary>
    /// Reports a pass boundary to <paramref name="observations"/>'s <see cref="StageObserver"/>; nothing without one.
    /// A pass that throws reports no end: the observer's next event (or the operation's end) closes it.
    /// </summary>
    internal static void PassBoundary(FrontEndTraversalObservations? observations, string pass, bool begin)
        => observations?.StageObserver?.Invoke(pass, begin);
    // Diagnostic-only: keys retain the actual contextual equation, including its branch/owner identity.
    // A repeated evaluation is work even when it returns the same answer; a read is not an evaluation.
    internal Dictionary<StaticQueryKey, long> StaticQueryEvaluations { get; } = [];
    internal Dictionary<StaticQueryKey, StaticFactKind> StaticQueryAnswers { get; } = [];
    public long StaticQueryEvaluationCount { get; private set; }
    public long StaticQueryReads { get; private set; }
    public long StaticQueryUnknownReads { get; private set; }
    public long StaticImportedFactReads { get; private set; }
    public long StaticSyntaxIndexBuilds { get; private set; }
    public long StaticSyntaxPropertyEntries { get; private set; }

    internal void RecordStaticQueryRead(StaticQueryKey key, StaticFact fact)
    {
        StaticQueryReads++;
        if (fact.IsUnknown) StaticQueryUnknownReads++;
        StaticQueryAnswers[key] = fact.Kind;
    }

    internal void RecordStaticImportedFactRead() => StaticImportedFactReads++;

    internal void RecordStaticSyntaxIndexBuild(int properties)
    {
        StaticSyntaxIndexBuilds++;
        StaticSyntaxPropertyEntries += properties;
    }

    /// <summary>Actual Q2 target equation evaluations, including fixed-point re-evaluations; cached reads add none.</summary>
    public long StaticOpenTargetEvaluations { get; private set; }
    /// <summary>Distinct contextual Q2 target equations computed. Completed-publication reads add none.</summary>
    public int StaticOpenTargetComputations => _staticOpenTargets?.Count ?? 0;
    private HashSet<StaticQueryKey>? _staticOpenTargets;
    public long StaticOpenIndexBuilds { get; private set; }
    public long StaticOpenIndexMemberVisits { get; private set; }
    internal void RecordStaticOpenIndexBuild() => StaticOpenIndexBuilds++;
    internal void RecordStaticOpenIndexMemberVisit() => StaticOpenIndexMemberVisits++;

    /// <summary>
    /// Provider lists the operation built for its lookup adapters (<c>StaticStructureOperation.Providers</c>: one per level
    /// and stratum, again only after a registered level replaced a provider's declaring level), and the providers they hold.
    /// A retained list served again adds nothing.
    /// </summary>
    public long StaticLevelProviderBuilds { get; private set; }
    public long StaticLevelProviderEntries { get; private set; }
    internal void RecordStaticLevelProvidersBuild(int providers)
    {
        StaticLevelProviderBuilds++;
        StaticLevelProviderEntries += providers;
    }

    /// <summary>
    /// Opened-name selections at a level of more than eight providers that its settled closed member index answered: a
    /// name no provider offers, or exactly one offers (<c>StaticStructureOperation.SelectOpenLevel</c>). An ambiguous
    /// name, a smaller level and a level whose index is not final scan the providers and record nothing here.
    /// </summary>
    public long StaticSettledOpenSelections { get; private set; }
    internal void RecordStaticSettledOpenSelection() => StaticSettledOpenSelections++;
    internal void RecordStaticQueryEvaluation(StaticQueryKey key)
    {
        StaticQueryEvaluationCount++;
        StaticQueryEvaluations[key] = StaticQueryEvaluations.GetValueOrDefault(key) + 1;
        if (key.Kind != StaticQueryKind.OpenProviders || key.Projection != StaticQueryProjection.OpenTarget) return;
        StaticOpenTargetEvaluations = checked(StaticOpenTargetEvaluations + 1);
        (_staticOpenTargets ??= []).Add(key);
    }

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

    /// <summary>Shared bodies detection elaborated, once per body and binding region (<c>ParameterDetector.ProcessSharedBody</c>).</summary>
    public long DetectorSharedRegionExpansions { get; private set; }

    internal void RecordDetectorSharedRegionExpansion()
        => DetectorSharedRegionExpansions = checked(DetectorSharedRegionExpansions + 1);

    /// <summary>Reaches of a shared body detection served from its completed region.</summary>
    public long DetectorSharedRegionHits { get; private set; }

    internal void RecordDetectorSharedRegionHit()
        => DetectorSharedRegionHits = checked(DetectorSharedRegionHits + 1);

    /// <summary>Shared bodies exposure rewrote across parents, once per body and summary region.</summary>
    public long ExposureSharedRegionExpansions { get; private set; }

    internal void RecordExposureSharedRegionExpansion()
        => ExposureSharedRegionExpansions = checked(ExposureSharedRegionExpansions + 1);

    /// <summary>Reaches of a shared body exposure served from its completed region.</summary>
    public long ExposureSharedRegionHits { get; private set; }

    internal void RecordExposureSharedRegionHit()
        => ExposureSharedRegionHits = checked(ExposureSharedRegionHits + 1);

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

    // ── Report payloads under the diagnostic list's capacity (DiagnosticBag) ──
    //
    // The list counts every report and stores the first ones, so a report it drops must cost no payload. These counters
    // separate, for the two resolver producers whose payload grows with the source, the reports MADE (each counted by the
    // list, stored or not), the messages BUILT (only for reports the list stores), and the checks only a message reads.

    /// <summary>
    /// Individual callee parameter verdicts in the ordered bare-forwarding walk.
    /// </summary>
    public long BareForwardingVerdicts { get; private set; }

    internal void RecordBareForwardingVerdict()
        => BareForwardingVerdicts = checked(BareForwardingVerdicts + 1);

    /// <summary>Parameter visits building a rejected callee's name index and caller names probed against it.</summary>
    public long BareForwardingIndexSteps { get; private set; }

    internal void RecordBareForwardingIndexStep()
        => BareForwardingIndexSteps = checked(BareForwardingIndexSteps + 1);

    /// <summary>
    /// Arguments bare forwarding built for supplied parameters: none after a row's first unforwardable parameter, whose row
    /// is left as written.
    /// </summary>
    public long BareForwardingArgumentsBuilt { get; private set; }

    internal void RecordBareForwardingArgumentBuilt()
        => BareForwardingArgumentsBuilt = checked(BareForwardingArgumentsBuilt + 1);

    /// <summary>
    /// <see cref="DiagnosticCode.UnforwardableParameter"/> reports the resolver MADE — one per distinct unforwardable
    /// parameter of a bare-forwarding row, and one per re-issue for a further family sharing a branch body — each counted by
    /// the list whether it stores it or not.
    /// </summary>
    public long UnforwardableParameterReports { get; private set; }

    /// <summary><see cref="DiagnosticCode.UnforwardableParameter"/> messages BUILT: one per report a list stores.</summary>
    public long UnforwardableParameterMessages { get; private set; }

    /// <summary>
    /// Names the wording of an <see cref="DiagnosticCode.UnforwardableParameter"/> message checked to say whether the body
    /// binds the parameter in another form: a capture's one name, a structural pattern's leaves until one is bound. Read
    /// once per stored report, never for a dropped one.
    /// </summary>
    public long UnforwardableParameterWordingChecks { get; private set; }

    internal void RecordUnforwardableParameterWordingCheck()
        => UnforwardableParameterWordingChecks = checked(UnforwardableParameterWordingChecks + 1);

    /// <summary>
    /// <see cref="DiagnosticCode.OutputSpreadMarkerOnAlias"/> reports the resolver MADE (markers on aliases and on
    /// <c>.Algorithm</c> links; the parser's module-holder report is not the resolver's), each counted by the list whether it
    /// stores it or not.
    /// </summary>
    public long OutputSpreadMarkerOnAliasReports { get; private set; }

    /// <summary><see cref="DiagnosticCode.OutputSpreadMarkerOnAlias"/> messages the resolver BUILT: one per report a list stores.</summary>
    public long OutputSpreadMarkerOnAliasMessages { get; private set; }

    /// <summary>
    /// Target parameters the marked-wrapper suggestion of an <see cref="DiagnosticCode.OutputSpreadMarkerOnAlias"/> message
    /// read (<c>B(x, y)* = A(x, y)</c> lists every parameter of the alias's target): only for a stored report.
    /// </summary>
    public long OutputSpreadMarkerWrapperParameterReads { get; private set; }

    internal void RecordOutputSpreadMarkerWrapperParameterRead()
        => OutputSpreadMarkerWrapperParameterReads = checked(OutputSpreadMarkerWrapperParameterReads + 1);

    /// <summary>Counts reports of <paramref name="code"/> made into a diagnostic list.</summary>
    internal void RecordDiagnosticReport(DiagnosticCode code, int count = 1)
    {
        if (code == DiagnosticCode.UnforwardableParameter)
            UnforwardableParameterReports = checked(UnforwardableParameterReports + count);
        else if (code == DiagnosticCode.OutputSpreadMarkerOnAlias)
            OutputSpreadMarkerOnAliasReports = checked(OutputSpreadMarkerOnAliasReports + count);
    }

    /// <summary>Counts one message of <paramref name="code"/> built for a stored report; a code not followed here records nothing.</summary>
    internal void RecordDiagnosticMessage(DiagnosticCode code)
    {
        if (code == DiagnosticCode.UnforwardableParameter)
            UnforwardableParameterMessages = checked(UnforwardableParameterMessages + 1);
        else if (code == DiagnosticCode.OutputSpreadMarkerOnAlias)
            OutputSpreadMarkerOnAliasMessages = checked(OutputSpreadMarkerOnAliasMessages + 1);
    }

    /// <summary>
    /// Argument slots the D2 dependence check of declaration-level output spreading inspected
    /// (<c>ImplicitArgumentResolver.DependsOnPosition</c>): whether a slot's role differs at a known and an unknown
    /// position and the slot holds a bare reference the value role could lift — the question a reference whose lift
    /// only signature selection decides asks of the slots after it (<c>OutputSpreadReferenceNeedsCall</c>). The
    /// rewrite's role walk asks it of each written slot at most once, while such a reference awaits its verdict, so
    /// the count is bounded by the written argument slots of the walked calls, never by those slots times the
    /// references waiting on them.
    /// </summary>
    public long OutputSpreadDependenceSlotInspections { get; private set; }

    internal void RecordOutputSpreadDependenceSlotInspection()
        => OutputSpreadDependenceSlotInspections = checked(OutputSpreadDependenceSlotInspections + 1);

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
    // distinct lifted signature, an owner instance costs its own head, owners whose names meet the
    // lifted ones share the tail without those names once per distinct collision set, and only an
    // owner left with none of the shared tail stores a flat signature of its own.

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

    /// <summary>
    /// Owner-local head slots copied by <see cref="OwnerSignatureInstances"/>: the owner's own patterns plus, when the
    /// lifted signature it extends is itself composed, that signature's local head (never the shared flat tail).
    /// </summary>
    public long OwnerSignatureHeadSlots { get; private set; }

    internal void RecordOwnerSignatureInstance(int headSlots)
    {
        OwnerSignatureInstances = checked(OwnerSignatureInstances + 1);
        OwnerSignatureHeadSlots = checked(OwnerSignatureHeadSlots + headSlots);
    }

    /// <summary>
    /// Owners whose names MEET their lifted ones — an own capture or a reused enclosing parameter binding names a lifted
    /// capture — so the shared tail is read without those names (<c>ImplicitArgumentResolver.LiftSignature</c>,
    /// <c>ImplicitSignatureTemplateInterner.ComposeExcluding</c>). Each is also counted as an
    /// <see cref="OwnerSignatureInstances"/> or, when nothing of the shared tail is left, an
    /// <see cref="OwnerSignaturesMaterialized"/>.
    /// </summary>
    public long OwnerSignatureCollisions { get; private set; }

    internal void RecordOwnerSignatureCollision()
        => OwnerSignatureCollisions = checked(OwnerSignatureCollisions + 1);

    /// <summary>
    /// Shared tail parts built with an owner's real collisions excluded: one per distinct (shared flat part, excluded
    /// name set), however many owners meet that part with those names. Their templates are counted by
    /// <see cref="SignatureTemplatesBuilt"/> like every other flat template.
    /// </summary>
    public long SignatureCollisionPartsBuilt { get; private set; }

    /// <summary>Distinct excluded names of the parts counted by <see cref="SignatureCollisionPartsBuilt"/>.</summary>
    public long SignatureCollisionNamesExcluded { get; private set; }

    /// <summary>Capture or binding entries inspected when indexing a signature part for collision and forwarding keys.</summary>
    public long SignatureNameIndexSlots { get; private set; }

    /// <summary>Top-level pattern slots passed to the evaluator's META placement rule, including host lists.</summary>
    public long PreEvaluationMetaPlacementSlots { get; private set; }

    internal void RecordPreEvaluationMetaPlacementSlots(int count)
        => PreEvaluationMetaPlacementSlots = checked(PreEvaluationMetaPlacementSlots + count);

    internal void RecordSignatureNameIndexSlots(int count)
        => SignatureNameIndexSlots = checked(SignatureNameIndexSlots + count);

    internal void RecordSignatureCollisionPartBuilt(int excludedNames)
    {
        SignatureCollisionPartsBuilt = checked(SignatureCollisionPartsBuilt + 1);
        SignatureCollisionNamesExcluded = checked(SignatureCollisionNamesExcluded + excludedNames);
    }

    /// <summary>
    /// Owners whose signature is a flat list of their own: their names meet the lifted ones and EVERY capture of the shared
    /// tail part is already bound, so what is left — the owner's own patterns and a composed tail's remaining local head — is
    /// stored without a shared part (<c>ImplicitArgumentResolver.LiftSignature</c>).
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
    /// Ledger slots formula lifting charged to the operation's static ledger for the storage it allocated — signature
    /// patterns (<c>ImplicitSignatureTemplateInterner.SignatureStorageUnits</c> each: a flat template built on an intern
    /// miss, an owner head a composition copies) and synthesized arguments
    /// (<c>ImplicitArgumentResolver.BundleStorageUnits</c> each) — recorded only once the ledger accepted the charge.
    /// Every allocation site <see cref="SignatureTemplateSlotsBuilt"/>, <see cref="OwnerSignatureHeadSlots"/> and
    /// <see cref="ImplicitArgumentSlotsBuilt"/> observe is charged, so this equals their slot counts times the weights.
    /// </summary>
    public long LiftingStorageUnitsCharged { get; private set; }

    internal void RecordLiftingStorageCharged(long units)
        => LiftingStorageUnitsCharged = checked(LiftingStorageUnitsCharged + units);

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

    internal long CompletedStaticStructureReads { get; private set; }
    internal void RecordCompletedStaticStructureRead() => CompletedStaticStructureReads++;

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
    /// entry per name (FE-3) — the collision validator's declaration bindings, the one context that
    /// sees completed signatures (detection runs before automatic parameter forwarding, so its
    /// parameter-ownership map never meets a lifted template): an owner whose completed signature is an
    /// L-wide shared template costs one layer per enclosing context, never L
    /// <see cref="ContextEntriesWritten"/>.
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

    private long _suggestionCandidatesExamined;
    private long _suggestionDistanceCells;

    /// <summary>
    /// Candidate names a near-miss suggestion query compared against its unresolved name
    /// (<see cref="SuggestionQuery.Evaluate"/>). A promotion captures only the canonical candidate
    /// context; the comparison runs when a diagnostic actually renders the suggestion, so a valid
    /// program that never renders one records none, however many names it promotes.
    /// </summary>
    public long SuggestionCandidatesExamined => Interlocked.Read(ref _suggestionCandidatesExamined);

    internal void RecordSuggestionCandidateExamined()
        => Interlocked.Increment(ref _suggestionCandidatesExamined);

    /// <summary>
    /// Distance-table cells those comparisons computed: the banded, early-exiting kernel
    /// (<see cref="NameSuggestions.BoundedOptimalStringAlignmentDistance(ReadOnlySpan{char}, ReadOnlySpan{char}, int, Span{int}, ref int)"/>)
    /// computes at most <see cref="NameSuggestions.MaxDistanceCellsPerCandidate"/> per examined candidate, and none for a
    /// candidate a case-insensitive spelling, the threshold or the length difference already decides.
    /// </summary>
    public long SuggestionDistanceCells => Interlocked.Read(ref _suggestionDistanceCells);

    /// <summary>Test callback at completion of a suggestion comparison loop, including the final one of a message.</summary>
    internal Action? SuggestionCompared { get; init; }

    internal void RecordSuggestionDistanceCells(int cells)
    {
        Interlocked.Add(ref _suggestionDistanceCells, cells);
        SuggestionCompared?.Invoke();
    }

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
    /// User-algorithm regions the exposure pass processed (<c>PropertyExposureResolver.ProcessScopeBody</c>
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

    // EXPOSURE-OPEN-1 (October 2026): members read through `open` and settled at one owner. These
    // count the real work an opened chain or a cycle of opened libraries costs: serializing summary
    // seed keys, and settling pending references in the exposure pass.

    /// <summary>
    /// The size of the base-seed contents the member solver shares expansions by within a level, in characters of their
    /// canonical text (<c>SummarySeed.ContentKey</c>), one per member and solve. The solver compares the contents
    /// themselves (November 20 2026) and builds that text only for this observer.
    /// Each PROCESS-WIDE id inside the text (a bound or qualifying owner's <c>OwnerQualifiedParameter.OwnerKey</c>,
    /// a completed origin's requirement identity) counts as ONE character, with the length prefixes around it
    /// measured on that id-free text: the count depends only on the operation, never on how many ids the
    /// process issued before it, so two runs of one input agree on it.
    /// </summary>
    public long SummaryKeyCharacters { get; private set; }

    /// <param name="characters">The length of the key with every process-wide id written as <c>#</c>.</param>
    internal void RecordSummaryKeyCharacters(int characters)
        => SummaryKeyCharacters = checked(SummaryKeyCharacters + characters);

    /// <summary>
    /// Settlement frames the exposure pass runs (<c>PropertyExposureResolver.PendingResolution</c>): one
    /// per pending reference or seed it settles, nested settlements included — the work inside one
    /// top-level settlement that <see cref="RequiredAncestorResolutionComputations"/> does not see.
    /// </summary>
    public long RequiredAncestorSettlementFrames { get; private set; }
    internal Action<object>? RequiredAncestorSettlementObserver { get; set; }

    internal void RecordRequiredAncestorSettlementFrame(object subject)
    {
        RequiredAncestorSettlementFrames = checked(RequiredAncestorSettlementFrames + 1);
        RequiredAncestorSettlementObserver?.Invoke(subject);
    }

    /// <summary>
    /// Open-walk settlements COMPUTED (<c>PendingSelection.OpenWalks</c>; reuses from the share or a run's cache add
    /// none), per open level key (identity) — <see cref="OpenWalksSettlementsWithBoundOwners"/> of them with bound owners
    /// (a reader's own settlement rather than the level's shared one).
    /// </summary>
    internal Dictionary<object, long> OpenWalksSettlements { get; } = new(ReferenceEqualityComparer.Instance);

    public long OpenWalksSettlementsWithBoundOwners { get; private set; }

    internal void RecordOpenWalksSettlement(object level, bool withBoundOwners)
    {
        OpenWalksSettlements[level] = checked(OpenWalksSettlements.GetValueOrDefault(level) + 1);
        if (withBoundOwners) OpenWalksSettlementsWithBoundOwners = checked(OpenWalksSettlementsWithBoundOwners + 1);
    }

    /// <summary>
    /// Nested settlements kept in the exposure run's share (<c>PropertyExposureResolver.SettlementShare</c>):
    /// one per requested key with a complete settlement eligible for reuse which the share did not already answer.
    /// </summary>
    public long SettlementShareStores { get; private set; }

    internal void RecordSettlementShareStore()
        => SettlementShareStores = checked(SettlementShareStores + 1);

    /// <summary>
    /// The largest weight a run's settlement share retained (<c>PropertyExposureResolver.SettlementShare.Key.Weight</c>
    /// plus one per fact view and footprint membership; compared with <c>SettlementShare.DefaultCapacity</c>). A key's
    /// process-wide ids are counted at their widest and its bound owners structurally, so the weight is a function of
    /// the operation alone: two runs of one input agree on it however many ids the process issued between them.
    /// </summary>
    public long SettlementShareRetainedWeight { get; private set; }

    internal void RecordSettlementShareRetainedWeight(long retained)
    {
        if (retained > SettlementShareRetainedWeight)
            SettlementShareRetainedWeight = retained;
    }

    /// <summary>
    /// Settlement frames answered from the run's share instead of walking what their reference reaches:
    /// each is one of <see cref="RequiredAncestorSettlementFrames"/> and settles nothing below itself.
    /// </summary>
    public long SettlementShareHits { get; private set; }

    internal void RecordSettlementShareHit()
        => SettlementShareHits = checked(SettlementShareHits + 1);

    /// <summary>
    /// Settlement frames answered, inside one top-level settlement, from the PARTIAL settlement of their own key: one a
    /// cycle cut left incomplete, kept only while the component it belongs to is still being settled
    /// (<c>PropertyExposureResolver.PendingResolution</c>, COMPONENT SETTLEMENTS). Each is one of
    /// <see cref="RequiredAncestorSettlementFrames"/>, is cut where that settlement was cut, and is published nowhere.
    /// </summary>
    public long SettlementComponentReuses { get; private set; }

    internal void RecordSettlementComponentReuse()
        => SettlementComponentReuses = checked(SettlementComponentReuses + 1);

    /// <summary>
    /// Actual seed requests answered by verified union equations while their component is active.
    /// </summary>
    public long SettlementComponentCompletions { get; private set; }

    internal void RecordSettlementComponentCompletion()
        => SettlementComponentCompletions = checked(SettlementComponentCompletions + 1);

    /// <summary>Frames charged to collect and check component equations, including attempts that declined.</summary>
    public long SettlementComponentDiscoveryFrames { get; private set; }

    internal void RecordSettlementComponentDiscovery(long framesBeforeDiscovery)
        => SettlementComponentDiscoveryFrames += RequiredAncestorSettlementFrames - framesBeforeDiscovery;

    /// <summary>
    /// Shared settlements dropped at a lookup because a completed-fact view they consulted has changed its
    /// version since (<c>StaticLookupFacts.ViewVersion</c>); the settlement is then computed again.
    /// </summary>
    public long SettlementShareStaleViews { get; private set; }

    internal void RecordSettlementShareStaleView()
        => SettlementShareStaleViews = checked(SettlementShareStaleViews + 1);

    /// <summary>
    /// <see cref="SettlementShareHits"/> answered by a footprint candidate (<c>SettlementShare.Settled.Footprint</c>)
    /// rather than by a settlement kept for its exact bound owners.
    /// </summary>
    public long SettlementShareCandidateHits { get; private set; }

    internal void RecordSettlementShareCandidateHit()
        => SettlementShareCandidateHits = checked(SettlementShareCandidateHits + 1);

    /// <summary>Footprint candidates a share lookup or store examined (at most <c>SettlementShare.MaxCandidates</c> each).</summary>
    public long SettlementShareCandidateVisits { get; private set; }

    internal void RecordSettlementShareCandidateVisit()
        => SettlementShareCandidateVisits = checked(SettlementShareCandidateVisits + 1);

    /// <summary>
    /// Footprint work of settlement reuse: one per bound-owner membership a frame records (read directly, or taken
    /// from a nested frame or a reused result) and one per footprint membership a share lookup or store tests.
    /// </summary>
    public long SettlementFootprintWork { get; private set; }

    internal void RecordSettlementFootprintWork(long memberships)
        => SettlementFootprintWork = checked(SettlementFootprintWork + memberships);

    /// <summary>
    /// Bound-owner work for settlement keys (<c>BoundOwnerSet</c>): one per owner offered to a set and the
    /// set's count when distinct sets with the same count and fingerprint reach the membership comparison.
    /// </summary>
    public long SettlementBoundOwnerVisits { get; private set; }

    internal void RecordSettlementBoundOwnerVisits(long owners)
        => SettlementBoundOwnerVisits = checked(SettlementBoundOwnerVisits + owners);

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

    /// <summary>
    /// Expansions of the B3-5★ signature-analysis walk (<c>ImplicitArgumentResolver</c>'s equation recording): one per
    /// node with children first reached under one (role, guard) in one body's row region, so a shared subtree is walked
    /// once per body and context, never once per path.
    /// </summary>
    public long SignatureAnalysisExpansions { get; private set; }

    internal void RecordSignatureAnalysisExpansion()
        => SignatureAnalysisExpansions = checked(SignatureAnalysisExpansions + 1);

    /// <summary>
    /// Bodies the B3-5★ signature analysis analyzed: one per distinct analysis region (a body reached again in a region it was
    /// analyzed in reads that context's facts), mirroring <see cref="ResolverAlgorithmRegionExpansions"/>.
    /// </summary>
    public long SignatureAnalysisBodies { get; private set; }

    internal void RecordSignatureAnalysisBody()
        => SignatureAnalysisBodies = checked(SignatureAnalysisBodies + 1);

    /// <summary>
    /// Compositions of the signature selection and steps of its origin preparation, in execution order. A deterministic
    /// position inside a selection: a test uses <see cref="OnSignatureSelectionStep"/> to act exactly there.
    /// </summary>
    public long SignatureSelectionSteps { get; private set; }

    /// <summary>Called after each step with its number. Test-only, like every observer: production runs carry none.</summary>
    internal Action<long>? OnSignatureSelectionStep { get; init; }

    /// <summary>
    /// Called once per signature selection with what it read and what it decided (the correspondence bridge's read of the
    /// real selector, <see cref="SignatureSelectionProbe"/>). Test-only: production runs carry none, and it changes nothing.
    /// </summary>
    internal Action<SignatureSelectionProbe>? OnSignatureSelection { get; init; }

    internal void RecordSignatureSelectionStep()
    {
        SignatureSelectionSteps = checked(SignatureSelectionSteps + 1);
        OnSignatureSelectionStep?.Invoke(SignatureSelectionSteps);
    }

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

    /// <summary>
    /// The capacity hints the structural preflight's height tables were created with, summed over the walks this
    /// observer saw. An evaluator run's admission walk is handed the node count an earlier walk of the same run
    /// counted (the synchronous entry guard's, or the async entry's tree fact), and 0 when none was made. Capacity
    /// only: the hint decides nothing.
    /// </summary>
    public long StructuralPreflightCapacityHints { get; private set; }

    internal void RecordStructuralPreflightCapacityHint(int hint)
        => StructuralPreflightCapacityHints = checked(StructuralPreflightCapacityHints + hint);

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

    // ── Pre-evaluation validation: host-built parent scopes ───────────────────
    // Recorded by the pre-evaluation validation walker's own parent-scope walk
    // (PreEvaluationValidationWalker.VisitParentScopes), which the base-walker counters
    // above do not see. A scope's member algorithms are counted there as usual; these
    // count the scopes themselves.

    /// <summary>
    /// Parent scopes the pre-evaluation walk validated (walked their <c>open</c> targets and
    /// properties). A scope is validated once, whatever it parents.
    /// </summary>
    public long PreEvaluationParentScopeExpansions { get; private set; }

    internal void RecordPreEvaluationParentScopeExpansion()
        => PreEvaluationParentScopeExpansions = checked(PreEvaluationParentScopeExpansions + 1);

    /// <summary>
    /// Parent scopes the pre-evaluation walk reached along <c>Parent</c> links, including the
    /// already-validated scope at which a walk stops. A walk ends at the first scope already
    /// validated, so K inner scopes over one shared chain of N outer scopes reach N + 2K - 1
    /// scopes, never K × N.
    /// </summary>
    public long PreEvaluationParentScopeLinks { get; private set; }

    internal void RecordPreEvaluationParentScopeLink()
        => PreEvaluationParentScopeLinks = checked(PreEvaluationParentScopeLinks + 1);

    /// <summary>
    /// Alias-reach tables the pre-evaluation walk built or took over: one per walk that checks aliases over a
    /// graph that may hold one, and none for a graph the run's admission walk proved alias-free
    /// (<c>AstStructuralPreflight.AdmittedProgramFacts.IsAliasFree</c>) — such a walk asks no alias reach at all.
    /// </summary>
    public long PreEvaluationAliasReachTables { get; private set; }

    internal void RecordPreEvaluationAliasReachTable()
        => PreEvaluationAliasReachTables = checked(PreEvaluationAliasReachTables + 1);

    /// <summary>
    /// Tables the pre-evaluation walk took over, cleared, from an earlier pass of its run (<c>PreEvaluationTables</c>)
    /// instead of allocating them: the entry guard's node set as its visited set, the structural preflight's height
    /// table as its alias-reach table.
    /// </summary>
    public long PreEvaluationHandedOverTables { get; private set; }

    internal void RecordPreEvaluationHandedOverTable()
        => PreEvaluationHandedOverTables = checked(PreEvaluationHandedOverTables + 1);

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

    /// <summary>Owner properties and distinct row nodes inspected to index deconstruction source algorithms.</summary>
    public long SemanticDeconstructionSourceIndexNodes { get; private set; }

    internal void RecordSemanticDeconstructionSourceIndexNode()
        => SemanticDeconstructionSourceIndexNodes = checked(SemanticDeconstructionSourceIndexNodes + 1);

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

    /// <summary>
    /// Evaluations of one lookup level's open list for a DEFERRED module open by the semantic model builder:
    /// one when it creates a scope frame, which keeps the answer, and one for a level of the lookup chain it
    /// holds no frame for (the prelude level). Deferred-reference classification reads the kept answer at
    /// each level it walks, so the count does not grow with references or with the levels they cross.
    /// </summary>
    public long SemanticModelDeferredOpenChecks { get; private set; }

    internal void RecordSemanticModelDeferredOpenCheck()
        => SemanticModelDeferredOpenChecks = checked(SemanticModelDeferredOpenChecks + 1);

    // ── Scope visibility construction (editor, FE-4b) ─────────────────────────
    // Every visibility tree node is made by ONE interner (VisibilityTreeBuilder.Make) and
    // every layer change passes ONE entry (VisibilityTreeBuilder.Apply), so these counters
    // bound all visibility construction work: no per-scope snapshot can be built elsewhere.

    /// <summary>Frames whose visibility the builder derived: at most one per frame, and only for frames an emitted scope needs.</summary>
    public long ScopeVisibilityStatesDerived { get; private set; }

    internal void RecordScopeVisibilityStateDerived()
        => ScopeVisibilityStatesDerived = checked(ScopeVisibilityStatesDerived + 1);

    /// <summary>Layer changes (set or remove one name) applied to visibility trees; a memoized layer applies none.</summary>
    public long ScopeVisibilityLayerChanges { get; private set; }

    internal void RecordScopeVisibilityLayerChanges(int changes)
        => ScopeVisibilityLayerChanges = checked(ScopeVisibilityLayerChanges + changes);

    /// <summary>Layers served from the (parent tree, layer) memo: a shared open-provider set or FE-3 template table applied once.</summary>
    public long ScopeVisibilityLayerMemoHits { get; private set; }

    internal void RecordScopeVisibilityLayerMemoHit()
        => ScopeVisibilityLayerMemoHits = checked(ScopeVisibilityLayerMemoHits + 1);

    /// <summary>Distinct visibility tree nodes created — the physical backing of every scope's visible set.</summary>
    public long ScopeVisibilityNodesCreated { get; private set; }

    internal void RecordScopeVisibilityNodeCreated()
        => ScopeVisibilityNodesCreated = checked(ScopeVisibilityNodesCreated + 1);

    /// <summary>Node constructions answered by an existing identical node (hash-consing).</summary>
    public long ScopeVisibilityNodesReused { get; private set; }

    internal void RecordScopeVisibilityNodeReused()
        => ScopeVisibilityNodesReused = checked(ScopeVisibilityNodesReused + 1);

    /// <summary>Bulk (merge-and-rebuild) layer applications, and the entries they walked.</summary>
    public long ScopeVisibilityBulkBuilds { get; private set; }

    /// <summary>Entries walked by bulk layer applications.</summary>
    public long ScopeVisibilityBulkBuildEntries { get; private set; }

    internal void RecordScopeVisibilityBulkBuild(int entries)
    {
        ScopeVisibilityBulkBuilds = checked(ScopeVisibilityBulkBuilds + 1);
        ScopeVisibilityBulkBuildEntries = checked(ScopeVisibilityBulkBuildEntries + entries);
    }

    /// <summary>Distinct read-only views created (one per distinct tree and deferred reading context).</summary>
    public long ScopeVisibilityViews { get; private set; }

    internal void RecordScopeVisibilityView()
        => ScopeVisibilityViews = checked(ScopeVisibilityViews + 1);

    /// <summary>Property entries inspected by the compatibility metadata-registration worklists.</summary>
    public long ScopeVisibilityMetadataEntries { get; private set; }

    internal void RecordScopeVisibilityMetadataEntry()
        => ScopeVisibilityMetadataEntries = checked(ScopeVisibilityMetadataEntries + 1);

    /// <summary>
    /// Unfinished metadata-registration entries a closing scope found shadowed and parked on the shadowing
    /// frame until that frame's region closes (SemanticModelBuilder.RegisterVisibleMetadata): every later scope
    /// closing inside that region skips them instead of inspecting them again.
    /// </summary>
    public long ScopeVisibilityMetadataParks { get; private set; }

    internal void RecordScopeVisibilityMetadataPark()
        => ScopeVisibilityMetadataParks = checked(ScopeVisibilityMetadataParks + 1);

    // ── Elaborated scope-lookup work (M18) ────────────────────────────────────
    // Unlike the traversal counters above, these record LOOKUP work performed by
    // ElaboratedScopeLookup over one observed front-end pass: chain levels
    // visited, linear property-name comparisons, per-level acceleration-index
    // constructions, and open-target resolutions.
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

    /// <summary>Public-member index constructions: one per exact target in an operation's shared cache;
    /// providers without an operation cache build their own index.</summary>
    public long LookupOpenMemberIndexBuilds { get; private set; }

    internal void RecordLookupOpenMemberIndexBuild()
        => LookupOpenMemberIndexBuilds = checked(LookupOpenMemberIndexBuilds + 1);

    /// <summary>
    /// Source-processing cancellation checkpoints the elaboration passes reached (2.06): one per bounded
    /// block of pass work, recorded BEFORE the token is read (see <see cref="ObserveCancellation"/>), so a
    /// cancelled pass records the checkpoint that observed its cancellation. The other counters do not see
    /// checkpoints; this one moves on every observed run, cancelled or not.
    /// </summary>
    public long CancellationCheckpoints { get; private set; }

    /// <summary>
    /// Test-only hook invoked at every cancellation checkpoint, BEFORE the token is observed, with the
    /// checkpoint's kind and its 1-based ordinal among the checkpoints of that kind. A cancellation test
    /// cancels its own token source here to place a cancellation deterministically inside a pass; it
    /// belongs to this one observed operation (the SEC-03 shape of <see cref="PatternComparisonObservations.CheckpointReached"/>).
    /// </summary>
    internal Action<FrontEndCancellationCheckpoint, long>? CheckpointReached { get; init; }

    private long[]? _checkpointsByKind;

    /// <summary>The checkpoints of one kind reached so far.</summary>
    internal long CancellationCheckpointsOf(FrontEndCancellationCheckpoint kind)
        => _checkpointsByKind?[(int)kind] ?? 0;

    internal void RecordCancellationCheckpoint(FrontEndCancellationCheckpoint kind)
    {
        CancellationCheckpoints = checked(CancellationCheckpoints + 1);
        _checkpointsByKind ??= new long[FrontEndCancellationCheckpointKinds.Count];
        var ordinal = _checkpointsByKind[(int)kind] = checked(_checkpointsByKind[(int)kind] + 1);
        CheckpointReached?.Invoke(kind, ordinal);
    }

    /// <summary>
    /// THE source-processing cancellation checkpoint of the elaboration passes: records the checkpoint
    /// (and runs the test hook) when the pass is observed, then observes <paramref name="cancellationToken"/>,
    /// so an escaping <see cref="OperationCanceledException"/> carries that token. One volatile read when
    /// nothing observes the pass; it never allocates and changes no other counter.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    internal static void ObserveCancellation(
        FrontEndTraversalObservations? observations, FrontEndCancellationCheckpoint kind, CancellationToken cancellationToken)
    {
        observations?.RecordCancellationCheckpoint(kind);
        cancellationToken.ThrowIfCancellationRequested();
    }
}

/// <summary>
/// The bounded blocks of elaboration work at whose start the passes observe the source-processing
/// token (2.06; see <see cref="FrontEndTraversalObservations.ObserveCancellation"/>), the blocks of
/// semantic-model construction at whose start the builder observes the token of its cancellable entry,
/// and the blocks of an evaluator run's structural admission walk, which observes the run's evaluation token.
/// </summary>
internal enum FrontEndCancellationCheckpoint
{
    /// <summary>One algorithm (a body or a branch body) processed by parameter detection.</summary>
    DetectorAlgorithm,
    /// <summary>One property or output row of an algorithm processed by parameter detection.</summary>
    DetectorRow,
    /// <summary>One algorithm rewritten by implicit-argument resolution.</summary>
    ResolverAlgorithm,
    /// <summary>One property or output row of an algorithm rewritten by implicit-argument resolution.</summary>
    ResolverRow,
    /// <summary>
    /// One algorithm expanded by a front-end <see cref="AstWalker"/> that carries the token: the completed-signature
    /// validators (collision, open-provider and output rules) and the exposure pass's dot-member provenance finalizer.
    /// </summary>
    WalkerAlgorithm,
    /// <summary>One algorithm level of the exposure pass.</summary>
    ExposureAlgorithm,
    /// <summary>One equation evaluation of an exposure level's fixed point (<c>LevelSolver</c>).</summary>
    ExposureLevelEvaluation,
    /// <summary>One frame pushed by an exposure settlement (<c>PendingResolution.Run</c>).</summary>
    ExposureSettlementFrame,
    /// <summary>
    /// One unit of the exposure pass's summary channel: an algorithm summarized, a property of a level's summary
    /// graph, or a frame pushed by the level-expansion driver.
    /// </summary>
    SummaryChannel,
    /// <summary>
    /// One algorithm the semantic model builder's walk analyzes (a body, a branch body, an open-target block),
    /// for the cancellable <c>SemanticModelBuilder.Build</c> entry.
    /// </summary>
    SemanticModelAlgorithm,
    /// <summary>One output row of an algorithm the semantic model builder's walk analyzes.</summary>
    SemanticModelRow,
    /// <summary>One scope whose visibility the semantic model builder derives and emits after its walk.</summary>
    SemanticModelScope,
    /// <summary>A metadata entry, opened provider, or parked entry processed during scope-close registration.</summary>
    SemanticModelMetadata,
    /// <summary>One written open examined to establish a level's deferred ownership.</summary>
    SemanticModelDeferredOpen,
    /// <summary>One lookup level examined to classify a possible deferred reference.</summary>
    SemanticModelDeferredLookup,
    /// <summary>
    /// The start of an evaluator run's structural admission walk and every
    /// <see cref="AstStructuralPreflight.CancellationCheckpointEdges"/> edges after it, including the start and
    /// each block of slots replayed to locate a rejection. The walk observes the run's evaluation token, so a run
    /// over a large or expanded program is cancellable inside its preflight.
    /// </summary>
    EvaluatorPreflight,
}

/// <summary>
/// The <see cref="FrontEndTraversalObservations.StageObserver"/> names of the elaboration passes
/// (<c>FrontEndPipeline.CompleteBeforeExposure</c> and <c>FinalizeElaboration</c>), in pipeline order. Each is
/// reported with <c>begin: true</c> before the pass runs and <c>begin: false</c> after it returns. Diagnostic-only.
/// </summary>
internal static class FrontEndPassStage
{
    internal const string Admit = "pass:admit";
    internal const string Detect = "pass:detect";
    internal const string Resolve = "pass:resolve";
    internal const string Collisions = "pass:collisions";
    internal const string OpenProviders = "pass:open-providers";
    internal const string Outputs = "pass:outputs";
    internal const string Exposure = "pass:exposure";

    /// <summary>Whether a stage name is a pass boundary rather than an in-pass stage.</summary>
    internal static bool IsPass(string stage) => stage.StartsWith("pass:", StringComparison.Ordinal);
}

internal static class FrontEndCancellationCheckpointKinds
{
    internal const int Count = (int)FrontEndCancellationCheckpoint.EvaluatorPreflight + 1;
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
