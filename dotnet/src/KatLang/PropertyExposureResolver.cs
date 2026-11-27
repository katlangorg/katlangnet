namespace KatLang;

internal static class PropertyExposureResolver
{
    /// <summary>
    /// One owner-qualified required input: its name AND the exact scope that binds it (by reference;
    /// null when no level of the chain binds the name). Two same-named parameters of different owners
    /// are two requirements — the identity every requirement set is built from (FE-4a).
    /// </summary>
    internal readonly record struct Requirement(string Name, ElaboratedPropertyScope? Owner);

    /// <summary>
    /// What a settlement reads of its bound owners (<see cref="BoundOwnerSet"/>) — every membership it consults, with
    /// the answer, and whether it consulted that there are none at all — and whether one of its owner lookups found no
    /// owner on its site's chain. The settlement's FOOTPRINT (<see cref="SettlementShare.Settled.Footprint"/>) is built
    /// from these reads.
    /// </summary>
    internal interface ISettlementReader
    {
        /// <summary><paramref name="owner"/> was looked up in the bound owners: <paramref name="present"/> is the answer.</summary>
        void NoteMembership(Algorithm owner, bool present);

        /// <summary>Whether the bound owners are none at all (<paramref name="none"/>) decided a route.</summary>
        void NoteNoBoundOwners(bool none);

        /// <summary>A requirement's owner is on no level of the site's chain (it charged nothing there).</summary>
        void NoteOwnerOffChain();
    }

    /// <summary>Whether a settlement consulted that its bound owners are none (<see cref="ISettlementReader.NoteNoBoundOwners"/>).</summary>
    internal enum BoundOwnerEmptiness : byte
    {
        Unread,
        ReadNone,
        ReadSome,
    }

    /// <summary>
    /// TEST SEAM (C1 equivalence, <c>ExposureAccessCheckComplexityTests</c>): while set on the calling flow, every
    /// <see cref="PendingSelection.OpenWalks"/> reference is settled per reader with its own bound owners, the
    /// unshared settlement the shared one must equal. Never set by production code.
    /// </summary>
    internal static readonly AsyncLocal<bool> OpenWalksPerReaderForTesting = new();

    /// <summary>
    /// TEST SEAM (<c>ExposureSettlementFootprintTests</c>): the <see cref="SettlementShareMode"/> of every
    /// <see cref="SettlementShare"/> created on the calling flow — the former exact keys, or no share at all (the
    /// unshared settlement every summary must equal). Never set by production code.
    /// </summary>
    internal static readonly AsyncLocal<SettlementShareMode> SettlementShareModeForTesting = new();

    /// <summary>
    /// TEST SEAM (<c>ExposureSettlementComponentTests</c>): while set on the calling flow, no partial settlement is kept
    /// for its component (COMPONENT SETTLEMENTS, <c>PendingResolution</c>): a key a cycle cut left incomplete is walked
    /// again at every later meeting, the per-path settlement every component settlement must equal. Never set by
    /// production code.
    /// </summary>
    internal static readonly AsyncLocal<bool> ComponentSettlementsPerPathForTesting = new();

    /// <summary>
    /// TEST SEAM (<c>ExposureResidualReuseTests</c>): while set on the calling flow, no LIVE SETTLEMENT is kept
    /// (<c>PendingResolution</c>): a settlement other than the level's unbound open walks that read a summary of the level
    /// in progress is reused only inside its own Run, the former walk every kept live settlement must equal. Never set by
    /// production code.
    /// </summary>
    internal static readonly AsyncLocal<bool> LiveSettlementsPerRunForTesting = new();

    /// <summary>
    /// TEST SEAM (<c>ExposureResidualReuseTests</c>): while set on the calling flow, SEED PARTS are not used
    /// (<c>PendingResolution</c>): every settled seed is folded and its names canonicalized whole, and anchoring expands a
    /// seed at every intervening level, the former walk every seed-part settlement must equal. Never set by production
    /// code.
    /// </summary>
    internal static readonly AsyncLocal<bool> SeedPartsFoldedForTesting = new();

    /// <summary>
    /// TEST SEAM (<c>ExposurePathPartTests</c>): while set on the calling flow, PATH PARTS are not used
    /// (<c>PendingResolution</c>): a settled seed whose parts hold pending references is folded and each reference settled
    /// from the folded seed, the former walk every part-by-part settlement must equal. Never set by production code.
    /// </summary>
    internal static readonly AsyncLocal<bool> PathPartsFoldedForTesting = new();

    // Exercises saturation of the new reuse tables on small programs.
    internal static readonly AsyncLocal<int?> ResidualCacheCapacityForTesting = new();

    // A single union may visit two wide tries before its frame resumes. Each memo miss expands one pair of branches.
    internal sealed class LiveReadNameInterner(FrontEndTraversalObservations? observations, CancellationToken cancellationToken)
        : NameSetInterner
    {
        protected override void RecordOperationStep() => FrontEndTraversalObservations.ObserveCancellation(
            observations, FrontEndCancellationCheckpoint.ExposureLiveNameUnion, cancellationToken);
    }

    /// <summary>How a resolution's <see cref="SettlementShare"/> reuses completed settlements (test seam only).</summary>
    internal enum SettlementShareMode
    {
        /// <summary>The production rule: a settlement answers every bound-owner set that satisfies its footprint.</summary>
        Footprint,

        /// <summary>A settlement answers its exact bound owners only (the rule before footprints).</summary>
        ExactBoundOwners,

        /// <summary>Nothing is kept: every settlement is computed (the reference every reuse must agree with).</summary>
        Unshared,
    }

    /// <summary>
    /// One level of the resolver's lexical chain: the level's elaborated property scope (its
    /// declarations, its <c>open</c> targets, and the ancestor levels through
    /// <see cref="ElaboratedPropertyScope.Parent"/>) paired with the FINAL requirement summary
    /// of each property the level declares (the level in progress carries its fixed point's live
    /// map). Kept as a chain rather than one merged name→summary map
    /// so that a seed relative to an ANCESTOR level — the requirements of a member reached
    /// through an <c>open</c> provider or a member path declared farther out — is expanded from
    /// that level outward, never against declarations that shadow it only from the consumer's
    /// position. Summaries are canonical <see cref="RequirementSet"/>s (FE-4a): properties with equal
    /// requirements share one immutable set.
    /// </summary>
    internal sealed class SummaryScope
    {
        public SummaryScope(
            SummaryScope? parent,
            ElaboratedPropertyScope propertyScope,
            IReadOnlyDictionary<string, RequirementSet> summaries,
            IReadOnlySet<string>? parameters = null,
            Algorithm? algorithm = null,
            int parentDistance = 1)
        {
            Algorithm = algorithm;
            Parameters = parameters ?? NoParameters;
            Parent = parent;
            PropertyScope = propertyScope;
            Summaries = summaries;
            Root = parent is null ? this : parent.Root;
            Depth = parent is null ? 0 : parent.Depth + 1;
            ParentDistance = parentDistance;
        }

        /// <summary>The number of levels above this one.</summary>
        public int Depth { get; }

        /// <summary>
        /// The number of RUNTIME scope levels from this level to <see cref="Parent"/>: 1, or 2 for a level whose
        /// algorithm is written in a hoisted deconstruction right-hand side (see
        /// <see cref="ExposureWalkMemos.NestedDistance"/>). Only <see cref="OwnerDepth"/> reads it: the lookup
        /// chain, <see cref="Depth"/> and every settlement position are those of the written owner.
        /// </summary>
        public int ParentDistance { get; }

        private static readonly IReadOnlySet<string> NoParameters = new HashSet<string>(StringComparer.Ordinal);

        /// <summary>
        /// The names this level binds, as a SET (FE-1): a requirement is attributed to its owner by
        /// membership, so a level of W parameters answers in O(1) — the former list scan cost W per
        /// required name per level, for every property summary at a wide owner.
        /// </summary>
        public IReadOnlySet<string> Parameters { get; }
        public Algorithm? Algorithm { get; }

        public IEnumerable<Requirement> ResolveRequirements(IEnumerable<OwnerQualifiedParameter> requirements)
        {
            foreach (var requirement in requirements)
                if (TryResolveRequirement(requirement, boundOwners: null, reader: null, out var resolved, out _))
                    yield return resolved;
        }

        /// <summary>
        /// <see cref="ResolveRequirements(IEnumerable{OwnerQualifiedParameter})"/> with this level as a settlement
        /// SITE and <paramref name="boundOwners"/> discharging what they own, raising <paramref name="deepestLanding"/>
        /// to the depth of the deepest level an owner lookup landed at (see <see cref="SettlementShare"/>), and
        /// <see cref="NoOwnerLookup"/> when no requirement walked the chain. Every membership of
        /// <paramref name="boundOwners"/> consulted, present or absent, is reported to <paramref name="reader"/>, and so is
        /// a lookup that found no owner on the chain (<see cref="ISettlementReader.NoteOwnerOffChain"/>).
        /// </summary>
        public List<Requirement> ResolveRequirementsFromSite(IEnumerable<OwnerQualifiedParameter> requirements,
            BoundOwnerSet? boundOwners, ISettlementReader? reader, ref int deepestLanding)
        {
            var resolved = new List<Requirement>();
            foreach (var requirement in requirements)
            {
                if (!TryResolveRequirement(requirement, boundOwners, reader, out var one, out var landing))
                {
                    // A lookup that found no owner raises no landing (as since the fail-closed entry was retired), so
                    // the share keeps its settlement for its exact key. Another site below the level could hold that
                    // owner, so it is never answered for other bound owners.
                    if (landing == int.MaxValue)
                        reader?.NoteOwnerOffChain();
                    continue;
                }
                resolved.Add(one);
                deepestLanding = Math.Max(deepestLanding, landing);
            }

            return resolved;
        }

        /// <summary>The landing of a resolution that walked no chain: it is the same from every site.</summary>
        public const int NoOwnerLookup = -1;

        // The ONE owner lookup of an owner-qualified requirement: false when a bound owner supplies it, and false when
        // its owner is on no level of this chain. This level is the SITE of the access check the requirement stands for
        // (owner decision Q2, 2026-11-14), and a check whose owner is not a static ancestor of its site can never pass:
        // no chain there can hold an activation of that owner. No successful read depends on such a check, so it
        // charges nothing (owner decision Q1 = (b), 2026-11-14; the former fail-closed entry, owner depth -1, is
        // retired). The path still fails with LocalOnlyProperty at the member the evaluator checks when it runs.
        // The one bound-owner membership this reads (the owner's, present or absent) is reported to the reader: a
        // settlement is reused under other bound owners only where every membership it read is the same.
        private bool TryResolveRequirement(OwnerQualifiedParameter requirement, BoundOwnerSet? boundOwners,
            ISettlementReader? reader, out Requirement resolved, out int landing)
        {
            landing = NoOwnerLookup;
            resolved = default;
            if (requirement.Owner is null)
            {
                // No owner was recorded: the name's nearest binder on this chain owns it, as for a names-only requirement.
                foreach (var named in ResolveRequirements([requirement.Name]))
                {
                    resolved = named;
                    return true;
                }

                landing = int.MaxValue;
                return false;
            }

            var bound = boundOwners?.Contains(requirement.Owner) == true;
            reader?.NoteMembership(requirement.Owner, bound);
            if (bound)
                return false;

            var owner = OwnerLevel(requirement.Owner);
            landing = owner?.Depth ?? int.MaxValue;
            if (owner is null)
                return false;
            resolved = new Requirement(requirement.Name, BindingScope(owner, requirement.Name));
            return true;
        }

        /// <summary>
        /// The level of this chain, from here outward, whose algorithm is <paramref name="owner"/> (null: none). An owner
        /// lookup of <see cref="TryResolveRequirement"/>; QUALIFIED SEED PARTS (<c>PendingResolution</c>) make it once per
        /// owner for every requirement a seed's parts qualify with it.
        /// </summary>
        public SummaryScope? OwnerLevel(Algorithm owner)
        {
            var level = this;
            while (level is not null && !ReferenceEquals(level.Algorithm, owner))
                level = level.Parent;
            return level;
        }

        /// <summary>
        /// The scope that binds the owner-qualified parameter <paramref name="name"/> of the owner found at
        /// <paramref name="owner"/> (<see cref="OwnerLevel"/>): that level's, except at a branch binding region. The
        /// completed key names the branch binding region by its body, and runtime capture positions retain the separate
        /// family-binding frame above that body, so a name the body does not bind and that frame does is the frame's.
        /// </summary>
        public static ElaboratedPropertyScope BindingScope(SummaryScope owner, string name)
        {
            if (owner.PropertyScope.CompletedContext?.Key.BindingRegion is not null
                && !owner.Parameters.Contains(name)
                && owner.Parent?.Parameters.Contains(name) == true)
                owner = owner.Parent;
            return owner.PropertyScope;
        }

        /// <summary>
        /// The names-only requirements, each at the nearest level of this chain that binds the name. A name no level
        /// binds can be supplied by no activation on this chain, so it is no requirement (owner decision Q1).
        /// </summary>
        public IEnumerable<Requirement> ResolveRequirements(IEnumerable<string> names)
        {
            foreach (var name in names)
            {
                var owner = this;
                while (owner is not null && !owner.Parameters.Contains(name))
                    owner = owner.Parent;
                if (owner is not null)
                    yield return new Requirement(name, owner.PropertyScope);
            }
        }

        /// <summary>
        /// The distance from this level to the level whose scope is <paramref name="owner"/>, in the RUNTIME scope
        /// levels the evaluators' accessibility law counts (<see cref="ParentDistance"/> per step); -1 when off the
        /// chain.
        /// </summary>
        public int OwnerDepth(ElaboratedPropertyScope? owner)
        {
            var depth = 0;
            for (var level = this; level is not null; depth += level.ParentDistance, level = level.Parent)
                if (ReferenceEquals(level.PropertyScope, owner))
                    return depth;
            return -1;
        }

        public SummaryScope? Parent { get; }

        public ElaboratedPropertyScope PropertyScope { get; }

        public IReadOnlyDictionary<string, RequirementSet> Summaries { get; }

        /// <summary>The prelude level every inline <c>open</c> target region starts at.</summary>
        public SummaryScope Root { get; }

        /// <summary>
        /// Ownership-first PROPERTY lookup from this level outward — the direct lexical chain
        /// (the evaluator's <c>LookupLexicalDirect</c>); opens are never consulted here. The summary
        /// belongs to the run that built <paramref name="level"/>; combining adopts it into the
        /// reader's interner (<see cref="RequirementSetInterner.Union"/>).
        /// </summary>
        public bool TryLookup(string name, out SummaryScope level, out PropertyLookupHit hit, out RequirementSet summary)
        {
            for (var current = this; current is not null; current = current.Parent)
            {
                if (current.PropertyScope.TryLookupOwnProperty(name) is { } found)
                {
                    level = current;
                    hit = found;
                    summary = current.Summaries.TryGetValue(name, out var stored) ? stored : default;
                    return true;
                }
            }

            level = null!;
            hit = default;
            summary = default;
            return false;
        }
    }

    /// <summary>
    /// Shared subtrees (acyclic DAGs) are legal and DAG-safe: exposure classification of a
    /// node referenced from several parents matches the equivalent duplicated tree (summary
    /// seeds are name SETS, so multiplicities never mattered), while the rewrite walk is
    /// reference-identity memoized per constant-context region — work is bounded by the
    /// DISTINCT reachable nodes, never the number of root-to-node paths, and the rewritten
    /// output preserves sharing within a scope. One completed-summary memo (see
    /// <see cref="PropertyDependencyGraphBuilder.SummaryMemo"/>) spans the resolution, plus
    /// per-region rewrite memos. The pass runs ONCE: selection never depends on exposure
    /// (<c>open</c> selects public members, dot access declared members, accessibility is
    /// checked after selection), so classifying a member can never change what any name
    /// resolves to, and no re-elaboration round exists.
    /// </summary>
    public static Algorithm Resolve(Algorithm root)
        => Resolve(root, observations: null);

    /// <remarks><paramref name="hostOperations"/> are the run configuration's host operations,
    /// whose ambient prelude members the chain must see exactly as parameter detection and the
    /// evaluator do (the prelude is the outermost owner level, reached before any <c>open</c>): a
    /// host operation named like an opened member is what a bare reference selects, so charging
    /// the opened member instead would classify a self-contained property local-only.</remarks>
    internal static Algorithm Resolve(
        Algorithm root,
        FrontEndTraversalObservations? observations,
        HostOperations? hostOperations = null,
        ModuleUnits? modules = null,
        CancellationToken cancellationToken = default)
        => ResolveRoot(root, observations, hostOperations, modules, sourceUnit: false, cancellationToken);

    /// <summary>
    /// The eager pipeline's entry (<c>FrontEndPipeline.ResolveExposure</c>): <c>Resolve</c> of a compilation's resolved
    /// root, which must carry that compilation's unsealed unit, the operation its settlement frames are charged to
    /// (<see cref="SettlementLedgerOf"/>). A source root without one is an internal error, never an uncharged run.
    /// </summary>
    internal static Algorithm ResolveCompilation(
        Algorithm root,
        FrontEndTraversalObservations? observations,
        HostOperations? hostOperations,
        ModuleUnits? modules,
        CancellationToken cancellationToken)
        => ResolveRoot(root, observations, hostOperations, modules, sourceUnit: true, cancellationToken);

    private static Algorithm ResolveRoot(
        Algorithm root,
        FrontEndTraversalObservations? observations,
        HostOperations? hostOperations,
        ModuleUnits? modules,
        bool sourceUnit,
        CancellationToken cancellationToken)
    {
        try
        {
            var context = AnalyzedStaticStructures.ForBoundAst(root, hostOperations, cancellationToken: cancellationToken);
            var prelude = ElaboratedScopeLookup.CreateScope(context.Facts.Prelude,
                memberIndexes: new OpenMemberIndexCache(observations), completedContext: context.Facts.Context(context.Facts.PreludeKey));
            var physical = context.Key.Parent is { } declaring ? context.Level(declaring, prelude) : prelude;
            var chain = new Stack<ElaboratedPropertyScope>();
            for (var at = physical; at is not null; at = at.Parent) chain.Push(at);
            SummaryScope? parent = null;
            while (chain.TryPop(out var level))
                parent = new(parent, level, NoSummaries,
                    level.CompletedContext?.Facts.Facts(level.CompletedContext.Key)?.Parameters, level.OwnerAlgorithm);
            return ResolveInScope(root, parent!, observations, modules, context, sourceUnit, deferred: null, cancellationToken);
        }
        catch
        {
            // Even cancellation before the first rewrite aborts this unfinished unit. Successful sealed foreign
            // publications are independent of a later caller's token and remain immutable.
            if (root.CompletedStructure is { Entry: not null } publication) publication.Facts.RejectUnsealed();
            throw;
        }
    }

    private static readonly IReadOnlyDictionary<string, RequirementSet> NoSummaries =
        new Dictionary<string, RequirementSet>(StringComparer.Ordinal);

    /// <summary>
    /// SETTLEMENT FRAME CHARGE (2026-11-16; C#-only host resource policy, no classification or Lean rule): the static
    /// work ONE settlement frame costs the operation whose unit the exposure run completes. A frame is what
    /// <see cref="FrontEndTraversalObservations.RequiredAncestorSettlementFrames"/> counts: one per pending reference
    /// or seed settled, nested and reused ones included. Settlement frames can outgrow the source (a member chain
    /// whose links own parameters takes a quadratic number, and an exponential one when its links read two members
    /// below them). Their count measures work independently of retained storage, so they are charged as work: past the
    /// operation's work bound (<see cref="StaticStructureAdmission"/>: 16,384 + 1,024 per admitted node and edge,
    /// whatever the envelope) the run is refused with
    /// <see cref="StaticQueryLimitExceededException"/>, which every source entry reports as one unpositioned
    /// <see cref="DiagnosticCode.StaticStructureLimitExceeded"/> and publishes nothing. The charge changes no result of
    /// an admitted program, depends on the frames alone (never on time, the token or the machine), and is no
    /// cancellation checkpoint.
    /// </summary>
    internal const long SettlementFrameWork = 1;

    /// <summary>
    /// The ledger settlement frames are charged to (<see cref="SettlementFrameWork"/>): that of the operation whose
    /// unit this exposure call completes and seals. The entries that run exposure:
    /// <list type="bullet">
    /// <item>EAGER PARSE (<c>FrontEndPipeline.ResolveExposure</c>, <see cref="ResolveCompilation"/>): the resolved
    /// root carries the compilation's unsealed publication (<c>StaticStructureOperation.CompleteLookups</c>), whose
    /// table holds the admission operation's ledger until this call seals it.</item>
    /// <item>DEFERRED MATERIALIZATION (<see cref="ElaborateDeferredBranch"/>): the resolved branch body carries the
    /// materialization operation's unsealed publication in the same way. Its frames are that operation's, whose
    /// bounds were measured from the loaded body.</item>
    /// <item>STANDALONE ANALYSIS (<c>Resolve</c> of a root that is not the entry of an unsealed unit: a host-built
    /// tree, a declaration-preserving copy, or an already completed tree) has NO operation to charge, and the ledger
    /// is null. Its facts are an analysis snapshot or a sealed table, and both released their producer's ledger when
    /// they sealed, before this pass began (<see cref="AnalyzedStaticStructures"/> retains no producer operation;
    /// completed facts outlive theirs). No source reaches it: source is exposed only by the two entries above, which
    /// require the unit (<paramref name="sourceUnit"/>).</item>
    /// </list>
    /// A source entry without a unit, or an unsealed unit without a ledger, is a broken producer and throws: neither
    /// is ever an uncharged run.
    /// </summary>
    private static StaticQueryResourceBudget? SettlementLedgerOf(CompletedStaticStructures? unit, bool sourceUnit)
    {
        if (unit is not null)
            return unit.ProducerLedger ?? throw new InvalidOperationException(
                "Internal error: an unsealed structural unit reached exposure without its operation's resource ledger.");
        if (sourceUnit)
            throw new InvalidOperationException(
                "Internal error: source exposure requires the unsealed structural unit of the operation it completes.");
        return null;
    }

    /// <summary>
    /// The unit this exposure call completes: the root's own unsealed publication, read through the context the walk
    /// was given. It is the table the call retargets and seals, and whose producer its settlement frames are charged to.
    /// </summary>
    private static CompletedStaticStructures? CompletingUnit(Algorithm root, CompletedStructureContext? structuralContext)
        => root.CompletedStructure is { Entry: not null } completed && !completed.Facts.IsSealed
            && (structuralContext is null || ReferenceEquals(structuralContext.Facts, completed.Facts))
                ? completed.Facts
                : null;

    private static Algorithm ResolveInScope(
        Algorithm root,
        SummaryScope parent,
        FrontEndTraversalObservations? observations,
        ModuleUnits? modules,
        CompletedStructureContext? structuralContext,
        bool sourceUnit,
        DeferredBranchCheck? deferred,
        CancellationToken cancellationToken)
    {
        var unit = CompletingUnit(root, structuralContext);
        var run = new ExposureRun(observations, SettlementLedgerOf(unit, sourceUnit), cancellationToken)
        {
            Modules = modules ?? new(),
        };
        // A deferred branch's materialization counts each module declaration its body splices as one census unit, published
        // with the attempt and taken by later ones (CompletedModuleViews); every other resolution walks its whole input.
        run.SharedBodies = deferred is not null
            ? SharedBodyCensus.OfLoadedBody(root, modules?.CompletedViews, cancellationToken)
            : SharedBodyCensus.Of(root, cancellationToken);
        var summaryMemo = new PropertyDependencyGraphBuilder.SummaryMemo(observations)
        {
            SharedBodies = run.SharedBodies,
            PublishedModules = modules?.Registry,
            CancellationToken = cancellationToken,
            // A deferred branch's materialization is the one resolution that reads completed content an EARLIER
            // operation of the program published: it takes the summaries those operations kept for that content and
            // stages its own, which its attempt publishes with its unit (CompletedProviderSummaries).
            CompletedProviders = deferred is not null && unit is not null
                && CompletedProviderSummaries.ModeForTesting.Value != CompletedProviderSummaries.Mode.Unshared
                    ? modules?.CompletedProviderAttempt : null,
            CompletingUnit = deferred is not null ? unit : null,
            VerifiesAdoptedProviders = CompletedProviderSummaries.ModeForTesting.Value == CompletedProviderSummaries.Mode.Verified,
        };
        var resolved = root;
        root = ProcessAlgorithm(root, parent, summaryMemo, observations, run, structuralContext);
        // A deferred branch is compared with its family's provisional contribution BEFORE its unit is sealed: the
        // comparison is settlement work of this unit, charged to the materialization's ledger like the rest.
        if (deferred is not null)
            deferred.Uncharged = UnchargedByFamily(resolved, deferred, summaryMemo, observations, run);
        CompletedStaticStructures? sealedHere = null;
        if (root.CompletedStructure is { Entry: { } entry } completed && !completed.Facts.IsSealed
            && (structuralContext is null || ReferenceEquals(structuralContext.Facts, completed.Facts)))
        {
            observations?.StageObserver?.Invoke("retarget-and-seal", true);
            completed.Facts.RetargetTree(entry, root, cancellationToken);
            completed.Facts.Seal(cancellationToken);
            sealedHere = completed.Facts;
            observations?.StageObserver?.Invoke("retarget-and-seal", false);
        }
        if (run.HasDotMemberOrigins)
        {
            try
            {
                new DotMemberProvenanceFinalizer(parent.PropertyScope)
                {
                    TraversalObservations = observations, SharedBodies = SharedBodyCensus.Of(root, cancellationToken),
                    CancellationToken = cancellationToken,
                }.VisitAlgorithm(root);
            }
            catch
            {
                // This call has not completed exposure yet. Its own sealed facts must not survive a
                // cancellation/failure of the last walk; a previously completed foreign table is independent.
                sealedHere?.RejectIncompleteExposure();
                throw;
            }
        }
        return root;
    }

    private sealed class ExposureRun
    {
        public ExposureRun(FrontEndTraversalObservations? observations, StaticQueryResourceBudget? settlementLedger,
            CancellationToken cancellationToken)
        {
            Requirements = new RequirementSetInterner(observations);
            Outputs = new RequiredAncestorOutputs(Requirements, observations);
            Settlements = new SettlementShare(observations);
            SettlementLedger = settlementLedger;
            CancellationToken = cancellationToken;
        }

        /// <summary>
        /// The ledger every settlement frame of this run is charged to (<see cref="SettlementFrameWork"/>); null only
        /// for a standalone analysis, which has no operation (<see cref="SettlementLedgerOf"/>).
        /// </summary>
        public readonly StaticQueryResourceBudget? SettlementLedger;

        /// <summary>
        /// The source-processing token of this resolution (the materialization's linked token in a deferred
        /// compile), observed at the start of each algorithm level, level-equation evaluation and settlement
        /// frame (see <see cref="FrontEndTraversalObservations.ObserveCancellation"/>).
        /// </summary>
        public readonly CancellationToken CancellationToken;

        public bool HasDotMemberOrigins;

        /// <summary>What this exposure input shares across paths; null when nothing is.</summary>
        public SharedBodyCensus? SharedBodies;

        /// <summary>Rewritten shared bodies across parents (see <see cref="SharedExposureRegion"/>).</summary>
        public Dictionary<SharedExposureRegion, Algorithm>? SharedRegions;

        /// <summary>
        /// The prelude regions open lists are rewritten in where the chain's root is not the level that answers for a
        /// block head, by that level (<see cref="OpenTargetRegion"/>); null while none is.
        /// </summary>
        public Dictionary<ElaboratedPropertyScope, SummaryScope>? OpenTargetRegions;

        private RegionFreeNames? _regionNames;
        public RegionFreeNames RegionNames => _regionNames ??= new(new NameSetInterner());

        /// <summary>
        /// The operation's loaded module units (Q-32 I-U): every resolved module declaration (one
        /// per canonical URL) to its one classified declaration (see the module arm of
        /// <see cref="ProcessAlgorithm"/>).
        /// </summary>
        public ModuleUnits Modules = new();

        /// <summary>
        /// FE-4a: the run's one requirement-set interner — every level's summaries are canonical sets
        /// of this interner, so equal summaries are one shared set and compare by reference.
        /// </summary>
        public readonly RequirementSetInterner Requirements;

        /// <summary>FE-4a: the run's one output projection — one shared list per distinct set.</summary>
        public readonly RequiredAncestorOutputs Outputs;

        /// <summary>
        /// The run's completed nested settlements, shared across its top-level settlements and levels
        /// (see <see cref="SettlementShare"/>). Its results are sets of <see cref="Requirements"/>.
        /// </summary>
        public readonly SettlementShare Settlements;

        /// <summary>
        /// FE-3: whether an expression subtree is REWRITE-INVARIANT — it reaches no nested algorithm
        /// (the only thing this pass rewrites below an expression) and no dot-call edge (whose
        /// provenance the pass records) — by node reference, for the whole resolution. Such a subtree
        /// is returned as it is in every region instead of being re-copied per region, so one
        /// synthesized argument bundle shared by K owners stays one bundle, walked once.
        /// </summary>
        private Dictionary<object, bool>? _rewriteInvariant;

        public bool IsRewriteInvariant(Expr expr)
        {
            FrontEndStack.Ensure();
            if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
                return expr is not Expr.AlgorithmExpr and not Expr.DotCall;
            _rewriteInvariant ??= new(ReferenceEqualityComparer.Instance);
            if (_rewriteInvariant.TryGetValue(expr, out var invariant))
                return invariant;
            invariant = expr switch
            {
                Expr.AlgorithmExpr or Expr.DotCall => false,
                Expr.Grace grace => IsRewriteInvariant(grace.Inner),
                Expr.Unary unary => IsRewriteInvariant(unary.Operand),
                Expr.Binary binary => IsRewriteInvariant(binary.Left) && IsRewriteInvariant(binary.Right),
                Expr.Comparison comparison => IsRewriteInvariant(comparison.First)
                    && comparison.Links.All(link => IsRewriteInvariant(link.Operand)),
                Expr.Index index => IsRewriteInvariant(index.Target) && IsRewriteInvariant(index.Selectors),
                Expr.SequenceSpread spread => IsRewriteInvariant(spread.Operand),
                Expr.SequenceConstruct construct => IsRewriteInvariant(construct.Left) && IsRewriteInvariant(construct.Right),
                Expr.ListLiteral list => IsRewriteInvariant(list.Items),
                Expr.Capture capture => IsRewriteInvariant(capture.Body),
                Expr.Call call => IsRewriteInvariant(call.Function) && IsRewriteInvariant(call.Args),
                Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral
                    or Expr.EmptySequence or Expr.NativeCall => true,
            };
            _rewriteInvariant[expr] = invariant;
            return invariant;
        }

        public bool IsRewriteInvariant(OutputBundle bundle)
        {
            _rewriteInvariant ??= new(ReferenceEqualityComparer.Instance);
            if (_rewriteInvariant.TryGetValue(bundle, out var invariant))
                return invariant;
            invariant = bundle.Head.All(IsRewriteInvariant) && (bundle.Tail is not { } tail || IsRewriteInvariant(tail));
            _rewriteInvariant[bundle] = invariant;
            return invariant;
        }
    }

    /// <summary>
    /// The ONE classification rule, applied to every property declared in every body — the
    /// root, a brace block, a property value, an open-target block, and a conditional branch
    /// body alike. A property is <see cref="PropertyExposure.Exported"/> when its value is
    /// self-contained, and <see cref="PropertyExposure.LocalOnlyCapturedAncestorParameters"/>
    /// when its value (transitively) requires an input that only an enclosing owner's call
    /// binds: a parameter of an enclosing parameterized algorithm, or a pattern binder of an
    /// enclosing conditional branch (both reach the summary channel as the same
    /// <see cref="Expr.Param"/> references, and neither is owned by the declaring body). The
    /// required names are recorded on the property
    /// (<see cref="Property.RequiredAncestorParameters"/>): owner-qualified capture positions retain the original
    /// bindings for the evaluators' accessibility law, including across shadowing. Exported-ness is thus a fact
    /// about the property's VALUE — evaluable wherever the property can be reached — never
    /// about where the declaration is written, and never a universal hiding: a local-only
    /// member is usable from every lexical context inside the owners of its required inputs.
    /// WHERE it can be reached from is decided structurally by lookup, not here: a
    /// conditional family exposes no structural members, so nothing declared in a branch body
    /// is reachable BY NAME from outside the conditional (the evaluator, the front-end lookup,
    /// the editor, and Lean all deny that at the family and report it as
    /// <see cref="PropertyExposure.LocalOnlyConditionalAlgorithm"/>, which is a family-level
    /// error reason this pass never assigns). Inside the branch — and on the algorithm
    /// channel, for anything the branch itself hands out — a branch declaration therefore
    /// behaves exactly like the same declaration in a parameterized body.
    /// </summary>
    private static PropertyExposure ClassifyDeclaredProperty(RequirementSet summary)
        => summary.IsEmpty
            ? PropertyExposure.Exported
            : PropertyExposure.LocalOnlyCapturedAncestorParameters;

    /// <summary>
    /// Reference-identity memo state for ONE exposure rewrite region — one user algorithm's
    /// opens/output/property-value processing (the final visible summaries are fixed before
    /// any of it runs), or one conditional's open list. Shared expressions rewrite once and
    /// stay shared; <see cref="Algorithms"/> memoizes nested-algorithm processing (property
    /// values and <see cref="Expr.AlgorithmExpr"/> contents run under the identical context:
    /// the final summaries), so two properties or wrappers sharing ONE algorithm classify it
    /// once. The resolution-wide summary memo rides along so nested regions keep sharing
    /// completed summaries. Conditional BRANCH bodies use memo regions keyed by their relative binder/open
    /// context. Equivalent family contexts can share analysis, but a plain body or different
    /// binder context has different owner positions and must be classified separately.
    /// </summary>
    private sealed class ExposureWalkMemos(
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations,
        SummaryScope scope,
        ExposureRun run)
    {
        public Dictionary<Expr, Expr>? Rewrites;

        /// <summary>
        /// Call and dot-call argument bundles rewritten in this region, by bundle reference: implicit
        /// lifting gives every lifted reference to one callable in a resolver region the SAME
        /// synthesized bundle (FE-2), and it must stay one bundle here rather than being copied once
        /// per call edge (see <see cref="RewriteArgumentBundle"/>).
        /// </summary>
        public Dictionary<OutputBundle, OutputBundle>? ArgumentBundles;

        public Dictionary<Algorithm, Algorithm>? Algorithms;

        private Dictionary<IReadOnlyList<Expr>, Dictionary<int, ExposureWalkMemos>>? _branchRegions;

        public ExposureWalkMemos ForBranch(Algorithm.Conditional family, Pattern pattern)
        {
            // These are relative capture positions, not runtime family identities.
            // Equal binder sets and opens under one parent produce the same metadata;
            // retaining that equivalence prevents shared family diamonds expanding paths.
            var opens = family.Opens.Count == 0 ? Array.Empty<Expr>() : family.Opens;
            _branchRegions ??= new(ReferenceEqualityComparer.Instance);
            if (!_branchRegions.TryGetValue(opens, out var byBinders))
                _branchRegions[opens] = byBinders = new();
            var context = SummaryMemo.BranchContexts.NamesOf(pattern);
            var key = context.Id;
            if (!byBinders.TryGetValue(key, out var region))
            {
                var familyScope = ElaboratedScopeLookup.CreateScope(family, Scope.PropertyScope);
                region = new ExposureWalkMemos(SummaryMemo, Observations,
                    new SummaryScope(Scope, familyScope, NoSummaries, context.Names, family, NestedDistance), Run);
                byBinders[key] = region;
            }
            return region;
        }

        /// <summary>
        /// The number of RUNTIME scope levels from an algorithm written in this region's expressions to
        /// <see cref="Scope"/>: 1, except in the region of a hoisted deconstruction right-hand side
        /// (<see cref="ForDeconstructionSourceRows"/>), where it is 2.
        /// </summary>
        public int NestedDistance { get; private init; } = 1;

        /// <summary>
        /// The region of this level's hoisted deconstruction right-hand sides (<c>a, b = RHS</c>). Their rows are
        /// the written owner's for every lookup, so the region keeps this one's <see cref="Scope"/>: same visible
        /// summaries, same opens, same completed context. But the evaluators evaluate the rows as the output of the
        /// synthetic source property, a parameterless scope level of its own between the owner and whatever the
        /// rows nest: a block written there is wired under the source, not under the owner. Capture positions are
        /// read on that runtime chain (<c>IsAccessibleFrom</c>; Lean: <c>memberAccessible?</c>), so every level
        /// opened from this region stands one more level away from <see cref="Scope"/>
        /// (<see cref="SummaryScope.ParentDistance"/>). A position counted on the written chain alone named the
        /// source's level, which binds nothing, and the access of a captured member selected from such a block was
        /// refused inside its own owner's call. One region per level: its rows share one context.
        /// </summary>
        public ExposureWalkMemos ForDeconstructionSourceRows()
            => _deconstructionSourceRows ??= new ExposureWalkMemos(SummaryMemo, Observations, Scope, Run)
            {
                NestedDistance = NestedDistance + 1,
            };

        private ExposureWalkMemos? _deconstructionSourceRows;

        public readonly PropertyDependencyGraphBuilder.SummaryMemo SummaryMemo = summaryMemo;

        public readonly FrontEndTraversalObservations? Observations = observations;

        public readonly SummaryScope Scope = scope;

        public readonly ExposureRun Run = run;
    }

    private static Algorithm ProcessAlgorithm(
        Algorithm algorithm,
        SummaryScope parent,
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations,
        ExposureRun run,
        CompletedStructureContext? completedContext = null,
        int parentDistance = 1)
        => algorithm switch
        {
            // A loaded module (Q-31 H-P) is a source unit rooted at the prelude: its exposure is
            // settled under the prelude level whatever holds it — nothing in it can require the
            // holder's parameters — so it is classified ONCE per resolution (Q-32 I-U).
            Algorithm.User { IsModuleElaborated: true } or Algorithm.Alias { IsModuleElaborated: true }
                => ProcessModuleRoot(algorithm, parent, summaryMemo, observations, run),
            // A callable alias is a scope body like a user algorithm's — its own opens and
            // declarations, and its one row, the target reference it reads — so its exposure is
            // computed from that read exactly as a body whose one row names its target.
            Algorithm.User or Algorithm.Alias => ProcessScopeBody(algorithm, parent, summaryMemo, observations, run, completedContext,
                parentDistance),
            // A family reached outside any region (a host root, or a deferred branch's own
            // demand-time elaboration) opens a region of its own.
            Algorithm.Conditional conditional => ProcessConditionalAlgorithm(
                conditional,
                new ExposureWalkMemos(summaryMemo, observations, parent, run), completedContext),
            Algorithm.Builtin => algorithm,
        };

    private static Algorithm ProcessModuleRoot(
        Algorithm module,
        SummaryScope parent,
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations,
        ExposureRun run)
    {
        if (!run.Modules.TryGet(ModuleUnitPass.Exposure, module, out var classified))
        {
            classified = ProcessScopeBody(module, parent.Root, summaryMemo, observations, run);
            run.Modules.Add(ModuleUnitPass.Exposure, module, classified);
        }

        return classified;
    }

    private static Algorithm ProcessScopeBody(
        Algorithm algorithm,
        SummaryScope parent,
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations,
        ExposureRun run,
        CompletedStructureContext? completedContext = null,
        int parentDistance = 1)
    {
        FrontEndStack.Ensure();
        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is a fully-elaborated
        // leaf: no properties, no opens, and an output that is exactly its own bound Param. It
        // captures no ancestor-owned parameter, so it needs no exposure rewriting. The general
        // path would still analyze and rewrite it per helper for no observable effect.
        if (algorithm is Algorithm.User { AssignmentDeconstructionTarget: not null })
            return algorithm;

        observations?.RecordExposureAlgorithmExpansion();
        FrontEndTraversalObservations.ObserveCancellation(observations, FrontEndCancellationCheckpoint.ExposureAlgorithm, run.CancellationToken);

        // The summary channel is the ONLY builder data this pass consumes: what ancestors own
        // is not an input to it (a captured parameter is reported by name regardless), so no
        // ancestor-owned or locally-owned name context is threaded here (M17).
        var levelScope = ElaboratedScopeLookup.CreateScope(algorithm, parent.PropertyScope, completedContext: completedContext);
        // Every level is summarized and settled in its completed structural context: what escapes a level is
        // anchored there, and the settlement selects from that structure. A level without one is a broken
        // producer and is refused here, never summarized without an origin (there is no contextless mode).
        var levelContext = levelScope.CompletedContext ?? throw new InvalidOperationException(
            "Internal error: an exposure level has no completed structural context.");
        var summaryGraph = PropertyDependencyGraphBuilder.BuildSummaries(
            algorithm,
            levelContext,
            summaryMemo,
            observations);

        // This level's parameter names, materialized once per resolution and shared by every
        // fixed-point iteration's scope and the final one (FE-1).
        var parameterNames = summaryMemo.ParameterNamesOf(algorithm, observations);
        var walkMemos = PropertyDependencyGraphBuilder.CreateWalkMemos(summaryMemo, observations, levelContext);
        var summaries = new Dictionary<string, RequirementSet>(StringComparer.Ordinal);
        foreach (var property in algorithm.Properties)
            summaries[property.Name] = default;

        // The summary graph already centralizes the stable per-property seed facts:
        // direct required ancestor-owned names plus summary edges to visible names, sibling
        // properties, and pending member paths / opened names. What still changes here is each
        // property's accumulated requirement set after following those edges through the level's
        // summary map. That closure can be transitive or cyclic (mutually opening libraries
        // included), so the exposure pass solves the level's least fixed point before rewriting
        // children with the final summaries (FE-4a: dependency-driven, over canonical sets).
        var finalLevel = new SummaryScope(parent, levelScope, summaries, parameterNames, algorithm, parentDistance);
        if (algorithm.Properties.Count > 0)
            new LevelSolver(summaryGraph, finalLevel, summaries,
                    new PendingResolution(walkMemos, run.Requirements, finalLevel, run.Settlements, run.SettlementLedger,
                        run.CancellationToken), run.Requirements, observations,
                    run.CancellationToken)
                .Solve();

        // Properties and output share one lexical scope and summary context. Inline
        // open providers below have their own memo because they resolve at the prelude.
        var memos = new ExposureWalkMemos(summaryMemo, observations, finalLevel, run);
        Func<ElaboratedPropertyScope?, int> ownerDepth = finalLevel.OwnerDepth;
        // RETAINED-SIZE TRIM (implementation only): a user body WITH OUTPUT ROWS holds no empty opens or properties list of
        // its own. They are the shared zero-length arrays (immutable, as the parser's row bodies already hold), instead of
        // two list objects per body for the life of the result (8.3 MiB on a 2-MiB constant-row source). Record equality
        // is unchanged: such a body's rewritten output is a bundle of its own, which compares by reference, so it still
        // equals no other body. A body without rows (`X = {}`) and an alias (whose one row compares structurally) keep
        // their own lists, the only thing that tells two of them apart. The parameter-pattern list is not shared: it is
        // an identity input of the resolver's signature composition and bundle sharing (FE-3), so a shared empty list
        // would merge compositions and lower the ledger's charges.
        var sharesEmptyLists = algorithm is Algorithm.User { Output.Count: > 0 };
        var rewrittenProperties = algorithm.Properties.Count == 0 && sharesEmptyLists
            ? null
            : new List<Property>(algorithm.Properties.Count);
        for (var propertyIndex = 0; propertyIndex < algorithm.Properties.Count; propertyIndex++)
        {
            var property = algorithm.Properties[propertyIndex];
            // A hoisted source's rows are this level's own written rows, rewritten in their own region: what they
            // nest is wired below the source at runtime (ExposureWalkMemos.ForDeconstructionSourceRows).
            var rewrittenPropertyValue = property.Value is Algorithm.User { IsAssignmentDeconstructionSource: true } source
                ? source with { Output = RewriteExprList(source.Output, memos.ForDeconstructionSourceRows()) }
                : ProcessSharedNestedAlgorithm(property.Value, memos);

            // Equal final summaries are one canonical set, and the run materializes each distinct
            // backing once. Distinct wrappers preserve Property's list-reference equality (FE-4a).
            var summary = summaries[property.Name];
            var rewrittenProperty = new Property(property.Name, rewrittenPropertyValue, property.IsPublic, ClassifyDeclaredProperty(summary))
            {
                DeclarationSpans = property.DeclarationSpans,
                CaptureRequirements = RequiredAncestorList<CapturedParameterRequirement>.ForProperty(run.Outputs.Captures(summary, ownerDepth)),
                RequiredAncestorParameters = RequiredAncestorList<string>.ForProperty(run.Outputs.Names(summary)),
            };
            rewrittenProperties!.Add(rewrittenProperty);
        }

        IReadOnlyList<Expr> rewrittenOpens = algorithm.Opens.Count == 0 && sharesEmptyLists
            ? Array.Empty<Expr>()
            : RewriteExprList(
                algorithm.Opens,
                new ExposureWalkMemos(summaryMemo, observations, OpenTargetRegion(finalLevel, levelScope, run), run));
        var rewrittenOutput = RewriteExprList(algorithm.Output, memos);

        // The same variant back: a user's rewritten bundle, or an alias's one rewritten target row.
        return algorithm.WithOwnScopeBody(rewrittenOpens, rewrittenProperties ?? (IReadOnlyList<Property>)Array.Empty<Property>(), rewrittenOutput);
    }

    /// <summary>
    /// THE REGION AN OPEN LIST IS REWRITTEN IN. An inline open target is declared at the prelude, without the opener's
    /// declarations, so its nested algorithms are classified in a region of their own that starts at the prelude level
    /// carrying the facts that answer for a block head (<see cref="ElaboratedScopeLookup.OpenBlockHeadLevel"/>, the
    /// level open-provider validation enters the same target at), for the level <paramref name="asking"/> that writes the
    /// open. In an eagerly elaborated program that is the chain's root, and the region is <paramref name="level"/>'s
    /// root as before. In a materialized deferred unit the chain is the one recorded at the branch, whose root carries
    /// the EAGER program's facts, where the block is the placeholder's entry with no body; the region is then a
    /// prelude level over the unit's own facts, where the block is the body the unit completed, so its levels are
    /// summarized, settled and classified exactly as the same text is when nothing is deferred. A block the unit
    /// inherited completed keeps its classified view (the inherited-block arm of <see cref="RewriteExprCore"/>, which
    /// reads the same facts), and a loaded module keeps its own publication: neither depends on this region.
    /// <para>The level comes from the recorded chain's member-index cache, one per answering facts, so it is entered
    /// while that cache still takes the attempt's writes, before the deferred region takes them back and freezes the
    /// unit. One region per level and run, as the chain's root is one region: a block several open lists share is
    /// rewritten once there (<see cref="SharedExposureRegion"/>).</para>
    /// </summary>
    private static SummaryScope OpenTargetRegion(SummaryScope level, ElaboratedPropertyScope asking, ExposureRun run)
    {
        var root = level.Root;
        // Empty open lists can still need a fresh list for record identity. Rewriting one enters no block.
        if (asking.Opens.Count == 0)
            return root;
        var head = ElaboratedScopeLookup.OpenBlockHeadLevel(asking);
        if (ReferenceEquals(head, root.PropertyScope))
            return root;
        run.OpenTargetRegions ??= new(ReferenceEqualityComparer.Instance);
        if (!run.OpenTargetRegions.TryGetValue(head, out var region))
        {
            var context = head.CompletedContext;
            region = new SummaryScope(null, head, NoSummaries, context?.Facts.Facts(context.Key)?.Parameters, head.OwnerAlgorithm);
            run.OpenTargetRegions.Add(head, region);
        }
        return region;
    }

    /// <summary>
    /// Region-memoized nested-algorithm processing (property values,
    /// <see cref="Expr.AlgorithmExpr"/> contents, and conditional branch bodies share the
    /// identical region context — the region's final visible summaries). A nested USER
    /// algorithm opens its own region below; a nested FAMILY uses branch regions that retain
    /// the family's open surface and the matched binder view.
    /// </summary>
    private static Algorithm ProcessSharedNestedAlgorithm(Algorithm algorithm, ExposureWalkMemos memos, CompletedStructureContext? completedContext = null)
    {
        memos.Algorithms ??= new(ReferenceEqualityComparer.Instance);
        if (!memos.Algorithms.TryGetValue(algorithm, out var rewritten))
        {
            var region = algorithm is Algorithm.User or Algorithm.Alias && !algorithm.IsModuleRoot
                && memos.Run.SharedBodies?.Holds(algorithm) == true ? SharedExposureRegion.Of(algorithm, memos) : null;
            if (region is not null && memos.Run.SharedRegions?.TryGetValue(region, out var served) == true)
            {
                memos.Observations?.RecordExposureSharedRegionHit();
                rewritten = served;
            }
            else
            {
                rewritten = algorithm is Algorithm.Conditional conditional
                    ? ProcessConditionalAlgorithm(conditional, memos, completedContext)
                    : ProcessAlgorithm(
                        algorithm,
                        memos.Scope,
                        memos.SummaryMemo,
                        memos.Observations,
                        memos.Run, completedContext, memos.NestedDistance);
                if (region is not null)
                {
                    memos.Observations?.RecordExposureSharedRegionExpansion();
                    (memos.Run.SharedRegions ??= new())[region] = rewritten;
                }
            }

            memos.Algorithms[algorithm] = rewritten;
        }

        return rewritten;
    }

    /// <summary>
    /// The region of a shared body across parents: what its rewrite reads of the enclosing chain. Its property metadata is
    /// summaries over the body's free names and owner positions RELATIVE to the level, so a name's read is the level
    /// that declares it (the final summaries and members of one exact level), or the relative position of the level that binds
    /// it as a parameter; the depth positions what those summaries carry; and a name no direct level answers reaches the
    /// opens of the chain, exactly the nearest level with opens onward. The body's runtime distance to that level
    /// (<see cref="ExposureWalkMemos.NestedDistance"/>) shifts every capture position it records, so it is part of the region:
    /// one body held by a deconstruction right-hand side and by an ordinary row of the same level is two regions. Two contexts
    /// with equal regions rewrite the body to the same metadata, so the second holds the first's rewritten object and
    /// retargeting records it (no view of its own).
    /// </summary>
    private sealed class SharedExposureRegion : IEquatable<SharedExposureRegion>
    {
        private readonly Algorithm _body;
        private readonly int _depth;
        private readonly int _distance;
        private readonly SummaryScope? _opens;
        private readonly (object? Declaring, int Owner)[] _names;
        private readonly int _hash;

        private SharedExposureRegion(Algorithm body, int depth, int distance, SummaryScope? opens, (object?, int)[] names)
        {
            (_body, _depth, _distance, _opens, _names) = (body, depth, distance, opens, names);
            var hash = new HashCode();
            hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(body));
            hash.Add(depth);
            hash.Add(distance);
            hash.Add(opens is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(opens));
            foreach (var (declaring, owner) in names)
            {
                hash.Add(declaring is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(declaring));
                hash.Add(owner);
            }
            _hash = hash.ToHashCode();
        }

        public static SharedExposureRegion Of(Algorithm body, ExposureWalkMemos memos)
        {
            var scope = memos.Scope;
            var free = memos.Run.RegionNames.Of(body);
            var names = new (object?, int)[free.Count];
            var next = 0;
            var reachesOpens = false;
            foreach (var name in free.Names)
            {
                object? declaring = scope.TryLookup(name, out var level, out _, out _) ? level : null;
                var owner = -1;
                for (var at = scope; at is not null; at = at.Parent)
                    if (at.Parameters.Contains(name)) { owner = scope.Depth - at.Depth; break; }
                reachesOpens |= declaring is null && owner < 0;
                names[next++] = (declaring, owner);
            }

            SummaryScope? opens = null;
            if (reachesOpens)
                for (var at = scope; at is not null && opens is null; at = at.Parent)
                    if (at.PropertyScope.Opens.Count > 0) opens = at;
            return new(body, scope.Depth, memos.NestedDistance, opens, names);
        }

        public bool Equals(SharedExposureRegion? other)
        {
            if (other is null || !ReferenceEquals(_body, other._body) || _depth != other._depth || _distance != other._distance
                || !ReferenceEquals(_opens, other._opens) || _names.Length != other._names.Length) return false;
            for (var index = 0; index < _names.Length; index++)
                if (!ReferenceEquals(_names[index].Declaring, other._names[index].Declaring) || _names[index].Owner != other._names[index].Owner)
                    return false;
            return true;
        }

        public override bool Equals(object? obj) => Equals(obj as SharedExposureRegion);
        public override int GetHashCode() => _hash;
    }

    /// <summary>
    /// FE-4a: the LEAST FIXED POINT of one level's requirement equations. A property's summary is
    /// its constant own requirements (resolved once) united with the current summaries it reads —
    /// its sibling edges, and the level-local summaries its visible-name and pending-reference
    /// settlements consult. Every equation is monotone (unions of summaries; which providers settle a
    /// reference is structural, never summary-dependent), so ANY fair iteration from the empty
    /// summaries reaches the same least fixed point the former round-by-round (Jacobi) iteration
    /// reached. This one is dependency-driven: every equation is evaluated once, and later only when a
    /// summary it read has changed — so a chain of K properties costs O(K) evaluations instead of K
    /// rounds of all K, and over canonical sets an evaluation that merely inherits a sibling's summary
    /// SHARES that set instead of copying its W requirements. The map is keyed by NAME, and a name's
    /// equation is its LAST declaration's: every reader and every same-named declaration receives that
    /// summary, exactly as the former last-write-wins map did.
    ///
    /// <para>Settlements of visible names and pending references are memoized per top-level key and
    /// validated against the level-local summaries they read, so K properties reading one opened or
    /// navigated member settle it once. Across equation evaluations TOP-LEVEL settlements are
    /// cached, validated against every level-local summary they read. Inside ONE synchronous
    /// settlement, complete nested results also share their exact (reference, level, site, bound)
    /// key; that cache dies before any summary can grow. A complete nested result that read NO
    /// summary of this level is kept for the whole run instead (<see cref="SettlementShare"/>): every
    /// summary it read is final, so no growth can reach it. A nested result a cycle cut left partial
    /// is never published: within its own top-level settlement it answers later meetings of its exact
    /// key while its component is being settled, and nothing else (COMPONENT SETTLEMENTS,
    /// <c>PendingResolution</c>). Every read from a reused computation remains in the enclosing top-level
    /// recording, so dependency validation and reader notification remain complete.</para>
    ///
    /// <para>LIVE READ SETS (November 26 2026; implementation only, no classification, requirement, diagnostic or Lean
    /// rule). A top-level settlement records by name the summaries its own frames read, and by identity the canonical
    /// live-read set of each kept live settlement it reuses (<c>PendingResolution.ReplayLiveReads</c>): until then every
    /// reuse enumerated that set into the recording, each settlement copied every name with its summary, and the
    /// readers index held one entry per name and reader, so M readers taking one kept settlement of C names cost
    /// M × C three times over (the <c>liveb</c> shape at 400 × 400: 159,600 replayed names, 160,000 stored reads and
    /// 160,000 index entries). The DEPENDENCY INDEX now holds units: a name maps to the properties whose equation reads
    /// it as a sibling (static, indexed at their first evaluation), to the settlements taken by some reader that read it
    /// themselves, and to the live-read sets that hold it; a set maps to the settlements that reused it, a settlement to
    /// the readers whose LAST evaluation took it. A set is indexed under its names once, while a taken settlement holds
    /// it, whatever number of settlements and readers share it. A reader evaluated again leaves the settlements its new
    /// evaluation did not take, a settlement no reader takes leaves the index, and a set no indexed settlement holds
    /// leaves it too, so a stale membership lives no longer than its reader's next evaluation, which the change that
    /// made it stale has queued. A changed summary notifies each reader reachable from its name once, in the order of
    /// the readers' first evaluations: which summaries a settlement reads is structural, so this is exactly the reader
    /// set, the notification count and the queue order of the former index, which kept every reader by name in the
    /// order of its first read. A cached settlement stands with no test while no summary has changed since it last
    /// stood; otherwise its own reads are compared as before and each of its sets by one stamp: the change that last
    /// changed a summary the set names, which the change itself writes on every indexed set it reaches (StillValid; one
    /// test per set where the former comparison read up to every name, both uncharged).</para>
    /// </summary>
    private sealed class LevelSolver(
        PropertyDependencySummaryGraph graph,
        SummaryScope level,
        Dictionary<string, RequirementSet> summaries,
        PendingResolution resolution,
        RequirementSetInterner sets,
        FrontEndTraversalObservations? observations,
        CancellationToken cancellationToken)
    {
        private readonly RequirementSet?[] _constants = new RequirementSet?[graph.Count];
        private Dictionary<string, Settlement>? _visibleSettlements;
        private Dictionary<string, Settlement>? _pendingSettlements;

        /// <summary>
        /// One cached top-level settlement (LIVE READ SETS): its result, the level-local summaries its own frames read
        /// (name, set read), the distinct live-read sets of the kept settlements it reused, the solver's change count when
        /// it last stood, and the readers whose last evaluation took it. Identity is the reference: two settlements with
        /// equal parts are two units of the dependency index.
        /// </summary>
        private sealed class Settlement(RequirementSet result, (string Name, RequirementSet Read)[] reads,
            CanonicalNameSet[] readSets, long standsAt)
        {
            public RequirementSet Result => result;
            public (string Name, RequirementSet Read)[] Reads => reads;
            public CanonicalNameSet[] ReadSets => readSets;

            /// <summary>The solver's change count when this settlement was last known to stand (<see cref="_changes"/>).</summary>
            public long StandsAt = standsAt;

            /// <summary>The evaluation that last took it (<see cref="_evaluation"/>).</summary>
            public int TakenAt;

            // The properties whose last evaluation took this settlement; it is indexed while there are any. Most settlements
            // have one reader (their key holds the reader's origin), kept in place until a second one joins.
            private int _soleReader = -1;
            private HashSet<int>? _readers;

            public int ReaderCount => _readers?.Count ?? (_soleReader >= 0 ? 1 : 0);

            /// <summary>The readers when there may be more than one; null while <see cref="SoleReader"/> is the only one.</summary>
            public HashSet<int>? Readers => _readers;

            /// <summary>The one reader while <see cref="Readers"/> is null (-1 for none).</summary>
            public int SoleReader => _soleReader;

            public bool AddReader(int reader)
            {
                if (_readers is not null)
                    return _readers.Add(reader);
                if (_soleReader < 0)
                {
                    _soleReader = reader;
                    return true;
                }

                if (_soleReader == reader)
                    return false;
                _readers = [_soleReader, reader];
                _soleReader = -1;
                return true;
            }

            public bool RemoveReader(int reader)
            {
                if (_readers is not null)
                    return _readers.Remove(reader);
                if (_soleReader != reader)
                    return false;
                _soleReader = -1;
                return true;
            }
        }

        // Everything the dependency index holds under one name (LIVE READ SETS).
        private sealed class NameDependents
        {
            public HashSet<int>? Siblings;
            public HashSet<Settlement>? Settlements;
            public HashSet<ReadSet>? Sets;

            public bool IsEmpty => Siblings is null && Settlements is not { Count: > 0 } && Sets is not { Count: > 0 };
        }

        // One live-read set in the dependency index (keyed by its canonical set): the indexed settlements that hold it, and
        // the solver's change count at the last change of a summary it names since it was indexed (0 before any).
        private sealed class ReadSet
        {
            public readonly HashSet<Settlement> Settlements = [];
            public long ChangedAt;
        }

        private Dictionary<string, NameDependents>? _dependents;
        private Dictionary<CanonicalNameSet, ReadSet>? _readSets;
        private List<Settlement>? _taking;
        private object?[]? _taken;
        private int _evaluation;
        private long _changes;
        private long _entries;

        public void Solve()
        {
            var properties = graph.Properties;
            var equationOf = resolution.IndexEquations(properties);

            // Statically read equations: sibling edges, and level-local names a reference reads directly.
            IEnumerable<int> StaticReads(int index)
            {
                var node = graph[index];
                foreach (var dependencyIndex in node.SummarySiblingDependencyIndices)
                    yield return equationOf[properties[dependencyIndex].Name].Index;
                foreach (var name in node.SummaryVisiblePropertyDependencyNames)
                    if (equationOf.TryGetValue(name, out var read))
                        yield return read.Index;
                foreach (var (_, pending) in node.ReferenceInputs)
                    if (pending.Selection == PendingSelection.Lexical && equationOf.TryGetValue(pending.Head, out var read))
                        yield return read.Index;
            }

            var queue = new Queue<int>();
            var queued = new bool[properties.Count];
            // Each property is first evaluated at its place in this order, before any is evaluated again: a reader's rank
            // is the order of its first evaluation, the order the former index kept a name's readers in.
            var rank = new int[properties.Count];
            var count = 0;
            foreach (var index in DependencyFirstOrder.Of(properties.Count, i => equationOf[properties[i].Name].Index == i, StaticReads))
            {
                queue.Enqueue(index);
                queued[index] = true;
                rank[index] = count++;
            }

            int[]? notifiedAt = null;
            var change = 0;
            List<int>? woken = null;
            Comparison<int>? byRank = null;
            while (queue.TryDequeue(out var index))
            {
                queued[index] = false;
                observations?.RecordRequiredAncestorLevelEvaluation();
                FrontEndTraversalObservations.ObserveCancellation(
                    observations, FrontEndCancellationCheckpoint.ExposureLevelEvaluation, cancellationToken);
                _taking?.Clear();
                var next = Evaluate(index);
                Take(index);

                var name = properties[index].Name;
                if (next.Equals(summaries[name]))
                    continue;

                summaries[name] = next;
                _changes++;
                resolution.NoteSummaryChanged(name, index);
                if (_dependents is null || !_dependents.TryGetValue(name, out var dependents))
                    continue;

                // Every indexed set that names it changes now (StillValid).
                if (dependents.Sets is { } changedSets)
                    foreach (var set in changedSets)
                        set.ChangedAt = _changes;

                // Sibling readers alone are each held once, in the order of their first evaluations (rank order).
                if (dependents.Settlements is not { Count: > 0 } && dependents.Sets is not { Count: > 0 })
                {
                    foreach (var dependent in dependents.Siblings!)
                        Notify(dependent);
                    continue;
                }

                // Each reader reachable from the name once, in rank order.
                change++;
                notifiedAt ??= new int[properties.Count];
                (woken ??= []).Clear();
                if (dependents.Siblings is { } siblings)
                    foreach (var reader in siblings)
                        Wake(reader);
                if (dependents.Settlements is { } settlements)
                    foreach (var settlement in settlements)
                        WakeReaders(settlement);
                if (dependents.Sets is { } sets)
                    foreach (var set in sets)
                        foreach (var settlement in set.Settlements)
                            WakeReaders(settlement);
                for (var i = 1; i < woken.Count; i++)
                {
                    if (rank[woken[i - 1]] <= rank[woken[i]])
                        continue;
                    woken.Sort(byRank ??= (a, b) => rank[a] - rank[b]);
                    break;
                }

                foreach (var dependent in woken)
                    Notify(dependent);
            }

            void Notify(int dependent)
            {
                observations?.RecordRequiredAncestorReaderNotification();
                if (!queued[dependent])
                {
                    queued[dependent] = true;
                    queue.Enqueue(dependent);
                }
            }

            void Wake(int reader)
            {
                if (notifiedAt![reader] == change)
                    return;
                notifiedAt[reader] = change;
                woken!.Add(reader);
            }

            void WakeReaders(Settlement settlement)
            {
                if (settlement.Readers is { } readers)
                    foreach (var reader in readers)
                        Wake(reader);
                else
                    Wake(settlement.SoleReader);
            }
        }

        // The settlements one evaluation of `reader` took (_taking, each one that read a summary of the level) become its
        // dependency units: it joins the ones it did not hold and leaves the ones its previous evaluation took and this one
        // did not (LIVE READ SETS).
        private void Take(int reader)
        {
            var evaluation = ++_evaluation;
            // No settlement of this solve has read a summary of the level yet: no reader holds a unit.
            if (_taking is null)
                return;
            var took = 0;
            for (var t = 0; t < _taking.Count; t++)
            {
                var settlement = _taking[t];
                if (settlement.TakenAt == evaluation)
                    continue;
                settlement.TakenAt = evaluation;
                _taking[took++] = settlement;
                if (!settlement.AddReader(reader))
                    continue;
                Created(1);
                if (settlement.ReaderCount == 1)
                    IndexSettlement(settlement);
            }

            _taking.RemoveRange(took, _taking.Count - took);
            if (took == 0 && _taken is null)
                return;
            // What each property's last evaluation took, once any took a settlement with dependencies: nothing, its one
            // settlement, or an array of several.
            var taken = _taken ??= new object?[graph.Count];
            var same = false;
            switch (taken[reader])
            {
                case Settlement one:
                    Leave(one);
                    break;
                case Settlement[] several:
                    same = several.Length == took;
                    for (var i = 0; i < several.Length; i++)
                    {
                        same = same && ReferenceEquals(several[i], _taking[i]);
                        Leave(several[i]);
                    }

                    break;
            }

            if (!same)
                taken[reader] = took switch { 0 => null, 1 => _taking[0], _ => _taking.ToArray() };

            // The reader leaves a settlement its previous evaluation took and this one did not.
            void Leave(Settlement settlement)
            {
                if (settlement.TakenAt == evaluation || !settlement.RemoveReader(reader))
                    return;
                Retired(1);
                if (settlement.ReaderCount == 0)
                    UnindexSettlement(settlement);
            }
        }

        private void IndexSettlement(Settlement settlement)
        {
            var reads = settlement.Reads;
            for (var i = 0; i < reads.Length; i++)
            {
                CheckCancellation(i);
                (Dependents(reads[i].Name).Settlements ??= []).Add(settlement);
                Created(1);
            }

            foreach (var names in settlement.ReadSets)
            {
                var readSets = _readSets ??= [];
                if (!readSets.TryGetValue(names, out var set))
                {
                    readSets.Add(names, set = new ReadSet());
                    var i = 0;
                    foreach (var name in names.WalkNames())
                    {
                        if ((i++ & 255) == 0)
                            FrontEndTraversalObservations.ObserveCancellation(observations,
                                FrontEndCancellationCheckpoint.ExposureReadSetRegistration, cancellationToken);
                        (Dependents(name).Sets ??= []).Add(set);
                        Created(1);
                    }
                }

                set.Settlements.Add(settlement);
                Created(1);
            }
        }

        private void UnindexSettlement(Settlement settlement)
        {
            var reads = settlement.Reads;
            for (var i = 0; i < reads.Length; i++)
            {
                CheckCancellation(i);
                var dependents = _dependents![reads[i].Name];
                if (dependents.Settlements!.Remove(settlement))
                    Retired(1);
                Release(reads[i].Name, dependents);
            }

            foreach (var names in settlement.ReadSets)
            {
                var set = _readSets![names];
                if (set.Settlements.Remove(settlement))
                    Retired(1);
                if (set.Settlements.Count > 0)
                    continue;
                _readSets.Remove(names);
                var i = 0;
                foreach (var name in names.WalkNames())
                {
                    CheckCancellation(i++);
                    var dependents = _dependents![name];
                    if (dependents.Sets!.Remove(set))
                        Retired(1);
                    Release(name, dependents);
                }
            }
        }

        private NameDependents Dependents(string name)
        {
            var all = _dependents ??= new(StringComparer.Ordinal);
            if (!all.TryGetValue(name, out var dependents))
                all.Add(name, dependents = new NameDependents());
            return dependents;
        }

        private void Release(string name, NameDependents dependents)
        {
            if (dependents.IsEmpty)
                _dependents!.Remove(name);
        }

        private void Created(long entries)
        {
            _entries += entries;
            observations?.RecordRequiredAncestorDependencyEntries(entries, _entries);
        }

        private void Retired(long entries)
        {
            _entries -= entries;
            observations?.RecordRequiredAncestorDependencyRetirements(entries);
        }

        private void CheckCancellation(int index)
        {
            if ((index & 255) == 0)
                cancellationToken.ThrowIfCancellationRequested();
        }

        private RequirementSet Evaluate(int propertyIndex)
        {
            var node = graph[propertyIndex];
            var requirements = _constants[propertyIndex] ??= sets.From(
                level.ResolveRequirements(node.RequiredAncestorOwnedParameterNames)
                    .Concat(level.ResolveRequirements(node.OwnerQualifiedParameters)));

            // A bare visible name is settled by the ONE settlement the pending references use
            // (the chain's own properties first, then the owning level's and its ancestors'
            // opens, in the evaluator's order): a name the property reads through an `open`
            // declared at THIS level — or at an ancestor level — charges the provided member's
            // requirements exactly like a dotted path or an open written inside the value.
            // Dropping such a name classified `Y = X` as Exported beside a local-only opened `X`,
            // so the run-scoped cache handed the first activation's value to every later one.
            foreach (var dependencyName in node.SummaryVisiblePropertyDependencyNames)
                requirements = sets.Union(requirements, Settle(dependencyName, pending: null));

            // Sibling reads are the summary graph's static edges, the same at every evaluation: indexed by the first.
            foreach (var dependencyIndex in node.SummarySiblingDependencyIndices)
            {
                var dependencyName = graph.Properties[dependencyIndex].Name;
                if (summaries.TryGetValue(dependencyName, out var summary))
                {
                    if ((Dependents(dependencyName).Siblings ??= []).Add(propertyIndex))
                        Created(1);
                    requirements = sets.Union(requirements, summary);
                }
            }

            foreach (var (key, pending) in node.ReferenceInputs)
                requirements = sets.Union(requirements, Settle(key, pending));

            return requirements;
        }

        private RequirementSet Settle(string key, PendingReference? pending)
        {
            var settlements = pending is null
                ? _visibleSettlements ??= new(StringComparer.Ordinal)
                : _pendingSettlements ??= new(StringComparer.Ordinal);
            if (!settlements.TryGetValue(key, out var settlement) || !StillValid(settlement))
            {
                observations?.RecordRequiredAncestorResolutionComputation();
                var levelReads = resolution.BeginRecording();
                var result = pending is null
                    ? resolution.ResolveVisibleName(key, level)
                    : resolution.Resolve(pending, level);
                var readSets = resolution.EndRecording();
                (string Name, RequirementSet Read)[] read = levelReads.Count == 0
                    ? []
                    : new (string Name, RequirementSet Read)[levelReads.Count];
                var i = 0;
                foreach (var readName in levelReads)
                    read[i++] = (readName, summaries[readName]);
                observations?.RecordRequiredAncestorSettlementReads(read.Length, readSets.Length);
                settlements[key] = settlement = new Settlement(result, read, readSets, _changes);
            }

            // A settlement that read no summary of the level depends on none and is no unit of the dependency index.
            if (settlement.Reads.Length > 0 || settlement.ReadSets.Length > 0)
                (_taking ??= []).Add(settlement);
            return settlement.Result;
        }

        // Whether every summary the settlement read is still the current one: with no test while no summary has changed
        // since it last stood, otherwise its own reads compared and each live-read set tested by its last change (LIVE
        // READ SETS). A cached settlement is indexed: the reader that last settled its key took it, and a reader leaves it
        // only by taking another settlement of that key, which replaces it here. So each set it holds has been indexed, and
        // stamped at every change of a summary it names, since before the settlement last stood; a set indexed anew starts
        // at 0, because every settlement holding it then was settled after its last change. Summaries only grow, so a
        // changed one never equals what was read again: the stamp test is the comparison of every name it replaces.
        private bool StillValid(Settlement settlement)
        {
            if (settlement.StandsAt == _changes)
                return true;
            foreach (var (readName, read) in settlement.Reads)
            {
                if (!summaries[readName].Equals(read))
                    return false;
            }

            foreach (var names in settlement.ReadSets)
            {
                if (_readSets is null || !_readSets.TryGetValue(names, out var set))
                    throw new InvalidOperationException("A cached settlement that holds a live-read set is indexed.");
                observations?.RecordRequiredAncestorReadSetCheck(resolution.LiveNamesSaturated);
                if (set.ChangedAt > settlement.StandsAt)
                    return false;
            }

            settlement.StandsAt = _changes;
            return true;
        }
    }

    /// <summary>
    /// Completed nested settlements of ONE exposure run, shared across its top-level settlements and
    /// levels. A chain of N members opened from one another is settled from every link's level, and
    /// each of those settlements walks the links below it: N(N + 3) frames without the share, a
    /// constant number per link with it. Implementation only: every summary is the one the unshared
    /// settlement computes.
    ///
    /// <para>WHAT IS KEPT. A nested settlement whose WHOLE computation — its nested frames and every
    /// result it reused included — saw no cycle cut, read no summary of the level in progress, and
    /// resolved nothing that depends on its site (<see cref="Settled.StandsFromEverySite"/>). A level
    /// is solved before any level below it is processed, and which summaries a settlement reads is
    /// structural, never summary-dependent, so such a computation read only FINAL summaries; without
    /// a cut it is the complete union over everything its reference reaches. It is therefore a
    /// function of its key and of the completed-fact views it consulted, which are kept with it at
    /// the versions it read: a lookup answers only while each one stands
    /// (<see cref="StaticLookupFacts.ViewVersion"/>, the anchor cache's rule) and drops the entry
    /// otherwise.</para>
    ///
    /// <para>THE KEY is the settlement's own without its SITE: reference content or seed, level,
    /// bound owners. The site is the level a settlement resolves owner-qualified parameters from
    /// (<see cref="SummaryScope.ResolveRequirementsFromSite"/>); it lies at or below the settlement's
    /// level, on a chain through that level. When every such lookup landed at or above the level,
    /// every site below the level resolves it to the same scope (an owner on the level's chain cannot
    /// also be nested below the level: bodies are acyclic), so one entry answers them all. A
    /// settlement with a lookup that landed below its level, or found no owner (another site could
    /// hold it), depends on its site and is never kept. Keys hold identities — levels, seeds, the
    /// origin and owner ids inside a content key, and the bound owners themselves
    /// (<see cref="BoundOwnerSet"/>, equal by content) — never a spelling alone, so owners with
    /// same-named parameters stay apart.</para>
    ///
    /// <para>THE FOOTPRINT: WHICH BOUND OWNERS A SETTLEMENT DEPENDS ON. A settlement reads its bound
    /// owners in two ways only (<see cref="ISettlementReader"/>): one MEMBERSHIP at a time — a
    /// requirement's owner (<c>SummaryScope.TryResolveRequirement</c>), a parameter head's owner, and
    /// the level algorithms the open-walks route tests (<c>PendingResolution.SharedOpenWalksLevel</c>) —
    /// and, on that route only, whether there are none at all. A frame records every membership it
    /// read with its answer, present or absent, relative to its own bound owners, and the emptiness
    /// read; a nested frame's reads reach its parent except a membership of an owner the nested
    /// reference binds itself (present under any parent) and the emptiness read of a frame that binds
    /// any (never empty under any parent); a reused result brings its own record; the level's one
    /// unbound open-walks settlement (C1) is computed with no bound owners, so it reads none of its
    /// reader's. The record of a whole settlement, kept with it, is its <see cref="Settled.Footprint"/>.
    /// Every decision of a settlement — what a requirement charges, where its lookup lands, which route
    /// a reference takes, which frames it opens — is a function of its key's other parts, the final
    /// summaries and views it read, and those answers. Under bound owners that give the same answers
    /// it therefore makes the same decisions in every frame it reaches, transitively, and its frames
    /// correspond one to one with the same contributions (their bound owners extend the new ones by the
    /// same references' own owners); an owner it never read takes part in no decision, so it cannot
    /// expose a different dependency. Where a frame meets a key in progress (a cycle cut) may differ
    /// under other owners, because bound-owner sets of two frames may become equal or unequal; it
    /// changes no whole result, which is everything its reference reaches however its repeats are cut
    /// (EXPOSURE-OPEN-1), and partial results are never kept here (a component keeps its own for their exact
    /// keys while it is being settled, and its closing settlement's record covers every member:
    /// <c>PendingResolution</c>, COMPONENT SETTLEMENTS). So a kept settlement answers any key of
    /// its content and level whose bound owners satisfy its footprint — by exact membership tests,
    /// never a fingerprint — under the site, live-read and view rules above, which are unchanged. A
    /// settlement that read more than <see cref="MaxFootprint"/> memberships, or reused such a result,
    /// records no footprint and is kept for its exact bound owners only, as before; so is one whose
    /// content and level already hold <see cref="MaxCandidates"/> footprint candidates. So is, finally,
    /// one with an owner lookup that found no owner on its site's chain, or that reused such a result
    /// (<see cref="Settled.OwnerOffChain"/>): such a lookup charges nothing there (Q1) and raises no
    /// landing, so its settlement is kept as site-independent although another site below its level
    /// can hold that owner and charge it. Its exact key keeps that former behavior; footprints do not
    /// extend it to other bound owners.</para>
    ///
    /// <para>LIFETIME AND SIZE. One share belongs to one resolution (<see cref="ExposureRun"/>),
    /// whose interner its results are sets of, and dies with it. Only completed settlements are
    /// stored, so a cancelled or failed resolution leaves nothing partial behind. What it retains is
    /// bounded (<see cref="DefaultCapacity"/>): a program whose settlements never repeat a key would
    /// otherwise retain one entry per frame, where the unshared settlement retained none. Past the
    /// bound nothing more is kept; lookups still answer, and no result depends on a hit.</para>
    /// </summary>
    internal sealed class SettlementShare(FrontEndTraversalObservations? observations, long capacity = SettlementShare.DefaultCapacity)
    {
        /// <summary>
        /// The retained weight the share stops storing at. A chain the share serves keeps a constant number
        /// of small entries per link. Each entry charges its key, every fact-view record and every footprint
        /// membership it retains.
        /// </summary>
        internal const long DefaultCapacity = 1 << 19;

        /// <summary>
        /// The most bound-owner memberships a settlement's footprint records: one that reads more is answered
        /// for its exact bound owners only, so recording, merging and comparing a footprint costs a constant.
        /// </summary>
        internal const int MaxFootprint = 16;

        /// <summary>
        /// The most footprint candidates one content and level keep: a lookup compares at most this many
        /// footprints. A further settlement of them is kept for its exact bound owners.
        /// </summary>
        internal const int MaxCandidates = 8;

        /// <summary>
        /// <see cref="Content"/> is a pending reference's content key or a seed; <see cref="ContentLength"/> is the length
        /// the share charges for the content's text (<see cref="Weight"/>), a function of the content.
        /// </summary>
        internal readonly record struct Key(object Content, SummaryScope Level, BoundOwnerSet? Bound, long ContentLength)
        {
            /// <summary>A reference's key: its content key, charged at <see cref="SummaryReference.StableContentKeyLength"/>.</summary>
            public Key(PendingReference Content, SummaryScope Level, BoundOwnerSet? Bound)
                : this(Content.ContentKey, Level, Bound, Content.StableContentKeyLength) { }

            /// <summary>A seed's key: the seed itself, which holds no key text.</summary>
            public Key(PropertyDependencyGraphBuilder.SummarySeed Content, SummaryScope Level, BoundOwnerSet? Bound)
                : this(Content, Level, Bound, 0) { }

            /// <summary>
            /// One unit per entry, plus one per 64 characters of the content's key text — every process-wide id in it
            /// counted at its widest (<see cref="SummaryReference.StableIdWidth"/> digits,
            /// <see cref="SummaryReference.StableContentKeyLength"/>), so never less than the text the key retains — and of
            /// the bound owners' structural charge (<see cref="BoundOwnerSet.StableKeyLength"/>: one per owner and
            /// separator). Equal content weighs the same in every process: until November 20 2026 both counted the ids'
            /// decimal digits, so a program near the bound was admitted differently, and settled in other frames, after
            /// the process had issued more ids for unrelated work.
            /// </summary>
            internal long Weight => 1 + (ContentLength + (Bound?.StableKeyLength ?? 0)) / 64;
        }

        /// <summary>
        /// A completed settlement and what its computation depended on beyond its key: the deepest landing
        /// of its site lookups (<see cref="SummaryScope.NoOwnerLookup"/> when it made none), whether it read
        /// a summary of the level in progress (and which, <see cref="LiveReads"/>), the fact views it consulted
        /// with the versions it read (<see cref="InconsistentViews"/>: it saw one view at two versions), and what
        /// it read of its bound owners (<see cref="Footprint"/>, <see cref="Emptiness"/>).
        /// </summary>
        internal sealed class Settled(RequirementSet result, int siteDepth, bool readLive,
            (StaticLookupFacts Facts, int Version)[] views, bool inconsistentViews,
            (Algorithm Owner, bool Present)[]? footprint = null, BoundOwnerEmptiness emptiness = BoundOwnerEmptiness.Unread,
            bool ownerOffChain = false, CanonicalNameSet liveReads = default)
        {
            public RequirementSet Result => result;
            public int SiteDepth => siteDepth;
            public bool ReadLive => readLive;
            public (StaticLookupFacts Facts, int Version)[] Views => views;
            public bool InconsistentViews => inconsistentViews;

            /// <summary>
            /// The summaries of the level in progress the computation read, each name once (empty when it read none): a
            /// canonical set of its resolution's live-read interner (<c>PendingResolution</c>), so a frame takes a nested
            /// frame's or a reused result's set by the part the two do not share, whatever its width. A result that read
            /// a live summary is kept beyond its run only for the rest of its level's solve (<c>PendingResolution</c>'s
            /// unbound open walks and LIVE SETTLEMENTS), while each summary in this set stands, and only when
            /// <see cref="LiveReadsKnown"/>.
            /// </summary>
            public CanonicalNameSet LiveReads => liveReads;

            /// <summary>
            /// Whether <see cref="LiveReads"/> names every live summary the computation read: false when it read one and
            /// names none, because its resolution's live-read interner was past its capacity (<c>PendingResolution</c>,
            /// LIVE READS). Such a result is reused only inside its Run, never kept beyond it.
            /// </summary>
            public bool LiveReadsKnown => !readLive || liveReads.Count > 0;

            /// <summary>
            /// Whether this result, when its computation also saw no cycle cut, is the settlement of its key at
            /// <paramref name="level"/> from every site while the summaries of the level in progress it read stand: it
            /// saw no view at two versions, and no site lookup landed below <paramref name="level"/>.
            /// <see cref="StandsFromEverySite"/> adds that it read no such summary.
            /// </summary>
            public bool AnswersEverySite(SummaryScope level)
                => !inconsistentViews && siteDepth <= level.Depth;

            /// <summary>
            /// Every bound-owner membership the computation read, with its answer for the bound owners it ran
            /// under, each owner once (see the class summary); null when that is unknown — it read more than
            /// <see cref="MaxFootprint"/> memberships or reused a result without a footprint, or the settlement was
            /// built without one — and the result answers its exact bound owners only.
            /// </summary>
            public (Algorithm Owner, bool Present)[]? Footprint => footprint;

            /// <summary>Whether the computation read that its bound owners are none, and the answer.</summary>
            public BoundOwnerEmptiness Emptiness => emptiness;

            /// <summary>
            /// An owner lookup of the computation found no owner on its site's chain (see the class summary): the share
            /// keeps the result for its exact bound owners only. Its footprint is still what a settlement that reuses it
            /// read.
            /// </summary>
            public bool OwnerOffChain => ownerOffChain;

            /// <summary>
            /// Whether this result, when its computation also saw no cycle cut, is the settlement of its key at
            /// <paramref name="level"/> from every site for the rest of the run while its views stand.
            /// </summary>
            public bool StandsFromEverySite(SummaryScope level)
                => !readLive && AnswersEverySite(level);

            /// <summary>
            /// Whether <paramref name="bound"/> gives every read of <see cref="Footprint"/> and
            /// <see cref="Emptiness"/> the answer this computation had: exact membership by reference.
            /// </summary>
            internal bool Satisfies(BoundOwnerSet? bound, FrontEndTraversalObservations? observations)
            {
                if (footprint is null)
                    throw new InvalidOperationException("A settlement without a footprint answers its exact bound owners only.");
                if (emptiness != BoundOwnerEmptiness.Unread && (bound is null) != (emptiness == BoundOwnerEmptiness.ReadNone))
                    return false;
                for (var i = 0; i < footprint.Length; i++)
                {
                    observations?.RecordSettlementFootprintWork(1);
                    if ((bound?.Contains(footprint[i].Owner) == true) != footprint[i].Present)
                        return false;
                }

                return true;
            }

            /// <summary>Whether every view this computation consulted is still at the version it read.</summary>
            internal bool ViewsStand()
            {
                foreach (var (facts, version) in views)
                    if (facts.ViewVersion != version)
                        return false;
                return true;
            }
        }

        // Settlements answered for their exact bound owners: no footprint, or no room among their candidates.
        private readonly Dictionary<Key, Settled> _entries = [];

        // Settlements answered by footprint, per content and level, with each one's retained weight.
        private readonly Dictionary<(object Content, SummaryScope Level), List<(Settled Settled, long Weight)>> _candidates = [];
        private readonly SettlementShareMode _mode = SettlementShareModeForTesting.Value;
        internal bool KeepsSettlements => _mode != SettlementShareMode.Unshared;
        private long _retained;
        // The existing site-free exact cache can depend on the order in which off-chain
        // owner lookups were settled. Keep that order once a resolution has made one.
        internal bool SawOffChainLookup { get; set; }

        /// <summary>
        /// C1: per open level and facts view, the keys its walks' anchoring passes below the level's chain
        /// (<c>PendingResolution.OpenWalkAnchorsBelow</c>). Static facts only, so never partial.
        /// </summary>
        internal Dictionary<(StaticLookupFacts Facts, int Version, SummaryScope Opening), HashSet<StaticScopeKey>> OpenWalkAnchors { get; } = [];

        /// <summary>
        /// Q2: per crossed reference (its opened terminal) and facts view, the members its open crossing selects
        /// (<c>PendingResolution.ChargeOpenCrossing</c>), in selection order, with the views they were read from.
        /// Completed facts only, so never partial; an entry is recomputed once one of its views has moved on.
        /// </summary>
        internal Dictionary<(StaticLookupFacts Facts, int Version, StaticScopeKey Terminal), OpenCrossing> OpenCrossings { get; } = [];

        /// <summary>
        /// SEED PARTS (implementation only; <c>PendingResolution.ResolveSeed</c>, <c>AnchorPublishedSeed</c>): the
        /// canonical requirement set of a completed seed part that holds required names only, with everything it holds by
        /// reference, resolved at a level — a function of the part's content and the level's static chain, so it is kept for
        /// the whole resolution and is a set of its interner. Built once per part and level from the part's own names and
        /// its parts' sets, it lets a navigated member whose seed holds its predecessors by reference be settled without
        /// copying their width.
        /// </summary>
        internal Dictionary<(PropertyDependencyGraphBuilder.SummarySeed Part, SummaryScope Level), RequirementSet> SeedPartRequirements
            => _seedPartRequirements ??= [];

        /// <summary>Per completed seed part: whether it and every part it holds hold required names only.</summary>
        internal Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool> RequiredNameParts
            => _requiredNameParts ??= new(ReferenceEqualityComparer.Instance);

        /// <summary>Per completed seed part: whether it and every part it holds hold no visible name and no pending reference.</summary>
        internal Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool> NameAndReferenceFreeParts
            => _nameAndReferenceFreeParts ??= new(ReferenceEqualityComparer.Instance);

        /// <summary>
        /// QUALIFIED SEED PARTS (<c>PendingResolution.AnchorPublishedSeed</c>): per completed seed part that holds no
        /// visible name and no pending reference, and per intervening owner with the parameter set its level binds, the
        /// part as the expansion at that level makes it (<see cref="PropertyDependencyGraphBuilder.SummarySeed.QualifiedOwnSets"/>;
        /// the part itself when the level binds none of its names). Its retained weight is <see cref="QualifiedPartWeight"/>.
        /// </summary>
        internal Dictionary<(PropertyDependencyGraphBuilder.SummarySeed Part, Algorithm Owner, IReadOnlySet<string> Parameters),
            PropertyDependencyGraphBuilder.SummarySeed> QualifiedParts => _qualifiedParts ??= new(QualifiedPartKeyComparer.Instance);

        /// <summary>One unit per entry, own requirement and child reference retained by a new qualified copy.</summary>
        internal long QualifiedPartWeight { get; set; }

        /// <summary>
        /// QUALIFIED SEED PARTS (<c>PendingResolution.ResolveSeed</c>): per completed seed part that holds no visible name and
        /// no pending reference, the distinct owners of the owner-qualified requirements it and every part it holds carry,
        /// in the order first met; null when one of them has no owner or there are more than <see cref="MaxFootprint"/>.
        /// </summary>
        internal Dictionary<PropertyDependencyGraphBuilder.SummarySeed, Algorithm[]?> PartOwners
            => _partOwners ??= new(ReferenceEqualityComparer.Instance);

        /// <summary>
        /// QUALIFIED SEED PARTS: per completed seed part and a level of a site's chain, the canonical set of the requirements
        /// the part and every part it holds qualify with that level's algorithm, each at the scope that binds it there
        /// (<see cref="SummaryScope.BindingScope"/>) — a function of the part's content and the level's static chain, so it
        /// is kept for the whole resolution.
        /// </summary>
        internal Dictionary<(PropertyDependencyGraphBuilder.SummarySeed Part, SummaryScope OwnerLevel), RequirementSet> QualifiedPartRequirements
            => _qualifiedPartRequirements ??= [];

        /// <summary>
        /// PATH PARTS (<c>PendingResolution.ResolveSeed</c>): per completed seed part, whether no pending reference it or any
        /// part it holds carries binds an owner of its own, so folding them never narrows a reference.
        /// </summary>
        internal Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool> UnboundReferenceParts
            => _unboundReferenceParts ??= new(ReferenceEqualityComparer.Instance);

        /// <summary>PATH PARTS: per completed seed part, whether it and every part it holds hold no pending reference.</summary>
        internal Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool> ReferenceFreeParts
            => _referenceFreeParts ??= new(ReferenceEqualityComparer.Instance);

        /// <summary>
        /// PATH PARTS (<c>PendingResolution.AnchorPublishedSeed</c>): per completed seed part, whether it and every part it
        /// holds hold no visible name and only pending references every level expansion keeps as they are.
        /// </summary>
        internal Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool> ExpansionStableParts
            => _expansionStableParts ??= new(ReferenceEqualityComparer.Instance);

        /// <summary>
        /// PATH PARTS: the whole settlement of a seed — a part settled on its own, or a seed settled part by part — at a
        /// level, from an EXACT site, under exact bound owners, with the record of what it read
        /// (<see cref="Settled"/>). Kept for the resolution only when it read no summary of a level in progress and made no
        /// owner lookup off its site's chain, and while the resolution has made none; served while its views stand.
        /// Its retained weight is <see cref="PathPartWeight"/>.
        /// </summary>
        internal Dictionary<PathPartKey, Settled> PathParts => _pathParts ??= [];

        /// <summary>Total retained weight of the exact path-part keys, fact views and footprint memberships.</summary>
        internal long PathPartWeight { get; set; }

        /// <summary>A path-part settlement's key: the seed and both scopes by reference, the bound owners by content.</summary>
        internal readonly record struct PathPartKey(PropertyDependencyGraphBuilder.SummarySeed Part, SummaryScope Level,
            SummaryScope Site, BoundOwnerSet? Bound)
        {
            internal Key SeedKey => new(Part, Level, Bound);
            internal long RetainedWeight(Settled settled) => SettlementShare.RetainedWeight(SeedKey, settled);
        }

        private Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool>? _unboundReferenceParts;
        private Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool>? _referenceFreeParts;
        private Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool>? _expansionStableParts;
        private Dictionary<PathPartKey, Settled>? _pathParts;

        // Created when first used: most shares (a component discovery's above all) never settle a seed with parts.
        private Dictionary<(PropertyDependencyGraphBuilder.SummarySeed Part, SummaryScope Level), RequirementSet>? _seedPartRequirements;
        private Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool>? _requiredNameParts;
        private Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool>? _nameAndReferenceFreeParts;
        private Dictionary<(PropertyDependencyGraphBuilder.SummarySeed Part, Algorithm Owner, IReadOnlySet<string> Parameters),
            PropertyDependencyGraphBuilder.SummarySeed>? _qualifiedParts;
        private Dictionary<PropertyDependencyGraphBuilder.SummarySeed, Algorithm[]?>? _partOwners;
        private Dictionary<(PropertyDependencyGraphBuilder.SummarySeed Part, SummaryScope OwnerLevel), RequirementSet>? _qualifiedPartRequirements;

        // A qualified part's key by identity: the part, the owner algorithm (a record, whose generated equality compares
        // content) and the parameter set object its level reads.
        private sealed class QualifiedPartKeyComparer
            : IEqualityComparer<(PropertyDependencyGraphBuilder.SummarySeed Part, Algorithm Owner, IReadOnlySet<string> Parameters)>
        {
            public static readonly QualifiedPartKeyComparer Instance = new();

            public bool Equals((PropertyDependencyGraphBuilder.SummarySeed Part, Algorithm Owner, IReadOnlySet<string> Parameters) x,
                (PropertyDependencyGraphBuilder.SummarySeed Part, Algorithm Owner, IReadOnlySet<string> Parameters) y)
                => ReferenceEquals(x.Part, y.Part) && ReferenceEquals(x.Owner, y.Owner) && ReferenceEquals(x.Parameters, y.Parameters);

            public int GetHashCode((PropertyDependencyGraphBuilder.SummarySeed Part, Algorithm Owner, IReadOnlySet<string> Parameters) key)
                => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Part),
                    System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Owner),
                    System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Parameters));
        }

        /// <summary>The members one open crossing selects: each by the view, owner and name it is charged with.</summary>
        internal sealed class OpenCrossing((StaticLookupFacts Facts, StaticScopeKey Owner, string Name)[] selections,
            (StaticLookupFacts Facts, int Version)[] views)
        {
            public (StaticLookupFacts Facts, StaticScopeKey Owner, string Name)[] Selections => selections;
            public (StaticLookupFacts Facts, int Version)[] Views => views;

            public bool Stands()
            {
                foreach (var (facts, version) in views)
                    if (facts.ViewVersion != version) return false;
                return true;
            }
        }

        /// <summary>
        /// The settlement kept for <paramref name="key"/>, while every view it consulted stands: the one kept for its
        /// exact bound owners, or else the first candidate of its content and level whose footprint its bound owners
        /// satisfy. A stale entry met is dropped, and the key is then computed again.
        /// </summary>
        public bool TryGet(Key key, [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out Settled? settled)
        {
            if (!KeepsSettlements)
            {
                settled = null;
                return false;
            }

            if (_entries.TryGetValue(key, out settled))
            {
                if (!settled.ViewsStand())
                {
                    observations?.RecordSettlementShareStaleView();
                    _entries.Remove(key);
                    _retained -= RetainedWeight(key, settled);
                    settled = null;
                    return false;
                }

                observations?.RecordSettlementShareHit();
                return true;
            }

            if (_mode == SettlementShareMode.Footprint && _candidates.TryGetValue((key.Content, key.Level), out var candidates))
            {
                for (var i = 0; i < candidates.Count; i++)
                {
                    observations?.RecordSettlementShareCandidateVisit();
                    var (candidate, weight) = candidates[i];
                    if (!candidate.Satisfies(key.Bound, observations))
                        continue;
                    if (!candidate.ViewsStand())
                    {
                        observations?.RecordSettlementShareStaleView();
                        candidates.RemoveAt(i);
                        if (candidates.Count == 0)
                            _candidates.Remove((key.Content, key.Level));
                        _retained -= weight;
                        settled = null;
                        return false;
                    }

                    observations?.RecordSettlementShareHit();
                    observations?.RecordSettlementShareCandidateHit();
                    settled = candidate;
                    return true;
                }
            }

            settled = null;
            return false;
        }

        /// <summary>
        /// Keeps a settlement that completed without a cycle cut and <see cref="Settled.StandsFromEverySite"/>
        /// at <paramref name="key"/>'s level: as a candidate of its content and level when it has a footprint and
        /// they hold fewer than <see cref="MaxCandidates"/>, for its exact bound owners otherwise; nothing when a
        /// kept settlement already answers the key, or once the share is full.
        /// </summary>
        public void Store(Key key, Settled settled)
        {
            if (!settled.StandsFromEverySite(key.Level))
                throw new InvalidOperationException("Only a settlement that stands from every site for the rest of the run is shared.");
            if (!KeepsSettlements)
                return;
            var weight = RetainedWeight(key, settled);
            if (settled.Footprint is not null && !settled.OwnerOffChain && _mode == SettlementShareMode.Footprint)
            {
                _candidates.TryGetValue((key.Content, key.Level), out var candidates);
                for (var i = 0; candidates is not null && i < candidates.Count; i++)
                {
                    observations?.RecordSettlementShareCandidateVisit();
                    if (!candidates[i].Settled.Satisfies(key.Bound, observations))
                        continue;
                    if (candidates[i].Settled.ViewsStand())
                        return;
                    observations?.RecordSettlementShareStaleView();
                    _retained -= candidates[i].Weight;
                    candidates.RemoveAt(i--);
                }

                // The group itself retains its content and level. Release it even if the replacement cannot fit.
                if (candidates is { Count: 0 })
                {
                    _candidates.Remove((key.Content, key.Level));
                    candidates = null;
                }

                if ((candidates?.Count ?? 0) < MaxCandidates)
                {
                    if (_retained + weight > capacity)
                        return;
                    // Most groups keep one candidate: its list starts with room for one.
                    if (candidates is null)
                        _candidates.Add((key.Content, key.Level), candidates = new(1));
                    candidates.Add((settled, weight));
                    _retained += weight;
                    observations?.RecordSettlementShareStore();
                    observations?.RecordSettlementShareRetainedWeight(_retained);
                    return;
                }
            }

            if (_retained + weight > capacity || !_entries.TryAdd(key, settled))
                return;
            _retained += weight;
            observations?.RecordSettlementShareStore();
            observations?.RecordSettlementShareRetainedWeight(_retained);
        }

        private static long RetainedWeight(Key key, Settled settled)
            => key.Weight + settled.Views.Length + (settled.Footprint?.Length ?? 0);
    }

    /// <summary>
    /// The owning level's settlement of the references the scope-free summary walk left
    /// pending (<see cref="PendingReference"/>), in exactly the evaluator's lookup order: the
    /// head as a PROPERTY of the chain of the reference's origin (ownership first), then the
    /// <c>open</c> targets of that chain's levels, innermost first — a reference carries no
    /// provider, so each target is resolved here, from the level that
    /// declares the open, level by level: the first level at which a target publicly provides
    /// the head decides, its sole provider charging and two or more charging NOTHING (the
    /// evaluator's ambiguousOpen selects no declaration; list order never picks one). A member
    /// reached by navigation charges its requirement seed expanded from ITS declaring level
    /// outward. Requirement sets are monotone unions, so a reference re-entered through a
    /// cycle of mutually opening libraries contributes nothing new (the least fixed point);
    /// the enclosing sibling fixed point iterates the rest to stability. Results are canonical
    /// sets of the run's interner (FE-4a), and every read of a summary of the level in progress
    /// (<paramref name="levelInProgress"/>) is recorded while a recording is open, so the level's
    /// solver can reuse a settlement exactly as long as what it read still stands. A complete nested
    /// settlement that read none of them and does not depend on its site is kept in the run's
    /// <paramref name="shared"/> settlements and answers every later level (<see cref="SettlementShare"/>).
    /// Every frame is charged to the run's <paramref name="ledger"/> (<see cref="SettlementFrameWork"/>).
    /// </summary>
    private sealed class PendingResolution(
        PropertyDependencyGraphBuilder.SummaryWalkMemos memos,
        RequirementSetInterner sets,
        SummaryScope levelInProgress,
        SettlementShare shared,
        StaticQueryResourceBudget? ledger,
        CancellationToken cancellationToken)
    {
        private readonly record struct SettlementKey(string Key, SummaryScope Level, SummaryScope Site, BoundOwnerSet? Bound);

        /// <summary>
        /// A seed anchored at a level of the chain. <see cref="Site"/>, when set, is the site its requirements are
        /// checked from instead of the frame's own (owner decision Q2, 2026-11-14: each check where the evaluator makes
        /// it): the consulted level for an open target's walk step, the reference's own scope for a value crossing.
        /// </summary>
        /// <see cref="OpenWalkMember"/> marks a member an open-target walk selects, a step of the target or a member of a
        /// reference it crosses (<see cref="ChargePublishedOpenPath"/>, <see cref="ChargeOpenCrossing"/>): its seed is
        /// resolved in place when it reads nothing further (<see cref="TryResolveInPlace"/>).
        private readonly record struct AnchoredSeed(PropertyDependencyGraphBuilder.SummarySeed Seed, SummaryScope Level,
            SummaryScope? Site = null, bool OpenWalkMember = false);
        private readonly record struct SeedSettlementKey(PropertyDependencyGraphBuilder.SummarySeed Seed,
            SummaryScope Level, SummaryScope Site, BoundOwnerSet? Bound);

        // The settlements in progress, each with its frame: a reference met again while its own settlement runs is a
        // cycle cut, and the frame says how far out the cut reaches (Frame.OutermostCut).
        private readonly Dictionary<SettlementKey, Frame> _inProgress = [];
        private readonly record struct SeedSite(PropertyDependencyGraphBuilder.SummarySeed Seed, SummaryScope Level, SummaryScope Site);
        private readonly Dictionary<SeedSite, Frame> _firstSeed = [];
        private bool _triedEquations;
        private ComponentEquations? _collecting;
        private SolvedComponent? _solved;
        private Frame? _solvedUntil;

        private sealed record SolvedComponent(HashSet<SeedSite> Members, SettlementShare.Settled Union)
        {
            public bool Answers(SeedSite site, BoundOwnerSet? bound)
                => Members.Contains(site) && Union.Satisfies(bound, null) && Union.ViewsStand();
        }

        // Collect each seed's direct union and the seed settlements it reads. The ordinary reference walk
        // selects every edge. A discarded result, a live read, an off-chain lookup or a changing view
        // disqualifies the graph. At an edge the child's union is a variable, initially empty.
        private sealed class ComponentEquations
        {
            public readonly List<SeedSite> Vertices = [];
            private readonly Dictionary<SeedSite, List<SeedSite>> _readers = [];
            private readonly HashSet<BoundOwnerSet> _extensions = new(ReferenceEqualityComparer.Instance);
            public SeedSite Current;
            public int Edges;
            public bool Disqualified;

            public List<SeedSite> Add(SeedSite site)
            {
                if (_readers.TryGetValue(site, out var readers))
                    return readers;
                readers = [];
                _readers.Add(site, readers);
                Vertices.Add(site);
                return readers;
            }

            public void Edge(SeedSite site, BoundOwnerSet? added)
            {
                Edges++;
                Add(site).Add(Current);
                if (added is not null)
                    _extensions.Add(added);
            }

            public SolvedComponent? Complete(SeedSite root, SettlementShare.Settled union, CancellationToken cancellationToken)
            {
                if (union.Footprint is null)
                    return null;
                foreach (var extension in _extensions)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    if (!union.Satisfies(extension, null))
                        return null;
                }

                // Every vertex is reachable from root. Exactly those which also reach root have
                // its entire reachable union. The remaining vertices contribute only as dependencies.
                var stack = new Stack<SeedSite>();
                var members = new HashSet<SeedSite> { root };
                stack.Push(root);
                while (stack.TryPop(out var next))
                    foreach (var reader in _readers[next])
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        if (members.Add(reader))
                            stack.Push(reader);
                    }
                return new(members, union);
            }
        }

        // The equations are computed at the meeting's bound owners. Their direct terms are invariant
        // for every input satisfying the combined footprint: every edge extends that input by its
        // written owners, and Complete checks that none of those extensions flips any read. C1 can
        // reset the bound set; a seed dependency inside that unbound trial disqualifies the equations.
        // Thus substitution on all paths preserves the direct terms. Their union is the least solution
        // for each seed that both reaches and is reached by the entry. Only those exact sites answer.
        private SolvedComponent? SolveComponent(SeedSite entry, BoundOwnerSet? bound)
        {
            var equations = new ComponentEquations();
            var directShare = new SettlementShare(null, capacity: 0);
            var direct = new PendingResolution(memos, sets, levelInProgress, directShare,
                ledger, cancellationToken) { _collecting = equations };
            var record = new Frame(memos.Observations);
            equations.Add(entry);
            for (var i = 0; i < equations.Vertices.Count; i++)
            {
                var site = equations.Current = equations.Vertices[i];
                direct.ChargeFrame();
                memos.Observations?.RecordRequiredAncestorSettlementFrame(site.Seed);
                var frame = new Frame(memos.Observations);
                frame.Body = direct.ResolveSeed(frame, site.Seed, site.Level, site.Site, bound);
                direct.Run(frame);
                if (equations.Disqualified || frame.ReadLive || directShare.SawOffChainLookup)
                    return null;
                record.Absorb(frame, this);
                record.Result = sets.Union(record.Result, frame.Result);
            }

            var union = record.Complete();
            return !union.InconsistentViews && union.ViewsStand() ? equations.Complete(entry, union, cancellationToken) : null;
        }

        // Unlike anchoring, settlement reads live equations. A complete result that read one, or that depends
        // on its site, is reused only inside ONE synchronous Run; the run's share keeps the others, and
        // _liveOpenWalks the level's own open walks.
        private readonly Dictionary<SettlementKey, SettlementShare.Settled> _completed = [];
        private readonly Dictionary<SeedSettlementKey, SettlementShare.Settled> _completedSeeds = [];

        /// <summary>
        /// COMPONENT SETTLEMENTS (2026-11-22; implementation only, no classification or Lean rule). A settlement a cycle
        /// cut left partial (<see cref="Frame.IsWhole"/> false) is the union over what its reference reaches short of
        /// the settlements that were in progress when it ran. It used to be discarded when it completed, so every later
        /// meeting of its key walked everything below it again: once per simple path through a component of mutually
        /// reading members, exponentially many when each member reads two or more others. It is now kept, by its exact
        /// key (content, level, site, bound owners), while the component it belongs to is still being settled:
        /// <list type="bullet">
        /// <item>REUSE. A later meeting of that key in the same <see cref="Run"/> takes its result and its record
        /// (<see cref="Frame.Reuse"/>) and is CUT WHERE IT WAS CUT: its <see cref="Frame.OutermostCut"/> is the kept
        /// one's. The kept settlement began before the meeting, so the meeting is partial too, and so is every
        /// settlement around it that does not hold the settlements the result still lacks. Those are settled in the
        /// first whole settlement around the one that was kept, whose union they reach as its own nested frames
        /// complete: a whole settlement is still everything its reference reaches (EXPOSURE-OPEN-1).</item>
        /// <item>NEVER PUBLISHED. A partial settlement is kept here only: never in <see cref="_completed"/>,
        /// <see cref="_completedSeeds"/>, the run's share or <see cref="_liveOpenWalks"/>, and never beyond its Run.</item>
        /// <item>RELEASE. When a keyed settlement completes whole, every partial settlement kept since it began
        /// belongs to a component it closes (each cut inside it reached it or a settlement nested in it), and all of
        /// them are released (<see cref="CloseComponents"/>): from then on only whole settlements answer.</item>
        /// <item>DISCARDED RESULTS. A settlement that runs nested settlements and then discards their results (the
        /// unbound open walks when C1 does not take them; an open level that turns out to select nothing, and the walks
        /// of a name nothing provides) stops what was kept inside them from answering a meeting whose result is used
        /// (<see cref="DiscardPartials"/>): what such a partial result lacks was to reach the enclosing unions through
        /// the discarded results.</item>
        /// <item>THE COMPONENT'S RECORD. What a settlement depended on beyond its key reaches its reader translated by
        /// the frames on the way: a reference that binds owners drops the reads of them, an unbound walk drops every
        /// read of bound owners, a consulted-level walk bounds a lookup that found no owner. The per-path settlement
        /// carried a member's reads along every path that met it. A reused partial result brings only what its own
        /// settlement had read, so the whole settlement that closes a component in which one was reused takes the
        /// record of EVERY member, untranslated (<see cref="Frame.AbsorbComponentMember"/>): at least what any path
        /// would have brought it.</item>
        /// </list>
        /// A top-level settlement returns the set it returned before; <see cref="ComponentSettlementsPerPathForTesting"/>
        /// is the former walk.
        /// </summary>
        private readonly Dictionary<SettlementKey, PartialSettlement> _partial = [];
        private readonly Dictionary<SeedSettlementKey, PartialSettlement> _partialSeeds = [];
        // Every partial settlement kept and not yet released, in completion order: a frame's ComponentMark is the count
        // when it began, so the ones from there on were kept inside it.
        private readonly List<PartialSettlement> _component = [];
        private readonly bool _componentSettlements = !ComponentSettlementsPerPathForTesting.Value;
        private readonly bool _liveSettlements = !LiveSettlementsPerRunForTesting.Value;
        private readonly bool _seedParts = !SeedPartsFoldedForTesting.Value;
        private readonly bool _pathParts = !PathPartsFoldedForTesting.Value && shared.KeepsSettlements;
        private readonly long _residualCapacity = ResidualCacheCapacityForTesting.Value ?? SettlementShare.DefaultCapacity;
        // The next discovery index of the Run in progress (Frame.Index).
        private int _nextIndex;

        /// <summary>
        /// One partial settlement kept for its component (<see cref="_partial"/>): its result and record as its frame
        /// completed, the outermost settlement its cuts reached, and what the closing settlement needs of it untranslated
        /// (the deepest landing and the off-chain lookup before the frame's own consulted-level bound).
        /// </summary>
        private sealed class PartialSettlement(SettlementShare.Settled settled, int outermostCut, int siteLanding, bool ownerOffChain,
            SettlementKey? key, SeedSettlementKey? seedKey)
        {
            public SettlementShare.Settled Settled => settled;
            public int OutermostCut => outermostCut;
            public int SiteLanding => siteLanding;
            public bool OwnerOffChain => ownerOffChain;
            public SettlementKey? Key => key;
            public SeedSettlementKey? SeedKey => seedKey;

            /// <summary>A later meeting of the key took this result: its component's closing settlement takes every member's record.</summary>
            public bool Reused;

            /// <summary>The <see cref="Frame.Index"/> of the frame that ran this settlement's frame.</summary>
            public int ParentIndex { get; init; }

            /// <summary>
            /// Every partial settlement a meeting inside this one took was kept inside it (<see cref="Frame.OldestReuse"/>):
            /// what its result lacks lies only beyond the settlements that enclosed it when it ran.
            /// </summary>
            public bool ReusedOnlyItsOwn { get; init; }

            /// <summary>Its place among the kept ones (<see cref="_component"/>), stable while it is kept.</summary>
            public int Place;

            /// <summary>The discarded result cannot answer a meeting which consumes it.</summary>
            public bool Discarded;
        }

        /// <summary>
        /// THE NAMES OF THE LIVE SUMMARIES A SETTLEMENT READ (<see cref="SettlementShare.Settled.LiveReads"/>, implementation
        /// only): canonical sets of this resolution's own interner, created at its first live read and dropped with the
        /// level's solve. A frame adds a name it reads along one trie path (a name its set holds already changes nothing),
        /// and takes a nested frame's or a reused result's set as a memoized union, the set itself when it has read none (a
        /// chain of frames passes one set up unchanged). Until November 2026 a frame kept at most sixteen names in a list
        /// scanned per read, and a settlement that read more was reused only inside its Run: the unbound open walks of a level
        /// that read seventeen or more summaries of the level in progress were settled again by every reader with bound
        /// owners (the November 21 audit's <c>exposure-live-open-walks-maxlivereads</c>).
        /// <para>THE BOUND (2026-11-25). The interner keeps every branch it builds and every union it memoizes until the
        /// level's solve ends, also for settlements no table then keeps: readers whose read sets differ (overlapping windows
        /// of the level's properties, or one set read in different orders) build different sets, path by path, and those
        /// entries grew with the readers times their reads. So each entry it creates is one unit of static work, charged and
        /// counted (<see cref="FrontEndTraversalObservations.SettlementLiveNameEntries"/>) at the end of its insertion or
        /// union. Between operations it holds at most <see cref="_residualCapacity"/> entries: the operation that
        /// takes it past that releases it (sets already handed out stay valid: nodes reference no table) and returns no set.
        /// From then on, for the rest of the level's solve, a frame that reads a live summary records its live reads as
        /// UNKNOWN (<see cref="Frame.LiveReadsKnown"/>: it read live and names none), as does every frame that absorbs or
        /// reuses one, and such a settlement is never kept beyond its Run (C1's open walks, LIVE SETTLEMENTS): the ordinary
        /// settlement, which is what the sixteen-name list did past its cap. The level's own record of what its top-level
        /// settlement read, which decides when the level solver evaluates a reader again, stays complete: the names its own
        /// frames read (<c>_levelReads</c>) are recorded without the interner, and the set of a kept settlement it reuses
        /// (LIVE READ SETS, <see cref="ReplayLiveReads"/>) stays valid after the interner is released.</para>
        /// Never static, and never shared: the component discovery (<see cref="SolveComponent"/>) has its own, since a frame
        /// there that reads a live summary disqualifies the component.
        /// </summary>
        private LiveReadNameInterner? _liveNameInterner;
        private int _liveNameEntries;
        private bool _liveNamesSaturated;
        public bool LiveNamesSaturated => _liveNamesSaturated;

        // `set` with the live summary `name` (LIVE READS); no set (unknown) once the interner is past its capacity.
        private CanonicalNameSet WithLiveName(CanonicalNameSet set, string name)
        {
            if (_liveNamesSaturated)
                return default;
            var interner = _liveNameInterner ??= new(memos.Observations, cancellationToken);
            return CountLiveNameEntries(interner, interner.WithName(set, name));
        }

        // The union of two live-read sets of this resolution (LIVE READS); no set (unknown) once the interner is past its
        // capacity.
        private CanonicalNameSet UnionLiveNames(CanonicalNameSet first, CanonicalNameSet second)
        {
            if (_liveNamesSaturated)
                return default;
            var interner = _liveNameInterner ??= new(memos.Observations, cancellationToken);
            return CountLiveNameEntries(interner, interner.Union(first, second));
        }

        // Charges and counts the entries the last operation created, and releases the interner once it holds more than its
        // capacity: that operation's set is not handed out.
        private CanonicalNameSet CountLiveNameEntries(NameSetInterner interner, CanonicalNameSet result)
        {
            var held = interner.Entries;
            var created = held - _liveNameEntries;
            _liveNameEntries = held;
            if (created > 0)
            {
                ledger?.Work(created, cancellationToken);
                memos.Observations?.RecordSettlementLiveNameEntries(created, held);
            }

            if (held <= _residualCapacity)
                return result;
            _liveNamesSaturated = true;
            _liveNameInterner = null;
            _recentSummaryChanges = null;
            memos.Observations?.RecordSettlementLiveNameSaturation();
            return default;
        }

        // C1 WHILE THE LEVEL IS IN PROGRESS (implementation only): the level's unbound open-walk settlement
        // (SharedOpenWalksLevel) whose walks read summaries of this level, kept for the rest of this level's solve with the
        // level's summary revision it last stood at (LIVE REVISIONS). A later Run reuses it exactly when no summary it read
        // has changed since and every view it consulted still stands: it is then the settlement that Run would compute (its
        // key holds the site, it is whole, no summary changes within a Run), and its live reads are recorded again for the
        // new top-level settlement. The run's share keeps only settlements that read no live summary, so without this every
        // reader walked the level again.
        private Dictionary<SettlementKey, (SettlementShare.Settled Settled, long Revision)>? _liveOpenWalks;
        private long _wideOpenWalkNames;

        // LIVE SETTLEMENTS (implementation only): every other whole settlement that read summaries of this level, kept for
        // the rest of this level's solve (LiveSettlements). Null until the first one completes.
        private LiveSettlements? _live;
        private HashSet<string>? _levelReads;

        /// <summary>
        /// LIVE REVISIONS (2026-11-26; implementation only, no classification, requirement, diagnostic or Lean rule). A
        /// settlement kept live (<c>_liveOpenWalks</c>, <see cref="LiveSettlements"/>) stands while no summary it read has
        /// changed. Until then each one copied the names and summaries it read into a snapshot when it was kept, and each
        /// reuse compared every one of them with the current summary: the audit's <c>liveb</c> shape at width 400 took
        /// 2,003 frames but 159,600 comparisons and 161,600 snapshot names, and readers whose read sets are distinct
        /// paid the snapshots of settlements nothing took again. Now the summaries of the level in progress carry one
        /// REVISION, the number of changes since the first live keep (<see cref="LevelSolver"/>, between Runs, through
        /// <see cref="NoteSummaryChanged"/>); a kept settlement holds the revision it last stood at and copies nothing. A
        /// reuse at the same revision stands with no comparison. Otherwise it tests each change since against the names
        /// the settlement read (<see cref="LiveReadsStand"/>), or, when the changes outnumber those names or the live-read
        /// interner that named them is released (THE BOUND, <see cref="_liveNameInterner"/>), tests each name's last change
        /// (in the level's equation index): one unit of static work per change or name tested, charged before it runs.
        /// A settlement that stands takes the current revision, so no change is tested twice for it.
        /// <para>A settlement stands only when no summary it read was replaced at all, so it never stands where the former
        /// comparison of every summary found one changed. It is exactly that comparison: a change is recorded only when
        /// the new summary differs from the one it replaces, and every equation is monotone (<see cref="LevelSolver"/>: a
        /// summary only grows), so a summary replaced after a settlement read it never equals what it read again. The
        /// history holds at most the smaller of the level's name count and the residual capacity. Revisions older than
        /// that window use the equation stamps. Releasing the interner releases the history as well.</para>
        /// </summary>
        private long _summaryRevision = -1;
        private List<string>? _recentSummaryChanges;
        private int ChangeWindowCapacity => (int)Math.Min(_residualCapacity, levelInProgress.Summaries.Count);
        private Dictionary<string, (int Index, long ChangedAt)>? _equations;

        // The solver already indexes the last declaration of each name. Store its version there too, so updating a
        // repeatedly changing equation or a never-read name cannot grow a separate table.
        public IReadOnlyDictionary<string, (int Index, long ChangedAt)> IndexEquations(IReadOnlyList<Property> properties)
        {
            _equations = new(StringComparer.Ordinal);
            for (var i = 0; i < properties.Count; i++)
                _equations[properties[i].Name] = (i, 0);
            return _equations;
        }

        /// <summary>
        /// The level solver changed the summary <paramref name="name"/> of the level in progress to a different set
        /// (LIVE REVISIONS): the level's next revision, recorded once a settlement is kept live.
        /// </summary>
        public void NoteSummaryChanged(string name, int index)
        {
            if (_summaryRevision < 0)
                return;
            if (!_liveNamesSaturated)
            {
                var recent = _recentSummaryChanges ??= [];
                var capacity = ChangeWindowCapacity;
                if (recent.Count < capacity)
                    recent.Add(name);
                else
                    recent[(int)(_summaryRevision % capacity)] = name;
            }

            _equations![name] = (index, ++_summaryRevision);
            memos.Observations?.RecordSettlementLiveSummaryChange(_recentSummaryChanges?.Count ?? 0);
        }

        private long KeepRevision()
        {
            if (_summaryRevision < 0)
                _summaryRevision = 0;
            return _summaryRevision;
        }

        /// <summary>
        /// LIVE SETTLEMENTS (November 2026; implementation only, no classification, requirement, diagnostic or Lean rule).
        /// The run's share keeps a whole settlement only when it read no summary of the level in progress, because such a
        /// summary may still grow; and <c>_liveOpenWalks</c> keeps only the level's unbound open walks (C1). Every other
        /// settlement that read one, a member seed reading the level's properties above all, was therefore reused only
        /// inside its own Run: K readers with bound owners of a member that reads W such summaries took K × W frames (the
        /// November 21 audit's broader <c>exposure-live-open-walks-maxlivereads</c> shapes: a namespace member listing the
        /// level's properties, reached by a written path or through an <c>open</c>).
        /// <para>Here such a settlement is kept for the rest of the level's solve, with the level's summary revision it last
        /// stood at (LIVE REVISIONS), under the share's own rules otherwise (<see cref="SettlementShare"/>): it is whole; it answers every site at
        /// its level (no view at two versions, no site lookup below the level); it made no owner lookup off its site's
        /// chain, here or in anything it reached or reused (such a result answers its exact key only, and keeping it
        /// would extend THE OFF-CHAIN GAP to keys the current walk computes afresh: it is never kept here); and it is
        /// answered by its footprint, by exact <c>Contains</c>, at most <see cref="SettlementShare.MaxCandidates"/> per
        /// content and level, within <see cref="SettlementShare.DefaultCapacity"/> of retained weight. A later settlement
        /// of the same content and level takes it exactly when its bound owners satisfy that footprint, every view it
        /// consulted stands, and EVERY summary it read still equals the current one (no summary it read has changed since
        /// the revision it holds, LIVE REVISIONS): it is then the settlement that Run would compute, because which
        /// summaries a settlement reads is structural, the summaries it read are the ones that Run reads (none changes
        /// within a Run), and the share's argument covers its key, views and bound owners. Its live reads are recorded
        /// again in the reusing top-level settlement, so the level solver evaluates that reader again when one of them
        /// changes, exactly as when it is computed. A stale entry is dropped and computed again. The retained weight
        /// still counts the names an entry read: its name set outlives the interner that built it once that is
        /// released. The test seam <see cref="SettlementShareModeForTesting"/> applies: exact bound owners only, or
        /// nothing kept.</para>
        /// </summary>
        private sealed class LiveSettlements(PendingResolution resolution, FrontEndTraversalObservations? observations)
        {
            private readonly record struct Kept(SettlementShare.Settled Settled, BoundOwnerSet? Bound, long Revision, long Weight);

            private readonly Dictionary<(object Content, SummaryScope Level), List<Kept>> _kept = [];
            private readonly SettlementShareMode _mode = SettlementShareModeForTesting.Value;
            private long _retained;

            /// <summary>
            /// The kept settlement of <paramref name="key"/>'s content and level that answers its bound owners, while its
            /// views and the summaries it read stand; it then holds the current revision. A stale entry met is dropped.
            /// The resolution charges each validation (<see cref="LiveReadsStand"/>).
            /// </summary>
            public bool TryGet(SettlementShare.Key key,
                [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out SettlementShare.Settled? settled)
            {
                settled = null;
                if (!_kept.TryGetValue((key.Content, key.Level), out var entries))
                    return false;
                for (var i = 0; i < entries.Count; i++)
                {
                    var entry = entries[i];
                    observations?.RecordSettlementShareCandidateVisit();
                    if (!Answers(entry, key.Bound))
                        continue;
                    if (!entry.Settled.ViewsStand() || !resolution.LiveReadsStand(entry.Settled, entry.Revision, out var revision))
                    {
                        observations?.RecordSettlementShareStaleView();
                        Remove(key, entries, i);
                        return false;
                    }

                    entries[i] = entry with { Revision = revision };
                    observations?.RecordSettlementLiveHit();
                    settled = entry.Settled;
                    return true;
                }

                return false;
            }

            /// <summary>
            /// Keeps a whole settlement that read summaries of the level in progress, at the current revision, under the
            /// rules of the class summary; nothing when a kept one already answers the key, past
            /// <see cref="SettlementShare.MaxCandidates"/> per content and level, or once the retained weight is full.
            /// </summary>
            public void Store(SettlementShare.Key key, SettlementShare.Settled settled)
            {
                if (!settled.ReadLive || !settled.LiveReadsKnown || settled.OwnerOffChain || !settled.AnswersEverySite(key.Level))
                    throw new InvalidOperationException("Only a whole settlement that read a live summary, names every one it read, answers every site and made no off-chain lookup is kept live.");
                if (_mode == SettlementShareMode.Unshared || _mode == SettlementShareMode.Footprint && settled.Footprint is null)
                    return;
                _kept.TryGetValue((key.Content, key.Level), out var entries);
                if (entries is not null)
                {
                    if (entries.Count >= SettlementShare.MaxCandidates)
                        return;
                    foreach (var entry in entries)
                        if (Answers(entry, key.Bound))
                            return;
                }

                var weight = key.Weight + settled.Views.Length + (settled.Footprint?.Length ?? 0) + settled.LiveReads.Count;
                if (_retained + weight > resolution._residualCapacity)
                    return;
                if (entries is null)
                    _kept.Add((key.Content, key.Level), entries = new(1));
                entries.Add(new(settled, key.Bound, resolution.KeepRevision(), weight));
                _retained += weight;
                observations?.RecordSettlementLiveStore();
                if (!resolution._liveNamesSaturated)
                    observations?.LiveSettlementStoredBeforeSaturation?.Invoke(settled);
            }

            private bool Answers(Kept entry, BoundOwnerSet? bound)
                => _mode == SettlementShareMode.Footprint
                    ? entry.Settled.Satisfies(bound, observations)
                    : Equals(entry.Bound, bound);

            private void Remove(SettlementShare.Key key, List<Kept> entries, int index)
            {
                _retained -= entries[index].Weight;
                entries.RemoveAt(index);
                if (entries.Count == 0)
                    _kept.Remove((key.Content, key.Level));
            }
        }

        // A kept live settlement for `key` (LiveSettlements), its live reads recorded again in the top-level settlement in
        // progress; the validation is charged like TryLiveOpenWalks', before it runs (LiveReadsStand).
        private bool TryLiveSettlement(SettlementShare.Key key, [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out SettlementShare.Settled? settled)
        {
            settled = null;
            if (_live is null || !_live.TryGet(key, out settled))
                return false;
            ReplayLiveReads(settled.LiveReads);
            return true;
        }

        /// <summary>
        /// Whether no summary <paramref name="settled"/> read has changed since <paramref name="revision"/>, the revision it
        /// was kept at or last stood at (LIVE REVISIONS), and the <paramref name="current"/> revision it then stands at.
        /// At the current revision nothing is tested. Otherwise each change since is tested against the names it read, or,
        /// when the changes outnumber those names or the interner that named them is released, each name's last change:
        /// one unit of static work per change or name, charged before the test runs, even when an early change ends it.
        /// </summary>
        private bool LiveReadsStand(SettlementShare.Settled settled, long revision, out long current)
        {
            current = _summaryRevision;
            var changes = current - revision;
            if (changes == 0)
            {
                memos.Observations?.RecordSettlementLiveRevisionHit();
                return true;
            }

            var names = settled.LiveReads;
            var byChanges = TestsChanges(names, changes);
            var units = byChanges ? changes : names.Count;
            ledger?.Work(units, cancellationToken);
            memos.Observations?.RecordSettlementLiveReadChecks(units);
            if (byChanges)
                memos.Observations?.RecordSettlementLiveChangeChecks(changes);
            if (ChangedSince(names, revision, changes, byChanges))
                return Stale(settled);
            return true;
        }


        // Whether the changes since a revision are tested against a set's names, one interner Contains each: only while the
        // interner and its history exist, every change is still in the history, and the changes are no more than the names.
        // Otherwise each name's last-change stamp is tested.
        private bool TestsChanges(CanonicalNameSet names, long changes)
            => _liveNameInterner is not null && changes <= names.Count && _recentSummaryChanges is { } recent && changes <= recent.Count;

        // Whether a summary named in `names` changed after `revision`: one of the `changes` since then is a name the set
        // holds, or (byChanges false) one of its names has a later last-change stamp (LIVE REVISIONS).
        private bool ChangedSince(CanonicalNameSet names, long revision, long changes, bool byChanges)
        {
            if (byChanges)
            {
                var interner = _liveNameInterner!;
                var capacity = ChangeWindowCapacity;
                for (var i = 0; i < changes; i++)
                {
                    CheckWideWalkCancellation(i);
                    if (interner.Contains(names, _recentSummaryChanges![(int)((revision + i) % capacity)]))
                        return true;
                }

                return false;
            }

            var index = 0;
            foreach (var name in names.WalkNames())
            {
                CheckWideWalkCancellation(index++);
                if (_equations!.TryGetValue(name, out var equation) && equation.ChangedAt > revision)
                    return true;
            }

            return false;
        }

        private bool Stale(SettlementShare.Settled settled)
        {
            if (_liveNamesSaturated)
                memos.Observations?.LiveSettlementStaleAfterSaturation?.Invoke(settled);
            return false;
        }

        // A reused kept settlement's live reads become reads of the top-level settlement in progress (LIVE READ SETS): its
        // canonical set is recorded by identity, never enumerated, and the level solver indexes each distinct set once.
        private void ReplayLiveReads(CanonicalNameSet names)
        {
            if (_levelReads is null) return;
            cancellationToken.ThrowIfCancellationRequested();
            memos.Observations?.RecordSettlementLiveReadReplay();
            var sets = _levelReadSets ??= [];
            // Keep one entry per identity even if a recording alternates between the same sets. A
            // single set needs no hash table. The list preserves the order of the first replays.
            if (sets.Count > 0 && (sets[0].Equals(names) || !(_otherReadSets ??= []).Add(names)))
                return;
            sets.Add(names);
        }

        private void CheckWideWalkCancellation(int index)
        {
            if ((index & 255) == 0)
                cancellationToken.ThrowIfCancellationRequested();
        }

        // Keeps a whole settlement that read summaries of this level for the rest of its solve (LiveSettlements).
        private void KeepLiveSettlement(SettlementShare.Key key, SettlementShare.Settled settled)
        {
            if (!_liveSettlements)
                return;
            (_live ??= new LiveSettlements(this, memos.Observations)).Store(key, settled);
        }

        // The frame whose body is running: what it consults beyond its key is recorded on it (see Frame).
        private Frame? _running;

        /// <summary>
        /// Starts recording the level-in-progress summaries a top-level settlement reads: by name what its own frames read
        /// (the returned set), and by identity the live-read set of each kept settlement it reuses (<see cref="ReplayLiveReads"/>,
        /// taken by <see cref="EndRecording"/>). A settlement with no names read leaves its empty set available for the next one.
        /// </summary>
        public HashSet<string> BeginRecording()
            => _levelReads = _emptyRecording ?? new HashSet<string>(StringComparer.Ordinal);

        private HashSet<string>? _emptyRecording;
        private List<CanonicalNameSet>? _levelReadSets;
        private HashSet<CanonicalNameSet>? _otherReadSets;

        /// <summary>
        /// Ends the recording: the distinct live-read sets of the kept settlements it reused, in the order first reused.
        /// Each stood when it was reused, and no summary changes during a recording.
        /// </summary>
        public CanonicalNameSet[] EndRecording()
        {
            // A nonempty recording belongs to its reader. Recycling it would make later small recordings
            // repeatedly clear a bucket array sized for the largest preceding settlement.
            _emptyRecording = _levelReads is { Count: 0 } ? _levelReads : null;
            _levelReads = null;
            if (_levelReadSets is not { Count: > 0 } sets)
                return [];
            var recorded = sets.ToArray();
            sets.Clear();
            _otherReadSets?.Clear();
            return recorded;
        }

        // The direct-chain property lookup, recording a read of the level-in-progress summary it returns.
        private bool TryLookupSummary(SummaryScope from, string name, out SummaryScope level, out PropertyLookupHit hit, out RequirementSet summary)
        {
            if (!from.TryLookup(name, out level, out hit, out summary))
                return false;
            if (ReferenceEquals(level, levelInProgress))
            {
                _levelReads?.Add(name);
                _running?.NoteLiveRead(name, this);
            }

            return true;
        }

        // A completed-fact view the running frame consults: a shared settlement stands while each one it read does.
        private void NoteView(StaticLookupFacts facts) => _running?.NoteView(facts, facts.ViewVersion);

        /// <summary>The settlement of <paramref name="pending"/> at <paramref name="level"/> (a top-level settlement).</summary>
        public RequirementSet Resolve(PendingReference pending, SummaryScope level)
            => Run(ReferenceFrame(pending, level, site: null, boundOwners: null));

        /// <summary>
        /// The settlement of a whole CONTRIBUTION at <paramref name="level"/> (a top-level settlement): what a family's
        /// summary seed, or one branch body's, requires of the owners at and above the level the family is written in,
        /// as owner-qualified requirements. It is the settlement a level's equation gives a property whose value is
        /// that seed (<see cref="ResolveSeed"/>: the seed's own requirements and each reference it
        /// holds). The frame is charged and observed like every other, and keeps no entry of its own: its nested
        /// settlements are cached and shared exactly as any reader's.
        /// </summary>
        public RequirementSet ResolveContribution(PropertyDependencyGraphBuilder.SummarySeed seed, SummaryScope level)
        {
            if (seed.IsEmptyWithoutFolding())
                return default;
            ChargeFrame();
            memos.Observations?.RecordRequiredAncestorSettlementFrame(seed);
            var frame = new Frame(memos.Observations);
            frame.Body = ResolveSeed(frame, seed, level, level, boundOwners: null);
            return Run(frame);
        }

        /// <summary>
        /// ONE suspended settlement — a pending reference's or a seed's. Settlements nest as deep as a
        /// chain of member reads (`P1.A1` charging `P2.A2` charging `P3.A3`…, or the same through
        /// `open`s), so they never recurse on the host stack: each is a heap frame whose body yields the
        /// nested frame it needs next, and <see cref="Run"/> resumes it with that frame's
        /// <see cref="Result"/> exactly where the recursive form would have returned — the evaluation
        /// order and every in-progress cut follow the recursive form. Completed nested settlements
        /// may be reused during one run, with their reads already in its recording, so shared tails
        /// cost their distinct keys and edges rather than their path count.
        ///
        /// <para>A frame also carries what its settlement depended on BEYOND its key — the deepest landing
        /// of its site lookups, a read of a live summary, the fact views it consulted, the bound-owner
        /// memberships it read (its footprint, <see cref="SettlementShare"/>) — for its own body, every
        /// nested frame (<see cref="Absorb(Frame, PendingResolution)"/>) and every result it reused (<see cref="Reuse"/>), so a
        /// settlement never looks independent merely because what it depended on arrived through a cache.
        /// <see cref="Complete"/> is that record with the result.</para>
        /// </summary>
        private sealed class Frame(FrontEndTraversalObservations? observations) : ISettlementReader
        {
            public IEnumerator<Frame> Body = null!;
            public RequirementSet Result;
            public SettlementKey? CacheKey;
            public SeedSettlementKey? SeedCacheKey;
            public bool FirstSeedAtSite;

            /// <summary>
            /// The frame's discovery index in its <see cref="Run"/>: frames are numbered as they are pushed, so a frame
            /// that began before this one has a smaller index, and the frames in progress with a smaller index are
            /// exactly the settlements enclosing this one.
            /// </summary>
            public int Index;

            /// <summary>
            /// The outermost settlement a cycle cut inside this one reached, as that frame's <see cref="Index"/>;
            /// <see cref="int.MaxValue"/> when it saw none. A cut is a reference met again while its own settlement
            /// is in progress, and it contributes nothing where it is met; a reference met again after its settlement
            /// completed PARTIAL contributes that partial result and is cut where that settlement was cut (COMPONENT
            /// SETTLEMENTS, <see cref="_partial"/>). When every cut inside a settlement reached that settlement itself
            /// or one nested in it, each of them is settled inside it, so its union is whole (<see cref="IsWhole"/>): it
            /// is the settlement its key has as a top-level one. A cut that reached a settlement that began BEFORE this
            /// one leaves it a partial union, which is published nowhere and answers only its own key while its
            /// component is being settled (EXPOSURE-OPEN-1).
            /// </summary>
            public int OutermostCut = int.MaxValue;

            /// <summary>No cycle cut inside this settlement reached a settlement that began before it.</summary>
            public bool IsWhole => OutermostCut >= Index;

            /// <summary>The number of partial settlements kept when this frame began (<see cref="_component"/>).</summary>
            public int ComponentMark;

            /// <summary>The <see cref="Index"/> of the frame that ran this one (-1 for the frame a Run starts with).</summary>
            public int ParentIndex = -1;

            /// <summary>
            /// The oldest partial settlement a meeting inside this settlement took, as its place among the kept ones
            /// (<see cref="_component"/>); <see cref="int.MaxValue"/> when it took none. At or after
            /// <see cref="ComponentMark"/>, every one it took was kept inside this settlement itself.
            /// </summary>
            public int OldestReuse = int.MaxValue;

            /// <summary>The bound owners of a keyed frame's key (null for none, and on a frame without a key).</summary>
            public BoundOwnerSet? Bound;

            /// <summary>Set on a frame that computes a settlement the run's share may keep.</summary>
            public SettlementShare.Key? ShareKey;

            /// <summary>Whether this settlement read a summary of the level in progress, itself or in what it reached or reused.</summary>
            public bool ReadLive { get; private set; }

            // Those summaries by name, each once: a canonical set of the resolution's live-read interner (LIVE READS). Empty
            // while ReadLive once their names are unknown (an interner past its capacity): see LiveReadsKnown.
            private CanonicalNameSet _liveReads;

            /// <summary>
            /// Whether the names of every live summary this settlement read are recorded: false only when it read one and
            /// names none, because its resolution's live-read interner is past its capacity (LIVE READS) here or in what it
            /// absorbed or reused. Otherwise a settlement that read live names at least the summary it read.
            /// </summary>
            public bool LiveReadsKnown => !ReadLive || _liveReads.Count > 0;

            /// <summary>
            /// Set on the walk of an open target settled AT its consulted level (owner decision Q2), to that level: the
            /// walk's site is the level its key already names, so an owner it found on no level of that chain is found
            /// by no other settlement of the same key either. Such a lookup makes an ordinary settlement depend on its
            /// site (<see cref="int.MaxValue"/>); this one depends on nothing deeper than its own level, which is what
            /// it reports.
            /// </summary>
            public SummaryScope? SiteIsItsLevel;
            private int _siteDepth = SummaryScope.NoOwnerLookup;
            private bool _inconsistentViews;
            // The fact views consulted, each once, in the order first consulted: the first one in place (a settlement
            // usually consults one or two), any further ones in a list.
            private StaticLookupFacts? _firstView;
            private int _firstViewVersion;
            private List<(StaticLookupFacts Facts, int Version)>? _moreViews;

            /// <summary>
            /// The owners this frame's reference binds itself (<see cref="SummaryReference.BoundOwners"/>): its bound
            /// owners are its enclosing frame's extended by them, so each of them is present whatever the enclosing
            /// frame's are. Null for a seed, an inner route frame and a reference that binds none.
            /// </summary>
            public IReadOnlyList<Algorithm>? OwnOwners;

            /// <summary>
            /// Set on the level's unbound open-walks settlement (C1): it runs with no bound owners whatever its
            /// enclosing frame's are, so nothing it read of them is a read of the enclosing frame's.
            /// </summary>
            public bool RunsUnbound;

            /// <summary>
            /// Set on the frame of one seed part settled on its own (PATH PARTS, <c>PathPartFrame</c>): it has no key, binds no
            /// owner of its own and runs under its enclosing frame's bound owners, so its record is that frame's reads.
            /// </summary>
            public bool PathPart;

            // The footprint (SettlementShare): each bound-owner membership read, with its answer for this frame's own
            // bound owners, each owner once; null with _exactBoundOwners once it is unknown (MaxFootprint exceeded, or a
            // result without one reused).
            private List<(Algorithm Owner, bool Present)>? _footprint;
            private bool _exactBoundOwners;
            private BoundOwnerEmptiness _emptiness;

            // An owner lookup found no owner on the site's chain, here or in what this settlement reached or reused. Its
            // result may hold only from this site (SettlementShare), so it is never answered for other bound owners. A
            // consulted-level walk is settled from its own level whoever reads it, so that bounds it (as SiteDepth).
            private bool _ownerOffChain;

            public bool OwnerOffChain => _ownerOffChain && SiteIsItsLevel is null;

            /// <summary>
            /// An owner lookup found no owner here or in what this settlement reached or reused, whatever consulted
            /// level bounds it (<see cref="OwnerOffChain"/> is the bounded fact).
            /// </summary>
            public bool LookedUpOffChain => _ownerOffChain;

            public void NoteOwnerOffChain() => _ownerOffChain = true;

            public void NoteMembership(Algorithm owner, bool present)
            {
                if (_exactBoundOwners)
                    return;
                observations?.RecordSettlementFootprintWork(1);
                _footprint ??= [];
                foreach (var (known, answer) in _footprint)
                {
                    if (!ReferenceEquals(known, owner))
                        continue;
                    if (answer != present)
                        throw new InvalidOperationException("A settlement read one bound owner with two answers.");
                    return;
                }

                if (_footprint.Count == SettlementShare.MaxFootprint)
                {
                    ReadExactBoundOwners();
                    return;
                }

                _footprint.Add((owner, present));
            }

            public void NoteNoBoundOwners(bool none)
            {
                var read = none ? BoundOwnerEmptiness.ReadNone : BoundOwnerEmptiness.ReadSome;
                if (_emptiness != BoundOwnerEmptiness.Unread && _emptiness != read)
                    throw new InvalidOperationException("A settlement read its bound owners as both none and some.");
                _emptiness = read;
            }

            private void ReadExactBoundOwners()
            {
                _exactBoundOwners = true;
                _footprint = null;
            }

            // What a nested settlement read of its own bound owners, as reads of this frame's: a membership of an owner
            // the nested reference binds itself, and its emptiness read once it binds any, read nothing of this frame's.
            private void AbsorbFootprint(IReadOnlyList<(Algorithm Owner, bool Present)>? footprint, bool exact, BoundOwnerEmptiness emptiness,
                IReadOnlyList<Algorithm>? ownOwners)
            {
                var bindsOwners = ownOwners is { Count: > 0 };
                if (emptiness != BoundOwnerEmptiness.Unread && !bindsOwners)
                    NoteNoBoundOwners(emptiness == BoundOwnerEmptiness.ReadNone);
                if (exact)
                {
                    ReadExactBoundOwners();
                    return;
                }

                if (footprint is null)
                    return;
                for (var i = 0; i < footprint.Count; i++)
                {
                    var (owner, present) = footprint[i];
                    if (present && bindsOwners && BindsItself(ownOwners!, owner))
                        continue;
                    NoteMembership(owner, present);
                }
            }

            private static bool BindsItself(IReadOnlyList<Algorithm> ownOwners, Algorithm owner)
            {
                for (var i = 0; i < ownOwners.Count; i++)
                    if (ReferenceEquals(ownOwners[i], owner))
                        return true;
                return false;
            }

            // The deepest landing this settlement depends on. Every lookup of a consulted-level walk starts at that
            // level, so one that found no owner is bounded by the level's own depth.
            private int SiteDepth => SiteIsItsLevel is { } own && _siteDepth == int.MaxValue ? own.Depth : _siteDepth;

            public void NoteSiteLanding(int landing) => _siteDepth = Math.Max(_siteDepth, landing);

            public void NoteView(StaticLookupFacts facts, int version)
            {
                if (_firstView is null)
                {
                    _firstView = facts;
                    _firstViewVersion = version;
                    return;
                }

                if (ReferenceEquals(_firstView, facts))
                {
                    _inconsistentViews |= _firstViewVersion != version;
                    return;
                }

                _moreViews ??= [];
                foreach (var (known, seen) in _moreViews)
                {
                    if (!ReferenceEquals(known, facts))
                        continue;
                    _inconsistentViews |= seen != version;
                    return;
                }

                _moreViews.Add((facts, version));
            }

            // The views a nested frame consulted, as this frame's reads, in the order that frame first consulted them.
            private void NoteViewsOf(Frame nested)
            {
                if (nested._firstView is not { } first)
                    return;
                NoteView(first, nested._firstViewVersion);
                if (nested._moreViews is { } more)
                    foreach (var (facts, version) in more)
                        NoteView(facts, version);
            }

            private (StaticLookupFacts Facts, int Version)[] Views()
            {
                if (_firstView is null)
                    return [];
                var views = new (StaticLookupFacts Facts, int Version)[1 + (_moreViews?.Count ?? 0)];
                views[0] = (_firstView, _firstViewVersion);
                for (var i = 1; i < views.Length; i++)
                    views[i] = _moreViews![i - 1];
                return views;
            }

            /// <summary>
            /// A read of the summary <paramref name="name"/> of the level in progress (<c>TryLookupSummary</c>), named in
            /// <paramref name="resolution"/>'s live-read interner; unknown from then on when the interner has no room.
            /// </summary>
            public void NoteLiveRead(string name, PendingResolution resolution)
            {
                if (!LiveReadsKnown)
                    return;
                ReadLive = true;
                _liveReads = resolution.WithLiveName(_liveReads, name);
            }

            // The live reads of a nested settlement or a reused result, as this frame's: one union of canonical sets (the
            // other set itself while this frame has read none). Unknown names on either side, or an interner with no room
            // for the union, leave this frame's unknown.
            private void AbsorbLiveReads(bool readLive, CanonicalNameSet names, PendingResolution resolution)
            {
                if (!readLive || !LiveReadsKnown)
                    return;
                var first = !ReadLive;
                ReadLive = true;
                _liveReads = names.Count == 0 ? default : first ? names : resolution.UnionLiveNames(_liveReads, names);
            }

            public void Absorb(Frame nested, PendingResolution resolution)
            {
                OutermostCut = Math.Min(OutermostCut, nested.OutermostCut);
                OldestReuse = Math.Min(OldestReuse, nested.OldestReuse);
                NoteSiteLanding(nested.SiteDepth);
                AbsorbLiveReads(nested.ReadLive, nested._liveReads, resolution);
                _inconsistentViews |= nested._inconsistentViews;
                NoteViewsOf(nested);
                _ownerOffChain |= nested.OwnerOffChain;
                if (!nested.RunsUnbound)
                    AbsorbFootprint(nested._footprint, nested._exactBoundOwners,
                        nested._emptiness, nested.OwnOwners);
            }

            /// <summary>
            /// Takes a completed settlement as this frame's result, with everything it depended on: its footprint's
            /// answers hold for this frame's bound owners, which are its exact ones or satisfy it. The settlement is a
            /// whole one, or a partial one kept for this frame's exact key (<see cref="ReusePartial"/>, which also cuts
            /// this frame where that one was cut).
            /// </summary>
            public void Reuse(SettlementShare.Settled settled, PendingResolution resolution)
            {
                Result = settled.Result;
                AbsorbRecord(settled, resolution);
            }

            /// <summary>
            /// Takes what a completed WHOLE settlement depended on as this frame's reads, exactly as
            /// <see cref="Absorb(Frame, PendingResolution)"/> takes them from the nested frame that computed it (a frame
            /// that binds no owner of its own and runs under this frame's bound owners): PATH PARTS reuses a kept part
            /// settlement this way, its result united by the caller.
            /// </summary>
            public void AbsorbRecord(SettlementShare.Settled settled, PendingResolution resolution)
            {
                NoteSiteLanding(settled.SiteDepth);
                AbsorbLiveReads(settled.ReadLive, settled.LiveReads, resolution);
                _inconsistentViews |= settled.InconsistentViews;
                foreach (var (facts, version) in settled.Views)
                    NoteView(facts, version);
                _ownerOffChain |= settled.OwnerOffChain;
                AbsorbFootprint(settled.Footprint, exact: settled.Footprint is null, settled.Emptiness, ownOwners: null);
            }

            public SettlementShare.Settled Complete()
                => new(Result, SiteDepth, ReadLive, Views(), _inconsistentViews,
                    _exactBoundOwners ? null : _footprint is null ? [] : [.. _footprint], _emptiness, OwnerOffChain,
                    _liveReads);

            /// <summary>
            /// This frame's partial settlement as its component keeps it (COMPONENT SETTLEMENTS): the record
            /// <see cref="Complete"/> gives a meeting of its key, and the deepest landing and off-chain lookup BEFORE this
            /// frame's own consulted-level bound (<see cref="SiteIsItsLevel"/>), which the component's closing
            /// settlement takes untranslated.
            /// </summary>
            public PartialSettlement CompletePartial()
                => new(Complete(), OutermostCut, _siteDepth, _ownerOffChain, CacheKey, SeedCacheKey)
                {
                    ParentIndex = ParentIndex,
                    ReusedOnlyItsOwn = OldestReuse >= ComponentMark,
                };

            /// <summary>
            /// Takes the record of one member of a component this settlement closes, UNTRANSLATED (COMPONENT
            /// SETTLEMENTS). A reused partial result brought the meeting only what its own settlement had read, and
            /// what it lacked arrived along the paths its frames ran on; the per-path settlement would have carried the
            /// member's reads along every path that met it, and each path drops or bounds a different part. So no frame
            /// on the way is trusted to have dropped or bounded anything: each bound owner the member read is a read of
            /// THIS frame's bound owners (<paramref name="bound"/>), recorded with their own answer — except an owner
            /// the member read as present that they do not hold, which every path to the member's key bound on the way
            /// and which is therefore no read of them; a member that read whether its bound owners are none, or read
            /// them in full, makes this frame read its own likewise; and its deepest landing and off-chain lookup count
            /// before any consulted-level bound but this frame's own. Every answer recorded is a fact of this frame's
            /// bound owners, so the record only narrows where the settlement is reused.
            /// </summary>
            public void AbsorbComponentMember(PartialSettlement member, BoundOwnerSet? bound)
            {
                NoteSiteLanding(member.SiteLanding);
                _ownerOffChain |= member.OwnerOffChain;
                var settled = member.Settled;
                if (settled.Emptiness != BoundOwnerEmptiness.Unread)
                    NoteNoBoundOwners(bound is null);
                if (settled.Footprint is not { } footprint)
                {
                    ReadExactBoundOwners();
                    return;
                }

                for (var i = 0; i < footprint.Length; i++)
                {
                    var held = bound?.Contains(footprint[i].Owner) == true;
                    if (footprint[i].Present && !held)
                        continue;
                    NoteMembership(footprint[i].Owner, held);
                }
            }

            /// <summary><see cref="SettlementShare.Settled.AnswersEverySite"/> of what this frame has recorded so far.</summary>
            public bool AnswersEverySite(SummaryScope level)
                => !_inconsistentViews && SiteDepth <= level.Depth;
        }

        /// <summary>
        /// Runs <paramref name="root"/> to completion over an explicit stack: a frame yielding a nested
        /// frame is suspended until that frame completes. An exception unwinds every suspended frame
        /// innermost first, so each one's in-progress key is released exactly as the recursion's
        /// <c>finally</c> blocks released it.
        /// </summary>
        private RequirementSet Run(Frame root)
        {
            // One synchronous settlement: summaries cannot change while these frames run. All reads
            // from the first computation remain in the top-level recording even on later cache hits.
            _completed.Clear();
            _completedSeeds.Clear();
            ClearPartials();
            _nextIndex = 0;
            _triedEquations = false;
            root.Index = _nextIndex++;
            // One stack per resolution: a Run never nests in its own resolution (its first step clears the run state), and
            // the finally below empties the stack again.
            var frames = _frames ??= new Stack<Frame>();
            frames.Push(root);
            try
            {
                // One cancellation checkpoint per frame pushed, before its body first runs (2.06): a
                // cancelled settlement unwinds through the finally below like any other exception.
                ObserveCancellation();
                while (frames.TryPeek(out var frame))
                {
                    _running = frame;
                    if (frame.Body.MoveNext())
                    {
                        var nested = frame.Body.Current;
                        nested.Index = _nextIndex++;
                        nested.ComponentMark = _component.Count;
                        nested.ParentIndex = frame.Index;
                        if (_componentSettlements && nested.SeedCacheKey is { } entering)
                            nested.FirstSeedAtSite = _firstSeed.TryAdd(new(entering.Seed, entering.Level, entering.Site), nested);
                        frames.Push(nested);
                        ObserveCancellation();
                    }
                    else
                    {
                        frames.Pop();
                        if (frame.LookedUpOffChain)
                            shared.SawOffChainLookup = true;
                        if (frame.FirstSeedAtSite && frame.SeedCacheKey is { } leaving)
                        {
                            _firstSeed.Remove(new(leaving.Seed, leaving.Level, leaving.Site));
                            if (ReferenceEquals(frame, _solvedUntil))
                            {
                                _solved = null;
                                _solvedUntil = null;
                            }
                        }
                        var keyed = frame.CacheKey is not null || frame.SeedCacheKey is not null;
                        // A settlement a cycle cut left partial is published nowhere (Frame.OutermostCut): its
                        // component keeps it until the settlement that closes the component completes.
                        if (keyed && !frame.IsWhole)
                        {
                            if (_componentSettlements)
                                KeepPartial(frame);
                        }
                        else if (keyed)
                        {
                            CloseComponents(frame);
                            var settled = frame.Complete();
                            if (frame.CacheKey is { } key)
                                _completed.TryAdd(key, settled);
                            if (frame.SeedCacheKey is { } seedKey)
                                _completedSeeds.TryAdd(seedKey, settled);
                            if (frame.ShareKey is { } shareKey && settled.StandsFromEverySite(shareKey.Level))
                                shared.Store(shareKey, settled);
                            else if (frame.RunsUnbound && frame.CacheKey is { } unboundKey && settled.ReadLive && settled.LiveReadsKnown
                                && settled.AnswersEverySite(unboundKey.Level))
                                KeepLiveOpenWalks(unboundKey, settled);
                            else if (!frame.RunsUnbound && frame.ShareKey is { } liveKey && settled.ReadLive && settled.LiveReadsKnown
                                && !settled.OwnerOffChain && settled.AnswersEverySite(liveKey.Level))
                                KeepLiveSettlement(liveKey, settled);
                        }

                        if (frames.TryPeek(out var enclosing))
                            enclosing.Absorb(frame, this);
                    }
                }
            }
            finally
            {
                _running = null;
                _firstSeed.Clear();
                _solved = null;
                _solvedUntil = null;
                while (frames.TryPop(out var suspended))
                    suspended.Body.Dispose();
                _completed.Clear();
                _completedSeeds.Clear();
                ClearPartials();
            }

            return root.Result;
        }

        private Stack<Frame>? _frames;

        // Nothing partial outlives its Run: a completed, cancelled or failed settlement leaves none behind.
        private void ClearPartials()
        {
            _partial.Clear();
            _partialSeeds.Clear();
            _component.Clear();
        }

        // A keyed settlement completed partial: it answers later meetings of its exact key until the settlement that
        // closes its component completes (COMPONENT SETTLEMENTS). A seed has no in-progress cut of its own, so a second
        // frame of one seed key can complete inside the first: the later, outer one then answers, and both stay members.
        private void KeepPartial(Frame frame)
        {
            var kept = frame.CompletePartial();
            if (kept.Key is { } key)
                _partial[key] = kept;
            else if (kept.SeedKey is { } seedKey)
                _partialSeeds[seedKey] = kept;
            kept.Place = _component.Count;
            _component.Add(kept);
        }

        // The partial settlement kept for a key, as a later meeting of that key takes it: the meeting is counted, and its
        // component's closing settlement will take every member's record (PartialSettlement.Reused).
        private SettlementShare.Settled ReusePartial(PartialSettlement kept, Frame meeting)
        {
            kept.Reused = true;
            memos.Observations?.RecordSettlementComponentReuse();
            meeting.OutermostCut = Math.Min(meeting.OutermostCut, kept.OutermostCut);
            meeting.OldestReuse = Math.Min(meeting.OldestReuse, kept.Place);
            return kept.Settled;
        }

        // A keyed settlement completed WHOLE: every partial settlement kept since it began is a member of a component it
        // closes, because no cut inside it reached a settlement that began before it. When a member was reused, the
        // closing settlement takes every member's record untranslated (Frame.AbsorbComponentMember) before it is
        // completed and published; then all of them are released, and only whole settlements answer from here on.
        private void CloseComponents(Frame closing)
        {
            var first = closing.ComponentMark;
            if (first == _component.Count)
                return;
            var reused = false;
            for (var i = first; i < _component.Count && !reused; i++)
                reused = _component[i].Reused;
            for (var i = first; i < _component.Count; i++)
            {
                cancellationToken.ThrowIfCancellationRequested();
                var member = _component[i];
                if (reused)
                    closing.AbsorbComponentMember(member, closing.Bound);
                Release(member);
            }

            _component.RemoveRange(first, _component.Count - first);
        }

        /// <summary>
        /// <paramref name="host"/> discards the results of the nested settlements it ran since <paramref name="mark"/>.
        /// A partial settlement kept inside them lacks what lies beyond the settlements it was cut at, and expects
        /// those to bring it to the enclosing unions themselves; one of them that ran INSIDE the discarded settlements
        /// brings it only as far as the host, which drops it. So a kept settlement answers no meeting whose result is
        /// used (<see cref="PartialSettlement.Discarded"/>) unless nothing it lacks lies inside: it is one of the
        /// host's own nested settlements, so every settlement that enclosed it began before the host did, and every
        /// partial settlement its meetings took was kept inside itself (<see cref="PartialSettlement.ReusedOnlyItsOwn"/>).
        /// A discarded one stays a member of its component, whose closing settlement still takes its record. A
        /// reference's also stays in the table for the one meeting whose result is discarded too, the unbound open
        /// walks; a seed has no such meeting and is released.
        /// </summary>
        private void DiscardPartials(int mark, Frame host)
        {
            if (_collecting is not null)
                _collecting.Disqualified = true;
            for (var i = mark; i < _component.Count; i++)
            {
                var kept = _component[i];
                cancellationToken.ThrowIfCancellationRequested();
                if (kept.Discarded || kept.ParentIndex == host.Index && kept.ReusedOnlyItsOwn)
                    continue;
                kept.Discarded = true;
                if (kept.SeedKey is not null)
                    Release(kept);
            }
        }

        // Remove only the entry this member still owns.
        private void Release(PartialSettlement member)
        {
            if (member.Key is { } key)
            {
                if (_partial.TryGetValue(key, out var kept) && ReferenceEquals(kept, member))
                    _partial.Remove(key);
            }
            else if (member.SeedKey is { } seedKey && _partialSeeds.TryGetValue(seedKey, out var keptSeed)
                && ReferenceEquals(keptSeed, member))
                _partialSeeds.Remove(seedKey);
        }

        private void ObserveCancellation()
            => FrontEndTraversalObservations.ObserveCancellation(
                memos.Observations, FrontEndCancellationCheckpoint.ExposureSettlementFrame, cancellationToken);

        // One unit of static work per settlement frame, charged before the frame is counted or built: a frame the
        // operation's work bound refuses is never observed and settles nothing (SettlementFrameWork). No token is
        // passed, so this is no cancellation checkpoint: those stay one per frame pushed (Run). The ledger is null
        // only for a standalone analysis, which has no operation (SettlementLedgerOf).
        private void ChargeFrame() => ledger?.Work(SettlementFrameWork);

        // Keeps the level's unbound open-walk settlement that read summaries of this level (_liveOpenWalks) at the current
        // revision: no summary changes within a Run, so the summaries it read are the ones of that revision (LIVE
        // REVISIONS). Only one that names every summary it read: a kept one is reused exactly while none of them changes.
        private void KeepLiveOpenWalks(SettlementKey key, SettlementShare.Settled settled)
        {
            if (!settled.LiveReadsKnown)
                throw new InvalidOperationException("An open-walk settlement whose live reads are unknown is never kept beyond its Run.");
            // Narrow entries already belonged to this per-level cache. Bound the names wide ones keep named, which their
            // sets hold once the interner that built them is released.
            var previous = _liveOpenWalks is not null && _liveOpenWalks.TryGetValue(key, out var prior)
                ? WideOpenWalkNames(prior.Settled.LiveReads.Count) : 0;
            var retained = _wideOpenWalkNames - previous + WideOpenWalkNames(settled.LiveReads.Count);
            if (retained > _residualCapacity)
                return;
            (_liveOpenWalks ??= [])[key] = (settled, KeepRevision());
            _wideOpenWalkNames = retained;
        }

        private static int WideOpenWalkNames(int count) => count > 16 ? count : 0;

        // A kept open-walk settlement of this level, while no summary it read has changed and every view it consulted
        // stands; its live reads become reads of the top-level settlement in progress, exactly as if it had been computed
        // in it. The validation is charged before it runs (LiveReadsStand).
        private bool TryLiveOpenWalks(SettlementKey key, [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out SettlementShare.Settled? settled)
        {
            settled = null;
            if (_liveOpenWalks is null || !_liveOpenWalks.TryGetValue(key, out var kept))
                return false;
            if (!LiveReadsStand(kept.Settled, kept.Revision, out var revision) || !kept.Settled.ViewsStand())
            {
                _liveOpenWalks.Remove(key);
                _wideOpenWalkNames -= WideOpenWalkNames(kept.Settled.LiveReads.Count);
                return false;
            }

            _liveOpenWalks[key] = (kept.Settled, revision);
            ReplayLiveReads(kept.Settled.LiveReads);
            settled = kept.Settled;
            return true;
        }

        private Frame ReferenceFrame(PendingReference pending, SummaryScope level, SummaryScope? site, BoundOwnerSet? boundOwners)
        {
            // Every reference a settlement receives carries its origin (PendingReference.Origin): what a summary walk let
            // escape a body carries that body's context, BuildSummaries anchors a hoisted deconstruction source's raw rows
            // at their level, and a bare name the chain does not declare is anchored at the level (ResolveVisibleName).
            ChargeFrame();
            memos.Observations?.RecordRequiredAncestorSettlementFrame(pending);
            var frame = new Frame(memos.Observations);
            frame.Body = ResolveReference(frame, pending, level, site, boundOwners);
            return frame;
        }

        private Frame SeedFrame(PropertyDependencyGraphBuilder.SummarySeed seed, SummaryScope level, SummaryScope site, BoundOwnerSet? boundOwners)
        {
            ChargeFrame();
            memos.Observations?.RecordRequiredAncestorSettlementFrame(seed);
            var siteKey = new SeedSite(seed, level, site);
            if (_collecting is not null)
            {
                _collecting.Edge(siteKey, boundOwners);
                return new Frame(memos.Observations) { Body = NoFrames() };
            }
            var key = new SeedSettlementKey(seed, level, site, boundOwners);
            var shareKey = new SettlementShare.Key(seed, level, boundOwners);
            if (shared.TryGet(shareKey, out var settled) || _completedSeeds.TryGetValue(key, out settled)
                || TryLiveSettlement(shareKey, out settled))
            {
                var reused = new Frame(memos.Observations) { Body = NoFrames() };
                reused.Reuse(settled, this);
                return reused;
            }

            var frame = new Frame(memos.Observations);
            if (!_triedEquations && !shared.SawOffChainLookup && _firstSeed.TryGetValue(siteKey, out var first)
                && memos.CompletedContext.Facts is CompletedStaticStructures { HasProvisional: false })
            {
                _triedEquations = true;
                // The enclosing driver pushes and checks this charged frame before any discovery work.
                frame.Body = DiscoverAndSettle(frame, first, siteKey, key, shareKey);
            }
            else frame.Body = SeedBody(frame, siteKey, key, shareKey);

            return frame;
        }

        private IEnumerator<Frame> DiscoverAndSettle(Frame frame, Frame first, SeedSite site, SeedSettlementKey key, SettlementShare.Key shareKey)
        {
            var observations = memos.Observations;
            var before = observations?.RequiredAncestorSettlementFrames ?? 0;
            _solved = SolveComponent(site, key.Bound);
            observations?.RecordSettlementComponentDiscovery(before);
            _solvedUntil = _solved is null ? null : first;
            using var body = SeedBody(frame, site, key, shareKey);
            while (body.MoveNext())
                yield return body.Current;
        }

        private IEnumerator<Frame> SeedBody(Frame frame, SeedSite site, SeedSettlementKey key, SettlementShare.Key shareKey)
        {
            if (_solved is { } solved && !shared.SawOffChainLookup && solved.Answers(site, key.Bound))
            {
                frame.SeedCacheKey = key;
                frame.ShareKey = shareKey;
                frame.Bound = key.Bound;
                memos.Observations?.RecordSettlementComponentCompletion();
                frame.Reuse(solved.Union, this);
                return NoFrames();
            }
            if (_partialSeeds.TryGetValue(key, out var partial))
            {
                frame.Reuse(ReusePartial(partial, frame), this);
                return NoFrames();
            }
            frame.SeedCacheKey = key;
            frame.ShareKey = shareKey;
            frame.Bound = key.Bound;
            return ResolveSeed(frame, site.Seed, site.Level, site.Site, key.Bound);
        }

        private static IEnumerator<Frame> NoFrames() { yield break; }

        /// <summary>
        /// THE SITE OF A CHECK (owner decision Q2, 2026-11-14): the deepest level, from <paramref name="site"/> upward,
        /// that is the scope <paramref name="checkedIn"/> or one of its ancestors. The evaluator makes an access check
        /// in one scope (the consulted level of an open walk, a reference's own scope for a value crossing), and an
        /// owner activation can satisfy it only on that scope's chain. A requirement reaches the reader through every
        /// enclosing check, so what counts is the part of that chain the settlement's site shares: a frame's site only
        /// ever moves outward. <paramref name="isThatScope"/>: the level found is <paramref name="checkedIn"/> itself.
        /// </summary>
        private static SummaryScope CheckSite(SummaryScope site, StaticScopeKey checkedIn, out bool isThatScope)
        {
            // The scope itself on the chain: the common case, and no allocation.
            for (var at = site; at is not null; at = at.Parent)
                if (ReferenceEquals(at.PropertyScope.CompletedContext?.Key, checkedIn))
                {
                    isThatScope = true;
                    return at;
                }

            isThatScope = false;
            var ancestors = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
            for (var key = checkedIn.Parent; key is not null; key = key.Parent)
                ancestors.Add(key);
            for (var at = site; at.Parent is not null; at = at.Parent)
                if (at.PropertyScope.CompletedContext?.Key is { } key && ancestors.Contains(key))
                    return at;
            // Every chain ends at the prelude, which every scope shares.
            return site.Root;
        }

        /// <summary>The settlement of one pending reference (see the class summary); its result is <paramref name="self"/>'s.</summary>
        private IEnumerator<Frame> ResolveReference(Frame self, PendingReference pending, SummaryScope level, SummaryScope? site,
            BoundOwnerSet? boundOwners)
        {
            site ??= level;
            // Q2 (owner decision 2026-11-14): an open target's walk is checked from the CONSULTED level, the level that
            // holds the `open`, never from the reader (LookupOpens resolves a level's opens with that level as the site).
            // A consulted level on the site's chain is the frame itself: the walk is settled at that level, from that
            // level, whoever reads through it. A level off that chain (a member's own body, the reader's own block) is
            // checked from the deepest level the two chains share.
            if (pending.OpenPath)
            {
                var checkedFrom = CheckSite(site, pending.Origin.Key, out var isConsultedLevel);
                if (isConsultedLevel || checkedFrom.Depth < level.Depth)
                    level = checkedFrom;
                site = checkedFrom;
                self.SiteIsItsLevel = isConsultedLevel ? checkedFrom : null;
            }

            // The walk's bound owners plus this reference's own: the set is extended, never copied or
            // serialized (BoundOwnerSet), and is itself the bound part of both keys. The share answers it from a
            // settlement of the same content and level whose footprint it satisfies (SettlementShare); in progress
            // and within the run, keys stay exact.
            if (pending.BoundOwners.Count > 0)
            {
                boundOwners = BoundOwnerSet.With(boundOwners, pending.BoundOwners, memos.Observations);
                self.OwnOwners = pending.BoundOwners;
            }
            var key = new SettlementKey(pending.ContentKey, level, site, boundOwners);
            var shareKey = new SettlementShare.Key(pending, level, boundOwners);
            if (shared.TryGet(shareKey, out var settled) || _completed.TryGetValue(key, out settled)
                || (self.RunsUnbound ? TryLiveOpenWalks(key, out settled) : TryLiveSettlement(shareKey, out settled)))
            {
                self.Reuse(settled, this);
                yield break;
            }
            if (_inProgress.TryGetValue(key, out var inProgress))
            {
                if (_collecting is not null)
                    _collecting.Disqualified = true;
                self.OutermostCut = Math.Min(self.OutermostCut, inProgress.Index);
                self.Result = default;
                yield break;
            }

            // The key's settlement completed PARTIAL earlier in this Run and its component is still being settled: it is
            // taken as it is, and this meeting is cut where it was cut (COMPONENT SETTLEMENTS). The key is exact, as in
            // progress: the same content, level, site and bound owners.
            // A kept settlement whose result an enclosing settlement discarded answers only the unbound open walks
            // (C1): this meeting is partial, so C1 does not take it and discards its result as well.
            if (_partial.TryGetValue(key, out var partial) && (!partial.Discarded || self.RunsUnbound))
            {
                self.Reuse(ReusePartial(partial, self), this);
                yield break;
            }

            _inProgress.Add(key, self);
            self.CacheKey = key;
            self.ShareKey = shareKey;
            self.Bound = boundOwners;
            var edgesAtEntry = _collecting?.Edges;

            try
            {
                if (pending.Selection == PendingSelection.OpenWalks && SharedOpenWalksLevel(self, pending, level, boundOwners) is { } opening)
                {
                    // C1: the level's walks settled ONCE, at the level itself with no bound owners, answer every reader
                    // that consults it when that settlement answers every site there (see SharedOpenWalksLevel).
                    // That settlement reads none of this reader's bound owners: only the choice of this route does. A
                    // summary of the level in progress it read is the one this reader's own walks would read in this Run,
                    // so it does not decide the route; it keeps the result out of the run's share, and _liveOpenWalks
                    // keeps it for the rest of this level's solve instead.
                    var unbound = ReferenceFrame(PropertyDependencyGraphBuilder.SummaryMemo.OpenWalksOf(pending.Origin),
                        opening, site, boundOwners: null);
                    var edgesBeforeUnbound = _collecting?.Edges;
                    unbound.RunsUnbound = true;
                    yield return unbound;
                    if (_collecting is { } collection && collection.Edges != edgesBeforeUnbound)
                        collection.Disqualified = true;
                    if (unbound.IsWhole && unbound.AnswersEverySite(opening))
                    {
                        self.Result = unbound.Result;
                        yield break;
                    }

                    // The unbound walks are not taken, so their result is discarded: no partial settlement kept inside
                    // them answers the reader's own walks below (COMPONENT SETTLEMENTS).
                    DiscardPartials(unbound.ComponentMark, self);
                }
                var published = new Frame(memos.Observations);
                published.Body = ResolvePublishedReference(published, pending, level, site, boundOwners);
                yield return published;
                self.Result = published.Result;
            }
            finally
            {
                _inProgress.Remove(key);
                // During discovery an edge represents another seed's unknown union. A cached direct
                // result containing such a term would hide the edge if a later C1 trial read it.
                if (_collecting is { } collecting && collecting.Edges != edgesAtEntry)
                {
                    self.CacheKey = null;
                    self.ShareKey = null;
                }
            }
        }

        /// <summary>
        /// ONE open lookup level's verdict (the evaluator's <c>LookupOpens</c>): every PROVIDER of
        /// the level that provides the head is offered once, by its semantic identity (Q-19 D-I —
        /// two targets of one provider are one offer); the level decides the lookup as soon as any
        /// provider provides the head — the sole provider's charge when exactly one does, and
        /// NOTHING when two or more do, because the evaluator then selects no declaration
        /// (ambiguousOpen).
        /// </summary>
        private sealed class OpenLevelSettlement
        {
            private HashSet<OpenProviderIdentity>? _providers;
            private RequirementSet _charge;

            public bool HasProvider(OpenProviderIdentity identity) => _providers?.Contains(identity) == true;

            public void Offer(OpenProviderIdentity identity, RequirementSet charge)
            {
                if ((_providers ??= []).Add(identity))
                    _charge = charge;
            }

            public bool Decides(RequirementSetInterner sets, ref RequirementSet names, out bool sole)
            {
                var providers = _providers?.Count ?? 0;
                sole = providers == 1;
                if (sole)
                    names = sets.Union(names, _charge);
                return providers > 0;
            }
        }

        private IEnumerator<Frame> ResolvePublishedReference(Frame self, PendingReference pending, SummaryScope level,
            SummaryScope site, BoundOwnerSet? boundOwners)
        {
            var origin = memos.SharedMemo.RequirementContext(pending.Origin);
            var facts = origin.Facts;
            NoteView(facts);
            // The requirement view is chosen from the written origin's facts, which are a view of their own.
            if (!ReferenceEquals(pending.Origin.Facts, facts))
                NoteView(pending.Origin.Facts);
            if (facts.Facts(origin.Key) is not { } originFacts || originFacts.Body is null && !originFacts.IsProvisional) yield break;
            var parts = new List<AnchoredSeed>();
            if (pending.Selection == PendingSelection.BlockHead)
            {
                // An inline-block head: every member of the path is SELECTED from the block, wired under the reading
                // scope, so each one is charged and the block's own VALUE is not, unless the first step selects
                // nothing (the fallback or intrinsic then reads it).
                var members = new List<string>(pending.Members.Count + 1) { pending.Head };
                members.AddRange(pending.Members);
                if (originFacts.Body is { } block
                    && ChargePublishedPath(facts, origin.Key, members, level, parts, firstIsNamespace: true) == 0)
                    parts.Add(AnchorPublishedSeed(facts,
                        PropertyDependencyGraphBuilder.GetAlgorithmSummary(block, memos, facts.Context(origin.Key)).OutputSeed,
                        origin.Key.Parent, level));
                foreach (var part in parts)
                {
                    if (part.Seed.IsEmptyWithoutFolding()) continue;
                    if (TryResolveInPlace(self, part, site, boundOwners)) continue;
                    var charge = SeedFrame(part.Seed, part.Level, part.Site ?? site, boundOwners);
                    yield return charge;
                    self.Result = sets.Union(self.Result, charge.Result);
                }
                yield break;
            }
            var scope = memos.SharedMemo.RequirementLevel(origin);
            if (pending.Selection == PendingSelection.OpenWalks)
            {
                // Every open target of this level is resolved once a lookup reaches the level (resolveAllOpens):
                // each target's walk is charged, whether or not it provides the name.
                memos.Observations?.RecordOpenWalksSettlement(origin.Key, boundOwners is not null);
                foreach (var target in scope.Opens)
                {
                    if (!memos.SharedMemo.OpenTargetMayCharge(scope, target)
                        || target.OpenTargetHead(out var steps) is not Expr.Resolve(var head)) continue;
                    var walk = ReferenceFrame(new PendingReference(head, steps, origin: pending.Origin, openPath: true),
                        level, site, boundOwners);
                    yield return walk;
                    self.Result = sets.Union(self.Result, walk.Result);
                }
                yield break;
            }
            if (pending.OpenPath)
            {
                Expr target = new Expr.Resolve(pending.Head);
                foreach (var member in pending.Members) target = new Expr.DotCall(target, member, null);
                ChargePublishedOpenPath(level, scope, target, parts);
            }
            else
            {
                var owned = ElaboratedScopeLookup.SelectOwnedDeclaration(scope, pending.Head, ElaboratedScopeLookup.OwnParameterBindings.Instance);
                if (owned.TryGetParameter(out var parameterOwner))
                {
                    var bound = parameterOwner.OwnerAlgorithm is { } owner && boundOwners?.Contains(owner) == true;
                    if (parameterOwner.OwnerAlgorithm is { } read)
                        self.NoteMembership(read, bound);
                    if (!bound)
                    {
                        var landing = SummaryScope.NoOwnerLookup;
                        self.Result = sets.From(site.ResolveRequirementsFromSite(
                            [new OwnerQualifiedParameter(pending.Head, parameterOwner.OwnerAlgorithm)], boundOwners, self, ref landing));
                        self.NoteSiteLanding(landing);
                    }

                    yield break;
                }
                if (owned.TryGetProperty(out var declaring, out var hit))
                {
                    // Q1 has selected this declaration. Read its published member key directly:
                    // an earlier resolved module view need not be the final exposed body object.
                    var declaringKey = declaring.CompletedContext?.Key
                        ?? throw new InvalidOperationException("A published selection requires its declaring context.");
                    var key = facts.Member(declaringKey, hit.Property.Name)
                        ?? throw new InvalidOperationException("A published declaration requires its authoritative member key.");
                    var navigated = ChargePublishedPath(facts, key, pending.Members, level, parts);
                    // The head was crossed as a receiver: a transparent reference's target walk selects in the
                    // reference's own scope, so those selections are charged; its VALUE is not.
                    if (navigated > 0)
                        self.Result = ChargeReferenceCrossing(facts, key, hit.Property.Name, declaringKey, level, site, parts);
                    if (navigated == 0)
                    {
                        // A direct summary of this live equation must remain a recorded read.
                        SummaryScope? found = level;
                        while (found is not null && !ReferenceEquals(found.PropertyScope.CompletedContext?.Key, declaring.CompletedContext?.Key))
                            found = found.Parent;
                        if (found is not null && TryLookupSummary(found, pending.Head, out _, out _, out var summary))
                            self.Result = sets.Adopt(summary);
                        else parts.Add(AnchorPublishedSeed(facts,
                            PropertyDependencyGraphBuilder.GetAlgorithmSummary(hit.Property.Value, memos, facts.Context(key)).OutputSeed,
                            key.Parent, level));
                    }
                }
                else
                {
                    var walks = default(RequirementSet);
                    for (var current = scope; current is not null; current = current.Parent)
                    {
                        // The lookup consults this level's opens: it resolves every one of them before it looks for the
                        // name, so every target's walk is charged (once per level, shared by every reader).
                        if (memos.SharedMemo.OpenWalksMayCharge(current))
                        {
                            var walk = ReferenceFrame(PropertyDependencyGraphBuilder.SummaryMemo.OpenWalksOf(current.CompletedContext!),
                                level, site, boundOwners);
                            yield return walk;
                            walks = sets.Union(walks, walk.Result);
                        }
                        var group = new OpenLevelSettlement();
                        // Q2: the providing target's walk steps are checked from this consulted level, the member it
                        // provides from the reader (LookupOpens: the site is the algorithm whose body reads the name).
                        SummaryScope? consultedSite = null;
                        foreach (var target in current.Opens)
                            if (TryProvideCompleted(level, target, pending, out var offered, out var identity, current,
                                    consultedSite ??= current.CompletedContext is { } consultedContext
                                        ? CheckSite(site, consultedContext.Key, out _) : site)
                                && !group.HasProvider(identity))
                            {
                                var names = default(RequirementSet);
                                foreach (var part in offered)
                                {
                                    if (part.Seed.IsEmptyWithoutFolding()) continue;
                                    var charge = SeedFrame(part.Seed, part.Level, part.Site ?? site, boundOwners);
                                    yield return charge;
                                    names = sets.Union(names, charge.Result);
                                }
                                group.Offer(identity, names);
                            }
                        var result = default(RequirementSet);
                        // A level with two or more providers selects nothing (ambiguousOpen): it charges nothing.
                        if (group.Decides(sets, ref result, out var sole))
                        {
                            self.Result = sole ? sets.Union(result, walks) : default;
                            // The walks and the providers' charges settled above are discarded with it: no partial
                            // settlement kept inside them answers a later meeting (COMPONENT SETTLEMENTS).
                            if (!sole)
                                DiscardPartials(self.ComponentMark, self);
                            yield break;
                        }
                    }

                    // No level provides the name: it charges nothing, and the walks settled on the way are discarded.
                    DiscardPartials(self.ComponentMark, self);
                }
            }
            foreach (var part in parts)
            {
                if (part.Seed.IsEmptyWithoutFolding()) continue;
                if (TryResolveInPlace(self, part, site, boundOwners)) continue;
                var charge = SeedFrame(part.Seed, part.Level, part.Site ?? site, boundOwners);
                yield return charge;
                self.Result = sets.Union(self.Result, charge.Result);
            }
        }

        /// <summary>
        /// A member an open-target walk selects whose seed names parameters only: its requirements are resolved here, at
        /// the frame's site, exactly as <see cref="ResolveSeed"/> resolves them, without a frame of their own (the walk
        /// that selected it is the settlement that is kept). A seed that holds a reference is settled as every seed is
        /// (false). Level expansion has already resolved or anchored the member's bare names.
        /// </summary>
        private bool TryResolveInPlace(Frame self, AnchoredSeed part, SummaryScope site, BoundOwnerSet? boundOwners)
        {
            if (!part.OpenWalkMember || part.Seed.PendingReferences.Count != 0)
                return false;
            var landing = SummaryScope.NoOwnerLookup;
            self.Result = sets.Union(self.Result, sets.From(part.Level.ResolveRequirements(part.Seed.RequiredAncestorOwnedParameterNames)
                .Concat((part.Site ?? site).ResolveRequirementsFromSite(part.Seed.OwnerQualifiedParameters, boundOwners, self, ref landing))));
            self.NoteSiteLanding(landing);
            return true;
        }

        /// <summary>
        /// The walk of one open target of the level <paramref name="scope"/> (<c>resolveOpen</c>): the head by the
        /// direct lexical chain, each PUBLIC step selected from its receiver's open structure. Every selection is
        /// checked from the consulted level, which is the frame's site (<see cref="ResolveReference"/>): the steps
        /// here, and the target walk of every transparent reference the walk reads through, head or step
        /// (<see cref="ChargeOpenCrossing"/>).
        /// </summary>
        private void ChargePublishedOpenPath(SummaryScope opening, ElaboratedPropertyScope scope, Expr target,
            List<AnchoredSeed> parts)
        {
            var facts = scope.CompletedContext!.Facts;
            NoteView(facts);
            var head = target.OpenTargetHead(out var steps);
            if (ElaboratedScopeLookup.ResolveOpenProviderHead(scope, head, out var declaring) is not { } resolved
                || CompletedStructureContext.For(resolved.Target, declaring) is not { } context) return;
            // A head that is a transparent reference is crossed: its target walk is checked from here too.
            if (head is Expr.Resolve(var name) && declaring.CompletedContext?.Key is { } declaringKey
                && facts.Member(declaringKey, name) is { } headKey)
                ChargeOpenCrossing(facts, headKey, name, declaringKey, opening, parts);
            var current = context.Key;
            foreach (var step in steps)
            {
                if (facts.Facts(current)?.Open.Target is not { } owner
                    || facts.Facts(owner)?.Body is not { } body
                    || ElaboratedScopeLookup.TryLookupPublicProperty(body, step) is null
                    || facts.Member(owner, step) is not { } member) return;
                AddOpenWalkCharge(facts, owner, step, opening, parts);
                // What follows reads this member through its open structure: a reference is crossed in turn.
                if (facts.Facts(member)?.Body is Algorithm.Alias { IsReference: true })
                    ChargeOpenCrossing(facts, member, step, owner, opening, parts);
                current = member;
            }
        }

        /// <summary><see cref="AddPublishedCharge"/> of a member an open-target walk selects (<see cref="AnchoredSeed.OpenWalkMember"/>).</summary>
        private void AddOpenWalkCharge(StaticLookupFacts facts, StaticScopeKey owner, string name, SummaryScope opening,
            List<AnchoredSeed> parts)
        {
            var first = parts.Count;
            AddPublishedCharge(facts, owner, name, opening, parts);
            for (var added = first; added < parts.Count; added++)
                parts[added] = parts[added] with { OpenWalkMember = true };
        }

        /// <summary>
        /// Q2 (owner decision 2026-11-14): the charge of crossing the declaration <paramref name="key"/> while an OPEN
        /// target is resolved. <c>openStructure</c> walks a transparent reference's static target with the context it
        /// was given, the consulted level's, and reads every reference RECEIVER of that walk the same way: so every
        /// member those walks select is checked from the consulted level, never in the reference's own scope. Each
        /// selected member's requirement seed is therefore added to <paramref name="parts"/>, to be resolved at the
        /// frame's site; the reference's own summary, which is resolved in its own scope, is never adopted. The head of
        /// a reference's target is resolved by the direct lexical chain only, and its value is never read; a member-less
        /// chain is followed, and a runtime reference ends it with nothing charged
        /// (<see cref="PropertyDependencyGraphBuilder.SummaryMemo.ReferenceTerminal"/>, opened). Each reference is
        /// walked once per crossing, so a cycle of references ends.
        /// </summary>
        private void ChargeOpenCrossing(StaticLookupFacts facts, StaticScopeKey key, string name, StaticScopeKey declaring,
            SummaryScope opening, List<AnchoredSeed> parts)
        {
            if (memos.SharedMemo.ReferenceTerminal(facts, key, name, declaring, opened: true) is not { } first) return;
            // What a crossing selects is a fact of the reference: it is found once per view, and charged at each crossing.
            var crossings = shared.OpenCrossings;
            var memoKey = (facts, facts.ViewVersion, first.Key);
            if (!crossings.TryGetValue(memoKey, out var crossing) || !crossing.Stands())
                crossings[memoKey] = crossing = OpenCrossingOf(facts, first);
            foreach (var (view, version) in crossing.Views)
                _running?.NoteView(view, version);
            foreach (var (view, owner, member) in crossing.Selections)
                AddOpenWalkCharge(view, owner, member, opening, parts);
        }

        /// <summary>The members the open crossing of the reference <paramref name="first"/> selects (<see cref="ChargeOpenCrossing"/>).</summary>
        private SettlementShare.OpenCrossing OpenCrossingOf(StaticLookupFacts facts,
            (StaticScopeKey Key, string Name, StaticScopeKey Declaring) first)
        {
            var selections = new List<(StaticLookupFacts Facts, StaticScopeKey Owner, string Name)>();
            var views = new List<(StaticLookupFacts Facts, int Version)>();
            HashSet<StaticScopeKey>? crossed = null;
            Stack<(StaticLookupFacts Facts, (StaticScopeKey Key, string Name, StaticScopeKey Declaring) Terminal)>? next = null;
            List<(StaticScopeKey Key, string Name, StaticScopeKey Owner)>? selected = null;
            for (var (view, terminal) = (facts, first); ;)
            {
                if ((crossed ??= new(ReferenceEqualityComparer.Instance)).Add(terminal.Key)
                    && view.Facts(terminal.Key)?.Body is { } reference)
                {
                    var row = PropertyDependencyGraphBuilder.GetAlgorithmSummary(reference, memos, view.Context(terminal.Key)).OutputSeed;
                    // A head an open provides is no direct-lexical head: openStructure resolves nothing through it.
                    var directHead = true;
                    foreach (PendingReference written in row.PendingReferences)
                        directHead &= written.Selection != PendingSelection.OpenWalks;
                    foreach (PendingReference written in row.PendingReferences)
                    {
                        if (!directHead || written.OpenPath) continue;
                        var origin = memos.SharedMemo.RequirementContext(written.Origin);
                        var seen = false;
                        foreach (var (known, _) in views) seen |= ReferenceEquals(known, origin.Facts);
                        if (!seen) views.Add((origin.Facts, origin.Facts.ViewVersion));
                        (selected ??= []).Clear();
                        if (written.Selection == PendingSelection.BlockHead)
                        {
                            // The block is wired under the reference: its members are selected from it.
                            var members = new List<string>(written.Members.Count + 1) { written.Head };
                            members.AddRange(written.Members);
                            SelectPublishedPath(origin.Facts, origin.Key, members, firstIsNamespace: true, selected);
                        }
                        else
                        {
                            var owned = ElaboratedScopeLookup.SelectOwnedDeclaration(memos.SharedMemo.RequirementLevel(origin),
                                written.Head, ElaboratedScopeLookup.OwnParameterBindings.Instance);
                            if (!owned.TryGetProperty(out var headLevel, out var hit)
                                || headLevel.CompletedContext?.Key is not { } headDeclaring
                                || origin.Facts.Member(headDeclaring, hit.Property.Name) is not { } headKey)
                                continue;
                            // The head is crossed in turn when it is a reference (asked only then: the terminal walk is a
                            // summary checkpoint).
                            if (SelectPublishedPath(origin.Facts, headKey, written.Members, firstIsNamespace: false, selected) > 0
                                && origin.Facts.Facts(headKey)?.Body is Algorithm.Alias { IsReference: true }
                                && memos.SharedMemo.ReferenceTerminal(origin.Facts, headKey, hit.Property.Name, headDeclaring,
                                    opened: true) is { } headTerminal)
                                (next ??= new()).Push((origin.Facts, headTerminal));
                        }

                        foreach (var member in selected)
                        {
                            selections.Add((origin.Facts, member.Owner, member.Name));
                            if (origin.Facts.Facts(member.Key)?.Body is Algorithm.Alias { IsReference: true }
                                && memos.SharedMemo.ReferenceTerminal(origin.Facts, member.Key, member.Name, member.Owner,
                                    opened: true) is { } memberTerminal)
                                (next ??= new()).Push((origin.Facts, memberTerminal));
                        }
                    }
                }

                if (next is null || !next.TryPop(out var following)) return new([.. selections], [.. views]);
                (view, terminal) = following;
            }
        }

        /// <summary>
        /// The charge of crossing the declaration <paramref name="key"/> (<paramref name="name"/>, declared at
        /// <paramref name="declaring"/>) as the receiver of a written path WITHOUT selecting it, a VALUE crossing: nothing
        /// unless it is a transparent reference, whose target walk the evaluator performs in the reference's OWN scope
        /// (<c>aliasStepNavigateWith</c>: the alias chase pushes the reference), access-checking each member it selects.
        /// A reference whose target selects a member, or whose head is not found by the owner walk (an open provides
        /// it), charges its VALUE requirement, which is exactly those selections (its head's value is never read). A
        /// member-less reference to a lexically found name selects nothing itself: the chain is followed while it names
        /// references (<see cref="PropertyDependencyGraphBuilder.SummaryMemo.ReferenceTerminal"/>), and a name that is
        /// not a reference charges nothing. The live summary, which is resolved in the reference's scope, is returned
        /// when the terminal's level is on the chain (a recorded read); otherwise its anchored seed is added to
        /// <paramref name="parts"/>, to be resolved from that scope too (owner decision Q2, 2026-11-14). The crossing
        /// made while an OPEN target is resolved is <see cref="ChargeOpenCrossing"/>: the consulted level checks it.
        /// </summary>
        private RequirementSet ChargeReferenceCrossing(StaticLookupFacts facts, StaticScopeKey key, string name,
            StaticScopeKey declaring, SummaryScope opening, SummaryScope site, List<AnchoredSeed> parts)
        {
            if (memos.SharedMemo.ReferenceTerminal(facts, key, name, declaring, opened: false) is not { } terminal) return default;
            SummaryScope? found = opening;
            while (found is not null && !ReferenceEquals(found.PropertyScope.CompletedContext?.Key, terminal.Declaring))
                found = found.Parent;
            if (found is not null && TryLookupSummary(found, terminal.Name, out var at, out _, out var summary) && ReferenceEquals(at, found))
                return sets.Adopt(summary);
            // Q2: a value crossing is checked in the reference's OWN scope (the alias chase pushes the reference), so a
            // reference declared off the chain is resolved from the part of its declaring chain the site shares.
            parts.Add(AnchorPublishedSeed(facts,
                PropertyDependencyGraphBuilder.GetAlgorithmSummary(facts.Facts(terminal.Key)!.Body!, memos, facts.Context(terminal.Key)).OutputSeed,
                terminal.Key.Parent, opening) with { Site = CheckSite(site, terminal.Declaring, out _) });
            return default;
        }

        /// <summary>
        /// C1 (owner decision 2, 2026-11-13): the level of <paramref name="level"/>'s chain whose open walks the
        /// <see cref="PendingSelection.OpenWalks"/> reference <paramref name="pending"/> names, when the unbound
        /// settlement of those walks AT that level answers this one exactly; null when this settlement must be computed
        /// as written (the per-reader settlement). With L the frame's level, L′ the returned level and B the bound
        /// owners, the answer is exact when:
        /// <list type="number">
        /// <item>L′ is L or an ancestor of it, and the frame is not already that unbound settlement;</item>
        /// <item>no owner in B is the algorithm of a level at or above L′;</item>
        /// <item>no level from L up to (not including) L′ is passed by the anchoring of L′'s walks
        /// (<see cref="OpenWalkAnchorsBelow"/>): their direct anchorings and reference-crossing lookups start at the
        /// frame's level, and from such a level they would stop earlier than from L′;</item>
        /// <item>the caller's check: the unbound settlement saw no cycle cut and answers every site at L′
        /// (<see cref="SettlementShare.Settled.AnswersEverySite"/>: no view read at two versions, no site lookup below
        /// L′).</item>
        /// </list>
        /// Then every selection and anchoring is the same from L and from L′ (3); every owner a bound owner could
        /// discharge (<see cref="SummaryScope.TryResolveRequirement"/>, a parameter head) landed at or above L′ (4), where
        /// none is in B (2), so B discharges nothing the unbound walk charged. A summary of the level in progress the
        /// walks read is adopted as it is, whatever the bound owners, and no summary changes within one Run, so it gives
        /// both routes the same set and does not decide the route. Readers of any bound owners at any depth below L′
        /// thus reuse one settlement: kept in the run's share, or, when it read a summary of the level in progress, for
        /// the rest of that level's solve while those summaries stand (<c>_liveOpenWalks</c>). Otherwise the result
        /// depends on the reader or the site, and it is settled per reader exactly as before.
        ///
        /// <para>The route reads B: whether it is empty (the null shortcut of (1), and the skipped test of (2)), and
        /// each membership (2) tests up to the first owner found. Each read is noted on <paramref name="self"/>'s
        /// footprint (<see cref="SettlementShare"/>), so a settlement reused under other bound owners takes this route
        /// under them too.</para>
        /// </summary>
        private SummaryScope? SharedOpenWalksLevel(Frame self, PendingReference pending, SummaryScope level, BoundOwnerSet? boundOwners)
        {
            if (OpenWalksPerReaderForTesting.Value) return null;
            var origin = memos.SharedMemo.RequirementContext(pending.Origin);
            SummaryScope? opening = level;
            while (opening is not null && !ReferenceEquals(opening.PropertyScope.CompletedContext?.Key, origin.Key))
                opening = opening.Parent;
            if (opening is null) return null;
            self.NoteNoBoundOwners(boundOwners is null);
            if (ReferenceEquals(opening, level) && boundOwners is null) return null;
            if (boundOwners is not null)
                for (var at = opening; at is not null; at = at.Parent)
                {
                    if (at.Algorithm is not { } owner) continue;
                    var bound = boundOwners.Contains(owner);
                    self.NoteMembership(owner, bound);
                    if (bound) return null;
                }
            if (!ReferenceEquals(opening, level))
            {
                var below = OpenWalkAnchorsBelow(opening, origin);
                for (var at = level; !ReferenceEquals(at, opening); at = at!.Parent)
                    if (at!.PropertyScope.CompletedContext?.Key is { } key && below.Contains(key)) return null;
            }
            return opening;
        }

        /// <summary>
        /// The keys the anchoring of <paramref name="opening"/>'s open walks passes before it reaches
        /// <paramref name="opening"/>'s chain, from that level: every declaring key <see cref="ChargePublishedOpenPath"/>
        /// anchors a selected member at (<see cref="AddPublishedCharge"/>: the selecting owner's parent) and the
        /// declaring level and parent of each crossed reference's terminal (<see cref="ChargeReferenceCrossing"/>), with
        /// their ancestors up to that chain. A superset only refuses more sharing. Completed facts only; computed once
        /// per level and facts view, in the run's share.
        /// </summary>
        private HashSet<StaticScopeKey> OpenWalkAnchorsBelow(SummaryScope opening, CompletedStructureContext origin)
        {
            var facts = origin.Facts;
            var memoKey = (facts, facts.ViewVersion, opening);
            if (shared.OpenWalkAnchors.TryGetValue(memoKey, out var known)) return known;
            var below = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
            var scope = memos.SharedMemo.RequirementLevel(origin);
            foreach (var target in scope.Opens)
            {
                if (!memos.SharedMemo.OpenTargetMayCharge(scope, target)) continue;
                var head = target.OpenTargetHead(out var steps);
                if (ElaboratedScopeLookup.ResolveOpenProviderHead(scope, head, out var declaring) is not { } resolved
                    || CompletedStructureContext.For(resolved.Target, declaring) is not { } context) continue;
                if (head is Expr.Resolve(var name) && declaring.CompletedContext?.Key is { } declaringKey
                    && facts.Member(declaringKey, name) is { } headKey
                    && memos.SharedMemo.ReferenceTerminal(facts, headKey, name, declaringKey, opened: true) is { } terminal)
                {
                    Passed(terminal.Declaring);
                    Passed(terminal.Key.Parent);
                }
                var current = context.Key;
                foreach (var step in steps)
                {
                    if (facts.Facts(current)?.Open.Target is not { } owner
                        || facts.Facts(owner)?.Body is not { } body
                        || ElaboratedScopeLookup.TryLookupPublicProperty(body, step) is null
                        || facts.Member(owner, step) is not { } member) break;
                    Passed(owner.Parent);
                    current = member;
                }
            }
            shared.OpenWalkAnchors.Add(memoKey, below);
            return below;

            // AnchorPublishedSeed's walk from a declaring key: every key before the first one on the opening's chain.
            void Passed(StaticScopeKey? at)
            {
                for (; at is not null; at = at.Parent)
                {
                    for (var level = opening; level is not null; level = level.Parent)
                        if (ReferenceEquals(level.PropertyScope.CompletedContext?.Key, at) || at.Parent is null && level.Parent is null)
                            return;
                    below.Add(at);
                }
            }
        }

        // Select only through completed Q2/Q3/Q4 facts. Requirement seeds, expansion and settlement
        // still belong to Q8; each seed is anchored at the selected namespace's actual declaring owner.
        // The providing target's walk steps are checked from the consulted level (consultedSite, on whose chain they are
        // anchored); the member it provides is checked from the reader, at the frame's own site.
        private bool TryProvideCompleted(SummaryScope opening, Expr target, PendingReference pending,
            out List<AnchoredSeed> parts, out OpenProviderIdentity identity, ElaboratedPropertyScope? lookupScope = null,
            SummaryScope? consultedSite = null)
        {
            parts = [];
            identity = null!;
            var scope = lookupScope ?? opening.PropertyScope;
            var facts = scope.CompletedContext!.Facts;
            NoteView(facts);
            if (ElaboratedScopeLookup.ResolveOpenProvider(scope, target) is not { } selected)
                return false;
            var head = target.OpenTargetHead(out var steps);
            if (ElaboratedScopeLookup.ResolveOpenProviderHead(scope, head, out var declaring) is not { } resolved
                || CompletedStructureContext.For(resolved.Target, declaring) is not { } context)
                return false;
            var current = context.Key;
            foreach (var step in steps)
            {
                if (facts.Facts(current)?.Open.Target is not { } owner
                    || facts.Facts(owner)?.Body is not { } body
                    || ElaboratedScopeLookup.TryLookupPublicProperty(body, step) is null
                    || facts.Member(owner, step) is not { } member)
                    return false;
                AddPublishedCharge(facts, owner, step, consultedSite ?? opening, parts);
                current = member;
            }
            if (consultedSite is not null)
                for (var i = 0; i < parts.Count; i++)
                    parts[i] = parts[i] with { Site = consultedSite };
            if (facts.Facts(current)?.Open.Target is not { } provider
                || facts.Facts(provider)?.Body is not { } providerBody
                || ElaboratedScopeLookup.TryLookupPublicProperty(providerBody, pending.Head) is null
                || facts.Member(provider, pending.Head) is not { }) return false;
            var members = new List<string>(pending.Members.Count + 1) { pending.Head };
            members.AddRange(pending.Members);
            ChargePublishedPath(facts, provider, members, opening, parts, firstIsNamespace: true);
            identity = selected.Identity;
            return true;
        }

        private int ChargePublishedPath(StaticLookupFacts facts, StaticScopeKey declaration,
            IReadOnlyList<string> members, SummaryScope opening, List<AnchoredSeed> parts,
            bool firstIsNamespace = false)
        {
            var current = declaration;
            for (var i = 0; i < members.Count; i++)
            {
                var owner = i == 0 && firstIsNamespace ? current : facts.Facts(current)?.Receiver.Target;
                if (owner is null || facts.Facts(owner)?.Body is not { } body
                    || facts.Member(owner, members[i]) is not { } next)
                {
                    // Preserve the existing later-member miss law: the lexical fallback demands
                    // the reached receiver's VALUE, so its output requirement seed is charged.
                    if (i > 0 && facts.Facts(current)?.Body is { } reached)
                        parts.Add(AnchorPublishedSeed(facts,
                            PropertyDependencyGraphBuilder.GetAlgorithmSummary(reached, memos, facts.Context(current)).OutputSeed,
                            current.Parent, opening));
                    return i;
                }
                AddPublishedCharge(facts, owner, members[i], opening, parts);
                current = next;
            }
            return members.Count;
        }

        /// <summary>
        /// The members of a reference's target path walked while an open target is resolved
        /// (<see cref="OpenCrossingOf"/>): the navigation of <see cref="ChargePublishedPath"/>, each selected member
        /// reported in <paramref name="selected"/> and nothing charged here. A step that selects nothing reads no value
        /// in this mode (an <c>.Algorithm</c> link is the reference's own namespace).
        /// </summary>
        private static int SelectPublishedPath(StaticLookupFacts facts, StaticScopeKey declaration, IReadOnlyList<string> members,
            bool firstIsNamespace, List<(StaticScopeKey Key, string Name, StaticScopeKey Owner)> selected)
        {
            var current = declaration;
            for (var i = 0; i < members.Count; i++)
            {
                var owner = i == 0 && firstIsNamespace ? current : facts.Facts(current)?.Receiver.Target;
                if (owner is null || facts.Facts(owner)?.Body is null || facts.Member(owner, members[i]) is not { } next)
                    return i;
                selected.Add((next, members[i], owner));
                current = next;
            }
            return members.Count;
        }

        private void AddPublishedCharge(StaticLookupFacts facts, StaticScopeKey owner, string name,
            SummaryScope opening, List<AnchoredSeed> parts)
        {
            if (facts.Facts(owner)?.Body is { } body
                && PropertyDependencyGraphBuilder.GetAlgorithmSummary(body, memos, facts.Context(owner)).MemberSeeds.TryGetValue(name, out var seed))
                parts.Add(AnchorPublishedSeed(facts, memos.SharedMemo.ForNavigation(seed), owner.Parent, opening));
        }

        private AnchoredSeed AnchorPublishedSeed(StaticLookupFacts facts,
            PropertyDependencyGraphBuilder.SummarySeed seed, StaticScopeKey? declaring, SummaryScope opening)
        {
            var intervening = new List<StaticScopeKey>();
            for (var at = declaring; at is not null; at = at.Parent)
            {
                for (var level = opening; level is not null; level = level.Parent)
                    if (ReferenceEquals(level.PropertyScope.CompletedContext?.Key, at)
                        || at.Parent is null && level.Parent is null)
                    {
                        var anchors = memos.SharedMemo.AnchoredRequirements ??= [];
                        var cacheKey = (facts, facts.ViewVersion, seed, declaring, at);
                        if (anchors.TryGetValue(cacheKey, out var cached)) return new(cached, level);
                        foreach (var ownerKey in intervening)
                        {
                            var ownerBody = facts.Facts(ownerKey)!.Body!;
                            var ownerContext = facts.Context(ownerKey);
                            var ownerMemos = PropertyDependencyGraphBuilder.CreateWalkMemos(memos.SharedMemo, memos.Observations, ownerContext);
                            var ownerLevel = new PropertyDependencyGraphBuilder.LevelContext(ownerBody,
                                PropertyDependencyGraphBuilder.GetAlgorithmSummary(ownerBody, ownerMemos, ownerContext).MemberSeeds, ownerMemos);
                            // SEED PARTS: a seed with no visible name and no pending reference, here or in any part it holds,
                            // expands at a level without parameters to the same content (nothing to resolve, escape or
                            // qualify), and settling it at the prelude keeps that content too. It is carried through as it is:
                            // formerly every intervening level copied its whole width (navigated members of a library
                            // nested in parameterless blocks: depth × width per member).
                            var parameterNames = ownerLevel.ParameterNames;
                            if (_seedParts && parameterNames.Count == 0 && seed.OwnSetsHoldNoNamesOrReferences
                                && (seed.AbsorbedPartsWithoutFolding is not { Count: > 0 } parts
                                    || PartsSatisfy(parts, NoNamesOrReferences, shared.NameAndReferenceFreeParts)))
                                continue;
                            // QUALIFIED SEED PARTS: at a level that binds parameters such a seed expands to its content with
                            // the required names the level binds qualified with its owner, name by name, so the expansion is
                            // taken part by part: each part's is kept for the resolution (QualifiedAt), and the seed's width is
                            // never folded and copied per member (output rows reading K chained library members under their
                            // owner: K² / 2 names folded and qualified). Settling it at the prelude keeps that content too.
                            if (_seedParts && parameterNames.Count > 0 && seed.AbsorbedPartsWithoutFolding is { Count: > 0 } held
                                && seed.OwnSetsHoldNoNamesOrReferences
                                && PartsSatisfy(held, NoNamesOrReferences, shared.NameAndReferenceFreeParts)
                                && QualifiedAt(seed, held, ownerBody, parameterNames) is { } qualified)
                            {
                                seed = qualified;
                                continue;
                            }
                            // PATH PARTS: a seed whose parts carry pending references, each a reference every expansion keeps
                            // as it is, here and in every part (no visible name, no bare name the level could select as its
                            // own member), expands to its content with the names the level binds qualified, in the same
                            // order: it is carried through a level without parameters and qualified part by part at one
                            // with parameters, as above, instead of folded and copied per member. Not at a module root,
                            // whose prelude settlement drops the references.
                            if (_seedParts && _pathParts && !ownerBody.IsModuleRoot && seed.AbsorbedPartsWithoutFolding is { Count: > 0 } pathHeld
                                && seed.OwnSetsStayAtEveryExpansion
                                && PartsSatisfy(pathHeld, StayAtEveryExpansion, shared.ExpansionStableParts))
                            {
                                if (parameterNames.Count == 0)
                                {
                                    memos.Observations?.RecordSettlementPathPartAnchoring();
                                    continue;
                                }
                                // The seed itself is kept as a qualified part too: the member that holds this one holds
                                // the same copy, so the settlement of this seed kept for its reader is the part it reuses.
                                memos.SharedMemo.ObserveCancellation();
                                if (QualifiedPart(seed, ownerBody, parameterNames) is { } pathQualified)
                                {
                                    memos.Observations?.RecordSettlementPathPartAnchoring();
                                    seed = pathQualified;
                                    continue;
                                }
                            }
                            seed = PropertyDependencyGraphBuilder.ExpandAtLevel(seed, ownerLevel);
                            if (ownerBody.IsModuleRoot) seed = PropertyDependencyGraphBuilder.SettledAtPrelude(seed);
                        }
                        anchors.Add(cacheKey, seed);
                        return new(seed, level);
                    }
                if (facts.Facts(at)?.Body is not { } owner)
                    throw new InvalidOperationException("A completed requirement owner is unavailable.");
                intervening.Add(at);
            }
            throw new InvalidOperationException("A completed requirement has no shared lexical ancestor.");
        }

        /// <summary>
        /// The requirements of a seed relative to <paramref name="level"/>, resolved from there outward: its own
        /// requirements and the settlement of each reference it holds. The result is <paramref name="self"/>'s (see
        /// <see cref="Frame"/>). Member and branch contributions contain only expanded requirements and references.
        /// </summary>
        private IEnumerator<Frame> ResolveSeed(Frame self, PropertyDependencyGraphBuilder.SummarySeed seed, SummaryScope level,
            SummaryScope site, BoundOwnerSet? boundOwners)
        {
            // The seed's own requirements are the frame's result first (SeedRequirements); each reference it holds then adds
            // its settlement, accumulated on the frame as ResolvePublishedReference does.
            var (references, pathParts) = SeedRequirements(self, seed, level, site, boundOwners);
            foreach (PendingReference pending in references)
            {
                var settled = ReferenceFrame(pending, level, site, boundOwners);
                yield return settled;
                self.Result = sets.Union(self.Result, settled.Result);
            }

            if (pathParts is null)
            {
                if (self.PathPart)
                    KeepPathPart(self, seed, level, site, boundOwners);
                yield break;
            }

            // PATH PARTS: then each part the seed holds, in the order the fold would take its references, through the kept
            // settlement of that part at this level, from this site, under these bound owners, or its own frame. Small
            // flat deltas settle in place. A flat predecessor with many paths needs its own settlement too: each of its
            // sibling readers would otherwise pay a reference frame for every path it holds, even after the first reader.
            for (var i = 0; i < pathParts.Count; i++)
            {
                CheckWideWalkCancellation(i);
                var part = pathParts[i];
                if (TryKeptPathPart(self, part, level, site, boundOwners))
                    continue;
                if (part.AbsorbedPartsWithoutFolding is null
                    && (part.OwnPendingReferencesWithoutFolding?.Count ?? 0) <= PropertyDependencyGraphBuilder.SummarySeed.CopiedCompletedEntries)
                {
                    var landing = SummaryScope.NoOwnerLookup;
                    self.Result = sets.Union(self.Result, sets.From(level.ResolveRequirements(part.OwnRequiredNamesWithoutFolding ?? NoNames)
                        .Concat(site.ResolveRequirementsFromSite(part.OwnQualifiedParametersWithoutFolding ?? NoQualifiedParameters,
                            boundOwners, self, ref landing))));
                    self.NoteSiteLanding(landing);
                    if (part.OwnPendingReferencesWithoutFolding is { Count: > 0 } own)
                        foreach (PendingReference pending in own)
                        {
                            var inPlace = ReferenceFrame(pending, level, site, boundOwners);
                            yield return inPlace;
                            self.Result = sets.Union(self.Result, inPlace.Result);
                        }
                    continue;
                }

                var settled = PathPartFrame(part, level, site, boundOwners);
                yield return settled;
                self.Result = sets.Union(self.Result, settled.Result);
            }

            KeepPathPart(self, seed, level, site, boundOwners);
        }

        // ResolveSeed's first step: the requirements `seed` names itself become `self`'s result, with its site landing noted,
        // and the references it holds are returned for settlement, with the parts to settle one by one (PATH PARTS) when
        // they are not folded into the seed.
        private (IEnumerable<SummaryReference> References, IReadOnlyList<PropertyDependencyGraphBuilder.SummarySeed>? PathParts)
            SeedRequirements(Frame self, PropertyDependencyGraphBuilder.SummarySeed seed, SummaryScope level, SummaryScope site,
                BoundOwnerSet? boundOwners)
        {
            var landing = SummaryScope.NoOwnerLookup;
            IEnumerable<SummaryReference> references;
            IReadOnlyList<PropertyDependencyGraphBuilder.SummarySeed>? pathParts = null;
            if (TryPartUnion(self, seed, level, site, boundOwners, ref landing, out var partUnion))
            {
                // SEED PARTS: the parts hold required names (and, QUALIFIED SEED PARTS, owner-qualified requirements) only,
                // so the folded seed's pending references are this seed's own, and its names and owner-qualified parameters
                // are its own and its parts'. The parts' are resolved exactly as the folded ones would be, through their kept
                // sets (TryQualifiedPartUnion: each owner once): no copy of their width.
                var names = sets.From(level.ResolveRequirements(seed.OwnRequiredNamesWithoutFolding ?? NoNames)
                    .Concat(site.ResolveRequirementsFromSite(seed.OwnQualifiedParametersWithoutFolding ?? NoQualifiedParameters,
                        boundOwners, self, ref landing)));
                self.Result = sets.Union(names, partUnion);
                references = (IEnumerable<SummaryReference>?)seed.OwnPendingReferencesWithoutFolding ?? [];
            }
            else if (TakesPathParts(seed) is { } parts)
            {
                // PATH PARTS: the seed's own sets here; its parts are settled one by one after its own references
                // (ResolveSeed), each with everything it holds, as the folded seed's requirements and references would be.
                self.Result = sets.From(level.ResolveRequirements(seed.OwnRequiredNamesWithoutFolding ?? NoNames)
                    .Concat(site.ResolveRequirementsFromSite(seed.OwnQualifiedParametersWithoutFolding ?? NoQualifiedParameters,
                        boundOwners, self, ref landing)));
                // A copy: a nested settlement of this very seed (a cycle) may fold it in place, which writes its parts'
                // references into its own set while these are being settled. The parts' list itself is never changed.
                references = seed.OwnPendingReferencesWithoutFolding is { Count: > 0 } own ? [.. own] : [];
                pathParts = parts;
                memos.Observations?.RecordSettlementPathPartSeed();
            }
            else
            {
                self.Result = sets.From(level.ResolveRequirements(seed.RequiredAncestorOwnedParameterNames)
                    .Concat(site.ResolveRequirementsFromSite(seed.OwnerQualifiedParameters, boundOwners, self, ref landing)));
                references = seed.PendingReferences;
            }

            self.NoteSiteLanding(landing);
            return (references, pathParts);
        }

        private static readonly Func<PropertyDependencyGraphBuilder.SummarySeed, bool> StayAtEveryExpansion = static seed => seed.OwnSetsStayAtEveryExpansion;
        private static readonly Func<PropertyDependencyGraphBuilder.SummarySeed, bool> ReferencesBindNoOwners = static seed => seed.OwnReferencesBindNoOwners;
        private static readonly Func<PropertyDependencyGraphBuilder.SummarySeed, bool> HoldsNoReferences = static seed => seed.OwnSetsHoldNoReferences;

        /// <summary>
        /// PATH PARTS (November 2026; implementation only, no classification, requirement, diagnostic or Lean rule): the parts
        /// of a seed that holds parts carrying pending references, to be settled one by one instead of folded; null when the
        /// seed is folded and settled whole, as before. Folding unites the parts' sets into the seed's own — its own entries
        /// first, then each part's in the order it holds them, depth first, each part once — and the settlement then resolves
        /// every name and owner-qualified requirement on its own and settles each reference on its own, in that order. The
        /// result is the union of those settlements and the record the union of their records (landing, views, live reads,
        /// memberships, off-chain lookups). Settling the seed's own sets and references and then each part with everything it
        /// holds (ResolveSeed) takes the same requirements and the same references in the same order, and a reference the
        /// fold met twice is settled again under its exact key, which a completed settlement answers. Folding also NARROWS a
        /// reference written twice with different bound owners to the owners both carry; so the parts are settled one by one
        /// only when no reference of the seed or any part binds an owner of its own (then no write narrows one). The parts
        /// must carry a reference: a seed whose parts hold requirements only is decided by SEED PARTS and QUALIFIED SEED
        /// PARTS. Never during a component's equation discovery, whose direct walk records seeds as its edges, and never once
        /// the resolution has made an owner lookup off its site's chain (THE OFF-CHAIN GAP: the share's site-free entries can
        /// then depend on the order of settlements, which a kept part settlement would freeze).
        /// </summary>
        private IReadOnlyList<PropertyDependencyGraphBuilder.SummarySeed>? TakesPathParts(PropertyDependencyGraphBuilder.SummarySeed seed)
        {
            if (!_seedParts || !_pathParts || _collecting is not null || shared.SawOffChainLookup
                || seed.AbsorbedPartsWithoutFolding is not { Count: > 0 } parts || !seed.OwnReferencesBindNoOwners
                || PartsSatisfy(parts, HoldsNoReferences, shared.ReferenceFreeParts)
                || !PartsSatisfy(parts, ReferencesBindNoOwners, shared.UnboundReferenceParts))
                return null;
            return parts;
        }

        /// <summary>
        /// PATH PARTS: the frame that settles one part of a seed on its own (<see cref="ResolveSeed"/>, which takes the part's
        /// own parts one by one again where they qualify): charged and observed like every frame, keyed by nothing, so a
        /// partial result stays its enclosing settlement's, and kept when whole (<see cref="KeepPathPart"/>).
        /// </summary>
        private Frame PathPartFrame(PropertyDependencyGraphBuilder.SummarySeed part, SummaryScope level, SummaryScope site,
            BoundOwnerSet? boundOwners)
        {
            ChargeFrame();
            memos.Observations?.RecordRequiredAncestorSettlementFrame(part);
            memos.Observations?.RecordSettlementPathPartFrame();
            var frame = new Frame(memos.Observations) { PathPart = true };
            frame.Body = ResolveSeed(frame, part, level, site, boundOwners);
            return frame;
        }

        /// <summary>
        /// PATH PARTS: takes the kept settlement of <paramref name="part"/> at <paramref name="level"/> from
        /// <paramref name="site"/> under <paramref name="boundOwners"/> as part of <paramref name="self"/>'s: its result
        /// united and its record absorbed as from the frame that computed it (<see cref="Frame.AbsorbRecord"/>). That frame
        /// completed whole, consulted views that still stand and made no owner lookup off its site's chain while the
        /// resolution had made none, and either read no summary of a level in progress (the exact table) or read only
        /// summaries that still stand (the level's live settlements, which also replay those reads): computed again, it reads
        /// the same static facts, summaries and completed settlements (the share answers only whole results that hold from
        /// every site) and so has the same result and record. One unit of seed-part work.
        /// </summary>
        private bool TryKeptPathPart(Frame self, PropertyDependencyGraphBuilder.SummarySeed part, SummaryScope level,
            SummaryScope site, BoundOwnerSet? boundOwners)
        {
            if (shared.SawOffChainLookup)
                return false;
            var key = new SettlementShare.PathPartKey(part, level, site, boundOwners);
            if (!shared.PathParts.TryGetValue(key, out var kept))
            {
                // A kept LIVE settlement of the part (KeepPathPart), validated against the summaries it read since.
                if (!TryLiveSettlement(key.SeedKey, out kept))
                    return false;
            }
            else if (!kept.ViewsStand())
            {
                shared.PathParts.Remove(key);
                shared.PathPartWeight -= key.RetainedWeight(kept);
                return false;
            }

            ChargeSeedPartWork(1);
            memos.Observations?.RecordSettlementPathPartReuse();
            self.Result = sets.Union(self.Result, kept.Result);
            self.AbsorbRecord(kept, this);
            return true;
        }

        /// <summary>
        /// PATH PARTS: keeps <paramref name="frame"/>'s settlement of <paramref name="seed"/> — a part settled on its own, or a
        /// seed settled part by part — after the frame has absorbed its nested settlements. Keeping a result requires
        /// a whole settlement with consistent views and no off-chain lookup. An eligible live read goes to the
        /// revision-validated level store. Otherwise the resolution can keep it under its exact key while capacity permits.
        /// </summary>
        private void KeepPathPart(Frame frame, PropertyDependencyGraphBuilder.SummarySeed seed, SummaryScope level,
            SummaryScope site, BoundOwnerSet? boundOwners)
        {
            if (!_pathParts || _collecting is not null || shared.SawOffChainLookup || !frame.IsWhole || frame.LookedUpOffChain
                || frame.OldestReuse < frame.ComponentMark || _component.Count != frame.ComponentMark)
                return;
            var settled = frame.Complete();
            if (settled.InconsistentViews)
                return;
            if (settled.ReadLive)
            {
                // LIVE: read a summary of the level in progress. Kept, as a seed's settlement of the same content is, for the
                // rest of the level's solve while every summary it read stands (LiveSettlements), under the seed's own key,
                // when it names every summary it read and answers every site at the level; never in the exact table.
                if (settled.LiveReadsKnown && settled.AnswersEverySite(level))
                    KeepLiveSettlement(new SettlementShare.Key(seed, level, boundOwners), settled);
                return;
            }

            var key = new SettlementShare.PathPartKey(seed, level, site, boundOwners);
            var weight = key.RetainedWeight(settled);
            if (shared.PathParts.ContainsKey(key) || shared.PathPartWeight + weight > _residualCapacity)
                return;
            shared.PathParts.Add(key, settled);
            shared.PathPartWeight += weight;
            memos.Observations?.RecordSettlementPathPartKept(shared.PathPartWeight);
        }

        private static readonly string[] NoNames = [];
        private static readonly OwnerQualifiedParameter[] NoQualifiedParameters = [];
        private static readonly Func<PropertyDependencyGraphBuilder.SummarySeed, bool> RequiredNamesOnly = static seed => seed.OwnSetsHoldOnlyRequiredNames;
        private static readonly Func<PropertyDependencyGraphBuilder.SummarySeed, bool> NoNamesOrReferences = static seed => seed.OwnSetsHoldNoNamesOrReferences;

        private bool TryPartUnion(Frame self, PropertyDependencyGraphBuilder.SummarySeed seed, SummaryScope level, SummaryScope site,
            BoundOwnerSet? boundOwners, ref int landing, out RequirementSet result)
        {
            result = default;
            if (!_seedParts || seed.AbsorbedPartsWithoutFolding is not { Count: > 0 } parts)
                return false;
            if (!PartsSatisfy(parts, RequiredNamesOnly, shared.RequiredNameParts))
                return TryQualifiedPartUnion(self, parts, level, site, boundOwners, ref landing, out result);
            ChargeSeedPartWork(parts.Count);
            for (var i = 0; i < parts.Count; i++)
            {
                CheckWideWalkCancellation(i);
                if (PartRequirements(parts[i], level) is not { } requirements)
                    return false;
                result = sets.Union(result, requirements);
            }
            return true;
        }

        // SEED PARTS: whether every part of `parts`, and everything each holds by reference, satisfies `own`. Each part is
        // examined once per resolution (`memo`, the run's share), one unit of static work when it is first examined.
        private bool PartsSatisfy(IReadOnlyList<PropertyDependencyGraphBuilder.SummarySeed> parts,
            Func<PropertyDependencyGraphBuilder.SummarySeed, bool> own, Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool> memo)
        {
            ChargeSeedPartWork(parts.Count);
            for (var i = 0; i < parts.Count; i++)
            {
                CheckWideWalkCancellation(i);
                if (!PartSatisfies(parts[i], own, memo))
                    return false;
            }
            return true;
        }

        private bool PartSatisfies(PropertyDependencyGraphBuilder.SummarySeed root,
            Func<PropertyDependencyGraphBuilder.SummarySeed, bool> own, Dictionary<PropertyDependencyGraphBuilder.SummarySeed, bool> memo)
        {
            if (memo.TryGetValue(root, out var known))
                return known;
            // Post-order over the parts (they form no cycle), on the heap: a seed holds parts as deep as a member chain.
            var pending = new Stack<(PropertyDependencyGraphBuilder.SummarySeed Seed, bool PartsDone)>();
            pending.Push((root, false));
            var visited = 0;
            while (pending.TryPop(out var entry))
            {
                CheckWideWalkCancellation(visited++);
                var (seed, partsDone) = entry;
                if (memo.ContainsKey(seed))
                    continue;
                if (memo.Count >= _residualCapacity)
                    return false; // This optimization cannot certify the part within its retention bound.
                if (!partsDone)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    ChargeSeedPartWork(1);
                    if (!own(seed))
                    {
                        memo.Add(seed, false);
                        continue;
                    }

                    pending.Push((seed, true));
                    if (seed.AbsorbedPartsWithoutFolding is { } nested)
                    {
                        ChargeSeedPartWork(nested.Count);
                        for (var i = nested.Count - 1; i >= 0; i--)
                        {
                            CheckWideWalkCancellation(i);
                            if (!memo.ContainsKey(nested[i]))
                                pending.Push((nested[i], false));
                        }
                    }
                    continue;
                }

                var satisfied = true;
                if (seed.AbsorbedPartsWithoutFolding is { } children)
                    for (var i = 0; i < children.Count; i++)
                    {
                        CheckWideWalkCancellation(i);
                        if (!memo[children[i]])
                        {
                            satisfied = false;
                            break;
                        }
                    }
                memo.Add(seed, satisfied);
            }

            return memo[root];
        }

        // SEED PARTS: the canonical requirement set of a part that holds required names only (PartsSatisfy), with everything
        // it holds by reference, resolved at `level` as ResolveSeed resolves a seed's names: kept per part and level for the
        // whole resolution (the run's share). Building one charges its own names and the parts it unites, once.
        private RequirementSet? PartRequirements(PropertyDependencyGraphBuilder.SummarySeed root, SummaryScope level)
        {
            var memo = shared.SeedPartRequirements;
            if (memo.TryGetValue((root, level), out var known))
                return known;
            var pending = new Stack<(PropertyDependencyGraphBuilder.SummarySeed Seed, bool PartsDone)>();
            pending.Push((root, false));
            var visited = 0;
            while (pending.TryPop(out var entry))
            {
                CheckWideWalkCancellation(visited++);
                var (seed, partsDone) = entry;
                if (memo.ContainsKey((seed, level)))
                    continue;
                if (memo.Count >= _residualCapacity)
                    return null; // Use the ordinary folded settlement once the retained (part, level) table fills.
                if (!partsDone)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    pending.Push((seed, true));
                    if (seed.AbsorbedPartsWithoutFolding is { } nested)
                    {
                        ChargeSeedPartWork(nested.Count);
                        for (var i = nested.Count - 1; i >= 0; i--)
                        {
                            CheckWideWalkCancellation(i);
                            if (!memo.ContainsKey((nested[i], level)))
                                pending.Push((nested[i], false));
                        }
                    }
                    continue;
                }

                cancellationToken.ThrowIfCancellationRequested();
                var own = seed.OwnRequiredNamesWithoutFolding;
                var children = seed.AbsorbedPartsWithoutFolding;
                ChargeSeedPartWork((own?.Count ?? 0) + (children?.Count ?? 0));
                var result = own is { Count: > 0 } ? sets.From(level.ResolveRequirements(own)) : default;
                if (children is not null)
                    for (var i = 0; i < children.Count; i++)
                    {
                        CheckWideWalkCancellation(i);
                        result = sets.Union(result, memo[(children[i], level)]);
                    }
                memo.Add((seed, level), result);
            }

            return memo[(root, level)];
        }

        /// <summary>
        /// QUALIFIED SEED PARTS (November 2026; implementation only, no classification, requirement, diagnostic or Lean rule):
        /// the union of a seed's parts that hold owner-qualified requirements besides required names — no visible name, no
        /// pending reference, every requirement with its owner — resolved exactly as <see cref="ResolveSeed"/> resolves the
        /// folded seed's (<see cref="SeedRequirements"/>). The parts' required names are resolved at
        /// <paramref name="level"/> through the kept sets of SEED PARTS (<see cref="PartRequirements"/>). Each owner the
        /// parts qualify requirements with is looked up ONCE from <paramref name="site"/>, as
        /// <c>SummaryScope.TryResolveRequirement</c> looks it up for each of them: its bound-owner membership is read and
        /// noted; a bound owner discharges every requirement qualified with it; otherwise the level of the site's chain whose
        /// algorithm it is gives the landing and, through the kept set of each part and that level
        /// (<see cref="QualifiedRequirements"/>), the requirements, each at the scope that binds it there; and an owner on no
        /// level of that chain charges nothing and is noted off-chain. The folded settlement read the same memberships with
        /// the same answers (one read per requirement), landed at the same levels and made the same off-chain lookups, so
        /// the result and the record are the same, and only the per-requirement repetitions are gone: K readers of a chain
        /// whose member i holds i requirements of one owner read it K² / 2 times. False, with nothing noted on
        /// <paramref name="self"/>, when a part holds a name, a path or a requirement without an owner, when the parts
        /// qualify with more owners than a footprint records, or when a kept table has no room: the caller then folds the
        /// seed and settles it whole, as before.
        /// </summary>
        private bool TryQualifiedPartUnion(Frame self, IReadOnlyList<PropertyDependencyGraphBuilder.SummarySeed> parts,
            SummaryScope level, SummaryScope site, BoundOwnerSet? boundOwners, ref int landing, out RequirementSet result)
        {
            result = default;
            if (!PartsSatisfy(parts, NoNamesOrReferences, shared.NameAndReferenceFreeParts))
                return false;
            ChargeSeedPartWork(parts.Count);
            var owners = NoOwners;
            for (var i = 0; i < parts.Count; i++)
            {
                CheckWideWalkCancellation(i);
                if (PartOwners(parts[i]) is not { } partOwners || MergeOwners(owners, partOwners) is not { } merged)
                    return false;
                owners = merged;
            }

            // Each owner's outcome from the site, decided before anything is noted on the frame.
            ChargeSeedPartWork(owners.Length);
            var outcomes = new (Algorithm Owner, bool Bound, SummaryScope? Level)[owners.Length];
            for (var j = 0; j < owners.Length; j++)
            {
                var bound = boundOwners?.Contains(owners[j]) == true;
                var ownerLevel = bound ? null : site.OwnerLevel(owners[j]);
                if (!bound)
                    ChargeSeedPartWork(site.Depth - (ownerLevel?.Depth ?? 0) + 1L);
                outcomes[j] = (owners[j], bound, ownerLevel);
            }

            for (var i = 0; i < parts.Count; i++)
            {
                CheckWideWalkCancellation(i);
                if (PartRequirements(parts[i], level) is not { } names)
                    return false;
                result = sets.Union(result, names);
                var partOwners = shared.PartOwners[parts[i]]!;
                foreach (var (owner, _, ownerLevel) in outcomes)
                {
                    if (ownerLevel is null || !HoldsOwner(partOwners, owner))
                        continue;
                    if (QualifiedRequirements(parts[i], ownerLevel) is not { } qualified)
                        return false;
                    result = sets.Union(result, qualified);
                }
            }

            foreach (var (owner, bound, ownerLevel) in outcomes)
            {
                self.NoteMembership(owner, bound);
                if (bound)
                    continue;
                if (ownerLevel is null)
                    self.NoteOwnerOffChain();
                else
                    landing = Math.Max(landing, ownerLevel.Depth);
            }

            memos.Observations?.RecordSettlementQualifiedPartOwnerLookups(outcomes.Length);
            return true;
        }

        private static readonly Algorithm[] NoOwners = [];

        // Membership by reference: an owner is an algorithm, whose generated record equality compares content.
        private static bool HoldsOwner(IReadOnlyList<Algorithm> owners, Algorithm owner)
        {
            for (var i = 0; i < owners.Count; i++)
                if (ReferenceEquals(owners[i], owner))
                    return true;
            return false;
        }

        // `owners` with every owner of `more` it lacks appended: `owners` itself (or `more`, when `owners` is empty) when
        // nothing is added; null past what a footprint records (SettlementShare.MaxFootprint).
        private static Algorithm[]? MergeOwners(Algorithm[] owners, IReadOnlyList<Algorithm> more)
        {
            if (owners.Length == 0 && more is Algorithm[] { Length: <= SettlementShare.MaxFootprint } whole)
                return whole;
            List<Algorithm>? merged = null;
            for (var i = 0; i < more.Count; i++)
                if (!HoldsOwner(owners, more[i]) && (merged is null || !HoldsOwner(merged, more[i])))
                    (merged ??= [.. owners]).Add(more[i]);
            if (merged is null)
                return owners;
            return merged.Count > SettlementShare.MaxFootprint ? null : [.. merged];
        }

        // QUALIFIED SEED PARTS: the owners the owner-qualified requirements of a part and everything it holds carry, each once
        // (SettlementShare.PartOwners), kept per part for the resolution, in post-order on the heap; null when one has no owner
        // or there are more than a footprint records, or when the table has no room. Building one charges its own
        // requirements and the parts it holds, once.
        private Algorithm[]? PartOwners(PropertyDependencyGraphBuilder.SummarySeed root)
        {
            var memo = shared.PartOwners;
            if (memo.TryGetValue(root, out var known))
                return known;
            var pending = new Stack<(PropertyDependencyGraphBuilder.SummarySeed Seed, bool PartsDone)>();
            pending.Push((root, false));
            var visited = 0;
            while (pending.TryPop(out var entry))
            {
                CheckWideWalkCancellation(visited++);
                var (seed, partsDone) = entry;
                if (memo.ContainsKey(seed))
                    continue;
                if (memo.Count >= _residualCapacity)
                    return null;
                if (!partsDone)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    pending.Push((seed, true));
                    if (seed.AbsorbedPartsWithoutFolding is { } nested)
                    {
                        ChargeSeedPartWork(nested.Count);
                        for (var i = nested.Count - 1; i >= 0; i--)
                        {
                            CheckWideWalkCancellation(i);
                            if (!memo.ContainsKey(nested[i]))
                                pending.Push((nested[i], false));
                        }
                    }
                    continue;
                }

                cancellationToken.ThrowIfCancellationRequested();
                var own = seed.OwnQualifiedParametersWithoutFolding;
                var children = seed.AbsorbedPartsWithoutFolding;
                ChargeSeedPartWork(1);
                Algorithm[]? owners = NoOwners;
                var inspected = 0;
                while (children is not null && owners is not null && inspected < children.Count)
                {
                    CheckWideWalkCancellation(inspected);
                    owners = memo[children[inspected++]] is { } childOwners ? MergeOwners(owners, childOwners) : null;
                }
                if (own is { Count: > 0 } && owners is not null)
                {
                    List<Algorithm>? added = null;
                    var index = 0;
                    foreach (var parameter in own)
                    {
                        CheckWideWalkCancellation(index++);
                        if (parameter.Owner is not { } owner)
                        {
                            owners = null;
                            break;
                        }
                        if (HoldsOwner(owners, owner) || added is not null && HoldsOwner(added, owner))
                            continue;
                        if (owners.Length + (added?.Count ?? 0) == SettlementShare.MaxFootprint)
                        {
                            owners = null;
                            break;
                        }
                        (added ??= []).Add(owner);
                    }
                    if (owners is not null && added is not null)
                        owners = MergeOwners(owners, added);
                    inspected += index;
                }
                ChargeSeedPartWork(inspected);
                memo.Add(seed, owners);
            }

            return memo[root];
        }

        // QUALIFIED SEED PARTS: the canonical set of the requirements a part and everything it holds qualify with the
        // algorithm of `ownerLevel`, a level of a site's chain, each at the scope that binds it there (SummaryScope.BindingScope,
        // as TryResolveRequirement resolves it), kept per part and level for the resolution (the run's share), in post-order
        // on the heap. A part whose kept owners (PartOwners, computed first) lack that algorithm is not visited. Building one
        // charges its own requirements and the parts it unites, once; null when the table has no room.
        private RequirementSet? QualifiedRequirements(PropertyDependencyGraphBuilder.SummarySeed root, SummaryScope ownerLevel)
        {
            var owner = ownerLevel.Algorithm ?? throw new InvalidOperationException("An owner level has its algorithm.");
            var memo = shared.QualifiedPartRequirements;
            if (memo.TryGetValue((root, ownerLevel), out var known))
                return known;
            var owners = shared.PartOwners;
            var pending = new Stack<(PropertyDependencyGraphBuilder.SummarySeed Seed, bool PartsDone)>();
            pending.Push((root, false));
            var visited = 0;
            while (pending.TryPop(out var entry))
            {
                CheckWideWalkCancellation(visited++);
                var (seed, partsDone) = entry;
                if (memo.ContainsKey((seed, ownerLevel)))
                    continue;
                if (memo.Count >= _residualCapacity)
                    return null;
                if (!partsDone)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    pending.Push((seed, true));
                    if (seed.AbsorbedPartsWithoutFolding is { } nested)
                    {
                        ChargeSeedPartWork(nested.Count);
                        for (var i = nested.Count - 1; i >= 0; i--)
                        {
                            CheckWideWalkCancellation(i);
                            if (HoldsOwner(owners[nested[i]]!, owner) && !memo.ContainsKey((nested[i], ownerLevel)))
                                pending.Push((nested[i], false));
                        }
                    }
                    continue;
                }

                cancellationToken.ThrowIfCancellationRequested();
                var own = seed.OwnQualifiedParametersWithoutFolding;
                var children = seed.AbsorbedPartsWithoutFolding;
                ChargeSeedPartWork((own?.Count ?? 0) + (children?.Count ?? 0));
                var result = default(RequirementSet);
                if (own is { Count: > 0 })
                {
                    List<Requirement>? requirements = null;
                    var index = 0;
                    foreach (var parameter in own)
                    {
                        CheckWideWalkCancellation(index++);
                        if (ReferenceEquals(parameter.Owner, owner))
                        {
                            (requirements ??= []).Add(new Requirement(parameter.Name, SummaryScope.BindingScope(ownerLevel, parameter.Name)));
                            if (requirements.Count == 256)
                            {
                                result = sets.Union(result, sets.From(requirements));
                                requirements.Clear();
                            }
                        }
                    }
                    if (requirements is { Count: > 0 })
                        result = sets.Union(result, sets.From(requirements));
                }
                for (var i = 0; children is not null && i < children.Count; i++)
                {
                    CheckWideWalkCancellation(i);
                    if (HoldsOwner(owners[children[i]]!, owner))
                        result = sets.Union(result, memo[(children[i], ownerLevel)]);
                }
                memo.Add((seed, ownerLevel), result);
            }

            return memo[(root, ownerLevel)];
        }

        /// <summary>
        /// QUALIFIED SEED PARTS (November 2026; implementation only, <see cref="AnchorPublishedSeed"/>): the expansion of
        /// <paramref name="seed"/> at an intervening level whose algorithm <paramref name="owner"/> binds
        /// <paramref name="parameterNames"/>, for a seed whose own sets and parts hold no visible name and no pending
        /// reference. Such an expansion only copies the content and qualifies the required names the level binds with
        /// <paramref name="owner"/>, name by name (<see cref="PropertyDependencyGraphBuilder.ExpandAtLevel"/>), so it is
        /// taken part by part: the seed's own names are qualified, and each part is replaced by its own expansion
        /// (<see cref="QualifiedPart"/>), kept for the resolution. Formerly the seed was folded, copying its whole width,
        /// and every name was qualified once per anchored member: output rows reading K chained library members under
        /// their owner folded and qualified K² / 2 names. The seed itself when the level binds none of its names; null
        /// when the kept table has no room (the caller expands the seed as before).
        /// </summary>
        private PropertyDependencyGraphBuilder.SummarySeed? QualifiedAt(PropertyDependencyGraphBuilder.SummarySeed seed,
            IReadOnlyList<PropertyDependencyGraphBuilder.SummarySeed> parts, Algorithm owner, IReadOnlySet<string> parameterNames)
        {
            // The expansion's own cancellation checkpoint (ExpandAtLevel observes one on entry).
            memos.SharedMemo.ObserveCancellation();
            ChargeSeedPartWork(parts.Count);
            for (var i = 0; i < parts.Count; i++)
            {
                CheckWideWalkCancellation(i);
                if (QualifiedPart(parts[i], owner, parameterNames) is null)
                    return null;
            }
            return QualifyWithCompletedChildren(seed, owner, parameterNames, retain: false);
        }

        // QUALIFIED SEED PARTS: a completed part that holds no visible name and no pending reference (PATH PARTS: or only
        // references every expansion keeps as they are), here or in any part it holds, as the expansion at the level of
        // `owner` (binding `parameterNames`) makes it: a copy of its own sets with the names the level binds qualified, holding
        // the same expansion of each of its parts by reference; the part itself when the level binds none of its names, here
        // or below. Kept per part, owner and parameter set for the resolution (the run's share), in post-order on the heap. A
        // new copy also retains its own requirements, references and child references.
        private PropertyDependencyGraphBuilder.SummarySeed? QualifiedPart(PropertyDependencyGraphBuilder.SummarySeed root,
            Algorithm owner, IReadOnlySet<string> parameterNames)
        {
            var memo = shared.QualifiedParts;
            if (memo.TryGetValue((root, owner, parameterNames), out var known))
                return known;
            var pending = new Stack<(PropertyDependencyGraphBuilder.SummarySeed Seed, bool PartsDone)>();
            pending.Push((root, false));
            var visited = 0;
            while (pending.TryPop(out var entry))
            {
                CheckWideWalkCancellation(visited++);
                var (seed, partsDone) = entry;
                if (memo.ContainsKey((seed, owner, parameterNames)))
                    continue;
                if (shared.QualifiedPartWeight >= _residualCapacity)
                    return null;
                if (!partsDone)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    pending.Push((seed, true));
                    if (seed.AbsorbedPartsWithoutFolding is { } nested)
                    {
                        ChargeSeedPartWork(nested.Count);
                        for (var i = nested.Count - 1; i >= 0; i--)
                        {
                            CheckWideWalkCancellation(i);
                            if (!memo.ContainsKey((nested[i], owner, parameterNames)))
                                pending.Push((nested[i], false));
                        }
                    }
                    continue;
                }

                cancellationToken.ThrowIfCancellationRequested();
                if (QualifyWithCompletedChildren(seed, owner, parameterNames, retain: true) is not { } qualified)
                    return null;
                memo.Add((seed, owner, parameterNames), qualified);
            }

            return memo[(root, owner, parameterNames)];
        }

        // The children have already been qualified. Charge the smaller name set even on a disjoint intersection.
        // Reserve the retained weight before allocating the copied sets or their list and index of child references.
        private PropertyDependencyGraphBuilder.SummarySeed? QualifyWithCompletedChildren(
            PropertyDependencyGraphBuilder.SummarySeed seed, Algorithm owner, IReadOnlySet<string> parameterNames, bool retain)
        {
            var children = seed.AbsorbedPartsWithoutFolding;
            ChargeSeedPartWork(1L + Math.Min(seed.OwnRequiredNamesWithoutFolding?.Count ?? 0, parameterNames.Count));
            var names = seed.SharedOwnNames(parameterNames, memos.Observations, cancellationToken);
            var copy = names is { Count: > 0 };
            var parts = shared.QualifiedParts;
            if (!copy && children is not null)
            {
                var inspected = 0;
                while (inspected < children.Count && !copy)
                {
                    CheckWideWalkCancellation(inspected);
                    var child = children[inspected++];
                    copy = !ReferenceEquals(child, parts[(child, owner, parameterNames)]);
                }
                ChargeSeedPartWork(inspected);
            }
            // A copy retains its own requirements, the references a path part carries (PATH PARTS) and its child references.
            var copiedEntries = copy
                ? (long)seed.OwnRequirementCount + (seed.OwnPendingReferencesWithoutFolding?.Count ?? 0) + (children?.Count ?? 0)
                : 0;
            if (retain)
            {
                if (shared.QualifiedPartWeight + 1 + copiedEntries > _residualCapacity)
                    return null;
                shared.QualifiedPartWeight += 1 + copiedEntries;
            }
            if (!copy)
                return seed;
            ChargeSeedPartWork(copiedEntries);
            var qualified = seed.QualifiedOwnSets(owner, names, cancellationToken);
            for (var i = 0; children is not null && i < children.Count; i++)
            {
                CheckWideWalkCancellation(i);
                qualified.AbsorbReference(parts[(children[i], owner, parameterNames)]);
            }
            if (retain)
                memos.Observations?.RecordSettlementQualifiedPartCopy();
            return qualified;
        }

        // Charge a part's classification, edge scans, and the inputs of each requirement set built.
        private void ChargeSeedPartWork(long units)
        {
            ledger?.Work(units, cancellationToken);
            memos.Observations?.RecordSettlementSeedPartWork(units);
        }

        /// <summary>
        /// Settlement of a BARE visible name the scope-free summary walk could not reduce
        /// further: the same rule as a member-less pending reference — the
        /// name as a property of the level's chain first (its stored summary), and only then
        /// the level's and its ancestors' <c>open</c> providers, whose provided member charges
        /// its own requirements. A name provided by nothing (an unresolvable name, or one the
        /// prelude declares) contributes no requirement. The name is one a hoisted deconstruction
        /// source's raw rows write at this resolution's level, so its reference is anchored at that
        /// level's completed context.
        /// </summary>
        public RequirementSet ResolveVisibleName(string name, SummaryScope level)
        {
            if (TryLookupSummary(level, name, out _, out _, out var summary))
                return sets.Adopt(summary);

            return Run(ReferenceFrame(new PendingReference(name, [], origin: memos.CompletedContext), level, site: null, boundOwners: null));
        }
    }

    private static Algorithm ProcessConditionalAlgorithm(
        Algorithm.Conditional algorithm,
        ExposureWalkMemos memos,
        CompletedStructureContext? completedContext = null)
    {
        FrontEndStack.Ensure();
        // Family-owned opens exist in host trees only (parsed families own none; the branch
        // bodies own theirs). They are a lookup level of their own for the branch bodies, and
        // they are rewritten like any open list: an open target's nested algorithms classify
        // under the one rule exactly like every other body, in the region the family's own
        // level enters them at (OpenTargetRegion).
        var lookupFamily = ElaboratedScopeLookup.CreateScope(algorithm, memos.Scope.PropertyScope, completedContext: completedContext);
        var rewrittenOpens = RewriteExprList(
            algorithm.Opens,
            new ExposureWalkMemos(memos.SummaryMemo, memos.Observations, OpenTargetRegion(memos.Scope, lookupFamily, memos.Run), memos.Run));

        var rewrittenBranches = new List<CondBranch>(algorithm.Branches.Count);
        // Settled on the family's first deferred branch and handed to every one of them (one canonical set).
        RequirementSet? provisionalContribution = null;
        foreach (var branch in algorithm.Branches)
        {
            var branchMemos = memos.ForBranch(algorithm, branch.Pattern);

            if (branch.Body.DeferredRegion is { } region)
            {
                // B2c: a deferred module region is not materialized eagerly (its provisional
                // body is never evaluated; the FAMILY's classification reads the
                // provisional body through the summary channel above: its captures, and the
                // forwardings implicit-argument resolution made in it as if its modules were
                // empty, ImplicitArgumentResolver.ResolveProvisionalBranch). This pass's
                // output view of the placeholder carries the region forked with the summary
                // chain at the branch — the tree's final region, complete with every earlier
                // context and the recorded validation bindings — and with what the family
                // charged its enclosing declarations, which the materialized body is held to.
                provisionalContribution ??= ProvisionalFamilyContribution(algorithm, memos);
                rewrittenBranches.Add(branch with
                {
                    Body = branch.Body with
                    {
                        DeferredRegion = region.WithExposure(new DeferredBranchContext(branchMemos.Scope, provisionalContribution.Value)),
                    },
                });
                continue;
            }

            // A branch body is processed exactly like any nested body under the one
            // classification rule (ClassifyDeclaredProperty): its pattern binders are inputs
            // only the family's call binds and arrive as Expr.Param references the body does
            // not own, so a declaration that depends on one is local-only for the same reason
            // a parameter-capturing declaration is, while a self-contained one is Exported —
            // openable, dot-accessible, and hand-out-able within the branch, and unreachable
            // by name from outside it because the family exposes no structural members.
            // Bodies are reference-deduplicated within equivalent branch regions (M4).
            // An ordinary property body or a different binder/open context has different
            // owner positions and is classified separately.
            var rewrittenBody = ProcessSharedNestedAlgorithm(branch.Body, branchMemos,
                CompletedStructureContext.For(branch.Body, lookupFamily, branch.Pattern));

            rewrittenBranches.Add(branch with { Body = rewrittenBody });
        }

        return algorithm with
        {
            Opens = rewrittenOpens,
            Branches = rewrittenBranches,
        };
    }

    /// <summary>
    /// The exposure context of one deferred module region (B2c): the final summary chain the
    /// eager walk held at the branch (<paramref name="Scope"/>), so the demand-time run classifies the resolved body
    /// under the same ancestor facts, and the FAMILY'S PROVISIONAL CONTRIBUTION
    /// (<paramref name="FamilyContribution"/>, see <see cref="ProvisionalFamilyContribution"/>): what the family, with
    /// this branch's provisional body, charged the declarations around it. The contribution is one canonical set of
    /// the eager run's interner, shared by every deferred branch of the family and never copied per region.
    /// </summary>
    internal sealed record DeferredBranchContext(SummaryScope Scope, RequirementSet FamilyContribution);

    /// <summary>
    /// THE FAMILY'S PROVISIONAL CONTRIBUTION (audit of 2026-11-14 § 1.2; owner decisions 2026-11-15, option (C)
    /// "refuse at load", and 2026-11-16, "resolve the provisional body"). Exposure classifies a family, and every
    /// zero-argument property that reads it, from the union of its branches' summaries
    /// (<c>PropertyDependencyGraphBuilder.CollectSummarySeed</c> of a conditional), and a load-bearing branch
    /// contributes its PROVISIONAL body there, before its module exists: the body as detection and implicit-argument
    /// resolution elaborated it with its on-demand modules treated as empty
    /// (<c>ImplicitArgumentResolver.ResolveProvisionalBranch</c>), so it holds every written parameter read and every
    /// formula lift and bare forwarding to a callable those modules do not decide. This is that
    /// union, read from the resolution's summary memo (the enclosing level's equations already computed it: no
    /// second summary walk) and SETTLED at the level the family is written in, <paramref name="memos"/>' scope, whose
    /// summaries are final: owner-qualified requirements (<see cref="Requirement"/>: a name and the scope that binds
    /// it, by reference) of the owners at and above that level. It is exactly what decides the enclosing
    /// declarations' exposure: <see cref="ClassifyDeclaredProperty"/> reads nothing but a property's settled
    /// requirement set, and that set is its value's seed settled the same way — the seed's required
    /// ancestor-owned names and owner-qualified parameters, and the settlement
    /// of every reference that escapes the family (<c>PendingResolution.ResolveSeed</c>).
    /// <para>A materialized branch may require nothing of an enclosing owner beyond this set
    /// (<see cref="UnchargedByFamily"/>). The classification itself is never revised: it is static, decided before
    /// evaluation, and independent of which branches a run selects.</para>
    /// </summary>
    private static RequirementSet ProvisionalFamilyContribution(Algorithm.Conditional family, ExposureWalkMemos memos)
    {
        var level = memos.Scope;
        var walkMemos = ContributionWalkMemos(level, memos.SummaryMemo, memos.Observations);
        return new PendingResolution(walkMemos, memos.Run.Requirements, level, memos.Run.Settlements,
                memos.Run.SettlementLedger, memos.Run.CancellationToken)
            .ResolveContribution(PropertyDependencyGraphBuilder.GetAlgorithmSummary(family, walkMemos).OutputSeed.Clone(), level);
    }

    // The walk memos of a contribution settled at a level: that level's completed context (a family-owned level of a
    // host tree may hold none of its own; its nearest enclosing level's stands for it).
    private static PropertyDependencyGraphBuilder.SummaryWalkMemos ContributionWalkMemos(
        SummaryScope level, PropertyDependencyGraphBuilder.SummaryMemo summaryMemo, FrontEndTraversalObservations? observations)
    {
        for (var at = level; at is not null; at = at.Parent)
            if (at.PropertyScope.CompletedContext is { } context)
                return PropertyDependencyGraphBuilder.CreateWalkMemos(summaryMemo, observations, context);
        throw new InvalidOperationException("Internal error: a deferred branch's family has no completed structural context.");
    }

    /// <summary>
    /// One materialization's question and its answer: the branch pattern and eager context the materialized body is
    /// judged under, and the requirements it contributes that its family never charged (<see cref="UnchargedByFamily"/>).
    /// </summary>
    private sealed class DeferredBranchCheck(DeferredBranchContext context, Pattern pattern)
    {
        public DeferredBranchContext Context => context;
        public Pattern Pattern => pattern;
        public IReadOnlyList<Requirement> Uncharged = [];
    }

    /// <summary>
    /// REFUSE AT LOAD (owner decisions 2026-11-15 and 2026-11-16): the requirements the MATERIALIZED body of a deferred branch
    /// contributes to its family that the family's provisional contribution did not hold; empty for a body the
    /// eager classification already accounts for. The body's contribution is the one the family's own walk would
    /// compute for it (<c>PropertyDependencyGraphBuilder.BranchBodyContribution</c>: the resolved body under the
    /// branch pattern's binders, through this run's summary memo), settled at the level the family is written in
    /// exactly as <see cref="ProvisionalFamilyContribution"/> settled the family's, and compared by owner-qualified
    /// identity (<c>PropertyDependencyGraphBuilder.UnchargedRequirements</c>). The eager chain's scopes are the
    /// very objects both runs resolve owners to, so a requirement is the same element in both sets.
    /// <para>A non-empty answer means the loaded modules made the selected branch require an enclosing binding that
    /// no declaration around the family was charged for (a member of a loaded module that formula lifting or bare
    /// forwarding hands the binding, directly or through a declaration of the branch): an enclosing property
    /// classified <see cref="PropertyExposure.Exported"/> would be accessible outside the required activation.
    /// Every forwarding the modules do not decide is in the provisional contribution already, so the comparison is the
    /// whole decision: the materialization is refused
    /// (<see cref="DiagnosticCode.DeferredBranchForwardsEnclosingParameter"/>, <c>DeferredModuleRegion</c>) exactly when
    /// the answer is non-empty, with no question about which callee received the binding.</para>
    /// </summary>
    private static IReadOnlyList<Requirement> UnchargedByFamily(Algorithm resolvedBody, DeferredBranchCheck deferred,
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo, FrontEndTraversalObservations? observations, ExposureRun run)
    {
        var branch = deferred.Context.Scope;
        var level = branch.Parent ?? throw new InvalidOperationException(
            "Internal error: a deferred branch's exposure context has no level its family is written in.");
        // The body's own level context, derived exactly as the walk above derived it (ProcessScopeBody).
        var bodyContext = CompletedStructureContext.For(resolvedBody, branch.PropertyScope)
            ?? throw new InvalidOperationException("Internal error: a materialized deferred branch has no completed structural context.");
        var contribution = PropertyDependencyGraphBuilder.BranchBodyContribution(
            resolvedBody, deferred.Pattern, summaryMemo, observations, bodyContext);
        var settled = new PendingResolution(ContributionWalkMemos(level, summaryMemo, observations), run.Requirements, level,
                run.Settlements, run.SettlementLedger, run.CancellationToken)
            .ResolveContribution(contribution, level);
        var uncharged = PropertyDependencyGraphBuilder.UnchargedRequirements(settled, deferred.Context.FamilyContribution, run.Requirements);
        if (uncharged.IsEmpty)
            return [];
        // Reported in a stable order: by name, then from the innermost owner outward.
        var missing = uncharged.Elements.ToList();
        missing.Sort((left, right) =>
        {
            var byName = StringComparer.Ordinal.Compare(left.Name, right.Name);
            return byName != 0 ? byName : level.OwnerDepth(left.Owner).CompareTo(level.OwnerDepth(right.Owner));
        });
        return missing;
    }

    /// <summary>
    /// Demand-time exposure classification of a deferred region's RESOLVED body — the
    /// ordinary body walk under the ONE rule (<see cref="ClassifyDeclaredProperty"/>) — and its
    /// comparison with the family's provisional contribution (<see cref="UnchargedByFamily"/>).
    /// <paramref name="uncharged"/> is empty for a body the eager classification accounts for;
    /// otherwise the caller refuses the materialization, and a refused body's unit is never frozen
    /// or published.
    /// </summary>
    internal static Algorithm ElaborateDeferredBranch(
        Algorithm resolvedBody,
        DeferredBranchContext context,
        Pattern pattern,
        out IReadOnlyList<Requirement> uncharged,
        FrontEndTraversalObservations? observations = null,
        ModuleUnits? modules = null,
        CancellationToken cancellationToken = default)
    {
        var check = new DeferredBranchCheck(context, pattern);
        var exposed = ResolveInScope(resolvedBody, context.Scope, observations, modules, structuralContext: null, sourceUnit: true,
            check, cancellationToken);
        uncharged = check.Uncharged;
        return exposed;
    }

    /// <summary>
    /// A call's argument bundle may be shared by several call edges — implicit lifting gives every
    /// lifted reference to one callable in a resolver region the same synthesized bundle (FE-2) —
    /// so it rewrites once per region and stays shared, exactly like a shared expression node:
    /// copying it per edge would rebuild the K × L representation the sharing removed.
    /// </summary>
    private static OutputBundle RewriteArgumentBundle(OutputBundle arguments, ExposureWalkMemos memos)
    {
        // A rewrite-invariant bundle is the same bundle in every region (FE-3).
        if (memos.Run.IsRewriteInvariant(arguments))
            return arguments;

        memos.ArgumentBundles ??= new(ReferenceEqualityComparer.Instance);
        if (memos.ArgumentBundles.TryGetValue(arguments, out var rewritten))
            return rewritten;

        memos.Observations?.RecordExposureArgumentBundleRewrite();
        rewritten = OutputBundle.From(RewriteExprList(arguments, memos));
        memos.ArgumentBundles[arguments] = rewritten;
        return rewritten;
    }

    private static List<Expr> RewriteExprList(IReadOnlyList<Expr> expressions, ExposureWalkMemos memos)
    {
        var rewritten = new List<Expr>(expressions.Count);
        foreach (var expression in expressions)
            rewritten.Add(RewriteExpr(expression, memos));

        return rewritten;
    }

    // Expression descent exists to reach nested algorithms — block literals and
    // call/dot-call argument bundles — so their properties receive exposure
    // classifications too. Outside those nested algorithm replacements, each
    // expression keeps the same shape and metadata.
    private static Expr RewriteExpr(Expr expr, ExposureWalkMemos memos)
    {
        FrontEndStack.Ensure();
        // DAG-safety: one rewrite per shared node reference per region; the memo returns
        // the same rewritten node for every later reach, preserving the input's sharing.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return RewriteExprCore(expr, memos);

        // A rewrite-invariant subtree is returned as it is: its copy would be content-identical,
        // and returning it keeps a shared subtree shared across regions (FE-3).
        if (memos.Run.IsRewriteInvariant(expr))
            return expr;

        memos.Rewrites ??= new(ReferenceEqualityComparer.Instance);
        if (memos.Rewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        memos.Observations?.RecordExposureRewriteExpansion();
        rewritten = RewriteExprCore(expr, memos);
        memos.Rewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr RewriteExprCore(Expr expr, ExposureWalkMemos memos)
    {
        return expr switch
        {
            // Defensive only — parameter detection strips every grace
            // before exposure resolution runs; `with` keeps the stored
            // grace facts for host-built trees.
            Expr.Grace grace => grace with { Inner = RewriteExpr(grace.Inner, memos) },

            Expr.Unary unary => unary with { Operand = RewriteExpr(unary.Operand, memos) },

            Expr.Binary binary => binary with
            {
                Left = RewriteExpr(binary.Left, memos),
                Right = RewriteExpr(binary.Right, memos),
            },

            Expr.Comparison comparison => comparison with
            {
                First = RewriteExpr(comparison.First, memos),
                Links = AstHelpers.RewriteComparisonLinks(comparison.Links, operand => RewriteExpr(operand, memos)),
            },

            Expr.Index index => index with
            {
                Target = RewriteExpr(index.Target, memos),
                Selectors = RewriteExprList(index.Selectors, memos),
            },

            Expr.SequenceSpread spread => spread with { Operand = RewriteExpr(spread.Operand, memos) },

            Expr.SequenceConstruct construct => construct with
            {
                Left = RewriteExpr(construct.Left, memos),
                Right = RewriteExpr(construct.Right, memos),
            },

            Expr.ListLiteral list => list with { Items = RewriteExprList(list.Items, memos) },

            // The sealed facts of an inherited inline block name this exact classified view and its members.
            Expr.AlgorithmExpr block when memos.Scope.Parent is null && !block.Algorithm.IsModuleRoot
                && block.Algorithm.CompletedStructure?.Facts.IsSealed == true
                && memos.Run.Modules.Registry?.StructuralContinuation?.HasClassifiedOpenBlock(block.Algorithm) == true => block,
            Expr.AlgorithmExpr block => block with { Algorithm = ProcessSharedNestedAlgorithm(block.Algorithm, memos) },

            // A capture owns no names and no properties, so its rows rewrite
            // with the same visible summaries — the exact effect the
            // pre-split transparent wrapper had through ProcessAlgorithm.
            Expr.Capture capture => capture with { Body = RewriteExprList(capture.Body, memos) },

            // Argument bundles own no scope: slots rewrite in the enclosing
            // context, exactly like capture rows.
            Expr.Call call => call with
            {
                Function = RewriteExpr(call.Function, memos),
                Args = RewriteArgumentBundle(call.Args, memos),
            },

            Expr.DotCall dotCall => RewriteDotCall(dotCall, memos),

            // Intentional leaves: no nested algorithm to reach, so the
            // expression keeps its exact shape and metadata.
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral
                or Expr.EmptySequence or Expr.NativeCall => expr,
        };
    }

    private static Expr RewriteDotCall(Expr.DotCall dotCall, ExposureWalkMemos memos)
    {
        // Diagnostic claims are finalized after the whole pass by the provenance
        // finalizer, against the classified tree.
        memos.Run.HasDotMemberOrigins |= dotCall.InferredFallbackProvenance is not null;

        var rewrittenTarget = RewriteExpr(dotCall.Target, memos);
        var rewrittenArgs = dotCall.Args is { } args ? RewriteArgumentBundle(args, memos) : null;

        // `with` keeps the stored dot-edge facts (member span, lexical fallback, the
        // detector's elaborated fallback selection) intact: exposure never changes
        // what a receiver resolves to, so the detector's verdict is final.
        return dotCall with
        {
            Target = rewrittenTarget,
            Args = rewrittenArgs,
        };
    }
}
