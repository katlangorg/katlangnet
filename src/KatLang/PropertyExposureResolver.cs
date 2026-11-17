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

            var owner = this;
            while (owner is not null && !ReferenceEquals(owner.Algorithm, requirement.Owner))
                owner = owner.Parent;
            landing = owner?.Depth ?? int.MaxValue;
            if (owner is null)
                return false;
            // The completed key names the branch binding region by its body. Runtime capture
            // positions retain the existing separate family-binding frame above that body.
            if (owner.PropertyScope.CompletedContext?.Key.BindingRegion is not null
                && !owner.Parameters.Contains(requirement.Name)
                && owner.Parent?.Parameters.Contains(requirement.Name) == true)
                owner = owner.Parent;
            resolved = new Requirement(requirement.Name, owner.PropertyScope);
            return true;
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
            return ResolveInScope(root, parent!, observations, modules, context, sourceUnit, cancellationToken);
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
        CancellationToken cancellationToken)
    {
        var run = new ExposureRun(observations, SettlementLedgerOf(CompletingUnit(root, structuralContext), sourceUnit),
            cancellationToken)
        {
            Modules = modules ?? new(),
        };
        run.SharedBodies = SharedBodyCensus.Of(root, cancellationToken);
        root = ProcessAlgorithm(root, parent,
            new PropertyDependencyGraphBuilder.SummaryMemo(observations) { SharedBodies = run.SharedBodies, CancellationToken = cancellationToken },
            observations, run, structuralContext);
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
        var rewrittenProperties = new List<Property>(algorithm.Properties.Count);
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
            rewrittenProperties.Add(rewrittenProperty);
        }

        var rewrittenOpens = RewriteExprList(
            algorithm.Opens,
            new ExposureWalkMemos(summaryMemo, observations, finalLevel.Root, run));
        var rewrittenOutput = RewriteExprList(algorithm.Output, memos);

        // The same variant back: a user's rewritten bundle, or an alias's one rewritten target row.
        return algorithm.WithOwnScopeBody(rewrittenOpens, rewrittenProperties, rewrittenOutput);
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
    /// summary it read is final, so no growth can reach it. A nested result that encountered any cycle
    /// cut is never cached. Every read from a reused computation remains in the enclosing top-level
    /// recording, so dependency validation and reader notification remain complete.</para>
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

        // One cached top-level settlement and the level-local summaries it read (name, set read).
        private sealed record Settlement(RequirementSet Result, (string Name, RequirementSet Read)[] Reads);

        public void Solve()
        {
            var properties = graph.Properties;
            var equationOf = new Dictionary<string, int>(StringComparer.Ordinal);
            for (var i = 0; i < properties.Count; i++)
                equationOf[properties[i].Name] = i;

            // Statically read equations: sibling edges, and level-local names a reference reads directly.
            IEnumerable<int> StaticReads(int index)
            {
                var node = graph[index];
                foreach (var dependencyIndex in node.SummarySiblingDependencyIndices)
                    yield return equationOf[properties[dependencyIndex].Name];
                foreach (var name in node.SummaryVisiblePropertyDependencyNames)
                    if (equationOf.TryGetValue(name, out var read))
                        yield return read;
                foreach (var pending in node.PendingReferences)
                    if (pending.Selection == PendingSelection.Lexical && equationOf.TryGetValue(pending.Head, out var read))
                        yield return read;
            }

            var queue = new Queue<int>();
            var queued = new bool[properties.Count];
            foreach (var index in DependencyFirstOrder.Of(properties.Count, i => equationOf[properties[i].Name] == i, StaticReads))
            {
                queue.Enqueue(index);
                queued[index] = true;
            }

            var readers = new Dictionary<string, HashSet<int>>(StringComparer.Ordinal);
            var reads = new List<string>();
            while (queue.TryDequeue(out var index))
            {
                queued[index] = false;
                observations?.RecordRequiredAncestorLevelEvaluation();
                FrontEndTraversalObservations.ObserveCancellation(
                    observations, FrontEndCancellationCheckpoint.ExposureLevelEvaluation, cancellationToken);
                reads.Clear();
                var next = Evaluate(index, reads);
                foreach (var readName in reads)
                {
                    if (!readers.TryGetValue(readName, out var nameReaders))
                        readers.Add(readName, nameReaders = []);
                    nameReaders.Add(index);
                }

                var name = properties[index].Name;
                if (next.Equals(summaries[name]))
                    continue;

                summaries[name] = next;
                if (!readers.TryGetValue(name, out var dependents))
                    continue;
                foreach (var dependent in dependents)
                {
                    observations?.RecordRequiredAncestorReaderNotification();
                    if (!queued[dependent])
                    {
                        queued[dependent] = true;
                        queue.Enqueue(dependent);
                    }
                }
            }
        }

        private RequirementSet Evaluate(int propertyIndex, List<string> reads)
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
                requirements = sets.Union(requirements, Settle(dependencyName, pending: null, reads));

            foreach (var dependencyIndex in node.SummarySiblingDependencyIndices)
            {
                var dependencyName = graph.Properties[dependencyIndex].Name;
                if (summaries.TryGetValue(dependencyName, out var summary))
                {
                    reads.Add(dependencyName);
                    requirements = sets.Union(requirements, summary);
                }
            }

            foreach (var pending in node.PendingReferences)
                requirements = sets.Union(requirements, Settle(pending.ContentKey, pending, reads));

            return requirements;
        }

        private RequirementSet Settle(string key, PendingReference? pending, List<string> reads)
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
                resolution.EndRecording();
                var read = new (string Name, RequirementSet Read)[levelReads.Count];
                var i = 0;
                foreach (var readName in levelReads)
                    read[i++] = (readName, summaries[readName]);
                settlements[key] = settlement = new Settlement(result, read);
            }

            foreach (var (readName, _) in settlement.Reads)
                reads.Add(readName);
            return settlement.Result;
        }

        private bool StillValid(Settlement settlement)
        {
            foreach (var (readName, read) in settlement.Reads)
            {
                if (!summaries[readName].Equals(read))
                    return false;
            }

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
    /// (EXPOSURE-OPEN-1), and partial results are kept nowhere. So a kept settlement answers any key of
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

        /// <summary><see cref="Content"/> is a pending reference's content key or a seed.</summary>
        internal readonly record struct Key(object Content, SummaryScope Level, BoundOwnerSet? Bound)
        {
            /// <summary>
            /// One unit per entry, plus one per 64 characters of combined content key and former bound-owner
            /// key length. This preserves admission, including when earlier lifted chains compete for space
            /// with later reusable settlements. Each owner contributes at least one character and each pair
            /// of adjacent owners contributes a separator, which bounds retained owner memberships.
            /// </summary>
            internal long Weight => 1 + (((Content as string)?.Length ?? 0) + (Bound?.LegacyKeyLength ?? 0)) / 64;
        }

        /// <summary>
        /// A completed settlement and what its computation depended on beyond its key: the deepest landing
        /// of its site lookups (<see cref="SummaryScope.NoOwnerLookup"/> when it made none), whether it read
        /// a summary of the level in progress, the fact views it consulted with the versions it read
        /// (<see cref="InconsistentViews"/>: it saw one view at two versions), and what it read of its bound
        /// owners (<see cref="Footprint"/>, <see cref="Emptiness"/>).
        /// </summary>
        internal sealed class Settled(RequirementSet result, int siteDepth, bool readLive,
            (StaticLookupFacts Facts, int Version)[] views, bool inconsistentViews,
            (Algorithm Owner, bool Present)[]? footprint = null, BoundOwnerEmptiness emptiness = BoundOwnerEmptiness.Unread,
            bool ownerOffChain = false)
        {
            public RequirementSet Result => result;
            public int SiteDepth => siteDepth;
            public bool ReadLive => readLive;
            public (StaticLookupFacts Facts, int Version)[] Views => views;
            public bool InconsistentViews => inconsistentViews;

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
                => !readLive && !inconsistentViews && siteDepth <= level.Depth;

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
        private long _retained;

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
            if (_mode == SettlementShareMode.Unshared)
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
            if (_mode == SettlementShareMode.Unshared)
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
                    if (candidates is null)
                        _candidates.Add((key.Content, key.Level), candidates = []);
                    candidates.Add((settled, weight));
                    _retained += weight;
                    observations?.RecordSettlementShareStore();
                    return;
                }
            }

            if (_retained + weight > capacity || !_entries.TryAdd(key, settled))
                return;
            _retained += weight;
            observations?.RecordSettlementShareStore();
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
        // Unlike anchoring, settlement reads live equations. A complete result that read one, or that depends
        // on its site, is reused only inside ONE synchronous Run; the run's share keeps the others.
        private readonly Dictionary<SettlementKey, SettlementShare.Settled> _completed = [];
        private readonly Dictionary<SeedSettlementKey, SettlementShare.Settled> _completedSeeds = [];
        private HashSet<string>? _levelReads;
        // The frame whose body is running: what it consults beyond its key is recorded on it (see Frame).
        private Frame? _running;

        /// <summary>Starts recording the level-in-progress summaries a top-level settlement reads.</summary>
        public HashSet<string> BeginRecording() => _levelReads = new HashSet<string>(StringComparer.Ordinal);

        public void EndRecording() => _levelReads = null;

        // The direct-chain property lookup, recording a read of the level-in-progress summary it returns.
        private bool TryLookupSummary(SummaryScope from, string name, out SummaryScope level, out PropertyLookupHit hit, out RequirementSet summary)
        {
            if (!from.TryLookup(name, out level, out hit, out summary))
                return false;
            if (ReferenceEquals(level, levelInProgress))
            {
                _levelReads?.Add(name);
                if (_running is { } frame)
                    frame.ReadLive = true;
            }

            return true;
        }

        // A completed-fact view the running frame consults: a shared settlement stands while each one it read does.
        private void NoteView(StaticLookupFacts facts) => _running?.NoteView(facts, facts.ViewVersion);

        /// <summary>The settlement of <paramref name="pending"/> at <paramref name="level"/> (a top-level settlement).</summary>
        public RequirementSet Resolve(PendingReference pending, SummaryScope level)
            => Run(ReferenceFrame(pending, level, site: null, boundOwners: null));

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
        /// nested frame (<see cref="Absorb(Frame)"/>) and every result it reused (<see cref="Reuse"/>), so a
        /// settlement never looks independent merely because what it depended on arrived through a cache.
        /// <see cref="Complete"/> is that record with the result.</para>
        /// </summary>
        private sealed class Frame(FrontEndTraversalObservations? observations) : ISettlementReader
        {
            public IEnumerator<Frame> Body = null!;
            public RequirementSet Result;
            public SettlementKey? CacheKey;
            public SeedSettlementKey? SeedCacheKey;

            /// <summary>The number of frames below this one on the run's stack (<see cref="Run"/>).</summary>
            public int Depth;

            /// <summary>
            /// The outermost settlement a cycle cut inside this one reached, as that frame's <see cref="Depth"/>;
            /// <see cref="int.MaxValue"/> when it saw none. A cut is a reference met again while its own settlement
            /// is in progress, and it contributes nothing where it is met. When every cut inside a settlement
            /// reached that settlement itself or one nested in it, each of them is settled inside it, so its union
            /// is whole (<see cref="IsWhole"/>): it is the settlement its key has as a top-level one. A cut that
            /// reached an ENCLOSING settlement leaves this one a partial union, which is kept nowhere
            /// (EXPOSURE-OPEN-1).
            /// </summary>
            public int OutermostCut = int.MaxValue;

            /// <summary>No cycle cut inside this settlement reached a settlement that began before it.</summary>
            public bool IsWhole => OutermostCut >= Depth;

            /// <summary>Set on a frame that computes a settlement the run's share may keep.</summary>
            public SettlementShare.Key? ShareKey;
            public bool ReadLive;

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
            private List<(StaticLookupFacts Facts, int Version)>? _views;

            /// <summary>
            /// The owners this frame's reference binds itself (<see cref="PendingReference.BoundOwners"/>): its bound
            /// owners are its enclosing frame's extended by them, so each of them is present whatever the enclosing
            /// frame's are. Null for a seed, an inner route frame and a reference that binds none.
            /// </summary>
            public IReadOnlyList<Algorithm>? OwnOwners;

            /// <summary>
            /// Set on the level's unbound open-walks settlement (C1): it runs with no bound owners whatever its
            /// enclosing frame's are, so nothing it read of them is a read of the enclosing frame's.
            /// </summary>
            public bool RunsUnbound;

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
                _views ??= [];
                foreach (var (known, seen) in _views)
                {
                    if (!ReferenceEquals(known, facts))
                        continue;
                    _inconsistentViews |= seen != version;
                    return;
                }

                _views.Add((facts, version));
            }

            public void Absorb(Frame nested)
            {
                OutermostCut = Math.Min(OutermostCut, nested.OutermostCut);
                NoteSiteLanding(nested.SiteDepth);
                ReadLive |= nested.ReadLive;
                _inconsistentViews |= nested._inconsistentViews;
                if (nested._views is { } views)
                    foreach (var (facts, version) in views)
                        NoteView(facts, version);
                _ownerOffChain |= nested.OwnerOffChain;
                if (!nested.RunsUnbound)
                    AbsorbFootprint(nested._footprint, nested._exactBoundOwners,
                        nested._emptiness, nested.OwnOwners);
            }

            /// <summary>
            /// Takes a completed settlement as this frame's result, with everything it depended on: its footprint's
            /// answers hold for this frame's bound owners, which are its exact ones or satisfy it.
            /// </summary>
            public void Reuse(SettlementShare.Settled settled)
            {
                Result = settled.Result;
                NoteSiteLanding(settled.SiteDepth);
                ReadLive |= settled.ReadLive;
                _inconsistentViews |= settled.InconsistentViews;
                foreach (var (facts, version) in settled.Views)
                    NoteView(facts, version);
                _ownerOffChain |= settled.OwnerOffChain;
                AbsorbFootprint(settled.Footprint, exact: settled.Footprint is null, settled.Emptiness, ownOwners: null);
            }

            public SettlementShare.Settled Complete()
                => new(Result, SiteDepth, ReadLive, _views is null ? [] : [.. _views], _inconsistentViews,
                    _exactBoundOwners ? null : _footprint is null ? [] : [.. _footprint], _emptiness, OwnerOffChain);

            /// <summary><see cref="SettlementShare.Settled.StandsFromEverySite"/> of what this frame has recorded so far.</summary>
            public bool StandsFromEverySite(SummaryScope level)
                => !ReadLive && !_inconsistentViews && SiteDepth <= level.Depth;
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
            var frames = new Stack<Frame>();
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
                        frame.Body.Current.Depth = frames.Count;
                        frames.Push(frame.Body.Current);
                        ObserveCancellation();
                    }
                    else
                    {
                        frames.Pop();
                        // A settlement a cycle cut left partial is kept nowhere (Frame.OutermostCut).
                        if (frame.IsWhole && (frame.CacheKey is not null || frame.SeedCacheKey is not null))
                        {
                            var settled = frame.Complete();
                            if (frame.CacheKey is { } key)
                                _completed.TryAdd(key, settled);
                            if (frame.SeedCacheKey is { } seedKey)
                                _completedSeeds.TryAdd(seedKey, settled);
                            if (frame.ShareKey is { } shareKey && settled.StandsFromEverySite(shareKey.Level))
                                shared.Store(shareKey, settled);
                        }

                        if (frames.TryPeek(out var enclosing))
                            enclosing.Absorb(frame);
                    }
                }
            }
            finally
            {
                _running = null;
                while (frames.TryPop(out var suspended))
                    suspended.Body.Dispose();
                _completed.Clear();
                _completedSeeds.Clear();
            }

            return root.Result;
        }

        private void ObserveCancellation()
            => FrontEndTraversalObservations.ObserveCancellation(
                memos.Observations, FrontEndCancellationCheckpoint.ExposureSettlementFrame, cancellationToken);

        // One unit of static work per settlement frame, charged before the frame is counted or built: a frame the
        // operation's work bound refuses is never observed and settles nothing (SettlementFrameWork). No token is
        // passed, so this is no cancellation checkpoint: those stay one per frame pushed (Run). The ledger is null
        // only for a standalone analysis, which has no operation (SettlementLedgerOf).
        private void ChargeFrame() => ledger?.Work(SettlementFrameWork);

        private Frame ReferenceFrame(PendingReference pending, SummaryScope level, SummaryScope? site, BoundOwnerSet? boundOwners)
        {
            // A raw reference has no origin yet: a row of a hoisted deconstruction source, or a bare name the chain
            // does not declare. It is anchored at the level that settles it; one no level anchors is refused below
            // (ResolveReference). Every reference a summary walk let escape a body already carries that body's context.
            if (pending.Origin is null && level.PropertyScope.CompletedContext is { } completed)
                pending = pending.At(completed);
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
            var key = new SeedSettlementKey(seed, level, site, boundOwners);
            var shareKey = new SettlementShare.Key(seed, level, boundOwners);
            if (shared.TryGet(shareKey, out var settled) || _completedSeeds.TryGetValue(key, out settled))
            {
                var reused = new Frame(memos.Observations) { Body = NoFrames() };
                reused.Reuse(settled);
                return reused;
            }

            var frame = new Frame(memos.Observations) { SeedCacheKey = key, ShareKey = shareKey };
            frame.Body = ResolveSeed(frame, seed, level, site, boundOwners);
            return frame;
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
            if (pending.OpenPath && pending.Origin is { } consulted)
            {
                var checkedFrom = CheckSite(site, consulted.Key, out var isConsultedLevel);
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
            var shareKey = new SettlementShare.Key(pending.ContentKey, level, boundOwners);
            if (shared.TryGet(shareKey, out var settled) || _completed.TryGetValue(key, out settled))
            {
                self.Reuse(settled);
                yield break;
            }
            if (_inProgress.TryGetValue(key, out var inProgress))
            {
                self.OutermostCut = Math.Min(self.OutermostCut, inProgress.Depth);
                self.Result = default;
                yield break;
            }

            _inProgress.Add(key, self);
            self.CacheKey = key;
            self.ShareKey = shareKey;

            try
            {
                if (pending.Origin is null)
                    throw new InvalidOperationException("Requirement settlement requires an explicit structural context.");
                if (pending.Selection == PendingSelection.OpenWalks && SharedOpenWalksLevel(self, pending, level, boundOwners) is { } opening)
                {
                    // C1: the level's walks settled ONCE, at the level itself with no bound owners, answer every reader
                    // that consults it when that settlement stands from every site there (see SharedOpenWalksLevel).
                    // That settlement reads none of this reader's bound owners: only the choice of this route does.
                    var unbound = ReferenceFrame(PropertyDependencyGraphBuilder.SummaryMemo.OpenWalksOf(pending.Origin),
                        opening, site, boundOwners: null);
                    unbound.RunsUnbound = true;
                    yield return unbound;
                    if (unbound.IsWhole && unbound.StandsFromEverySite(opening))
                    {
                        self.Result = unbound.Result;
                        yield break;
                    }
                }
                var published = new Frame(memos.Observations);
                published.Body = ResolvePublishedReference(published, pending, level, site, boundOwners);
                yield return published;
                self.Result = published.Result;
            }
            finally
            {
                _inProgress.Remove(key);
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
            var origin = memos.SharedMemo.RequirementContext(pending.Origin)!;
            var facts = origin.Facts;
            NoteView(facts);
            // The requirement view is chosen from the written origin's facts, which are a view of their own.
            if (pending.Origin is { } written && !ReferenceEquals(written.Facts, facts))
                NoteView(written.Facts);
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
                        if (group.Decides(sets, ref result, out var sole)) { self.Result = sole ? sets.Union(result, walks) : default; yield break; }
                    }
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
        /// that selected it is the settlement that is kept). A seed that reads a name or holds a reference is settled
        /// as every seed is (false).
        /// </summary>
        private bool TryResolveInPlace(Frame self, AnchoredSeed part, SummaryScope site, BoundOwnerSet? boundOwners)
        {
            if (!part.OpenWalkMember || part.Seed.VisiblePropertyDependencyNames.Count != 0 || part.Seed.PendingReferences.Count != 0)
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
                    foreach (var written in row.PendingReferences)
                        directHead &= written.Selection != PendingSelection.OpenWalks;
                    foreach (var written in row.PendingReferences)
                    {
                        if (!directHead || written.OpenPath
                            || memos.SharedMemo.RequirementContext(written.Origin ?? view.Context(terminal.Key)) is not { } origin)
                            continue;
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
        /// <item>the caller's check: the unbound settlement saw no cycle cut and stands from every site at L′.</item>
        /// </list>
        /// Then every selection and anchoring is the same from L and from L′ (3); every owner a bound owner could
        /// discharge (<see cref="SummaryScope.TryResolveRequirement"/>, a parameter head) landed at or above L′ (4), where
        /// none is in B (2), so B discharges nothing the unbound walk charged. Readers of any bound owners at any depth
        /// below L′ thus reuse one settlement, kept in the run's share. Otherwise the result depends on the reader or
        /// the site, and it is settled per reader exactly as before.
        ///
        /// <para>The route reads B: whether it is empty (the null shortcut of (1), and the skipped test of (2)), and
        /// each membership (2) tests up to the first owner found. Each read is noted on <paramref name="self"/>'s
        /// footprint (<see cref="SettlementShare"/>), so a settlement reused under other bound owners takes this route
        /// under them too.</para>
        /// </summary>
        private SummaryScope? SharedOpenWalksLevel(Frame self, PendingReference pending, SummaryScope level, BoundOwnerSet? boundOwners)
        {
            if (OpenWalksPerReaderForTesting.Value) return null;
            var origin = memos.SharedMemo.RequirementContext(pending.Origin)!;
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
                parts.Add(AnchorPublishedSeed(facts, seed, owner.Parent, opening));
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
                            seed = PropertyDependencyGraphBuilder.ExpandAtLevel(seed,
                                new PropertyDependencyGraphBuilder.LevelContext(ownerBody,
                                    PropertyDependencyGraphBuilder.GetAlgorithmSummary(ownerBody, ownerMemos, ownerContext).MemberSeeds, ownerMemos));
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
        /// The requirements of a seed relative to <paramref name="level"/>, resolved from there outward;
        /// the result is <paramref name="self"/>'s (see <see cref="Frame"/>).
        /// </summary>
        private IEnumerator<Frame> ResolveSeed(Frame self, PropertyDependencyGraphBuilder.SummarySeed seed, SummaryScope level,
            SummaryScope site, BoundOwnerSet? boundOwners)
        {
            var landing = SummaryScope.NoOwnerLookup;
            var names = sets.From(level.ResolveRequirements(seed.RequiredAncestorOwnedParameterNames)
                .Concat(site.ResolveRequirementsFromSite(seed.OwnerQualifiedParameters, boundOwners, self, ref landing)));
            self.NoteSiteLanding(landing);
            foreach (var dependencyName in seed.VisiblePropertyDependencyNames)
            {
                // A bare visible name (see ResolveVisibleName): the chain's property first.
                if (TryLookupSummary(level, dependencyName, out _, out _, out var summary))
                {
                    names = sets.Union(names, sets.Adopt(summary));
                    continue;
                }

                var provided = ReferenceFrame(new PendingReference(dependencyName, []), level, site, boundOwners);
                yield return provided;
                names = sets.Union(names, provided.Result);
            }

            foreach (var pending in seed.PendingReferences)
            {
                var settled = ReferenceFrame(pending, level, site, boundOwners);
                yield return settled;
                names = sets.Union(names, settled.Result);
            }

            self.Result = names;
        }

        /// <summary>
        /// Settlement of a BARE visible name the scope-free summary walk could not reduce
        /// further: the same rule as a member-less pending reference — the
        /// name as a property of the level's chain first (its stored summary), and only then
        /// the level's and its ancestors' <c>open</c> providers, whose provided member charges
        /// its own requirements. A name provided by nothing (an unresolvable name, or one the
        /// prelude declares) contributes no requirement.
        /// </summary>
        public RequirementSet ResolveVisibleName(string name, SummaryScope level)
        {
            if (TryLookupSummary(level, name, out _, out _, out var summary))
                return sets.Adopt(summary);

            return Run(ReferenceFrame(new PendingReference(name, []), level, site: null, boundOwners: null));
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
        // under the one rule exactly like every other body.
        var rewrittenOpens = RewriteExprList(
            algorithm.Opens,
            new ExposureWalkMemos(memos.SummaryMemo, memos.Observations, memos.Scope.Root, memos.Run));

        var rewrittenBranches = new List<CondBranch>(algorithm.Branches.Count);
        var lookupFamily = ElaboratedScopeLookup.CreateScope(algorithm, memos.Scope.PropertyScope, completedContext: completedContext);
        foreach (var branch in algorithm.Branches)
        {
            var branchMemos = memos.ForBranch(algorithm, branch.Pattern);

            if (branch.Body.DeferredRegion is { } region)
            {
                // B2c: a deferred module region is not materialized eagerly (its provisional
                // body is never evaluated; the FAMILY's classification reads the
                // provisional body's captures through the summary channel above). This pass's
                // output view of the placeholder carries the region forked with the summary
                // chain at the branch — the tree's final region, complete with every earlier
                // context and the recorded validation bindings.
                rewrittenBranches.Add(branch with
                {
                    Body = branch.Body with
                    {
                        DeferredRegion = region.WithExposure(new DeferredBranchContext(branchMemos.Scope)),
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
    /// eager walk held at the branch, so the demand-time run classifies the resolved body
    /// under the same ancestor facts.
    /// </summary>
    internal sealed record DeferredBranchContext(SummaryScope Scope);

    /// <summary>
    /// Demand-time exposure classification of a deferred region's RESOLVED body — the
    /// ordinary body walk under the ONE rule (<see cref="ClassifyDeclaredProperty"/>).
    /// </summary>
    internal static Algorithm ElaborateDeferredBranch(
        Algorithm resolvedBody,
        DeferredBranchContext context,
        FrontEndTraversalObservations? observations = null,
        ModuleUnits? modules = null,
        CancellationToken cancellationToken = default)
        => ResolveInScope(resolvedBody, context.Scope, observations, modules, structuralContext: null, sourceUnit: true,
            cancellationToken);

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
