using System.Collections.Immutable;

namespace KatLang;

/// <summary>
/// AUTOMATIC PARAMETER FORWARDING: rewrites bare value-position references to algorithms that
/// REQUIRE supplied arguments into explicit <see cref="Expr.Call"/> nodes whose arguments hand on
/// the callee's parameters. A reference to an algorithm that accepts zero supplied arguments — no
/// parameters, or only a top-level collecting parameter — is never rewritten: it stays a
/// property-style value demand, which reads the property cache (Q-03, see
/// <see cref="RequiresSuppliedArguments"/>). Must run after <see cref="ParameterDetector"/>, which
/// is NAME RESOLUTION: every written name is decided there, and this pass never re-selects one.
///
/// <para><b>Forwarding preserves existing bindings (Q-04, decided September 28 2026).</b>
/// Automatic parameter forwarding must not change what an existing name refers to, so each
/// callee parameter is supplied by a PARAMETER binding only: the referencing algorithm's own
/// (written, inferred), or — through <see cref="ForwardableParameters"/> — the enclosing
/// parameter binding a written reference of that name already denotes (an ancestor's captured
/// parameter or a clause-branch binder). Properties, opened names, module members and prelude
/// builtins are never forwarded as parameters. Only when no parameter binding exists does an
/// inferring algorithm receive a new parameter, appended to its
/// <see cref="Algorithm.User.ParameterPatterns"/> and marked
/// (<see cref="Algorithm.User.ForwardingParameterStart"/>): it completes the signature for
/// callers and is never what a written name denotes. A closed parameter list receives nothing.</para>
///
/// <para><b>Internal by design (v0.8.187):</b> this is ONE stage of the authoritative
/// front-end pipeline (<see cref="FrontEndPipeline"/>), not a host-composable API — its
/// output still lacks the <see cref="PropertyExposureResolver"/> finalization the
/// evaluator's stored-exposure checks rely on (see
/// <c>FrontEndElaborationBoundaryTests</c>). Hosts elaborate through
/// <see cref="Parser.Parse(string)"/> / <see cref="Parser.ParseAsync"/> or run through
/// <see cref="KatLangEngine"/>, which always execute the complete pass sequence.</para>
/// </summary>
internal static partial class ImplicitArgumentResolver
{
    /// <summary>Consumes the exact detected view and admission, without re-detection or source replacement.</summary>
    internal static Algorithm Resolve(DetectedProgram program)
        => ResolvePrevalidated(program);

    internal static Algorithm ResolvePrevalidated(DetectedProgram program,
        FrontEndTraversalObservations? observations = null, DiagnosticBag? diagnostics = null)
    {
        var operation = program.Operation ?? throw new ArgumentException("Rejected syntax has no admitted detection operation.", nameof(program));
        operation.RequireDetectedRoot(program.Root);
        return ResolvePrevalidated(program.Root, observations, diagnostics ?? program.Diagnostics,
            program.HostOperations, program.Modules, operation);
    }

    /// <summary>
    /// Processes a root algorithm, resolving all implicit arguments throughout the tree.
    /// Returns a new AST where every bare value-position reference to an algorithm that
    /// requires supplied arguments has been rewritten into an explicit call with lifted
    /// parameters.
    ///
    /// <para><b>Host-AST contract:</b> the root may be a preconstructed (host-built)
    /// AST. A non-recursive structural preflight runs BEFORE this pass's recursive
    /// rewriting walk and throws <see cref="ArgumentException"/> for a structurally
    /// unsafe root (structural depth beyond
    /// <see cref="EvaluationLimits.MaxSupportedAstDepth"/> — the shared fat-frame
    /// elaboration ceiling, measured with a ≥2x stack margin for this pass on the
    /// documented 1 MiB thread baseline — or a cyclic node graph), matching the
    /// <see cref="Semantics.SemanticModelBuilder"/> convention, instead of
    /// overflowing the process stack. Roots reaching this pass through the front-end
    /// pipeline are already gated and pass unchanged.</para>
    /// </summary>
    /// <exception cref="ArgumentException">
    /// The root exceeds the structural AST depth limit or contains a reference cycle.
    /// </exception>
    /// <remarks>
    /// Shared subtrees (acyclic DAGs) are legal and DAG-safe: a node referenced from several
    /// parents resolves exactly like the equivalent duplicated tree (dependency collection is
    /// name-deduplicated, so multiplicities never mattered), while every walk of this pass is
    /// reference-identity memoized per constant-context region — traversal work is bounded by
    /// the DISTINCT reachable nodes, never the number of root-to-node paths, and the rewritten
    /// output preserves the input's sharing. Memos are run-local (created per resolution,
    /// garbage afterwards).
    /// </remarks>
    public static Algorithm ResolveNameResolved(Algorithm root)
    {
        if (AstStructuralPreflight.Check(
                root,
                EvaluationLimits.MaxSupportedAstDepth,
                AstConsumerProfile.FullyRecursive) is { } structuralRejection)
        {
            throw new ArgumentException(
                structuralRejection.Kind == AstStructuralViolation.CycleDetected
                    ? "Implicit-argument resolution requires an acyclic AST: the supplied root reaches itself again through its own children."
                    : "Implicit-argument resolution requires a structurally safe AST: the supplied root exceeds the structural AST depth limit of "
                        + $"{EvaluationLimits.MaxSupportedAstDepth} nodes, which protects the host process from stack overflow.",
                nameof(root));
        }

        return ResolveNameResolvedPrevalidated(root);
    }

    /// <summary>
    /// Explicit host/test boundary for a supplied name-resolved AST with no source operation. The AST's parameter
    /// classifications are input data. This admits that phase and registers its views; it never invokes detection.
    /// Raw-source compositions must retain and pass DetectedProgram instead.
    /// </summary>
    internal static Algorithm ResolveNameResolvedPrevalidated(Algorithm root,
        FrontEndTraversalObservations? observations = null, DiagnosticBag? diagnostics = null,
        HostOperations? hostOperations = null, ModuleUnits? modules = null, CancellationToken cancellationToken = default)
    {
        var operation = StaticStructureAdmission.Create(root, hostOperations, phase: StaticAstPhase.NameResolved,
            cancellationToken: cancellationToken).Operation;
        operation.RegisterNameResolvedInput(root);
        return ResolvePrevalidated(root, observations, diagnostics, hostOperations, modules, operation);
    }

    /// <summary>
    /// The resolution core behind <see cref="ResolveNameResolved(Algorithm)"/>, without the structural
    /// preflight. Only for callers that ALREADY gated the tree at the shared
    /// elaboration ceiling (the front-end pipeline's common gate); it must never
    /// become reachable with an unvalidated host tree.
    /// </summary>
    /// <remarks>The admitting operation must be shared with detection. A detected or resolved tree cannot safely
    /// be reinterpreted as raw syntax to reconstruct that operation. Raw compositions retain DetectedProgram; supplied host classifications use the explicit name-resolved admission.</remarks>
    internal static Algorithm ResolvePrevalidated(
        Algorithm root,
        FrontEndTraversalObservations? observations = null,
        DiagnosticBag? diagnostics = null,
        HostOperations? hostOperations = null,
        ModuleUnits? modules = null,
        StaticStructureOperation? structuralOperation = null)
    {
        ArgumentNullException.ThrowIfNull(structuralOperation);
        structuralOperation.RequireDetectedRoot(root);
        structuralOperation.Queries.Observations = observations;
        var run = new ResolutionRun(structuralOperation: structuralOperation)
        {
            Observations = observations,
            Prelude = PreludeContext.For(hostOperations, structuralOperation.SourceOf(structuralOperation.Queries.Keys.Root) as Algorithm.User),
            Diagnostics = diagnostics,
            Modules = modules ?? new(),
            StructuralOperation = structuralOperation,
        };

        // B3-5★: every Q8 fact is selected before anything is rewritten, so no body reads another's provisional signature.
        // A refused selection is a front-end error of the self-dependent-inference family (A1, non-settling recursion): nothing is
        // rewritten or published, and the caller takes A1's recovery route over the detected tree.
        run.Selected = SelectSignatures(root, SignatureMap.Empty(observations), ForwardableParameters.None, isRoot: true, branchContext: null, run);
        if (!run.Selected.Succeeded)
        {
            ReportRefusedSelection(run.Selected, run);
            run.ReleaseLevels();
            return root;
        }

        var resolved = ProcessAlgorithm(
            root,
            parentParamMap: SignatureMap.Empty(observations),
            ForwardableParameters.None,
            isRoot: true,
            observations,
            diagnostics,
            branchContext: null,
            run);
        if (structuralOperation.Published(structuralOperation.Root, StaticPublicationStage.Resolved) is null)
            structuralOperation.Publish(structuralOperation.Root, StaticPublicationStage.Resolved, resolved);
        run.CompletePendingTargets();
        run.CommitDeferredChecks();
        RequireEveryAnalyzedBodyRewritten(run);
        run.ReleaseLevels();
        observations?.StageObserver?.Invoke("completed-publication", true);
        structuralOperation.CompleteLookups(resolved);
        observations?.StageObserver?.Invoke("completed-publication", false);
        return resolved;
    }

    /// <summary>
    /// Run-scoped state of ONE resolution (a <c>ResolvePrevalidated</c> or
    /// <see cref="ElaborateStructuralDeferredBranch"/> call), threaded through every algorithm-processing
    /// path so an algorithm reached through several paths of a shared (acyclic) host tree —
    /// a property value shared by several properties, a block literal reached from several
    /// rows, a conditional branch body shared by several families — is rewritten once per
    /// SEMANTIC REGION rather than once per path (M4). Run-local: created per resolution,
    /// garbage afterwards — never static, never ambient.
    /// </summary>
    private sealed class ResolutionRun(SourceSpan? importSite = null, ProcessedBodies? outerBodies = null,
        StaticStructureOperation? structuralOperation = null)
    {
        /// <summary>
        /// The import site of the module content the walk is currently inside (see
        /// <see cref="KatLang.ImportSite"/>): where a report about imported content — an invalid
        /// inferred signature, an unforwardable parameter or callable, an unliftable clause family;
        /// imported content carries no source location — is positioned. Null over
        /// the document's own text; a deferred branch run starts from the site its region
        /// recorded. Walk state only: it decides no rewrite and keys no memo.
        /// </summary>
        public SourceSpan? ImportSite = importSite;

        /// <summary>
        /// Enters the content reached through an import edge: a non-null <paramref name="site"/>
        /// becomes the current site for the scope's duration (a nested view inherits the
        /// enclosing site when its own edge carries none); disposal restores the outer site.
        /// </summary>
        public ImportSiteScope EnterImportSite(SourceSpan? site)
        {
            var saved = ImportSite;
            if (site is not null)
                ImportSite = site;
            return new ImportSiteScope(this, saved);
        }

        public readonly struct ImportSiteScope(ResolutionRun run, SourceSpan? saved) : IDisposable
        {
            public void Dispose() => run.ImportSite = saved;
        }

        /// <summary>
        /// The declaring owners of the level the walk is currently inside (Q-19 D-I): the chain an
        /// open provider's identity is anchored at (<see cref="OpenProviderIdentity.DeclaredIn"/>),
        /// mirroring the scope chain parameter detection builds. Walk state only: it decides no
        /// rewrite and keys no memo (an open level's providers capture it when the level is built).
        /// </summary>
        public DeclaringOwners Owners = DeclaringOwners.Root;

        /// <summary>
        /// The operation's diagnostics sink — the run entry's. A loaded module reports into it
        /// whichever walk reaches the module first (<see cref="ProcessModuleRoot"/>).
        /// </summary>
        public DiagnosticBag? Diagnostics;

        /// <summary>
        /// The operation's loaded module units (Q-32 I-U): every detected module declaration (one
        /// per canonical URL) to its one resolved declaration (<see cref="ProcessModuleRoot"/>).
        /// </summary>
        public ModuleUnits Modules = new();
        public StaticStructureOperation? StructuralOperation = structuralOperation;

        /// <summary>The analysis in progress (B3-5★): non-null only while <see cref="SelectSignatures"/> walks the input.</summary>
        public SignatureAnalysis? Analysis;

        /// <summary>
        /// The selected Q8 facts of this resolution (B3-5★), decided before the rewrite starts: every open body's final
        /// signature by its context. The rewrite reads a document body's signature here and nowhere else.
        /// </summary>
        public SelectedSignatures? Selected;

        /// <summary>
        /// Declaration-level output spreading (D2): whether an open body's value-role references could lift, by its
        /// contextual key (<see cref="HoldsALiftableReference"/>). Final zero-supply signatures and callable roles cannot.
        /// Read only in a program that admitted a marker.
        /// </summary>
        public Dictionary<StaticScopeKey, bool>? LiftableReferenceBodies;

        /// <summary>The admitting operation's cancellation token.</summary>
        public CancellationToken CancellationToken => StructuralOperation?.Queries.OperationToken ?? default;

        /// <summary>
        /// The rewrite walk's cancellation checkpoint (2.06): once per algorithm and per property or output row, on the
        /// admitting operation's token (a deferred compile's operation owns the materialization's linked token).
        /// </summary>
        public void ObserveCancellation(FrontEndCancellationCheckpoint kind)
            => FrontEndTraversalObservations.ObserveCancellation(Observations, kind, CancellationToken);

        /// <summary>
        /// The DIRECT declaration chain of the level the walk is currently inside (<see cref="ResolverLevel"/>,
        /// M4★): what a static reference chase resolves a followed row in. Walk state only, set with
        /// <see cref="Owners"/>; null outside every level (a module root and an open target restart it).
        /// </summary>
        public ResolverLevel? Level;

        /// <summary>Enters a level with its declaring owners and direct declaration chain; disposal restores both.</summary>
        public OwnersScope EnterLevel(DeclaringOwners owners, ResolverLevel? level)
        {
            var saved = Owners;
            var savedLevel = Level;
            Owners = owners;
            Level = level;
            return new OwnersScope(this, saved, savedLevel);
        }

        public readonly struct OwnersScope(ResolutionRun run, DeclaringOwners saved, ResolverLevel? savedLevel) : IDisposable
        {
            public void Dispose()
            {
                run.Owners = saved;
                run.Level = savedLevel;
            }
        }

        /// <summary>
        /// Nested algorithms rewritten so far, by <see cref="AlgorithmRegionKey"/>. A family's
        /// NAME only words a branch body's family-named diagnostics (unforwardable parameters), so a second
        /// family sharing the body reuses the rewrite and REPLAYS those diagnostics under its
        /// own name (see <see cref="AlgorithmRegion.DiagnosticTemplates"/>).
        /// </summary>
        public Dictionary<AlgorithmRegionKey, AlgorithmRegion>? AlgorithmRegions;

        /// <summary>
        /// The free reference names of every algorithm node computed so far (a pure function
        /// of the node — see <see cref="FreeReferenceNames"/>), by node reference.
        /// </summary>
        public Dictionary<Algorithm, CanonicalNameSet>? FreeReferenceNames;
        /// <summary>
        /// FE-3: the shared signature templates of this run (see <see cref="LiftSignature"/>). Run-local:
        /// a template is shared by the owners of ONE resolution and never across parses. It charges the
        /// pattern arrays it builds to the operation's ledger (<see cref="LiftingLedger"/>).
        /// </summary>
        public ImplicitSignatureTemplateInterner Templates => _templates ??= new(Observations, LiftingLedger, CancellationToken);
        private ImplicitSignatureTemplateInterner? _templates;

        /// <summary>
        /// The ledger formula lifting charges its storage to where it allocates it (signature templates, owner heads,
        /// synthesized argument bundles): the admitting operation's. Every resolution entry has one —
        /// <see cref="ResolvePrevalidated(Algorithm, FrontEndTraversalObservations?, DiagnosticBag?, HostOperations?, ModuleUnits?, StaticStructureOperation?)"/>
        /// requires it (the eager pipeline's and the standalone host entry's, which admits its own name-resolved
        /// operation), and <see cref="ElaborateStructuralDeferredBranch"/> is given its materialization's — so there is no
        /// uncharged source path, and a run without one is an internal defect, never a reason to skip the charge.
        /// </summary>
        private StaticQueryResourceBudget LiftingLedger
            => (StructuralOperation ?? throw new InvalidOperationException(
                "Formula lifting requires the admitting structural operation's ledger.")).Queries.Resources;

        /// <summary>
        /// Charges one synthesized argument bundle the resolver just built — <paramref name="slots"/> arguments at
        /// <see cref="BundleStorageUnits"/> slots each — before it is observed or retained. A shared bundle that is
        /// reused (FE-2/FE-3) is never charged again.
        /// </summary>
        public void ChargeImplicitArgumentBundle(int slots)
        {
            var units = BundleStorageUnits * slots;
            LiftingLedger.Metadata(units, work: slots, CancellationToken);
            Observations?.RecordLiftingStorageCharged(units);
        }

        /// <summary>The traversal observations of this run (null when none are recorded).</summary>
        public FrontEndTraversalObservations? Observations;

        /// <summary>
        /// FE-3: synthesized implicit-argument bundles shared ACROSS owners, by the exact inputs a
        /// bundle is a pure function of (see <see cref="SharedBundleKey"/>). FE-2 shared one bundle per
        /// callee within a rewrite region; owners whose rewrite contexts give a callee identical
        /// forwarding share it here too, so K owners lifting one L-wide callee keep one bundle.
        /// </summary>
        public Dictionary<SharedBundleKey, OutputBundle>? SharedBundles;

        /// <summary>The capture-name set of each callee pattern list, by list reference (FE-3).</summary>
        public IReadOnlySet<string> CalleeNamesOf(IReadOnlyList<ParameterPattern> patterns)
        {
            if (patterns is ImplicitSignatureTemplate template)
                return template.Facts.NameSet;
            _calleeNames ??= new(ReferenceEqualityComparer.Instance);
            if (!_calleeNames.TryGetValue(patterns, out var names))
            {
                names = new HashSet<string>(ParameterPattern.CapturesExpandingSharedNodesOnce(patterns).Select(static capture => capture.Name), StringComparer.Ordinal);
                _calleeNames.Add(patterns, names);
            }

            return names;
        }

        private Dictionary<IReadOnlyList<ParameterPattern>, IReadOnlySet<string>>? _calleeNames;

        /// <summary>
        /// The COLLECTING capture names of each callee pattern list (at any pattern level), by list
        /// reference — usually none or one, so a question about them costs O(1) per reference.
        /// </summary>
        public IReadOnlyList<string> CollectingCaptureNamesOf(IReadOnlyList<ParameterPattern> patterns)
        {
            _collectingCaptureNames ??= new(ReferenceEqualityComparer.Instance);
            if (!_collectingCaptureNames.TryGetValue(patterns, out var names))
            {
                IReadOnlyList<ParameterDeclaration> captures = patterns is ImplicitSignatureTemplate { ComputedFacts: { } facts }
                    ? facts.Captures
                    : ParameterPattern.CapturesExpandingSharedNodesOnce(patterns);
                names = captures
                    .Where(static capture => capture.Kind == ParameterKind.Collecting)
                    .Select(static capture => capture.Name)
                    .Distinct(StringComparer.Ordinal)
                    .ToArray();
                _collectingCaptureNames.Add(patterns, names);
            }

            return names;
        }

        private Dictionary<IReadOnlyList<ParameterPattern>, IReadOnlyList<string>>? _collectingCaptureNames;

        /// <summary>
        /// Q-04: whether the lifted TAIL shares a capture name with the enclosing parameter bindings a
        /// forwarding owner reuses, by (bindings, tail) reference: the owners of one body share one
        /// bindings instance, so K siblings lifting one L-wide tail under W bindings pay one
        /// min(L, W) test, never K.
        /// </summary>
        public bool TailMeetsForwardable(ImplicitSignatureTemplate tail, ForwardableParameters forwardable)
        {
            _tailMeetsForwardable ??= new();
            var key = (forwardable, tail);
            if (!_tailMeetsForwardable.TryGetValue(key, out var meets))
            {
                var names = tail.Facts.NameSet;
                meets = names.Count <= forwardable.Count
                    ? names.Any(forwardable.Binds)
                    : forwardable.BoundNames.Any(names.Contains);
                _tailMeetsForwardable.Add(key, meets);
            }

            return meets;
        }

        private Dictionary<(ForwardableParameters, ImplicitSignatureTemplate), bool>? _tailMeetsForwardable;

        public readonly NameSetInterner ReferenceNameSets = new();
        public readonly SignatureFootprints Footprints = new();
        public readonly BranchContextInterner BranchContexts = new();

        /// <summary>The prelude a name the owner walk leaves to it resolves in (builtins, Math, host operations).</summary>
        public required PreludeContext Prelude { get; init; }

        /// <summary>The bodies this run processed — and, for a deferred branch's run, the eager run's (<see cref="ProcessedBodies"/>).</summary>
        public readonly ProcessedBodies Bodies = new(outerBodies, structuralOperation);

        // The provisional misses this run rewrote (Expr.DotCall.ProvisionalMiss), in the order it met them: the checks that
        // wait on them are made once the run has processed every body (CommitDeferredChecks).
        private List<ProvisionalMiss>? _awaited;
        private HashSet<ProvisionalMiss>? _awaitedSet;

        /// <summary>Records that the checks waiting on <paramref name="miss"/> are made when this run ends.</summary>
        public void Await(ProvisionalMiss miss)
        {
            if ((_awaitedSet ??= new(ReferenceEqualityComparer.Instance)).Add(miss))
                (_awaited ??= []).Add(miss);
        }

        /// <summary>
        /// Makes every check waiting on a provisional miss this run rewrote (<see cref="DeferredFallbackCheck"/>): called
        /// once the run has processed every body, so each miss is decided from the receiver as resolution leaves it, whatever
        /// order the bodies were processed in, and each report takes the place detection reserved for it. Then every such
        /// miss lets go of its decider and its checks (<see cref="ProvisionalMiss.Release"/>): the edges keep the cell into
        /// the published tree, which must reach no pass state (SEC-S1).
        /// </summary>
        public void CommitDeferredChecks()
        {
            if (_awaited is null)
                return;
            foreach (var miss in _awaited)
            {
                foreach (var check in miss.Checks)
                    check.Commit();
            }

            foreach (var miss in _awaited)
                miss.Release();
        }

        // The levels this run's walk processed, and whether a deferred branch's context keeps their chain for its own
        // run (its demand-time resolution reads the eager declarations as written).
        private List<ResolverLevel>? _walkLevels;

        /// <summary>Records a level this run's walk processes (released when the run ends, <see cref="ReleaseLevels"/>).</summary>
        public void AddWalkLevel(ResolverLevel level) => (_walkLevels ??= []).Add(level);

        /// <summary>
        /// Ends the run's hold on its input (SEC-S1): every level its walk processed lets go of its input entries and
        /// written opens (<see cref="ResolverLevel.Release"/>), because the published tree keeps entries — an alias's
        /// recorded target is the processed entry of its target, which names its level — and the input must be unreachable
        /// once the pass returns. A run whose levels a deferred branch's context keeps leaves them whole: that context is
        /// part of the output, as it keeps the eager run's processed bodies and signature map.
        /// </summary>
        public void ReleaseLevels()
        {
            if (_walkLevels is null)
                return;
            foreach (var level in _walkLevels)
                level.Release();
            StructuralOperation?.ReleaseResolverLevels();
            _walkLevels = null;
        }

        // The recorded alias targets whose endpoint this run has not processed yet (M4★), by the endpoint's identity (its
        // context, B3-5★): the target cells pending on it.
        private Dictionary<object, List<AliasTargetCell>>? _pendingTargets;

        /// <summary>
        /// The target cell of an alias whose endpoint <paramref name="target"/> this run has not processed yet: pending on
        /// it, completed once that body is processed (<see cref="CompleteStructure"/>, <see cref="CompletePendingTargets"/>).
        /// Its identity and signature are final already; only the processed algorithm is still to come.
        /// </summary>
        public AliasTargetCell PendingTargetOn(AliasTarget target)
        {
            var cell = AliasTargetCell.PendingOn(target);
            _pendingTargets ??= new(ReferenceEqualityComparer.Instance);
            if (!_pendingTargets.TryGetValue(target.Identity, out var cells))
                _pendingTargets.Add(target.Identity, cells = []);
            cells.Add(cell);
            return cell;
        }

        /// <summary>
        /// Records that <paramref name="written"/> — the value of a property, in the context <paramref name="key"/> — is
        /// processed as <paramref name="processed"/>, completing each target cell pending on that context with it.
        /// </summary>
        public void CompleteStructure(Algorithm written, Algorithm processed, StaticScopeKey? key)
        {
            Bodies.Record(written, processed);
            if (key is not null && _pendingTargets is not null && _pendingTargets.Remove(key, out var targets))
            {
                foreach (var target in targets)
                    target.Complete(ProcessedTarget(target.Target!, processed));
            }
        }

        /// <summary>
        /// Completes every target cell still pending when the rewrite ends (B3-5★; research defect D15): a cell pending on a
        /// body the rewrite processed as a nested region (a block's member) rather than as a property of a level it walked is
        /// completed from that body's contextual publication — through the region alias of a context the rewrite served from
        /// another context's processing (<see cref="StaticStructureOperation.AliasResolvedRegion"/>) — and so is every
        /// structure cell still pending. Never from a body-only memo: a body shared by two contexts has a processed form per
        /// context.
        /// </summary>
        public void CompletePendingTargets()
        {
            if (StructuralOperation is not { } operation)
                return;
            operation.CompletePendingStructureCells();
            if (_pendingTargets is null)
                return;
            foreach (var (identity, cells) in _pendingTargets.ToArray())
            {
                if (identity is not StaticScopeKey key || operation.ResolvedView(key) is not { } processed)
                    continue;
                foreach (var cell in cells)
                    cell.Complete(ProcessedTarget(cell.Target!, processed));
                _pendingTargets.Remove(identity);
            }
        }

        // The target a read of the processed body gives: the same identity and signature, the processed algorithm.
        private static AliasTarget? ProcessedTarget(AliasTarget written, Algorithm processed)
            => processed switch
            {
                Algorithm.Alias { HasRuntimeTarget: false } alias => alias.ResolvedTarget ?? written,
                Algorithm.Alias => written,
                _ => written with { Algorithm = processed },
            };

        /// <summary>The first-PUBLIC member index of each open provider, by exact provider reference.</summary>
        public OpenMemberIndexCache OpenMemberIndexes => _openMemberIndexes ??= new(Observations);
        private OpenMemberIndexCache? _openMemberIndexes;

        /// <summary>
        /// The lifting signature of each resolved algorithm outside the selection (prelude, opened and dotted members,
        /// families, closed bodies), by reference and the name it is displayed under — never the first name that reached
        /// it, which the analysis and the rewrite need not share (B3-5★).
        /// </summary>
        public readonly Dictionary<(Algorithm Algorithm, string Name), LiftingSignature> LiftingSignatures = new(NamedAlgorithmComparer.Instance);

        /// <summary>The run's static-chase memos (OD-D verdicts; <see cref="StructuralProcessingViews"/>).</summary>
        public StructuralProcessingViews StructuralViews => _structuralViews ??= new(OpenMemberIndexes, StructuralOperation);
        private StructuralProcessingViews? _structuralViews;

        /// <summary>The import site the current property loop started under (a demanded property is processed under it).</summary>
        public ImportSiteScope EnterImportSiteExactly(SourceSpan? site)
        {
            var saved = ImportSite;
            ImportSite = site;
            return new ImportSiteScope(this, saved);
        }
    }

    /// <summary>
    /// The prelude as formula lifting sees it: the members a program can call at run time — the
    /// builtins, the <c>Math</c> module and its aliases, and the run's host operations — resolved in
    /// the signature-only semantic prelude parameter detection used. <c>load</c> is a front-end
    /// directive, not a runtime callable, so it has no lifting signature. A Math member (whichever
    /// spelling reaches it — the alias and the canonical member share one algorithm) and a host
    /// operation demand every argument's value.
    /// </summary>
    internal sealed class PreludeContext
    {
        private static readonly Lazy<PreludeContext> SharedDefault =
            new(() => new PreludeContext(BuiltinRegistry.SharedSemanticPreludeAlgorithm));

        private readonly Algorithm.User _prelude;
        private readonly HashSet<string> _callableNames;
        private readonly HashSet<Algorithm> _strictValue = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<Algorithm> _registryAlgorithms = new(ReferenceEqualityComparer.Instance);

        private PreludeContext(Algorithm.User prelude)
        {
            _prelude = prelude;
            foreach (var member in prelude.Properties) _registryAlgorithms.Add(member.Value);
            _callableNames = new HashSet<string>(BuiltinRegistry.BuiltinNames, StringComparer.Ordinal);
            _callableNames.UnionWith(BuiltinRegistry.RuntimePreludeExtraNames);
            if (ElaboratedScopeLookup.TryLookupProperty(prelude, BuiltinRegistry.MathModuleName)?.Property.Value is { } math)
            {
                foreach (var member in math.Properties)
                {
                    _strictValue.Add(member.Value);
                    _registryAlgorithms.Add(member.Value);
                }
            }

            // A deferred continuation retains the admitted signature prelude, not runtime host
            // callbacks. Its extra declarations are the same host identities used at admission.
            foreach (var member in prelude.Properties)
            {
                if (HostOperations.ReservedPreludeNames.Contains(member.Name)) continue;
                _callableNames.Add(member.Name);
                _strictValue.Add(member.Value);
            }
        }

        public static PreludeContext For(HostOperations? hostOperations, Algorithm.User? admittedPrelude = null)
            => admittedPrelude is not null
                ? ReferenceEquals(admittedPrelude, BuiltinRegistry.SharedSemanticPreludeAlgorithm) ? SharedDefault.Value : new PreludeContext(admittedPrelude)
                : hostOperations is null ? SharedDefault.Value : new PreludeContext(hostOperations.SemanticPreludeAlgorithm);

        /// <summary>The prelude member a name the owner walk leaves undecided resolves to, if it is a runtime callable.</summary>
        public bool TryGetMember(string name, [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out Property? member)
        {
            member = _callableNames.Contains(name) ? ElaboratedScopeLookup.TryLookupProperty(_prelude, name)?.Property : null;
            return member is not null;
        }

        /// <summary>Whether a resolved algorithm is a Math member or a host operation (every argument a value).</summary>
        public bool IsStrictValue(Algorithm algorithm) => _strictValue.Contains(algorithm);
        internal bool IsFinalRegistryAlgorithm(Algorithm algorithm) => _registryAlgorithms.Contains(algorithm);


    }

    /// <summary>Q8 processing adapters over the operation's selected Q1–Q7 facts. No structural-result cache.</summary>
    internal sealed class StructuralProcessingViews(OpenMemberIndexCache indexes,
        StaticStructureOperation? structuralOperation = null)
    {
        internal StaticStructureOperation StructuralOperation { get; } = structuralOperation
            ?? throw new InvalidOperationException("Resolution requires an admitted structural operation.");
        public OpenMemberIndexCache Indexes { get; } = indexes;
        public ResolverLevel LevelOf(Algorithm body, DeclaringOwners declaring, ResolverLevel? outer, bool raw)
            => StructuralOperation.ResolverLevel(StructuralOperation.ContextOf(
                outer?.StaticContext?.Key ?? StructuralOperation.Queries.Keys.Root, body))!;
        public Algorithm? DeclaredMember(Algorithm body, string name)
            => ElaboratedScopeLookup.TryLookupProperty(body, name)?.Property.Value;
    }

    /// <summary>
    /// The minimal complete semantic context of one nested-algorithm rewrite: the node by
    /// REFERENCE; the <see cref="SignatureFootprints"/> projection of the signatures its FREE reference
    /// names see in the visible map (every signature the rewrite can read — the subtree's own
    /// bindings shadow the map, open targets use fresh maps, stored dot-edge fallbacks are
    /// never rewritten); the enclosing PARAMETER bindings its forwarding may reuse (Q-04: the
    /// canonical <see cref="ForwardableParameters"/> content, names and collecting names — a
    /// synthesized argument carries only a binding's spelling and kind, never its owner); for a
    /// conditional branch body the closed binder specification the pattern imposes, by CONTENT
    /// (<see cref="FrontEndRegionKeys.ClosedBranchSpecification"/>) — the head's whole structure,
    /// literal POSITIONS included, when the body is shaped like a bare-forwarding row
    /// (<see cref="FrontEndRegionKeys.BareForwardingBranchHead"/>, <see cref="HasLoneBareRowShape"/>);
    /// and the reporting mode. Two
    /// reaches with equal keys observe identical inputs, whatever path led to them and whatever
    /// else the property loop rewrote in between.
    /// </summary>
    private sealed record AlgorithmRegionKey(
        Algorithm Node,
        CanonicalNameSet Snapshot,
        CanonicalNameSet ForwardableNames,
        CanonicalNameSet ForwardableCollectingNames,
        int? ClosedSpecification,
        bool ReportsDiagnostics,
        OpenLevel? Opens)
    {
        public bool Equals(AlgorithmRegionKey? other)
            => other is not null
                && ReferenceEquals(Node, other.Node)
                && Snapshot.Equals(other.Snapshot)
                && ForwardableNames.Equals(other.ForwardableNames)
                && ForwardableCollectingNames.Equals(other.ForwardableCollectingNames)
                && ClosedSpecification == other.ClosedSpecification
                && ReportsDiagnostics == other.ReportsDiagnostics
                && ReferenceEquals(Opens, other.Opens);

        public override int GetHashCode()
            => HashCode.Combine(
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Node),
                Snapshot.GetHashCode(),
                ForwardableNames.GetHashCode(),
                ForwardableCollectingNames.GetHashCode(),
                ClosedSpecification,
                ReportsDiagnostics,
                Opens is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Opens));
    }

    /// <summary>
    /// The visible signature map of one rewrite: the signature of every property the algorithm
    /// can see, nearest declaration winning. PERSISTENT (FE-1): a nested algorithm that declares
    /// properties EXTENDS its parent's map with just those names, so a scope seeing W signatures
    /// with K such nested algorithms costs O(K) small extensions — never K copies of the W-entry
    /// map. IMMUTABLE (B3-5★): a level's entries carry its properties' SELECTED signatures from the
    /// moment the level creates its map (<see cref="SelectSignatures"/> decides every signature of
    /// the run before any rewrite reads one), so no map is written after it is created and no read
    /// depends on which sibling a level processes first.
    /// </summary>
    internal sealed class SignatureMap
    {
        private readonly ImmutableDictionary<string, VisibleProperty> _entries;
        public SignatureVersion Version { get; private set; }
        private readonly FrontEndTraversalObservations? _observations;
        private readonly Func<string, VisibleProperty?>? _external;

        private SignatureMap(
            ImmutableDictionary<string, VisibleProperty> entries,
            OpenLevel? opens,
            FrontEndTraversalObservations? observations,
            Func<string, VisibleProperty?>? external = null)
        {
            _entries = entries;
            Version = new(Parent: null, Changes: []);
            Opens = opens;
            _observations = observations;
            _external = external;
        }

        /// <summary>A fresh map with no visible signature (a root, an open-target region).</summary>
        public static SignatureMap Empty(FrontEndTraversalObservations? observations)
            => new(ImmutableDictionary.Create<string, VisibleProperty>(StringComparer.Ordinal), opens: null, observations);

        internal static SignatureMap CompletedExternal(Func<string, VisibleProperty?> lookup,
            FrontEndTraversalObservations? observations)
            => new(ImmutableDictionary.Create<string, VisibleProperty>(StringComparer.Ordinal), null, observations, lookup);

        /// <summary>
        /// The <c>open</c> levels visible here, innermost first: consulted for a name only after the
        /// whole owner walk (the entries, then the prelude) found nothing, one level at a time.
        /// </summary>
        public OpenLevel? Opens { get; private set; }

        /// <summary>The entry recorded for <paramref name="name"/>: its selected signature and its written algorithm.</summary>
        public bool TryGetValue(string name, [System.Diagnostics.CodeAnalysis.MaybeNullWhen(false)] out VisibleProperty entry)
        {
            if (_entries.TryGetValue(name, out entry)) return true;
            entry = _external?.Invoke(name);
            return entry is not null;
        }

        public bool ContainsKey(string name) => TryGetValue(name, out _);

        /// <summary>A NEW map: these entries overlaid with <paramref name="locals"/> (local wins), the open chain inherited.</summary>
        public SignatureMap Extend(IReadOnlyDictionary<string, VisibleProperty> locals)
        {
            var extended = _entries.ToBuilder();
            var changes = new SignatureChange[locals.Count];
            var index = 0;
            foreach (var (name, entry) in locals)
            {
                changes[index++] = new(name, TryGetValue(name, out var previous) ? previous : null, entry);
                extended[name] = entry;
                _observations?.RecordContextEntryWritten();
            }

            var result = new SignatureMap(extended.ToImmutable(), Opens, _observations, _external);
            result.Version = new(Version, changes);
            return result;
        }

        /// <summary>
        /// Makes the opener level's <c>open</c> declaration the innermost open level. Only on a map the opener level
        /// itself just created, before anything reads it: every nested body extends it, so each sees the level's opens.
        /// </summary>
        public void AttachOpens() => Opens = new OpenLevel(Opens);
    }

    /// <summary>
    /// One visible property of a rewrite: its SELECTED signature (B3-5★) and its WRITTEN algorithm.
    /// The algorithm answers member questions (a dotted or opened callee's own signature) and the
    /// kind questions processing never changes (a clause family, a user algorithm — whether a body
    /// becomes an alias is the static structure's answer, <see cref="StaticCalleeKindOf"/>); an
    /// entry's identity is a region-key token.
    /// </summary>
    internal sealed class VisibleProperty(CallableSignature signature, Algorithm value, DeclaringOwners? owners = null)
    {
        public CallableSignature Signature { get; } = signature;

        /// <summary>
        /// The level that DECLARES this property (<see cref="ResolverLevel"/>): where a static chase resolves its
        /// row when it is a reference. Null for an entry built outside a level (the prelude).
        /// </summary>
        public ResolverLevel? Level { get; init; }

        public Algorithm Value { get; } = value;

        /// <summary>
        /// The declaring owners of the level that declares this property (Q-19 D-I): what anchors
        /// the identity of an open provider headed by it. Null for an entry built outside a level.
        /// </summary>
        public DeclaringOwners? Owners { get; } = owners;
    }

    /// <summary>
    /// One level's <c>open</c> declaration as a REGION-KEY TOKEN (<see cref="AlgorithmRegionKey"/>, <see cref="OpensReadBy"/>):
    /// what an opened name resolves to is the static structure's answer (Q1's opened binding, read through the level's
    /// static context — <see cref="StaticOpenedDeclaration"/>), so the token carries no provider; it only distinguishes the
    /// open contexts a shared body is rewritten in, innermost first.
    /// </summary>
    internal sealed class OpenLevel(OpenLevel? outer)
    {
        public OpenLevel? Outer { get; } = outer;
    }

    /// <summary>
    /// One LEVEL of the resolver's DIRECT declaration chain (M4★; ALIAS-UNIFY-1 review): the properties the level
    /// itself declares and the enclosing level, so a static reference chase resolves a followed row from ITS OWN
    /// declarations outward — never in the map of the body that started the chase, where a nearer declaration
    /// could shadow the head or the head may not be visible at all (the evaluator's direct lookup from the
    /// reference's own scope). A level the walk processes records its INPUT entries; a body a chase NAVIGATES into — a
    /// provider's, a receiver's, a block's — is a level over that algorithm's own declared properties, ONE object per
    /// static scope (<see cref="StructuralProcessingViews.LevelOf"/>). A loaded module's body restarts the chain
    /// (Q-31 H-P). The operation keeps each level (<see cref="StaticStructureOperation.ResolverLevel"/>), so a level is
    /// shared, never rebuilt, wherever a chase reaches it.
    /// </summary>
    internal sealed class ResolverLevel
    {
        private Algorithm? _body;

        /// <summary>A level the walk processes; its entries are recorded once they are built (<see cref="Entries"/>).</summary>
        public ResolverLevel(DeclaringOwners owners, ResolverLevel? outer, IReadOnlyList<Expr>? opens = null, StaticStructureContext? staticContext = null)
        {
            Owners = owners;
            Outer = outer;
            Opens = opens ?? [];
            StaticContext = staticContext;
        }

        /// <summary>A body a chase navigates into: its own declared properties, inside <paramref name="outer"/>.</summary>
        public ResolverLevel(Algorithm body, DeclaringOwners owners, ResolverLevel? outer, StaticStructureContext? staticContext = null)
            : this(owners, body.IsModuleRoot ? null : outer, body.Opens, staticContext ?? outer?.StaticContext?.Inside(body))
        {
            _body = body;
        }

        /// <summary>The level's context in the admitted static-structure operation.</summary>
        internal StaticStructureContext? StaticContext { get; private set; }

        /// <summary>
        /// The level's own <c>open</c> targets as WRITTEN: a static chase follows a row through them after the whole
        /// direct chain and the prelude found nothing (<see cref="StaticOpenedDeclaration"/>).
        /// </summary>
        public IReadOnlyList<Expr> Opens { get; private set; }

        /// <summary>
        /// The body a chase NAVIGATED into, whose own declarations this level holds: the owner of every member found
        /// here. Null for a level the walk processes.
        /// </summary>
        public Algorithm? NavigatedBody => _body;

        /// <summary>
        /// Lets go of what a level the walk processed holds of its input — its entries and written opens — once the run
        /// that built it has ended: an entry the published tree keeps (an alias's recorded target) reaches its level, which
        /// must then reach no input (SEC-S1, <see cref="ResolutionRun.ReleaseLevels"/>).
        /// </summary>
        public void Release()
        {
            Entries = null;
            Opens = [];
            StaticContext = null;
            _body = null;
        }

        /// <summary>
        /// Whether a navigated body's declarations are its INPUT (the body was reached through an unprocessed
        /// declaration, <see cref="StaticDeclaration.Raw"/>): every member found here inherits it.
        /// </summary>
        public bool Raw { get; init; }

        /// <summary>The level's declaring owners (provider identities, Q-19 D-I).</summary>
        public DeclaringOwners Owners { get; }

        /// <summary>The enclosing level; null at a chain's root.</summary>
        public ResolverLevel? Outer { get; }

        /// <summary>A processed level's INPUT entries by name (set once, by the walk that builds them).</summary>
        public IReadOnlyDictionary<string, VisibleProperty>? Entries { get; set; }
    }

    /// <summary>
    /// One declaration a static chase reaches: the algorithm, its open-provider identity, its declaring level's
    /// owners and that level's direct declaration chain (<see cref="ResolverLevel"/>; null for a prelude member).
    /// </summary>
    internal readonly record struct StaticDeclaration(Algorithm Target, OpenProviderIdentity Identity, DeclaringOwners Owners, ResolverLevel? Level)
    {
        /// <summary>
        /// Whether <see cref="Target"/> is the declaration's INPUT — a recorded entry read as recorded, an entry its
        /// loop has not processed yet (a member of a sibling cycle), or a member of such a body — rather than its final
        /// processed algorithm. A written lone reference row is followed only in the input (the processed one is an
        /// alias, or was classified no alias); M4★, ALIAS-UNIFY-1 second review.
        /// </summary>
        public bool Raw { get; init; }

        /// <summary>This declaration's own body as a level: its own declarations, inside its declaring level (the run's one such level).</summary>
        public ResolverLevel OwnLevel(StructuralProcessingViews memos) => memos.LevelOf(Target, Owners, Level, Raw);

        /// <summary>A declared member of this structure: declared in its own body, a level inside this declaration's.</summary>
        public StaticDeclaration Member(Algorithm member, StructuralProcessingViews memos)
        {
            var own = OwnLevel(memos);
            return new StaticDeclaration(member, Identity.Member(member), own.Owners, own) { Raw = Raw };
        }

        /// <summary>A block written in this reference's row: declared in the reference's own body.</summary>
        public StaticDeclaration Block(Algorithm block, StructuralProcessingViews memos)
        {
            var own = OwnLevel(memos);
            return new StaticDeclaration(block, OpenProviderIdentity.DeclaredIn(block, own.Owners), own.Owners, own) { Raw = Raw };
        }
    }

    /// <summary>Projects the selected Q3 endpoint of a declaration (its detected input; B3-5★ reads no processed form).</summary>
    private static StaticDeclaration? StaticReferenceStructure(
        StaticDeclaration start, StructuralProcessingViews memos, bool viaOpens, StaticCycleCheck check)
    {
        var operation = memos.StructuralOperation;
        var key = operation.ContextOf(start.Level?.StaticContext?.Key ?? operation.Queries.Keys.Root, start.Target);
        return operation.SelectedStructure(key, viaOpens, check);
    }

    /// <summary>Projects Q1's owned declaration (or, outside every level, the prelude member).</summary>
    private static StaticDeclaration? DirectDeclaration(string name, ResolverLevel? level, PreludeContext prelude)
        => level?.StaticContext is { } context
            ? context.Operation.SelectedDeclaration(context.Key, name, StaticQueryProjection.OwnedBinding, StaticCycleCheck.Formation)
            : prelude.TryGetMember(name, out var member)
                ? new StaticDeclaration(member.Value, OpenProviderIdentity.DeclaredIn(member.Value, DeclaringOwners.Root), DeclaringOwners.Root, null)
                : null;

    /// <summary>Projects Q1's opened binding without independently selecting providers.</summary>
    private static StaticDeclaration? StaticOpenedDeclaration(
        string name, ResolverLevel? level, StaticCycleCheck stratum = StaticCycleCheck.Formation)
        => level?.StaticContext is { } context
            ? context.Operation.SelectedDeclaration(context.Key, name, StaticQueryProjection.OpenedBinding, stratum) : null;

    /// <summary>
    /// Q-04 (decided September 28 2026): the PARAMETER bindings automatic parameter forwarding may
    /// reuse inside one body — the answer to "which EXISTING parameter binding can satisfy this
    /// callee parameter?", kept separate from ordinary name resolution on purpose.
    ///
    /// <para>It holds, for every name, the parameter binding the owner walk
    /// (<see cref="ElaboratedScopeLookup.SelectOwnedDeclaration"/>) would select for a WRITTEN
    /// parameter occurrence of that name here: a parameter that an enclosing owner's name
    /// resolution established — written, inferred, a clause-branch binder, or an inferred name of
    /// the never-called root — nearest owner winning, and never a name a NEARER level declares as a
    /// property (the nearer declaration decides; only invalid source or the root's phantom exemption
    /// reach that case). Forwarding therefore hands a callee exactly the binding an existing written
    /// reference of the name already denotes, instead of adding a same-named parameter to the
    /// referencing body that would shadow it: automatic forwarding never changes what an existing
    /// name refers to. Properties, opened names, module members, and prelude builtins are
    /// deliberately absent — they are not forwarded as parameters — and so are the parameters
    /// forwarding itself adds (<see cref="Algorithm.User.ForwardingParameterStart"/>): they exist
    /// only for the callee that needed them.</para>
    ///
    /// <para>PERSISTENT and CANONICAL (FE-1): a body extends its parent's bindings by what it adds,
    /// so K nested bodies under a W-binding owner cost O(K + W); <see cref="Names"/> and
    /// <see cref="CollectingNames"/> are canonical name-set ids of the run's interner, so two
    /// derivations of equal bindings key the resolver's region memo alike.</para>
    /// </summary>
    internal sealed class ForwardableParameters
    {
        private readonly ImmutableDictionary<string, ParameterKind> _kinds;
        private readonly NameSetInterner? _interner;

        private ForwardableParameters(
            ImmutableDictionary<string, ParameterKind> kinds,
            NameSetInterner? interner,
            CanonicalNameSet names,
            CanonicalNameSet collectingNames)
        {
            _kinds = kinds;
            _interner = interner;
            Names = names;
            CollectingNames = collectingNames;
        }

        /// <summary>No parameter binding to reuse (the program root's body, an open-target region).</summary>
        public static ForwardableParameters None { get; } = new(
            ImmutableDictionary.Create<string, ParameterKind>(StringComparer.Ordinal),
            interner: null,
            NameSetInterner.Empty,
            NameSetInterner.Empty);

        /// <summary>The bound names (canonical set of the run's interner).</summary>
        public CanonicalNameSet Names { get; }

        /// <summary>The bound names whose binding is a collecting binding (canonical set).</summary>
        public CanonicalNameSet CollectingNames { get; }

        public bool IsEmpty => _kinds.IsEmpty;

        public int Count => _kinds.Count;

        public IEnumerable<string> BoundNames => _kinds.Keys;

        public bool Binds(string name) => _kinds.ContainsKey(name);

        /// <summary>The binding kind of <paramref name="name"/> when an enclosing parameter binds it.</summary>
        public bool TryGetKind(string name, out ParameterKind kind) => _kinds.TryGetValue(name, out kind);

        /// <summary>
        /// The bindings a body's OWN forwarding may reuse: these, minus every name the body
        /// declares as a property (a nearer declaration decides the owner walk). The same instance
        /// when the body declares none of the bound names.
        /// </summary>
        public ForwardableParameters WithoutProperties(IReadOnlyList<Property> properties, NameSetInterner interner)
        {
            if (_kinds.IsEmpty || properties.Count == 0)
                return this;

            List<string>? shadowed = null;
            foreach (var property in properties)
            {
                if (_kinds.ContainsKey(property.Name))
                    (shadowed ??= []).Add(property.Name);
            }

            if (shadowed is null)
                return this;

            var removed = interner.With(NameSetInterner.Empty, shadowed);
            var rebased = Rebase(interner);
            return new(
                rebased._kinds.RemoveRange(shadowed),
                interner,
                interner.Except(rebased.Names, removed),
                interner.Except(rebased.CollectingNames, removed));
        }

        /// <summary>
        /// The bindings a body's NESTED bodies may reuse: these plus the body's own name-resolution
        /// parameter bindings, which replace same-named outer ones (the nearest owner wins); the first
        /// capture of a repeated name decides its kind, as it does for a caller's own signature.
        /// The same instance when the body binds no parameter.
        /// </summary>
        public ForwardableParameters WithParameters(IEnumerable<ParameterDeclaration> parameters, NameSetInterner interner)
        {
            HashSet<string>? own = null;
            List<string>? collecting = null;
            List<string>? ordinary = null;
            foreach (var parameter in parameters)
            {
                own ??= new HashSet<string>(StringComparer.Ordinal);
                if (own.Add(parameter.Name))
                    (parameter.Kind == ParameterKind.Collecting ? collecting ??= [] : ordinary ??= []).Add(parameter.Name);
            }

            if (own is null)
                return this;

            var rebased = Rebase(interner);
            var kinds = rebased._kinds.ToBuilder();
            foreach (var name in ordinary ?? [])
                kinds[name] = ParameterKind.Normal;
            foreach (var name in collecting ?? [])
                kinds[name] = ParameterKind.Collecting;

            var collectingNames = rebased.CollectingNames;
            if (ordinary is not null)
                collectingNames = interner.Except(collectingNames, interner.With(NameSetInterner.Empty, ordinary));
            if (collecting is not null)
                collectingNames = interner.With(collectingNames, collecting);
            return new(kinds.ToImmutable(), interner, interner.With(rebased.Names, own), collectingNames);
        }

        /// <summary>
        /// These bindings with their canonical keys interned by <paramref name="interner"/>: a snapshot
        /// recorded by one resolution run (a deferred branch's context) is re-keyed once by the run
        /// that reads it, so region keys never compare ids of two different interners.
        /// </summary>
        public ForwardableParameters Rebase(NameSetInterner interner)
        {
            if (ReferenceEquals(_interner, interner) || _kinds.IsEmpty)
                return this;

            var collecting = _kinds.Where(static entry => entry.Value == ParameterKind.Collecting).Select(static entry => entry.Key);
            return new(
                _kinds,
                interner,
                interner.With(NameSetInterner.Empty, _kinds.Keys),
                interner.With(NameSetInterner.Empty, collecting));
        }
    }

    /// <summary>
    /// One map version: the entries changed since its parent, each with the entry it replaced
    /// (null when the name was absent) and the entry it recorded. Retained only by the resolution
    /// run, and deliberately WITHOUT the version's immutable dictionary (SEC-S1): a version chain
    /// that kept every superseded dictionary alive retained each write's path copy — O(P log P)
    /// nodes for a level of P properties, a third of the front end's live peak on dense source —
    /// although only the CURRENT entries of a map are ever probed. The change records are exactly
    /// what <see cref="SignatureFootprints.Capture"/> replays, and they recover any ancestor's
    /// entry for a name from the current one. Deferred regions retain the immutable dictionary alone.
    /// </summary>
    internal sealed record SignatureVersion(
        SignatureVersion? Parent,
        SignatureChange[] Changes);

    /// <summary>One entry a <see cref="SignatureVersion"/> wrote: the name, the entry it replaced (null when absent), and the new entry.</summary>
    internal readonly record struct SignatureChange(string Name, VisibleProperty? Previous, VisibleProperty Current);

    /// <summary>
    /// Exact canonical projections of visible signatures onto a body's free names. Version
    /// identity is only a cache over immutable inputs; REGION identity is the canonical set of
    /// (name, signature-reference) tokens. Equal projections reached through different map
    /// histories therefore compare in O(1). A small map delta updates only affected free names.
    /// A first query or a large delta probes the free names directly, never scans a wide map for
    /// a narrow query. Walking back at most that many changes also seeds shared ancestor caches.
    /// </summary>
    internal sealed class SignatureFootprints
    {
        private readonly NameSetInterner _tokens = new();
        private readonly Dictionary<string, Dictionary<VisibleProperty, CanonicalNameSet>> _bindings = new(StringComparer.Ordinal);
        private readonly Dictionary<int, Dictionary<SignatureVersion, CanonicalNameSet>> _projections = [];
        private int _nextToken;

        private CanonicalNameSet Binding(string name, VisibleProperty signature)
        {
            if (!_bindings.TryGetValue(name, out var signatures))
                _bindings.Add(name, signatures = new(ReferenceEqualityComparer.Instance));
            if (!signatures.TryGetValue(signature, out var token))
                signatures.Add(signature, token = _tokens.With(NameSetInterner.Empty,
                    [(++_nextToken).ToString(System.Globalization.CultureInfo.InvariantCulture)]));
            return token;
        }

        /// <summary>
        /// The projection of <paramref name="map"/>'s CURRENT entries (its <see cref="SignatureMap.Version"/>)
        /// onto <paramref name="freeNames"/>. A direct probe at an ANCESTOR version — the walk's
        /// first version, or one whose delta exceeds the remaining budget — reads that ancestor's
        /// entry for each free name from the current entries, undone by the oldest change the walked
        /// versions made to it: the same entries the ancestor's dictionary held, without retaining it.
        /// </summary>
        public CanonicalNameSet Capture(CanonicalNameSet freeNames, NameSetInterner names,
            SignatureMap map, FrontEndTraversalObservations? observations)
        {
            if (freeNames.Count == 0)
                return NameSetInterner.Empty;
            if (!_projections.TryGetValue(freeNames.Id, out var cache))
                _projections.Add(freeNames.Id, cache = new(ReferenceEqualityComparer.Instance));
            var pending = new Stack<SignatureVersion>();
            var current = map.Version;
            var work = 0;
            CanonicalNameSet result;
            while (!cache.TryGetValue(current, out result))
            {
                if (current.Parent is null || current.Changes.Length > freeNames.Count - work)
                {
                    // Entries the walked versions replaced, as the ancestor held them; the stack
                    // enumerates oldest first, so the first change seen for a name is decisive.
                    Dictionary<string, VisibleProperty?>? undone = null;
                    foreach (var walked in pending)
                    {
                        foreach (var change in walked.Changes)
                            (undone ??= new(StringComparer.Ordinal)).TryAdd(change.Name, change.Previous);
                    }

                    result = NameSetInterner.Empty;
                    foreach (var name in freeNames.Names)
                    {
                        observations?.RecordResolverSnapshotBindingProbe();
                        VisibleProperty? signature = null;
                        if (undone is not null && undone.TryGetValue(name, out var replaced))
                            signature = replaced;
                        else if (map.TryGetValue(name, out var entry))
                            signature = entry;
                        if (signature is not null)
                            result = _tokens.Union(result, Binding(name, signature));
                    }
                    cache.Add(current, result);
                    break;
                }
                work += current.Changes.Length;
                pending.Push(current);
                current = current.Parent;
            }
            while (pending.TryPop(out current))
            {
                foreach (var change in current.Changes)
                {
                    observations?.RecordResolverSnapshotBindingProbe();
                    if (!names.Contains(freeNames, change.Name))
                        continue;
                    if (change.Previous is { } previous)
                        result = _tokens.Except(result, Binding(change.Name, previous));
                    result = _tokens.Union(result, Binding(change.Name, change.Current));
                }
                cache.Add(current, result);
            }
            return result;
        }
    }

    /// <summary>
    /// A completed algorithm region: the rewritten algorithm and, for a conditional branch
    /// body, the diagnostics its own rewrite reported — unforwardable bare-forwarding parameters
    /// (worded with the family's name), unforwardable callables and unliftable clause families — as
    /// re-issuable templates; and the context it was processed in, whose publications every other
    /// context the region serves reads for its own descendants (B3-5★).
    /// </summary>
    private sealed record AlgorithmRegion(Algorithm Rewritten, IReadOnlyList<BranchDiagnosticTemplate>? DiagnosticTemplates,
        StaticScopeKey? Context);

    /// <summary>One branch-body report, minus the family name that words it.</summary>
    private readonly record struct BranchDiagnosticTemplate(
        DiagnosticCode Code,
        Func<string?, DiagnosticMessage> FormatMessage,
        SourceSpan? Span);

    /// <summary>
    /// The FREE reference names of an algorithm's subtree: every <see cref="Expr.Resolve"/>
    /// name in its output rows and property values (recursively) that the subtree does not
    /// bind itself (a body's property names bind for everything inside it; parameters and
    /// binders are already <see cref="Expr.Param"/>s). These are exactly the names whose
    /// visible-map signatures the rewrite of the subtree can read — bare and called
    /// references, the alias and canonical <c>Math</c> shadow checks, and the signature analysis's
    /// equation references all probe the map by a written name — plus the names of each
    /// body's OWN open heads: an open target is rewritten with fresh maps, but its head is
    /// resolved where the body is written and decides which callees the body's rows lift
    /// (equations read open providers), so two reaches whose open heads select different
    /// callees must not share a region (S-10 F2). A level's declarations never remove its
    /// own open heads: an open list is read outside the level that writes it, as in
    /// <see cref="RegionFreeNames"/>. Stored dot-edge lexical fallbacks (never rewritten)
    /// still read nothing here, deliberately unlike <see cref="RegionFreeNames"/>. A pure
    /// function of the node: memoized per run, and reference-visited per subtree so a
    /// shared expression contributes its names once.
    /// </summary>
    private sealed class ReferenceNames(NameSetInterner interner)
    {
        public CanonicalNameSet Set { get; private set; }
        public void Add(string name) => Set = interner.With(Set, [name]);
        public void Remove(string name) => Set = interner.Except(Set, interner.With(NameSetInterner.Empty, [name]));
        public void UnionWith(CanonicalNameSet other) => Set = interner.Union(Set, other);
    }

    /// <summary>
    /// The open chain a nested algorithm's rewrite can read: the map's, when one of its free names is
    /// neither a visible property nor a prelude member (only then does resolution consult opens).
    /// </summary>
    private static OpenLevel? OpensReadBy(CanonicalNameSet freeNames, SignatureMap map, ResolutionRun run)
    {
        if (map.Opens is not { } opens)
            return null;
        foreach (var name in freeNames.Names)
        {
            if (!map.ContainsKey(name) && !run.Prelude.TryGetMember(name, out _))
                return opens;
        }

        return null;
    }

    private static CanonicalNameSet FreeReferenceNames(Algorithm algorithm, ResolutionRun run)
    {
        FrontEndStack.Ensure();
        var memo = run.FreeReferenceNames ??= new(ReferenceEqualityComparer.Instance);
        if (memo.TryGetValue(algorithm, out var cached))
            return cached;

        var names = new ReferenceNames(run.ReferenceNameSets);
        switch (algorithm)
        {
            case Algorithm.User user:
            {
                var visited = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
                foreach (var row in user.Output)
                    CollectReferenceNames(row, names, visited, run);
                foreach (var property in user.Properties)
                    names.UnionWith(FreeReferenceNames(property.Value, run));
                foreach (var property in user.Properties)
                    names.Remove(property.Name);
                // A body's own open heads decide which callees its rows lift, and an open list is read outside the level
                // that writes it: they are added AFTER the level's declarations are removed (RegionFreeNames' rule).
                if (user.Opens.Count > 0)
                {
                    // A path shared with a row must be walked again: removing local names also removed its contribution.
                    visited.Clear();
                    foreach (var open in user.Opens)
                        CollectReferenceNames(open, names, visited, run);
                }
                break;
            }

            case Algorithm.Conditional conditional:
                foreach (var branch in conditional.Branches)
                    names.UnionWith(FreeReferenceNames(branch.Body, run));
                // Kept for RegionFreeNames' rule: elaboration leaves a family's own open list empty (its clauses own theirs).
                if (conditional.Opens.Count > 0)
                {
                    var heads = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
                    foreach (var open in conditional.Opens)
                        CollectReferenceNames(open, names, heads, run);
                }
                break;

            case Algorithm.Builtin:
                break;

            default:
                throw new InvalidOperationException(
                    $"Unhandled Algorithm variant in {nameof(ImplicitArgumentResolver)}.{nameof(FreeReferenceNames)}: {algorithm.GetType().Name}.");
        }

        memo[algorithm] = names.Set;
        return names.Set;
    }

    private static void CollectReferenceNames(Expr expr, ReferenceNames names, HashSet<Expr> visited, ResolutionRun run)
    {
        FrontEndStack.Ensure();
        if (AstTraversalDagSafety.HasTraversableExprChildren(expr) && !visited.Add(expr))
            return;

        switch (expr)
        {
            case Expr.Resolve(var name):
                names.Add(name);
                break;

            case Expr.Call(var function, var args):
                CollectReferenceNames(function, names, visited, run);
                foreach (var arg in args)
                    CollectReferenceNames(arg, names, visited, run);
                break;

            case Expr.Binary(_, var left, var right):
                CollectReferenceNames(left, names, visited, run);
                CollectReferenceNames(right, names, visited, run);
                break;

            case Expr.Comparison(var first, var links):
                CollectReferenceNames(first, names, visited, run);
                foreach (var link in links)
                    CollectReferenceNames(link.Operand, names, visited, run);
                break;

            case Expr.Unary(_, var operand):
                CollectReferenceNames(operand, names, visited, run);
                break;

            case Expr.Index(var target, var selectors):
                CollectReferenceNames(target, names, visited, run);
                foreach (var selector in selectors)
                    CollectReferenceNames(selector, names, visited, run);
                break;

            case Expr.SequenceSpread(var operand):
                CollectReferenceNames(operand, names, visited, run);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectReferenceNames(left, names, visited, run);
                CollectReferenceNames(right, names, visited, run);
                break;

            case Expr.ListLiteral(var items):
                foreach (var item in items)
                    CollectReferenceNames(item, names, visited, run);
                break;

            case Expr.DotCall dotCall:
                // The target is read (a bare `Math` receiver is a shadow check, a called
                // receiver is a name). The stored lexical fallback is never rewritten, but its
                // KIND classifies the edge's receiver and argument roles, so its name is read.
                CollectReferenceNames(dotCall.Target, names, visited, run);
                if (dotCall.EffectiveLexicalFallback is Expr.Resolve(var fallbackName))
                    names.Add(fallbackName);
                if (dotCall.Args is { } dotArgs)
                {
                    foreach (var arg in dotArgs)
                        CollectReferenceNames(arg, names, visited, run);
                }

                break;

            case Expr.Grace(var inner, _):
                CollectReferenceNames(inner, names, visited, run);
                break;

            case Expr.AlgorithmExpr(var nested):
                names.UnionWith(FreeReferenceNames(nested, run));
                break;

            case Expr.Capture(var rows):
                foreach (var row in rows)
                    CollectReferenceNames(row, names, visited, run);
                break;

            // Intentional leaves: no written name the resolver could look up.
            case Expr.Param:
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.BoolLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                break;

            // Runtime exhaustiveness guard (statement-form collector, which the closed Expr
            // hierarchy cannot make compiler-exhaustive — see AstWalker.VisitExpr): a new Expr
            // variant must be classified above rather than silently keeping its names out of
            // the region key.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ImplicitArgumentResolver)}.{nameof(CollectReferenceNames)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a recursive case or an intentional leaf.");
        }
    }

    /// <summary>
    /// The CALLER-dependent configuration one algorithm's implicit-call rewriting runs under:
    /// the enclosing algorithm's parameter patterns, the source binding kinds derived from
    /// them, and its closed-explicit-list gate. Every rewrite decision that is not a property
    /// of the node itself or of the visible signature map reads this record, so it must travel
    /// unchanged into every sub-context of the same algorithm — including value-demanding
    /// argument slots (a Math, host-operation, builtin value or family argument), which are
    /// ordinary value positions of the SAME caller: a value-demanding consumer decides WHERE
    /// lifting happens, never HOW (an earlier revision erased this context for Math arguments,
    /// and a neutral <c>Math.Abs(...)</c> wrapper then changed forwarding).
    ///
    /// <para>Bundling the values is deliberate: they are one semantic unit, and the
    /// defect this record replaces was exactly a call site that supplied some of them
    /// degenerately and silently defaulted the others away.</para>
    /// </summary>
    /// <param name="CallerParameterPatterns">
    /// The enclosing algorithm's parameter patterns — the forwarding SOURCE shape.
    /// </param>
    /// <param name="SourceBindingKinds">
    /// Caller capture name to binding kind, so re-spread decisions read the source binding
    /// (see <see cref="BuildSourceBindingKinds"/>).
    /// </param>
    /// <param name="ClosedParameterNames">
    /// Non-null inside an algorithm whose parameter list is CLOSED — a written explicit
    /// parameter list, or a conditional branch pattern — carrying that list's declared
    /// capture names: nothing may be lifted that would need a capture the list does not
    /// already declare. Null when the list is OPEN and lifting may add captures. The
    /// presence of the set IS the closed state; there is no separate flag to keep in step.
    /// </param>
    /// <param name="ConditionalBranchName">
    /// Non-null when the closed specification is a conditional BRANCH PATTERN rather than a
    /// written explicit parameter list: the family's property name, used only to word the
    /// branch's own diagnostics (an unforwardable parameter) in the branch's own terms.
    /// </param>
    /// <remarks>
    /// A reference type, allocated EXACTLY ONCE per rewrite region and forwarded by reference
    /// through the whole walk: that makes the region's memo-soundness guard one reference
    /// comparison (<see cref="ResolverWalkMemos.PinRewriteContext"/>) instead of a per-node
    /// field-by-field comparison, and keeps the recursion spine passing one reference rather
    /// than copying several values.
    /// </remarks>
    private sealed record ImplicitRewriteContext(
        IReadOnlyList<ParameterPattern> CallerParameterPatterns,
        IReadOnlyDictionary<string, ParameterKind> SourceBindingKinds,
        IReadOnlySet<string>? ClosedParameterNames,
        string? ConditionalBranchName = null)
    {
        /// <summary>
        /// FE-3: for an OPEN (liftable) context, the owner's final signature — the list whose facts
        /// <see cref="SourceBindingKinds"/> are — so a bundle can be shared with every other owner
        /// whose forwarding inputs are identical (<see cref="SharedBundleKey"/>). Null for a closed
        /// context (a written explicit list or a branch pattern), whose bundles stay region-local.
        /// </summary>
        public IReadOnlyList<ParameterPattern>? FinalSignature { get; init; }

        /// <summary>
        /// Q-04: the ENCLOSING parameter bindings this owner's forwarding reuses for a callee
        /// capture its own parameters do not bind — the source of that capture's synthesized
        /// argument and, for a re-spread decision, of its binding kind. A name they bind is never
        /// lifted into an open owner and is never missing from a closed one.
        /// </summary>
        public ForwardableParameters Forwardable { get; init; } = ForwardableParameters.None;

        /// <summary>
        /// The forwarding SOURCE kind of <paramref name="name"/>: the owner's own binding (its
        /// signature, lifted captures included), else the enclosing parameter binding forwarding
        /// reuses, else none (the name is about to be lifted as a copy of the callee's capture).
        /// </summary>
        public bool TryGetSourceBindingKind(string name, out ParameterKind kind)
            => SourceBindingKinds.TryGetValue(name, out kind) || Forwardable.TryGetKind(name, out kind);
    }

    /// <summary>
    /// FE-3: the EXACT inputs of <see cref="BuildImplicitCallArguments"/> for one callee in one open
    /// rewrite context, by reference: the callee's pattern list; the caller's single collecting
    /// stream (the only way the caller's OWN patterns enter the bundle — its forwarding source), or
    /// <see cref="NoForwardedStream"/>; and the list whose first-occurrence binding kinds are read for
    /// the callee's capture names — a composed owner signature's shared TAIL when none of those names
    /// is in the owner-local head (the kinds then come from the tail alone), otherwise the owner's
    /// whole signature. Owners with equal keys build byte-identical bundles, so they share one.
    /// </summary>
    private readonly record struct SharedBundleKey(object Callee, object ForwardedStream, object Kinds)
    {
        public bool Equals(SharedBundleKey other)
            => ReferenceEquals(Callee, other.Callee)
                && ReferenceEquals(ForwardedStream, other.ForwardedStream)
                && ReferenceEquals(Kinds, other.Kinds);

        public override int GetHashCode()
            => HashCode.Combine(
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Callee),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(ForwardedStream),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Kinds));
    }

    private static readonly object NoForwardedStream = new();

    /// <summary>
    /// The conditional branch a body belongs to, threaded into
    /// <see cref="ProcessAlgorithm"/> so the body resolves under the CLOSED branch-pattern
    /// rule: its pattern binders are its only inputs, exactly like a written explicit
    /// parameter list, and its <see cref="Algorithm.User.Parameters"/> stay empty.
    /// </summary>
    private sealed record ConditionalBranchContext(string BranchName, Pattern Pattern);

    /// <summary>
    /// Ledger slots (64 B each) charged per synthesized argument of an implicit-argument bundle the resolver BUILDS
    /// (<c>ResolverWalkMemos.BuildImplicitArgumentBundle</c> and closed bare forwarding): the argument node and its
    /// bundle slot. With <see cref="ImplicitSignatureTemplateInterner.SignatureStorageUnits"/> for the signature side, a
    /// logical lifted item costs 6 slots, the ≈335 B measured on the distinct-name lifting chain. A bundle served from
    /// the region's or the run's shared memo (FE-2/FE-3) allocates nothing and is never charged.
    /// </summary>
    internal const long BundleStorageUnits = 2;

    /// <summary>
    /// Reference-identity memo state for the walks of ONE constant rewrite context region —
    /// either one algorithm's output-rewrite phase (its visible signature map is final once
    /// the property loop completed, and its <see cref="ImplicitRewriteContext"/> is one fixed
    /// value for every row and every sub-context below them) or one algorithm's open-target
    /// region (fresh empty signature maps throughout; open targets never reach the rewrite
    /// maps at all). Maps are keyed by the ORIGINAL node reference and split by the ONE
    /// context dimension that legitimately changes a node's rewrite within the region: call
    /// position (a callee <see cref="Expr.Resolve"/> stays bare where a value-position one
    /// lifts). Shared input therefore rewrites once per distinct (node, position) and stays
    /// shared in the output. Strict-value diagnostic observation is tracked separately: it
    /// changes no rewrite, but a neutral memo hit must not suppress a later strict reach.
    /// <see cref="Algorithms"/> memoizes nested-algorithm processing so two distinct
    /// <see cref="Expr.AlgorithmExpr"/> wrappers over ONE shared algorithm resolve it once
    /// (same signature map for every such call inside the region).
    ///
    /// <para><b>Memo soundness invariant:</b> node reference plus call position is a complete
    /// key ONLY because the region's <see cref="ImplicitRewriteContext"/> is invariant. That
    /// is not a comment but a checked fact: <see cref="PinRewriteContext"/> records the first
    /// context the region rewrites under and throws on any later divergence, so a future
    /// caller that reintroduces a sub-context with its own configuration fails loudly here
    /// instead of silently serving another caller's rewrite. This is what made the
    /// pre-fix value-demanding sub-context safe to unify AND what made it wrong: it unified
    /// by ERASING the caller's configuration rather than by preserving it.</para>
    /// </summary>
    private sealed class ResolverWalkMemos(
        ResolutionRun run,
        FrontEndTraversalObservations? observations,
        DiagnosticBag? diagnostics)
    {
        private ImplicitRewriteContext? _pinnedRewriteContext;

        /// <summary>The resolution this region belongs to (its algorithm region memo).</summary>
        public readonly ResolutionRun Run = run;

        /// <summary>
        /// Q-04: the enclosing parameter bindings a block written in this region's rows may reuse
        /// for its own forwarding — the region owner's forwardable bindings plus its own
        /// name-resolution parameters (<see cref="ForwardableParameters.None"/> for an open-target
        /// region, whose targets are rooted at the prelude).
        /// </summary>
        public ForwardableParameters NestedForwarding { get; init; } = ForwardableParameters.None;

        /// <summary>
        /// Non-null only for a conditional branch body's own output-rewrite region: the
        /// templates of the diagnostics it issues for the branch (unforwardable-parameter and
        /// -callable and unliftable-family reports), kept on the region so a further family sharing the
        /// body re-issues them under its own name (M4).
        /// </summary>
        public List<BranchDiagnosticTemplate>? BranchDiagnosticTemplates;

        private static readonly string RewriteContextViolationMessage =
            $"{nameof(ImplicitArgumentResolver)} memo soundness violation: one rewrite region observed two "
            + "different caller rewrite contexts. The reference-identity rewrite memo is keyed by node and call "
            + "position only, which is complete solely while the region's caller configuration (parameter "
            + "patterns, source binding kinds, closed-explicit-list gate) stays fixed. Allocate the region's "
            + $"{nameof(ImplicitRewriteContext)} once and forward that instance; a sub-context that genuinely "
            + "needs its own configuration needs its own region memo.";

        public Dictionary<Expr, Expr>? ValueRewrites;

        public Dictionary<Expr, Expr>? CalleeRewrites;

        public Dictionary<Expr, Expr>? OpenRewrites;

        public Dictionary<Expr, Expr>? NestedRewrites;

        public Dictionary<Algorithm, Algorithm>? Algorithms;

        /// <summary>
        /// Family reports already issued in this region. Strict/eager diagnostic replay may
        /// revisit a value rewrite, but must not report its unnameable family a second time.
        /// </summary>
        public HashSet<Expr>? UnliftableFamilyDiagnosticVisits;

        /// <summary>
        /// Declaration-level output spreading (D2): the bare references already reported in this region as needing a
        /// written call (<see cref="DiagnosticCode.OutputSpreadReferenceNeedsCall"/>), once per reference.
        /// </summary>
        public HashSet<Expr>? OutputSpreadReferenceReports;

        /// <summary>
        /// The region's one rewrite context once its rewrite has started (<see cref="PinRewriteContext"/>); null in the
        /// analysis and while an open body's dependencies are collected, where no closed list exists.
        /// </summary>
        public ImplicitRewriteContext? PinnedRewriteContext => _pinnedRewriteContext;

        /// <summary>
        /// The verdict each MAY edge's roles read in this region (<see cref="MissSelectionOf"/>): one answer per edge, so
        /// the dependency walk and the rewrite never read two.
        /// </summary>
        public Dictionary<Expr.DotCall, LexicalFallbackSelection>? LiftMissSelections;

        public readonly FrontEndTraversalObservations? Observations = observations;

        /// <summary>
        /// The pass-wide diagnostic sink, threaded beside <see cref="Observations"/> so
        /// every region of one resolution appends to the SAME list. Null for the
        /// standalone entry points that only rewrite. A blocked lift returns the same
        /// reference either way, so rewrite maps never depend on this field; the separate
        /// strict-visit set above tracks the reporting side effect.
        /// </summary>
        public readonly DiagnosticBag? Diagnostics = diagnostics;

        /// <summary>
        /// Fail-loud guard for the memo soundness invariant above. One reference comparison,
        /// because a region allocates its <see cref="ImplicitRewriteContext"/> once and every
        /// walk below forwards that instance. Deliberately stricter than value equality: an
        /// equal-but-freshly-built context also trips, which can only over-report (never let an
        /// unsound reuse through) and points at the right fix — hoist the allocation.
        /// </summary>
        public void PinRewriteContext(ImplicitRewriteContext context)
        {
            if (_pinnedRewriteContext is null)
            {
                _pinnedRewriteContext = context;
                return;
            }

            if (!ReferenceEquals(_pinnedRewriteContext, context))
                throw new InvalidOperationException(RewriteContextViolationMessage);
        }

        // The closed-list forwarding verdict per callee pattern list, under the one context it was
        // computed for: every reference to one callable in the region asks the same question —
        // the closed-list gate for each, the blocked-forwarding report for each blocked one — so
        // it is answered once. Answering it per reference cost O(K × L) for K references to a
        // callable of L parameters (and the former list-scan dedup made each answer O(L²)).
        private Dictionary<IReadOnlyList<ParameterPattern>, IReadOnlyList<string>>? _missingForwardingNames;
        private ImplicitRewriteContext? _missingForwardingNamesContext;

        public IReadOnlyList<string> MissingForwardingNames(
            IReadOnlyList<ParameterPattern> calleePatterns,
            ImplicitRewriteContext context,
            IReadOnlySet<string> closedParameterNames)
        {
            // The verdict depends on the caller's patterns and closed list, which the region's
            // pinned context fixes; any other context instance is answered without the memo.
            _missingForwardingNamesContext ??= context;
            if (!ReferenceEquals(_missingForwardingNamesContext, context))
            {
                Observations?.RecordResolverForwardingVerdict();
                return MissingClosedListForwardingNames(calleePatterns, context.CallerParameterPatterns, closedParameterNames, context.Forwardable);
            }

            _missingForwardingNames ??= new(ReferenceEqualityComparer.Instance);
            if (!_missingForwardingNames.TryGetValue(calleePatterns, out var missing))
            {
                Observations?.RecordResolverForwardingVerdict();
                missing = MissingClosedListForwardingNames(calleePatterns, context.CallerParameterPatterns, closedParameterNames, context.Forwardable);
                _missingForwardingNames.Add(calleePatterns, missing);
            }

            return missing;
        }

        // FE-2: the synthesized implicit-argument bundle per callee pattern list, under the one context
        // it was built for. A bundle is a pure function of the callee's parameter patterns and the
        // caller configuration (BuildImplicitCallArguments reads nothing else), and the region pins that
        // configuration, so every lifted reference to one callable in the region forwards the SAME
        // arguments: K references share ONE immutable bundle of L synthesized slots instead of K copies.
        // The bundle is syntax, not activation state — spanless reads of the caller's own bindings that
        // every call evaluates afresh in its own activation — and each reference keeps its own call node,
        // which carries its span and its origin entry. Region-local, so it never outlives the run.
        private Dictionary<IReadOnlyList<ParameterPattern>, OutputBundle>? _implicitArguments;
        private ImplicitRewriteContext? _implicitArgumentsContext;

        public OutputBundle ImplicitArguments(IReadOnlyList<ParameterPattern> calleePatterns, ImplicitRewriteContext context)
        {
            // Any other context instance is answered without the memo, exactly like the forwarding verdict.
            _implicitArgumentsContext ??= context;
            if (!ReferenceEquals(_implicitArgumentsContext, context))
                return BuildImplicitArgumentBundle(calleePatterns, context);

            _implicitArguments ??= new(ReferenceEqualityComparer.Instance);
            if (!_implicitArguments.TryGetValue(calleePatterns, out var arguments))
            {
                // FE-3: an OPEN context shares the bundle with every owner whose forwarding inputs are
                // identical (SharedBundleKey); a closed context keeps the region-local FE-2 bundle, and
                // so does a bundle whose re-spread decision reads an ENCLOSING binding's kind (Q-04) —
                // an input the shared key does not carry.
                if (context.FinalSignature is { } finalSignature
                    && !ReadsForwardableBindingKind(calleePatterns, context))
                {
                    var key = SharedBundleKeyOf(calleePatterns, context, finalSignature);
                    Run.SharedBundles ??= new();
                    if (!Run.SharedBundles.TryGetValue(key, out arguments))
                    {
                        arguments = BuildImplicitArgumentBundle(calleePatterns, context);
                        Run.SharedBundles.Add(key, arguments);
                    }
                }
                else
                {
                    arguments = BuildImplicitArgumentBundle(calleePatterns, context);
                }

                _implicitArguments.Add(calleePatterns, arguments);
            }

            return arguments;
        }

        /// <summary>
        /// Q-04: whether a synthesized bundle for this callee reads the KIND of an enclosing binding
        /// its owner's forwarding reuses — only a COLLECTING callee capture decides a re-spread, and
        /// only when the owner itself does not bind its name. Such a bundle depends on the enclosing
        /// bindings, which <see cref="SharedBundleKey"/> does not carry, so it stays region-local.
        /// </summary>
        private bool ReadsForwardableBindingKind(IReadOnlyList<ParameterPattern> calleePatterns, ImplicitRewriteContext context)
        {
            if (context.Forwardable.IsEmpty)
                return false;

            foreach (var name in Run.CollectingCaptureNamesOf(calleePatterns))
            {
                if (!context.SourceBindingKinds.ContainsKey(name) && context.Forwardable.Binds(name))
                    return true;
            }

            return false;
        }

        /// <summary>
        /// The <see cref="SharedBundleKey"/> of one callee under one open context: the caller's own
        /// patterns enter only as a single forwarded collecting stream, and the binding kinds of the
        /// callee's capture names come from a composed signature's shared tail exactly when no such
        /// name is in the owner-local head (the head is small, so the test costs the head).
        /// </summary>
        private SharedBundleKey SharedBundleKeyOf(
            IReadOnlyList<ParameterPattern> calleePatterns,
            ImplicitRewriteContext context,
            IReadOnlyList<ParameterPattern> finalSignature)
        {
            object forwardedStream = TryGetSingleTopLevelCollectingCapture(context.CallerParameterPatterns, out _)
                ? context.CallerParameterPatterns
                : NoForwardedStream;
            object kinds = finalSignature;
            // A forwarded stream reads the kind of the CALLER's own collecting name (in the head), so
            // only a bundle without one may take the tail's kinds.
            if (ReferenceEquals(forwardedStream, NoForwardedStream)
                && finalSignature is ImplicitSignatureTemplate { Tail: { } tail } composed)
            {
                var calleeNames = Run.CalleeNamesOf(calleePatterns);
                var headTouchesCallee = false;
                foreach (var capture in ParameterPattern.CapturesExpandingSharedNodesOnce(composed.Head))
                {
                    if (calleeNames.Contains(capture.Name))
                    {
                        headTouchesCallee = true;
                        break;
                    }
                }

                if (!headTouchesCallee)
                    kinds = tail;
            }

            return new SharedBundleKey(calleePatterns, forwardedStream, kinds);
        }

        private OutputBundle BuildImplicitArgumentBundle(IReadOnlyList<ParameterPattern> calleePatterns, ImplicitRewriteContext context)
        {
            FrontEndStack.Ensure();
            if (calleePatterns is ImplicitSignatureTemplate { Tail: { } tail } composed
                && context.FinalSignature is ImplicitSignatureTemplate source
                && ReferenceEquals(source.Tail ?? source, tail))
            {
                // These inputs forward the callee's own kinds unchanged. The local head
                // and shared tail are independent, including collecting/grouped patterns.
                // Every tail name is the owner's own lifted capture, so the tail bundle reads
                // no enclosing binding (Q-04) and stays shareable by every owner.
                var tailContext = context with
                {
                    CallerParameterPatterns = [],
                    SourceBindingKinds = tail.Facts.BindingKinds,
                    FinalSignature = tail,
                    Forwardable = ForwardableParameters.None,
                };
                var tailKey = SharedBundleKeyOf(tail, tailContext, tail);
                Run.SharedBundles ??= new();
                if (!Run.SharedBundles.TryGetValue(tailKey, out var tailArguments))
                {
                    tailArguments = BuildImplicitArgumentBundle(tail, tailContext);
                    Run.SharedBundles.Add(tailKey, tailArguments);
                }
                var head = BuildImplicitCallArguments(composed.Head, [], context.SourceBindingKinds, context.Forwardable);
                Run.ChargeImplicitArgumentBundle(head.Count);
                Observations?.RecordImplicitArgumentBundleBuilt(head.Count);
                return OutputBundle.Prepend(head, tailArguments);
            }
            var arguments = OutputBundle.From(BuildImplicitCallArguments(
                calleePatterns, context.CallerParameterPatterns, context.SourceBindingKinds, context.Forwardable));
            Run.ChargeImplicitArgumentBundle(arguments.Count);
            Observations?.RecordImplicitArgumentBundleBuilt(arguments.Count);
            return arguments;
        }

        /// <summary>One lifted reference's own call edge, observed once per reference.</summary>
        public Expr SynthesizedImplicitCall(Expr call)
        {
            Observations?.RecordImplicitCallSynthesized();
            return call;
        }

        public Dictionary<Expr, Expr> RewriteMapFor(LiftingRole role)
            => role == LiftingRole.Callable
                ? CalleeRewrites ??= new(ReferenceEqualityComparer.Instance)
                : ValueRewrites ??= new(ReferenceEqualityComparer.Instance);


    }

    /// <summary>
    /// Reference-identity memo for ONE implicit-dependency collection region (one algorithm's
    /// output rows; the signature map and the shared seen/deps accumulators are constant).
    /// Every contribution is seen-set deduplicated, so a revisit of a completed node — split
    /// by call position, which changes what a node contributes — adds nothing and is skipped.
    /// </summary>
    private sealed class DepsWalkMemo(FrontEndTraversalObservations? observations, ResolverWalkMemos walk)
    {
        public readonly HashSet<Expr> ValueVisited = new(ReferenceEqualityComparer.Instance);

        public HashSet<Expr>? CalleeVisited;

        public readonly FrontEndTraversalObservations? Observations = observations;

        /// <summary>
        /// The owner's rewrite region: the dependency walk resolves callees exactly as its rewrite
        /// will (a block receiver of a dotted callee is processed once, through this region's memo).
        /// </summary>
        public readonly ResolverWalkMemos Walk = walk;
    }

    /// <summary>
    /// The INPUT entries of one level's properties, per declaration index and by name (a later
    /// declaration of a name wins the map, as ownership-first lookup reads one declaration).
    /// </summary>
    private static (VisibleProperty[] ByIndex, Dictionary<string, VisibleProperty> ByName) BuildPropertyEntries(
        IReadOnlyList<Property> properties,
        DeclaringOwners owners,
        ResolverLevel? level,
        ResolutionRun run)
    {
        var byIndex = new VisibleProperty[properties.Count];
        var byName = new Dictionary<string, VisibleProperty>(StringComparer.Ordinal);
        var operation = run.StructuralOperation;
        for (var i = 0; i < properties.Count; i++)
        {
            var property = properties[i];
            // B3-5★: an open body's entry carries its SELECTED signature from the start (once the selection exists), so
            // no read of it — before or after its rewrite — sees an intermediate one.
            var signature = run.Selected is not null && operation is not null && level?.StaticContext is { } context
                && SelectedSignatureOf(operation.ContextOf(context.Key, property.Value), property.Name, run) is { } selected
                    ? selected
                    : CallableSignature.FromAlgorithm(property.Name, property.Value);
            byIndex[i] = new VisibleProperty(signature, property.Value, owners) { Level = level };
            byName[property.Name] = byIndex[i];
        }

        return (byIndex, byName);
    }

    /// <summary>
    /// Processes an algorithm: processes each of its properties (in declaration order: every signature it reads is
    /// selected beforehand, B3-5★), then collects implicit deps and rewrites the algorithm's own output. Every NESTED
    /// algorithm — a property value, a block literal, an open target, a conditional branch
    /// body — goes through the run's region memo (M4): one rewrite per
    /// <see cref="AlgorithmRegionKey"/>, sharing preserved in the output, and a branch body's
    /// family-worded diagnostics replayed for every further family that shares it.
    /// </summary>
    /// <remarks>
    /// <paramref name="forwardable"/> is what the algorithm's enclosing owners bind as PARAMETERS by
    /// name resolution (Q-04): the bindings its automatic forwarding may reuse instead of lifting a
    /// same-named parameter of its own.
    /// </remarks>
    private static Algorithm ProcessAlgorithm(
        Algorithm alg,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        bool isRoot,
        FrontEndTraversalObservations? observations,
        DiagnosticBag? diagnostics,
        ConditionalBranchContext? branchContext,
        ResolutionRun run) => alg switch
        {
            Algorithm.Builtin => alg,

            Algorithm.Conditional conditional => ProcessConditionalProperty(
                conditional, "<anonymous>", parentParamMap, forwardable, observations, diagnostics, run),

            // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is a fully-elaborated
            // leaf: its output is a single bound Param (rewritten by ParameterDetector), it has no
            // properties or opens, and its explicit N-capture pattern lifts nothing. The general path
            // would still build an O(N) existing-parameter set and source-binding-kind map per helper —
            // O(N^2) across a wide deconstruction's N helpers — only to rewrite an output that has no
            // implicit calls. Returning it unchanged is O(1) and identical.
            Algorithm.User { AssignmentDeconstructionTarget: not null } => alg,

            Algorithm.User { IsModuleElaborated: true } module when !isRoot => ProcessModuleRoot(module, observations, run),

            Algorithm.User user => ProcessUserAlgorithmRegion(
                user, parentParamMap, forwardable, isRoot, observations, diagnostics, branchContext, run),

            // A callable alias is this pass's own OUTPUT (FWD-02): the input tree never holds one,
            // so one reached here is already elaborated.
            Algorithm.Alias => alg,
        };

    /// <summary>
    /// A loaded module (Q-31 H-P, decided 2026-10-06) is a hygienic source unit rooted at the
    /// prelude: it resolves with no enclosing signatures, no enclosing parameter bindings to forward
    /// (Q-04's sources are the module's own), and its levels declared at the root level (Q-19 D-I's
    /// provider identities restart at the module) — the same at every import site, so the operation
    /// resolves it ONCE (Q-32 I-U), with its diagnostics in the operation's sink. A holder's
    /// parameters reach the module's callables only through explicit arguments, bare forwarding, and
    /// formula lifting written at the holder — never by the module reading them.
    /// </summary>
    private static Algorithm ProcessModuleRoot(Algorithm.User module, FrontEndTraversalObservations? observations, ResolutionRun run)
    {
        if (!run.Modules.TryGet(ModuleUnitPass.Resolution, module, out var resolved))
        {
            using var owners = run.EnterLevel(DeclaringOwners.Root, level: null);
            resolved = ProcessUserAlgorithmRegion(
                module,
                SignatureMap.Empty(observations),
                ForwardableParameters.None,
                isRoot: false,
                observations,
                run.Diagnostics,
                branchContext: null,
                run);
            run.Modules.Add(ModuleUnitPass.Resolution, module, resolved);
        }

        return resolved;
    }

    /// <summary>
    /// The user-algorithm half of <see cref="ProcessAlgorithm"/>: the root is rewritten once
    /// (nothing shares it), every nested body once per <see cref="AlgorithmRegionKey"/>. A nested
    /// body may elaborate to a callable alias (<see cref="TryCompleteLoneCalleeRow"/>); the root
    /// never does.
    /// </summary>
    private static Algorithm ProcessUserAlgorithmRegion(
        Algorithm.User alg,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        bool isRoot,
        FrontEndTraversalObservations? observations,
        DiagnosticBag? diagnostics,
        ConditionalBranchContext? branchContext,
        ResolutionRun run)
    {
        // The root is processed exactly once and keeps its bare-root rule; nothing shares it.
        if (isRoot)
        {
            var root = ProcessUserAlgorithm(alg, parentParamMap, forwardable, isRoot: true, observations, diagnostics, branchContext: null, run, diagnosticTemplates: null);
            PublishStructuralBody(alg, root, null, run);
            return root;
        }

        forwardable = forwardable.Rebase(run.ReferenceNameSets);
        var freeNames = FreeReferenceNames(alg, run);
        var regionKey = new AlgorithmRegionKey(
            alg,
            run.Footprints.Capture(freeNames, run.ReferenceNameSets, parentParamMap, observations),
            forwardable.Names,
            forwardable.CollectingNames,
            branchContext is null ? null
                : HasLoneBareRowShape(alg) ? run.BranchContexts.BareForwardingHeadId(branchContext.Pattern)
                : run.BranchContexts.ClosedSpecificationId(branchContext.Pattern),
            ReportsDiagnostics: diagnostics is not null,
            // The open chain is an input exactly when a free name reaches it: one the owner walk
            // (the map and the prelude) leaves undecided.
            OpensReadBy(freeNames, parentParamMap, run));
        var regions = run.AlgorithmRegions ??= new();
        if (regions.TryGetValue(regionKey, out var completedRegion))
        {
            if (branchContext is not null)
                ReplayBranchDiagnostics(completedRegion, branchContext.BranchName, diagnostics);
            // The reach shares the region's processed object, so its descendants' resolved publications are the processing
            // context's (publishing them per reach would cost one copy per PATH of a shared graph).
            if (PublishStructuralBody(alg, completedRegion.Rewritten, branchContext, run) is { } reach && completedRegion.Context is { } processed)
                run.StructuralOperation!.AliasResolvedRegion(reach, processed);
            return completedRegion.Rewritten;
        }

        if (branchContext is null)
            observations?.RecordResolverAlgorithmRegionExpansion();
        else
            observations?.RecordResolverBranchBodyRegionExpansion();

        var diagnosticTemplates = branchContext is not null && diagnostics is not null
            ? new List<BranchDiagnosticTemplate>()
            : null;
        var rewritten = ProcessUserAlgorithm(alg, parentParamMap, forwardable, isRoot: false, observations, diagnostics, branchContext, run, diagnosticTemplates);
        var context = PublishStructuralBody(alg, rewritten, branchContext, run);
        // Admitted only after the whole body completed (acyclic by the structural preflight).
        regions[regionKey] = new AlgorithmRegion(rewritten, diagnosticTemplates, context);
        return rewritten;
    }

    /// <summary>Publishes <paramref name="processed"/> as the resolved view of <paramref name="source"/> in its context; the context.</summary>
    private static StaticScopeKey? PublishStructuralBody(Algorithm source, Algorithm processed, ConditionalBranchContext? branch, ResolutionRun run)
    {
        if (run.StructuralOperation is not { } operation) return null;
        var key = operation.ContextOf(run.Level?.StaticContext?.Key ?? operation.Queries.Keys.Root, source, branch?.Pattern);
        operation.Publish(key, StaticPublicationStage.Resolved, processed);
        return key;
    }

    private static Algorithm ProcessUserAlgorithm(
        Algorithm.User alg,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        bool isRoot,
        FrontEndTraversalObservations? observations,
        DiagnosticBag? diagnostics,
        ConditionalBranchContext? branchContext,
        ResolutionRun run,
        List<BranchDiagnosticTemplate>? diagnosticTemplates)
    {
        FrontEndStack.Ensure();
        run.ObserveCancellation(FrontEndCancellationCheckpoint.ResolverAlgorithm);
        // This body is a level of its own (Q-19 D-I: what its properties' provider identities
        // are anchored at).
        var levelOwners = run.Owners.Inside(alg);
        var structuralContext = run.StructuralOperation is { } operation
            ? operation.Context(operation.ContextOf(run.Level?.StaticContext?.Key ?? operation.Queries.Keys.Root, alg, branchContext?.Pattern)) : null;
        var level = new ResolverLevel(levelOwners, run.Level, alg.Opens, structuralContext);
        if (structuralContext is not null) structuralContext.Operation.RegisterResolverLevel(level);
        run.AddWalkLevel(level);
        using var levelScope = run.EnterLevel(levelOwners, level);

        var newOpens = ProcessOpenExprs(alg.Opens, observations, diagnostics, run);

        // Q-04: the enclosing PARAMETER bindings this body's own forwarding reuses — those its
        // owners established, minus any name this body declares as a property (the nearer
        // declaration decides) — and, for every body nested in this one (property values, branch
        // bodies, and blocks written in its rows), those plus this body's own name-resolution
        // parameters: its written or inferred ones, or a branch body's binders. Never the
        // parameters forwarding itself adds below: they exist only for the callee that needed them.
        var ownForwarding = forwardable.WithoutProperties(alg.Properties, run.ReferenceNameSets);
        var nestedForwarding = ownForwarding.WithParameters(
            branchContext is null
                ? ParameterPattern.CapturesExpandingSharedNodesOnce(alg.NameResolutionParameterPatterns)
                : ParameterPattern.CapturesExpandingSharedNodesOnce(BranchBinderParameterPatterns(branchContext.Pattern)),
            run.ReferenceNameSets);

        // The level's own entries: every property's written value with its FINAL signature — the one the selection chose
        // (B3-5★) — so every read of a sibling, before or after its rewrite, sees the same signature.
        var (_, localEntriesByName) = BuildPropertyEntries(alg.Properties, levelOwners, level, run);
        level.Entries = localEntriesByName;

        // Visible map = parent + local (local overrides), plus this level's `open` providers as the
        // innermost open level. When there are neither local properties nor opens — the common leaf
        // case, e.g. every simple property value `A = expr` — nothing overrides the parent map and the
        // per-property loop below (the only writer of visibleParamMap) is empty, so the parent map is
        // shared instead of copied. Cloning this O(P) parent map once per leaf property is what made
        // this pass O(P^2) in the property count.
        var visibleParamMap = localEntriesByName.Count == 0 && newOpens.Count == 0
            ? parentParamMap
            : parentParamMap.Extend(localEntriesByName);
        if (newOpens.Count > 0)
            visibleParamMap.AttachOpens();

        // Every signature this level can read is final (B3-5★), so its properties are processed in declaration order:
        // no processing order, sibling-order channel, on-demand processing or demand nesting exists, and none could change
        // what a read sees. The map is never re-written while the level is processed, so a body shared by two properties
        // keys one rewrite region whatever was processed in between.
        var processedProperties = new Property[alg.Properties.Count];
        var loopImportSite = run.ImportSite;
        for (var idx = 0; idx < alg.Properties.Count; idx++)
        {
            var prop = alg.Properties[idx];
            run.ObserveCancellation(FrontEndCancellationCheckpoint.ResolverRow);

            if (prop.Value is Algorithm.User { IsAssignmentDeconstructionSource: true })
            {
                // Hoisted deconstruction right-hand side: written as rows of THIS body, so it
                // is rewritten in the output phase below with this body's own context and
                // acquires no parameters of its own (see RewriteDeconstructionSourceRows).
                processedProperties[idx] = prop;
            }
            else if (prop.Value is Algorithm.Conditional condAlg)
            {
                // A family's entry keeps its input value: processing rewrites branch bodies, never
                // the heads its kind and lifting signature are read from.
                using (run.EnterImportSiteExactly(ImportSite.OfProperty(prop) ?? loopImportSite))
                using (run.EnterLevel(levelOwners, level))
                {
                    var processedFamily = ProcessConditionalProperty(
                        condAlg, prop.Name, visibleParamMap, nestedForwarding, observations, diagnostics, run);
                    processedProperties[idx] = prop.WithValue(processedFamily);
                    run.CompleteStructure(condAlg, processedFamily, run.StructuralOperation!.ContextOf(level.StaticContext!.Key, condAlg));
                }
            }
            else
            {
                Algorithm processedBody;
                using (run.EnterImportSiteExactly(ImportSite.OfProperty(prop) ?? loopImportSite))
                using (run.EnterLevel(levelOwners, level))
                {
                    processedBody = ProcessAlgorithm(
                        prop.Value, visibleParamMap, nestedForwarding, isRoot: false, observations, diagnostics, branchContext: null, run);
                }

                run.CompleteStructure(prop.Value, processedBody, run.StructuralOperation!.ContextOf(level.StaticContext!.Key, prop.Value));
                processedProperties[idx] = prop.WithValue(processedBody);
            }
        }

        var newProperties = processedProperties.ToList();

        // ONE memo bundle spans this algorithm's whole output-rewrite phase: the property
        // loop above has completed, so visibleParamMap's contents are final for every
        // rewrite below, and all rows share the exact same context (see ResolverWalkMemos).
        var walkMemos = new ResolverWalkMemos(run, observations, diagnostics)
        {
            BranchDiagnosticTemplates = diagnosticTemplates,
            NestedForwarding = nestedForwarding,
        };

        // A LONE BARE ROW (FWD-02, M4★): a non-root OPEN body whose ONE written row is a bare reference to
        // an existing algorithm of ANY arity is a CALLABLE ALIAS (binding indirection, nothing
        // synthesized); a CLOSED body (a written parameter list or a clause branch) whose row names a
        // callable that declares parameterized callable structure is bare forwarding (the callee
        // receives the existing bindings of its parameters' names, never renamed, reshaped or added).
        // Every other body keeps formula lifting below.
        // A lone row completes to a user body or a callable alias; either keeps its variant.
        if (!isRoot && TryCompleteLoneCalleeRow(alg, branchContext, visibleParamMap, ownForwarding, walkMemos) is { } completed)
            return completed.WithOwnScope(newOpens, newProperties);

        // A lone bare row FWD-02 did not complete stays what it is — a bare reference, the cached
        // zero-argument read — and is never formula-lifted: which callables a lone row can alias or
        // forward to is FWD-02's question, never the formula law's (the bare lone row is not a
        // formula). Its reference therefore takes the CALLABLE role; a dot edge that is a CALL
        // (`L.sum` is `sum(L)`) still classifies its receiver by the call's slot.
        var rowRole = !isRoot && HasLoneBareRowShape(alg) ? LiftingRole.Callable : LiftingRole.Value;

        if (alg.HasExplicitParameterList || branchContext is not null)
        {
            // Two CLOSED input specifications share one gate: a written explicit parameter
            // list, and a conditional branch pattern. A branch body's only inputs are its
            // pattern binders — bound through valEnv at runtime exactly like declared
            // parameters — and its Parameters stay empty by invariant, so nothing may be
            // lifted that would need a capture the pattern does not already bind. The open
            // implicit-lifting path below would instead invent that capture as a body
            // parameter nothing ever binds (`Unknown name` at runtime).
            var closedPatterns = branchContext is null
                ? alg.ParameterPatterns
                : BranchBinderParameterPatterns(branchContext.Pattern);
            var closedParameterNames = branchContext is null
                ? new HashSet<string>(ParameterPattern.CapturesExpandingSharedNodesOnce(alg.ParameterPatterns).Select(static capture => capture.Name))
                : new HashSet<string>(branchContext.Pattern.BoundNamesExpandingSharedNodesOnce());
            var explicitContext = new ImplicitRewriteContext(
                closedPatterns,
                BuildSourceBindingKinds(closedPatterns),
                ClosedParameterNames: closedParameterNames,
                branchContext?.BranchName)
            {
                Forwardable = ownForwarding,
            };
            var newOutput = new List<Expr>(alg.Output.Count);
            foreach (var expr in alg.Output)
            {
                run.ObserveCancellation(FrontEndCancellationCheckpoint.ResolverRow);
                // A whole output row is an output-spreading position (R2).
                newOutput.Add(SpreadIfMarked(
                    expr,
                    RewriteImplicitCalls(
                        expr,
                        visibleParamMap,
                        explicitContext,
                        rowRole,
                        walkMemos),
                    visibleParamMap,
                    walkMemos));
            }

            AstHelpers.RewriteDeconstructionSourceRows(
                alg,
                newProperties,
                expr => SpreadIfMarked(
                    expr, RewriteImplicitCalls(expr, visibleParamMap, explicitContext, LiftingRole.Value, walkMemos), visibleParamMap, walkMemos),
                (source, view) => run.StructuralOperation!.Publish(
                    run.StructuralOperation.ContextOf(level.StaticContext!.Key, source), StaticPublicationStage.Resolved, view));

            return alg with
            {
                Opens = newOpens,
                Properties = newProperties,
                Output = newOutput,
            };
        }

        // Collect implicit dependencies from the algorithm's output and lift
        // them into its parameter list. One deps memo spans all rows (they share
        // the seen/deps accumulators, so the walk context is one region).
        var deps = new List<LiftedDependency>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var depsMemo = new DepsWalkMemo(observations, walkMemos);
        foreach (var expr in AstHelpers.WrittenRows(
            alg, isRoot ? expr => !ShouldPreserveBareRootRow(expr, visibleParamMap, isRoot: true, walkMemos) : null))
        {
            CollectImplicitDeps(expr, visibleParamMap, seen, deps, rowRole, depsMemo);
        }

        // The lifted parameter patterns: existing patterns first, then new dependency captures with
        // their recursive shape preserved — as a SHARED signature template (FE-3, see LiftSignature),
        // composed once by the signature selection (B3-5★). A capture an enclosing parameter binding
        // supplies is reused, never lifted (Q-04). X-02: an inferred signature satisfies the rules a
        // written one is held to — a lift that would compose an invalid contract (two collecting
        // parameters at one pattern level) is this definition's front-end error, reported here at
        // elaboration, never at a later call.
        var lifting = SelectedLifting(level, alg.ParameterPatterns, deps, ownForwarding, walkMemos);
        var finalPatterns = lifting.Patterns;

        // Rewrite output expressions. Source binding kinds come from the
        // LIFTED pattern list: a callee name missing from the original caller
        // parameters binds through the capture lifted above (possibly by an
        // earlier dependency with a different kind), and that lifted capture
        // is the forwarding source — or, for a name an enclosing parameter
        // binding supplies, that reused binding (Q-04).
        var liftedContext = new ImplicitRewriteContext(
            alg.ParameterPatterns,
            lifting.SourceBindingKinds,
            ClosedParameterNames: null)
        {
            FinalSignature = finalPatterns,
            Forwardable = ownForwarding,
        };
        var rewrittenOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
        {
            run.ObserveCancellation(FrontEndCancellationCheckpoint.ResolverRow);
            rewrittenOutput.Add(
                ShouldPreserveBareRootRow(expr, visibleParamMap, isRoot, walkMemos)
                    // THE ROOT CLAUSE keeps the ROW unlifted, never its block: a block head (`{ … }.K`, `{ … }.S.K`) is a
                    // body of its own, elaborated like every other body (the analysis recorded it). A bare row is a
                    // read, never a call, so it is never spread.
                    ? WithProcessedBlockHead(expr, visibleParamMap, walkMemos)
                    // A whole output row is an output-spreading position (R2).
                    : SpreadIfMarked(
                        expr,
                        RewriteImplicitCalls(
                            expr,
                            visibleParamMap,
                            liftedContext,
                            rowRole,
                            walkMemos),
                        visibleParamMap,
                        walkMemos));
        }

        AstHelpers.RewriteDeconstructionSourceRows(
            alg,
            newProperties,
            expr => SpreadIfMarked(
                expr, RewriteImplicitCalls(expr, visibleParamMap, liftedContext, LiftingRole.Value, walkMemos), visibleParamMap, walkMemos),
            (source, view) => run.StructuralOperation!.Publish(
                run.StructuralOperation.ContextOf(level.StaticContext!.Key, source), StaticPublicationStage.Resolved, view));

        // Lean: withParameterPatterns on the rewritten body — the lifted list replaces the
        // stored channel; Parameters/Params follow it. The patterns forwarding appended are
        // marked (Q-04): they complete the signature for callers, and no written name ever
        // denotes them.
        var lifted = alg with
        {
            ParameterPatterns = finalPatterns,
            ForwardingParameterStart = alg.ForwardingParameterStart
                ?? (lifting.Lifted ? alg.ParameterPatterns.Count : null),
            Opens = newOpens,
            Properties = newProperties,
            Output = rewrittenOutput,
        };

        // A RUNTIME-TARGET ALIAS (FWD-02, META-S3-2, Option A): decided only AFTER inference — Q-75's
        // implicit parameters and formula lifting — has completed, so a body that owns a parameter
        // keeps it and stays a formula, exactly as before.
        if (isRoot || RuntimeAliasRow(lifted, visibleParamMap, walkMemos) is not { } runtimeRow)
        {
            // An `.Algorithm` link that stays a calculation is no static callee of a marker either (R3).
            if (!isRoot)
                ReportOutputSpreadMarkerOnLink(alg, walkMemos);
            return lifted;
        }

        var runtimeAlias = new Algorithm.Alias(lifted, runtimeRow) { HasRuntimeTarget = true };
        ReportOutputSpreadMarkerOnAlias(runtimeAlias, targetName: "", target: null, walkMemos);
        return runtimeAlias;
    }

    /// <summary>
    /// THE RUNTIME-TARGET ALIAS RULE (FWD-02, META-S3-2; owner decision D2 = Option A, Q-75 unchanged):
    /// the row of an OPEN, non-root body that is completed with NO parameter of its own — no written
    /// list, no clause branch, nothing inferred (Q-75 / DOT-05) and nothing lifted — and whose ONE
    /// written row is a reference whose callable identity only the run can supply:
    /// <list type="bullet">
    ///   <item>a RUNTIME ROW (<see cref="AliasTargetRows.IsRuntimeRow"/>): an enclosing parameter binding,
    ///   an argumentless <c>.Algorithm</c> link, or an argumentless parameter-rooted member path;</item>
    ///   <item>a name or static structural path whose identity resolution (<see cref="TryResolveCallable"/>)
    ///   ends at a runtime-target body (<see cref="IsRuntimeTargetEndpoint"/>) — a chain, forward references
    ///   included: the endpoint's class is selected (B3-5★), never read from a processing order.</item>
    /// </list>
    /// Null for every other body. The classification is by binding and elaboration (the row's kind
    /// after detection, the selected declaration), never by spelling; the synthetic deconstruction
    /// plumbing keeps its own shape.
    /// </summary>
    private static Expr? RuntimeAliasRow(Algorithm.User body, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        if (body.HasExplicitParameterList
            || body.ParameterPatterns.Count != 0
            || body.IsSyntheticDeconstructionPlumbing
            || body.Output.Count != 1
            || AstHelpers.WrittenRows(body).Count != 1)
        {
            return null;
        }

        var row = body.Output[0];
        if (AliasTargetRows.IsRuntimeRow(row))
            return row;
        return row is Expr.Resolve or Expr.DotCall { Args: null }
            && TryResolveCallable(row, paramMap, memos, out _) is { } target
            && IsRuntimeTargetEndpoint(target, memos.Run)
            ? row
            : null;
    }

    private static IReadOnlyList<Expr> ProcessOpenExprs(
        IReadOnlyList<Expr> opens,
        FrontEndTraversalObservations? observations,
        DiagnosticBag? diagnostics,
        ResolutionRun run)
    {
        if (opens.Count == 0)
            return opens;

        // One memo bundle per open-target region: every walk below runs with a fresh EMPTY
        // signature map, so the region's rewrite context is constant regardless of which
        // fresh map instance a call site allocates. The region reports into the CALLER's
        // diagnostic sink like every other region of the pass (X-48): prelude rooting decides
        // what an open target can SEE, never which rules apply to it (MOD-06), so its bare
        // forwarding, formula lifting and inferred-signature verdicts are reported exactly as
        // they are for a property body — and a recovered signature, which exists only beside
        // its reported error, can never reach evaluation.
        var memos = new ResolverWalkMemos(run, observations, diagnostics);
        var processed = new List<Expr>(opens.Count);
        // An open target is wired to the prelude: a block in it is a level of the root level.
        using var rootOwners = run.EnterLevel(DeclaringOwners.Root, level: null);
        foreach (var open in opens)
            processed.Add(ProcessOpenExpr(open, memos));
        return processed;
    }

    private static Algorithm.Conditional ProcessConditionalProperty(
        Algorithm.Conditional conditional,
        string propertyName,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        FrontEndTraversalObservations? observations,
        DiagnosticBag? diagnostics,
        ResolutionRun run)
    {
        FrontEndStack.Ensure();
        var operation = run.StructuralOperation!;
        var publicationKey = operation.ContextOf(run.Level?.StaticContext?.Key ?? operation.Queries.Keys.Root, conditional);
        var canonical = operation.Published(publicationKey, StaticPublicationStage.Resolved) as Algorithm.Conditional;
        // A family can have several binding names in one declaring context. Branch-region memo
        // hits below still replay occurrence-worded diagnostics; its structural view publishes once.
        var newOpens = canonical?.Opens ?? ProcessOpenExprs(conditional.Opens, observations, diagnostics, run);
        // A family that owns opens (host-built only) is a level of its own, as in detection.
        var familyOwners = newOpens.Count == 0 ? run.Owners : run.Owners.Inside(conditional);
        var familyLevel = newOpens.Count == 0 ? run.Level : new ResolverLevel(
            conditional, familyOwners, run.Level,
            staticContext: run.StructuralOperation!.Context(run.StructuralOperation.ContextOf(
                run.Level?.StaticContext?.Key ?? run.StructuralOperation.Queries.Keys.Root, conditional)));
        var branches = canonical is null ? new List<CondBranch>(conditional.Branches.Count) : null;
        using (run.EnterLevel(familyOwners, familyLevel))
        {
            for (var index = 0; index < conditional.Branches.Count; index++)
            {
                var branch = conditional.Branches[index];
                if (branch.Body.DeferredRegion is { } region)
                {
                    if (canonical is not null) continue;
                    if (region.Structure is { } structural)
                    {
                        branches!.Add(branch with { Body = branch.Body with
                        {
                            DeferredRegion = region.WithStructure(structural with { Forwardable = forwardable }),
                        }});
                        continue;
                    }
                    throw new ArgumentException("Deferred resolution requires detection's shared structural context.", nameof(conditional));
                }

                // M4: the body is rewritten through the run's region memo — once per (body,
                // free-name signature snapshot, forwardable parameter bindings, closed binder
                // specification, reporting mode). A body shared by several families under one
                // region is rewritten once (sharing preserved in the output) and only its
                // blocked-forwarding diagnostics, the one thing that names THIS family, are
                // re-issued for the later families.
                var body = ProcessAlgorithm(
                    branch.Body, parentParamMap, forwardable, isRoot: false, observations, diagnostics,
                    new ConditionalBranchContext(propertyName, branch.Pattern), run);
                if (canonical is not null)
                {
                    if (!ReferenceEquals(canonical.Branches[index].Body, body))
                        throw new InvalidOperationException("A completed family's branch view cannot change.");
                }
                else branches!.Add(branch with { Body = body });
            }

        }
        if (canonical is not null) return canonical;
        var resolvedFamily = conditional with { Opens = newOpens, Branches = branches! };
        operation.Publish(publicationKey, StaticPublicationStage.Resolved, resolvedFamily);
        return resolvedFamily;
    }

    /// <summary>
    /// Re-issues a completed region's branch reports (see <see cref="AlgorithmRegion"/>) for a further family that
    /// shares the body — same references, same missing names, same spans, worded with THIS
    /// family's name — so per-family diagnostic multiplicity matches a fresh rewrite without
    /// performing one, independent of which family was reached first.
    /// </summary>
    private static void ReplayBranchDiagnostics(AlgorithmRegion region, string branchName, DiagnosticBag? diagnostics)
    {
        if (diagnostics is null || region.DiagnosticTemplates is null)
            return;

        foreach (var template in region.DiagnosticTemplates)
        {
            diagnostics.Add(new Diagnostic(template.FormatMessage(branchName), DiagnosticSeverity.Error, template.Span)
            {
                Code = template.Code,
            });
        }
    }

    /// <summary>
    /// The bodies one resolution PROCESSED (M4★): each written body with its processed form — the first, for a body a
    /// shared tree reaches in several regions — and the set of processed forms, so a recorded reference structure is
    /// completed with the processed body and a refined miss verdict reads only processed receivers. Deferred materialization reads prior resolved publications from its shared operation.
    /// </summary>
    internal sealed class ProcessedBodies(ProcessedBodies? outer, StaticStructureOperation? structuralOperation = null)
    {
        private Dictionary<Algorithm, Algorithm>? _processedOf;
        private HashSet<Algorithm>? _processed;

        /// <summary>Records that <paramref name="written"/> is processed as <paramref name="processed"/>.</summary>
        public void Record(Algorithm written, Algorithm processed)
        {
            (_processedOf ??= new(ReferenceEqualityComparer.Instance)).TryAdd(written, processed);
            (_processed ??= new(ReferenceEqualityComparer.Instance)).Add(processed);
        }

        /// <summary>The processed form of the written body <paramref name="written"/>, when it is processed.</summary>
        public Algorithm? ProcessedFormOf(Algorithm written)
            => _processedOf is not null && _processedOf.TryGetValue(written, out var processed) ? processed
                : structuralOperation?.ResolvedSource(written) ?? outer?.ProcessedFormOf(written);

        /// <summary>Whether <paramref name="algorithm"/> is a processed form.</summary>
        public bool IsProcessed(Algorithm algorithm)
            => _processed?.Contains(algorithm) == true
                || ReferenceEquals(structuralOperation?.ResolvedSource(algorithm), algorithm) || outer?.IsProcessed(algorithm) == true;
    }

    private static Expr ProcessOpenExpr(Expr expr, ResolverWalkMemos memos)
    {
        // DAG-safety: a shared node reference rewrites once per open-target region and stays
        // shared in the output. Childless leaves skip the memo.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return ProcessOpenExprCore(expr, memos);

        memos.OpenRewrites ??= new(ReferenceEqualityComparer.Instance);
        if (memos.OpenRewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        memos.Observations?.RecordResolverRewriteExpansion();
        rewritten = ProcessOpenExprCore(expr, memos);
        memos.OpenRewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr ProcessOpenExprCore(Expr expr, ResolverWalkMemos memos)
    {
        FrontEndStack.Ensure();
        return expr switch
        {
            Expr.AlgorithmExpr block => block with
            {
                Algorithm = ProcessSharedNestedAlgorithm(block.Algorithm, ImportSite.OfBlock(block), SignatureMap.Empty(memos.Observations), memos),
            },

            // Capture targets own no scope; rows recurse without lifting,
            // with a fresh signature map like every other open target.
            Expr.Capture capture => capture with
            {
                Body = new OutputBundle(
                    capture.Body
                        .Select(row => ProcessExprNested(row, SignatureMap.Empty(memos.Observations), memos))
                        .ToList()),
            },

            // `with` keeps the stored dot-edge facts (member span, lexical
            // fallback) intact.
            Expr.DotCall dotCall => dotCall with
            {
                Target = ProcessOpenExpr(dotCall.Target, memos),
                Args = dotCall.Args is { } dotArgs
                    ? ProcessArgumentBundle(dotArgs, SignatureMap.Empty(memos.Observations), memos)
                    : null,
            },

            Expr.SequenceSpread spread => spread with { Operand = ProcessOpenExpr(spread.Operand, memos) },

            Expr.SequenceConstruct construct => construct with
            {
                Left = ProcessOpenExpr(construct.Left, memos),
                Right = ProcessOpenExpr(construct.Right, memos),
            },

            Expr.ListLiteral list => list with { Items = list.Items.Select(item => ProcessOpenExpr(item, memos)).ToList() },

            Expr.Call call => call with
            {
                Function = ProcessOpenExpr(call.Function, memos),
                Args = ProcessArgumentBundle(call.Args, SignatureMap.Empty(memos.Observations), memos),
            },

            // Operator forms are never valid open targets (open-form validation
            // rejects them: BadOpenForm), but the parser produces them in diagnostic
            // recovery trees, where parameter detection has already elaborated their
            // operands like a capture's rows. Their operands are resolved the same
            // way — the transparent walk with a fresh empty signature map — so a
            // block inside `open -{ ... }` is resolved exactly as one inside
            // `open ({ ... }, 1)`.
            Expr.Unary or Expr.Binary or Expr.Comparison or Expr.Index
                => ProcessExprNestedCore(expr, SignatureMap.Empty(memos.Observations), memos),

            // Intentional leaves: name/literal leaves carry no nested algorithm
            // to process (a bare Resolve IS the ordinary open-target form);
            // Grace cannot survive parameter detection, which runs first, so a
            // host-supplied wrapper passes through untouched.
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence
                or Expr.NativeCall or Expr.Grace => expr,
        };
    }

    /// <summary>
    /// THE ROOT CLAUSE of the formula-lifting law: a bare ROOT output row naming a callable that
    /// requires supplied arguments stays an unlifted reference — whatever its category (a property,
    /// a builtin, a Math member, a host operation, a dotted or opened member, a clause family) — so
    /// evaluation reports that callable's own zero-argument demand rejection at the reference
    /// instead of lifting its parameters into the never-called root. A callable that accepts zero
    /// supplied arguments is never lifted anywhere (<see cref="RequiresSuppliedArguments"/>), so it
    /// needs no preservation.
    /// <para>The row is the analysis's bare root callable row (<see cref="BareRootRowCallable"/>, the one static
    /// decision of both phases), refined by the callee's FINAL lifting signature — the very one
    /// <see cref="TryResolveLiftable"/> reads (<see cref="TargetOf"/> of the same static callable). A bare root callable
    /// row that is not preserved names a callee that accepts zero supplied arguments and lifts nothing
    /// (see <see cref="BareRootRowCallable"/> for why, and for the check that enforces it).</para>
    /// </summary>
    private static bool ShouldPreserveBareRootRow(
        Expr expr,
        SignatureMap paramMap,
        bool isRoot,
        ResolverWalkMemos memos)
        => isRoot
            && BareRootRowCallable(expr, paramMap, memos) is { } callable
            && TargetOf(callable, memos.Run).Signature is var signature
            && (signature.Unnameable is not null || RequiresSuppliedArguments(signature.Signature!));

    /// <summary>
    /// THE implicit-lifting eligibility rule (Q-03, decided September 28 2026), consulted for
    /// every value-role reference whatever its category (<see cref="CollectImplicitDeps"/>,
    /// <see cref="RewriteBareReference"/>, <see cref="RewriteDotCall"/>) and by root-row
    /// preservation (<see cref="ShouldPreserveBareRootRow"/>): a value-role reference lifts to an
    /// implicit forwarding call ONLY when its callee's lifting signature REQUIRES supplied
    /// arguments, that is, when an ordinary call supplying zero arguments could NOT bind it.
    ///
    /// <para>A callee that accepts zero supplied arguments — no parameters, or only a top-level
    /// collecting parameter such as <c>Roll(*xs)</c> — is NEVER lifted, whatever position it
    /// stands in (an operator or comparison operand, a list element, an index target, a spread
    /// operand, a Math argument, a block body): declaring a parameter does
    /// not by itself make a bare reference a call. The reference stays a property-style value
    /// demand, which the evaluator accepts (<see cref="Evaluator.AcceptsZeroSuppliedArguments"/>
    /// reads the SAME rule, <see cref="ParameterPattern.AcceptsZeroSuppliedSlots"/>) and serves
    /// from the property cache, so <c>Roll == Roll</c> reads ONE value; only a written call
    /// (<c>Roll()</c>, <c>Roll(args)</c>) evaluates afresh. Lifting had judged "declares any
    /// parameter" before, so a collecting-only callee in a lifting position became the fresh
    /// call <c>Roll(xs*)</c> and bypassed the cache (PV-03).</para>
    /// Lean: <c>liftsBareValueReference</c>.
    /// </summary>
    private static bool RequiresSuppliedArguments(CallableSignature signature)
        => !signature.AcceptsZeroSuppliedArguments;

    /// <summary>
    /// One callee a formula lifts: its name (a Math function's canonical key), its signature, and the
    /// FIRST reference that lifts it, in traversal order — the position a report about the lifted
    /// signature names. Held as the node itself, never a span copy, so the collecting walk's frames
    /// stay span-free.
    /// </summary>
    private readonly record struct LiftedDependency(string Name, CallableSignature Signature, Expr Reference);

    /// <summary>The outcome of <see cref="LiftSignature"/> for one open owner.</summary>
    private readonly record struct LiftedSignature(
        IReadOnlyList<ParameterPattern> Patterns,
        IReadOnlyDictionary<string, ParameterKind> SourceBindingKinds,
        bool Lifted);

    /// <summary>
    /// FE-3: the lifted signature of one open owner — its own patterns first, then every dependency
    /// capture it does not already bind, in dependency order with recursive shape preserved (the
    /// exact pre-FE-3 order) — built from SHARED signature templates instead of a fresh per-owner copy.
    ///
    /// <para>The dependencies' merged captures (the TAIL) are a function of the dependencies alone,
    /// so they are merged once per distinct dependency sequence and interned
    /// (<see cref="ImplicitSignatureTemplateInterner.LiftedTail"/>). The owner's own patterns (the
    /// HEAD) meet the tail only through their capture names: when none is lifted, the head filters
    /// nothing and the signature is exactly <c>head ++ tail</c> — the tail itself for an owner with
    /// no own parameter (K such owners share ONE template), otherwise a composed signature that costs
    /// the head (<see cref="ImplicitSignatureTemplateInterner.Compose"/>, which charges that copy — and a
    /// composed tail's local head, which extending copies too — to the operation's static ledger). When an own name IS lifted, the
    /// owner's order is genuinely its own (its capture stays first and the lifted one is filtered),
    /// so that signature is merged per owner exactly as before and held as an immutable template.</para>
    ///
    /// <para>Q-04 (decided September 28 2026): a dependency capture that an ENCLOSING parameter
    /// binding already supplies (<paramref name="forwardable"/> — the binding a written reference of
    /// that name here already denotes) is never lifted: forwarding reuses that exact binding, and
    /// adding a same-named parameter to this owner would make every existing reference of the name
    /// inside it denote the new parameter instead. Only a genuinely unbound dependency becomes a new
    /// (forwarded) parameter. When the lifted tail meets such a binding the signature is merged per
    /// owner, like an owner whose own name is lifted; otherwise the shared templates are used as
    /// before.</para>
    /// </summary>
    private static LiftedSignature LiftSignature(
        IReadOnlyList<ParameterPattern> own,
        List<LiftedDependency> deps,
        ForwardableParameters forwardable,
        ResolutionRun run)
    {
        // A dependency whose whole shape the owner's own single collecting stream forwards
        // contributes no capture (the same per-dependency test as always, O(1) each).
        List<IReadOnlyList<ParameterPattern>>? included = null;
        foreach (var dependency in deps)
        {
            if (!CanForwardSingleCollectingStream(own, dependency.Signature.ParameterPatterns))
                (included ??= []).Add(dependency.Signature.ParameterPatterns);
        }

        var tail = included is null ? null : run.Templates.LiftedTail(included, MergeLiftedTail);
        if (tail is null)
            return new(own, SourceBindingKindsOf(own), Lifted: false);

        if (!forwardable.IsEmpty && run.TailMeetsForwardable(tail, forwardable))
        {
            var reused = MergeOwnerSignature(own, included!, forwardable);
            if (reused is null)
                return new(own, SourceBindingKindsOf(own), Lifted: false);
            var reusedDistinct = run.Templates.InternFlat(reused);
            run.Observations?.RecordOwnerSignatureMaterialized(reused.Length);
            return new(reusedDistinct, reusedDistinct.Facts.BindingKinds, Lifted: true);
        }

        var tailNames = tail.Facts.NameSet;
        var disjoint = true;
        foreach (var capture in ParameterPattern.CapturesExpandingSharedNodesOnce(own))
        {
            if (tailNames.Contains(capture.Name))
            {
                disjoint = false;
                break;
            }
        }

        if (disjoint)
        {
            // Charged where it allocates: the owner's head plus a composed tail's local head, which extending copies — so
            // a chain of distinct-name links (each owner extending its callee's composed signature) meters its Θ(N²).
            var signature = run.Templates.Compose(own.Select(run.Templates.Freeze).ToArray(), tail);
            run.Observations?.RecordOwnerSignatureInstance(ReferenceEquals(signature, tail) ? 0 : signature.Head.Count);
            return new(signature, signature.Facts.BindingKinds, Lifted: true);
        }

        var merged = MergeOwnerSignature(own, included!, ForwardableParameters.None);
        if (merged is null)
            return new(own, SourceBindingKindsOf(own), Lifted: false);
        var distinct = run.Templates.InternFlat(merged);
        run.Observations?.RecordOwnerSignatureMaterialized(merged.Length);
        return new(distinct, distinct.Facts.BindingKinds, Lifted: true);
    }

    /// <summary>
    /// X-02 (decided September 30 2026): INFERRED SIGNATURES ARE HELD TO THE RULES OF WRITTEN ONES.
    /// Formula lifting composes an owner's signature from its callees' contracts, and the composition
    /// can describe a contract no source may declare — <c>C1(a, *p)</c> and <c>C2(b, *q)</c> make
    /// <c>K = C1 + C2</c> the signature <c>K(a, *p, b, *q)</c>, with two collecting parameters at one
    /// level, whose argument allocation is undefined. Such a signature is the definition's front-end
    /// error, reported where lifting builds it (<see cref="ParameterPattern.FindSignatureViolation"/>,
    /// the one validity rule every written parameter list is held to), never deferred to a call: a
    /// collecting binding is never chosen, merged, split or turned fixed to make the lift succeed.
    /// In a recursive group the judged signature is the settled one: a round may read another member's
    /// recovered list, whose flag is part of the state, and only a flag the settled state keeps is reported.
    /// Two callees that collect under the SAME name share one binding (by-name lifting), so
    /// <c>K(a, *rest, b)</c> is valid, and so is a collector nested in its own structural group.
    ///
    /// <para>The report is <see cref="DiagnosticCode.InvalidCollectingBinding"/> (the code of the
    /// same rule for a written head; the singleton rule keeps
    /// <see cref="DiagnosticCode.SingletonSequencePattern"/>), positioned at the reference whose lift
    /// completes the violation — the second collecting parameter's callee — or at the import site
    /// inside imported content. The returned signature is the parser's recovery shape for a written
    /// head (<see cref="ParameterPattern.KeepFirstCollectingCapturePerLevel"/>), so the erroneous tree
    /// still carries only signatures the binding plans behind evaluation and editor tooling accept;
    /// the reported error keeps it from being evaluated.</para>
    /// </summary>
    private static LiftedSignature RejectInvalidLiftedSignature(
        LiftedSignature lifting,
        ParameterSignatureViolation violation,
        IReadOnlyList<LiftedDependency> deps,
        ResolverWalkMemos memos)
    {
        ReportInvalidLiftedSignature(lifting.Patterns, violation, deps, memos);
        var recovered = memos.Run.Templates.InternFlat(ParameterPattern.KeepFirstCollectingCapturePerLevel(lifting.Patterns));
        return new(recovered, recovered.Facts.BindingKinds, Lifted: true);
    }

    /// <summary>The report of <see cref="RejectInvalidLiftedSignature"/> about the composed, unrecovered <paramref name="signature"/>.</summary>
    private static void ReportInvalidLiftedSignature(
        IReadOnlyList<ParameterPattern> signature,
        ParameterSignatureViolation violation,
        IReadOnlyList<LiftedDependency> deps,
        ResolverWalkMemos memos)
    {
        if (memos.Diagnostics is not { } diagnostics)
            return;
        var (message, reference) = DescribeInvalidLiftedSignature(signature, violation, deps);
        diagnostics.Add(new Diagnostic(message, DiagnosticSeverity.Error, reference?.Span ?? memos.Run.ImportSite)
        {
            Code = violation == ParameterSignatureViolation.SingletonSequencePattern
                ? DiagnosticCode.SingletonSequencePattern
                : DiagnosticCode.InvalidCollectingBinding,
        });
    }

    /// <summary>
    /// The wording and position of <see cref="RejectInvalidLiftedSignature"/>: for the collector rule,
    /// the collecting parameters at the offending level with the callee that needs each (the first
    /// callee whose own top level collects under that name) and the reference of the callee that
    /// adds the second one; otherwise the rule and the first lifted reference. Everything a callee
    /// contributes is echoed bounded.
    /// </summary>
    private static (DiagnosticMessage Message, Expr? Reference) DescribeInvalidLiftedSignature(
        IReadOnlyList<ParameterPattern> signature,
        ParameterSignatureViolation violation,
        IReadOnlyList<LiftedDependency> deps)
    {
        const string Repair = "Call the callable with explicit arguments, or declare this definition's parameters explicitly.";
        var firstReference = deps.Count > 0 ? deps[0].Reference : null;
        switch (violation)
        {
            case ParameterSignatureViolation.MultipleCollectingAtOneLevel:
            {
                var collectors = new List<(string Name, LiftedDependency? Callee)>();
                foreach (var pattern in signature)
                {
                    if (pattern is CaptureParameterPattern { Kind: ParameterKind.Collecting } collecting)
                        collectors.Add((collecting.Name, FirstTopLevelCollector(deps, collecting.Name)));
                }

                if (collectors.Count < 2)
                    break;

                var sink = new Rendering.BoundedDiagnosticSink(ExprNameRenderer.MaxRenderedNameLength);
                for (var index = 0; index < collectors.Count; index++)
                {
                    var separator = index == 0 ? ""
                        : collectors.Count == 2 ? " and "
                        : index == collectors.Count - 1 ? ", and "
                        : ", ";
                    var (name, callee) = collectors[index];
                    if (!sink.Append(separator) || !sink.Append("'*") || !sink.Append(name) || !sink.Append("'"))
                        break;
                    if (callee is { } needing
                        && (!sink.Append(" (needed by '") || !sink.Append(needing.Name) || !sink.Append("')")))
                    {
                        break;
                    }
                }

                var offending = collectors[1].Callee;
                return (DiagnosticMessage.JoinLines(
                        $"Formula lifting cannot complete this definition's signature: it would need the collecting parameters {sink.Finish()} "
                            + "at the same pattern level, but a signature may declare at most one collecting parameter per pattern level.",
                        offending is { } second
                            ? $"Call '{ExprNameRenderer.BoundName(second.Name)}' with explicit arguments, or declare this definition's parameters explicitly."
                            : Repair),
                    offending?.Reference ?? firstReference);
            }

            case ParameterSignatureViolation.RepeatedNameIncludesCollecting:
                return (DiagnosticMessage.JoinLines(
                        "Formula lifting cannot complete this definition's signature: it would repeat a parameter name with a collecting binding, "
                            + "which a signature may not declare.",
                        Repair),
                    firstReference);

            case ParameterSignatureViolation.SingletonSequencePattern:
                return (DiagnosticMessage.JoinLines(
                        "Formula lifting cannot complete this definition's signature: it would contain a sequence pattern with exactly one "
                            + "non-collecting item, which a signature may not declare (KatLang has no one-item sequence value).",
                        Repair),
                    firstReference);
        }

        // A collector violation below the top level: every lifted group is a callee's own valid group
        // (or part of one), so only a host-built callee can reach this.
        return (DiagnosticMessage.JoinLines(
                "Formula lifting cannot complete this definition's signature: it would place more than one collecting parameter "
                    + "at one pattern level, but a signature may declare at most one collecting parameter per pattern level.",
                Repair),
            firstReference);

        static LiftedDependency? FirstTopLevelCollector(IReadOnlyList<LiftedDependency> deps, string name)
        {
            foreach (var dependency in deps)
            {
                foreach (var pattern in dependency.Signature.ParameterPatterns)
                {
                    if (pattern is CaptureParameterPattern { Kind: ParameterKind.Collecting } collecting && collecting.Name == name)
                        return dependency;
                }
            }

            return null;
        }
    }

    /// <summary>The first-occurrence binding kinds of an owner's own list (a template's are cached).</summary>
    private static IReadOnlyDictionary<string, ParameterKind> SourceBindingKindsOf(IReadOnlyList<ParameterPattern> patterns)
        => patterns is ImplicitSignatureTemplate template
            ? template.Facts.BindingKinds
            : BuildSourceBindingKinds(patterns);

    /// <summary>The captures of a dependency sequence, first occurrence of each name winning.</summary>
    private static IReadOnlyList<ParameterPattern> MergeLiftedTail(IReadOnlyList<IReadOnlyList<ParameterPattern>> dependencies)
    {
        var existing = new HashSet<string>(StringComparer.Ordinal);
        var merged = new List<ParameterPattern>();
        HashSet<ParameterPattern>? expandedGroups = null;
        foreach (var dependency in dependencies)
            AppendMissingPatterns(dependency, existing, merged, ForwardableParameters.None, ref expandedGroups);
        return merged;
    }

    /// <summary>
    /// One owner's merge when an own name is also lifted, or (Q-04) when an enclosing parameter
    /// binding supplies a dependency capture: exactly the pre-FE-3 loop (own patterns, then each
    /// dependency's captures that neither the owner nor <paramref name="forwardable"/> binds).
    /// Null when nothing is lifted.
    /// </summary>
    private static ParameterPattern[]? MergeOwnerSignature(
        IReadOnlyList<ParameterPattern> own,
        IReadOnlyList<IReadOnlyList<ParameterPattern>> dependencies,
        ForwardableParameters forwardable)
    {
        var existing = new HashSet<string>(ParameterPattern.CapturesExpandingSharedNodesOnce(own).Select(static capture => capture.Name), StringComparer.Ordinal);
        var merged = new List<ParameterPattern>(own);
        var ownCount = merged.Count;
        HashSet<ParameterPattern>? expandedGroups = null;
        foreach (var dependency in dependencies)
            AppendMissingPatterns(dependency, existing, merged, forwardable, ref expandedGroups);
        return merged.Count == ownCount ? null : merged.ToArray();
    }

    /// <summary>
    /// FORMULA LIFTING IS BY BINDING NAME, regardless of how many times a name occurs in a
    /// callee's parameter patterns: the merge walks the captures left to right — across dependencies,
    /// across one dependency's patterns, and inside a group alike — and keeps a capture only when no
    /// earlier capture (the owner's own, an earlier dependency's, or an earlier one of the same
    /// pattern) and no reused enclosing binding already binds its name. So one binding name is ONE
    /// caller parameter: <c>P(x, x)</c> lifts <c>x</c> once exactly as <c>H = F + G</c> with
    /// <c>F(x)</c> and <c>G(x)</c> does, and <c>P((x, x))</c> lifts the bare binder <c>x</c> (a
    /// sequence group left with one binder IS that binder), never a caller pattern that repeats
    /// <c>x</c>. The synthesized call supplies the one binding to every occurrence
    /// (<see cref="BuildImplicitCallArguments"/>). A lone bare row never reaches this merge: it is a
    /// callable alias, which gains no parameter at all, or bare forwarding, which reuses existing
    /// bindings by name and adds none (<see cref="TryCompleteLoneCalleeRow"/>).
    /// </summary>
    private static void AppendMissingPatterns(
        IReadOnlyList<ParameterPattern> patterns,
        HashSet<string> existing,
        List<ParameterPattern> merged,
        ForwardableParameters forwardable,
        ref HashSet<ParameterPattern>? expandedGroups)
    {
        foreach (var pattern in patterns)
        {
            var missingPattern = MissingCapturePattern(pattern, existing, forwardable, ref expandedGroups);
            if (missingPattern is not null)
                merged.Add(missingPattern);
        }
    }

    /// <summary>
    /// The part of <paramref name="pattern"/> whose captures no earlier capture binds, recording
    /// each kept capture's name in <paramref name="existing"/> as it is kept, so a later occurrence
    /// of the name — in this very pattern too — is skipped.
    /// </summary>
    private static ParameterPattern? MissingCapturePattern(
        ParameterPattern pattern,
        HashSet<string> existing,
        ForwardableParameters forwardable,
        ref HashSet<ParameterPattern>? expandedGroups)
        => pattern switch
        {
            CaptureParameterPattern capture
                => forwardable.Binds(capture.Name) || !existing.Add(capture.Name) ? null : LiftedCapture(capture),
            SequenceValueParameterPattern or ListValueParameterPattern or UnpackingParameterPattern
                => MissingGroupCapturePattern(pattern, existing, forwardable, ref expandedGroups),
        };

    /// <summary>
    /// The caller binding a lifted capture becomes. A META capture (CallReference S1) keeps its mode on
    /// the callee's DECLARED signature only: lifting gives the caller an ORDINARY binding of the same
    /// name, which transports its supplied cell into the callee's META slot (so the callee still
    /// captures the caller's supplied call), and is never itself a META capture of an inferred
    /// signature. Every other capture lifts as itself (FE-3 record sharing).
    /// </summary>
    private static CaptureParameterPattern LiftedCapture(CaptureParameterPattern capture)
        => capture.Kind == ParameterKind.Meta
            ? new CaptureParameterPattern(capture.Parameter.WithKindOf(ParameterKind.Normal))
            : capture;

    /// <summary>
    /// The part of a structural group whose captures no earlier capture binds. The group keeps
    /// its KIND for the names that are new there (a list group stays a list group, a sequence
    /// group a sequence group), with one consequence of the value model: a SEQUENCE group left
    /// with exactly one non-collecting item IS that item, because there is no one-item sequence
    /// (the singleton rule) — <c>P((x, x))</c> lifts <c>x</c> and <c>P(x, (x, a))</c> lifts
    /// <c>x, a</c>, exactly as a redundant one-slot group is its content (SYN-06). A list group
    /// keeps its brackets at every cardinality (<c>P(x, [x, a])</c> lifts <c>x, [a]</c>), and a
    /// group with no new name contributes no caller parameter.
    /// </summary>
    private static ParameterPattern? MissingGroupCapturePattern(
        ParameterPattern group,
        HashSet<string> existing,
        ForwardableParameters forwardable,
        ref HashSet<ParameterPattern>? expandedGroups)
    {
        FrontEndStack.Ensure();
        // existing only grows during this merge, and forwardable is fixed. The first
        // complete visit handles every name below this group; any later visit contributes
        // nothing. Keep one reference set across dependencies, never across merge contexts.
        if (!(expandedGroups ??= new HashSet<ParameterPattern>(ReferenceEqualityComparer.Instance)).Add(group))
            return null;
        var groupItems = ParameterPattern.StructuralItems(group)!;
        var missingItems = new List<ParameterPattern>(groupItems.Count);
        var unchanged = true;
        foreach (var item in groupItems)
        {
            var missingItem = MissingCapturePattern(item, existing, forwardable, ref expandedGroups);
            unchanged &= ReferenceEquals(missingItem, item);
            if (missingItem is not null)
                missingItems.Add(missingItem);
        }

        // A group none of whose captures is already bound lifts AS ITSELF — the callee's record,
        // exactly like a lifted capture leaf — so owners lifting it share one record (FE-3).
        if (missingItems.Count == 0)
            return null;
        if (unchanged)
            return group;
        if (group is SequenceValueParameterPattern && ParameterPattern.IsSingletonSequenceItems(missingItems))
            return missingItems[0];
        return ParameterPattern.WithFilteredStructuralItems(group, missingItems);
    }

    private static bool TryGetSingleTopLevelCollectingCapture(
        IReadOnlyList<ParameterPattern> patterns,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CaptureParameterPattern? capture)
    {
        if (patterns.Count == 1
            && patterns[0] is CaptureParameterPattern { Kind: ParameterKind.Collecting } collecting)
        {
            capture = collecting;
            return true;
        }

        capture = null;
        return false;
    }

    /// <summary>
    /// The callee half of forwarding by shape: a callee whose whole parameter list is ONE
    /// structural group of either kind holding a lone collecting capture (<c>H((*xs))</c>,
    /// <c>H([*xs])</c>), which requires its one supplied slot. A callee whose whole list is a lone TOP-LEVEL collector
    /// (<c>H(*xs)</c>) accepts zero supplied arguments and is therefore never lifted (Q-03,
    /// <see cref="RequiresSuppliedArguments"/>), so it never reaches forwarding at all: a bare
    /// reference to it is a cached value read, and forwarding its caller's items is written
    /// explicitly (<c>H(items*)</c>).
    /// </summary>
    private static bool TryGetSingleForwardableCalleeStream(
        IReadOnlyList<ParameterPattern> patterns,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CaptureParameterPattern? capture)
    {
        // A grouped stream of either structural kind — `H((*xs))` or `H([*xs])` — is re-supplied
        // by a caller's lone collecting stream, rebuilt as that group's own kind.
        if (patterns.Count == 1
            && ParameterPattern.StructuralItems(patterns[0]) is [CaptureParameterPattern { Kind: ParameterKind.Collecting } groupedCollecting])
        {
            capture = groupedCollecting;
            return true;
        }

        capture = null;
        return false;
    }

    private static bool TryGetSingleCollectingForwarding(
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlyList<ParameterPattern> calleePatterns,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out string? calleeName,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out string? callerName)
    {
        if (TryGetSingleTopLevelCollectingCapture(callerPatterns, out var callerCapture)
            && TryGetSingleForwardableCalleeStream(calleePatterns, out var calleeCapture))
        {
            calleeName = calleeCapture.Name;
            callerName = callerCapture.Name;
            return true;
        }

        calleeName = null;
        callerName = null;
        return false;
    }

    private static bool CanForwardSingleCollectingStream(
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlyList<ParameterPattern> calleePatterns)
        => TryGetSingleCollectingForwarding(callerPatterns, calleePatterns, out _, out _);

    /// <summary>
    /// The callee capture names a CLOSED explicit parameter list cannot supply — the ONE
    /// implementation of the closed-list forwarding verdict: <see cref="ClosedListBlocksLifting"/>
    /// blocks exactly when it is non-empty, and the runtime value-demand rejection
    /// names exactly these (both read it through the region's
    /// <see cref="ResolverWalkMemos.MissingForwardingNames"/>). Forwarding availability and the
    /// names blamed for its absence therefore cannot drift apart: the caller's own forwarded
    /// collecting stream satisfies EVERY capture (so it yields no names at all), and otherwise a
    /// capture is missing exactly when the closed list does not declare it.
    /// <para>Q-04: a capture an ENCLOSING parameter binding supplies (<paramref name="forwardable"/>,
    /// the bindings a written reference of that name in the closed body already denotes) is never
    /// missing — forwarding reuses that binding, exactly as it does for an inferring owner.</para>
    /// <para>Order is <see cref="ParameterPattern.FlattenCaptures"/> order — the callee's
    /// own declaration order — deduplicated first-occurrence-wins, so a diagnostic built
    /// from it is stable and never hash-ordered.</para>
    /// </summary>
    private static IReadOnlyList<string> MissingClosedListForwardingNames(
        IReadOnlyList<ParameterPattern> calleePatterns,
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlySet<string> existingParameterNames,
        ForwardableParameters forwardable)
    {
        // A single forwarded collecting stream re-supplies the callee's whole parameter
        // shape by binding KIND, not by name, so nothing is missing even though the names
        // differ. Consulting the same helper the forwarding builder uses keeps fixed and
        // collecting bindings from ever being judged interchangeable here.
        if (CanForwardSingleCollectingStream(callerPatterns, calleePatterns))
            return [];

        List<string>? missing = null;
        HashSet<string>? seen = null;
        foreach (var capture in ParameterPattern.CapturesExpandingSharedNodesOnce(calleePatterns))
        {
            if (existingParameterNames.Contains(capture.Name) || forwardable.Binds(capture.Name))
                continue;

            seen ??= new(StringComparer.Ordinal);
            if (seen.Add(capture.Name))
                (missing ??= []).Add(capture.Name);
        }

        return missing ?? (IReadOnlyList<string>)[];
    }

    /// <summary>
    /// The CLOSED-explicit-parameter-list gate, in one place: inside an algorithm that wrote
    /// its own parameter list, a bare reference to a callable that requires supplied arguments
    /// (the only kind that is ever lifted, <see cref="RequiresSuppliedArguments"/>) may lift
    /// only when every capture the synthesized argument list would need is supplied by an
    /// existing parameter binding: declared by that list, the caller's own forwarded collecting
    /// stream, or (Q-04) an enclosing parameter binding a written reference of the name there
    /// already denotes. Lifting anything else would invent a parameter the programmer never wrote.
    ///
    /// <para>Every liftable arm of <see cref="RewriteImplicitCallsCore"/> consults THIS
    /// helper with the region's <see cref="ImplicitRewriteContext"/>, so no expression
    /// position — value-demanding Math arguments included — can be reached under a
    /// weaker gate than the rows around it.</para>
    /// </summary>
    private static bool ClosedListBlocksLifting(
        ImplicitRewriteContext context,
        IReadOnlyList<ParameterPattern> calleePatterns,
        ResolverWalkMemos memos)
        => context.ClosedParameterNames is { } closedParameterNames
            && memos.MissingForwardingNames(calleePatterns, context, closedParameterNames).Count > 0;





    // `'a'`, `'a' and 'b'`, `'a', 'b', and 'c'` — rendered within the rendered-name bound, reading
    // only the names it shows; text that fits is exactly the unbounded spelling.
    private static string FormatQuotedNameList(IReadOnlyList<string> values)
    {
        var sink = new Rendering.BoundedDiagnosticSink(ExprNameRenderer.MaxRenderedNameLength);
        for (var index = 0; index < values.Count; index++)
        {
            var separator = index == 0 ? ""
                : values.Count == 2 ? " and "
                : index == values.Count - 1 ? ", and "
                : ", ";
            if (!sink.Append(separator) || !sink.Append("'") || !sink.Append(values[index]) || !sink.Append("'"))
                break;
        }

        return sink.Finish();
    }

    /// <summary>
    /// Maps every caller-side capture name (top-level and nested) to its
    /// binding kind. Implicit forwarding consults this map so the decision to
    /// re-spread a forwarded value is made from the SOURCE binding, never from
    /// the destination parameter kind alone.
    /// </summary>
    private static Dictionary<string, ParameterKind> BuildSourceBindingKinds(
        IReadOnlyList<ParameterPattern> callerPatterns)
    {
        var kinds = new Dictionary<string, ParameterKind>(StringComparer.Ordinal);
        foreach (var capture in ParameterPattern.CapturesExpandingSharedNodesOnce(callerPatterns))
            kinds.TryAdd(capture.Name, capture.Kind);
        return kinds;
    }

    /// <summary>
    /// The binder shape of a conditional branch pattern as caller parameter patterns — the
    /// forwarding SOURCE shape of a branch body, mirroring
    /// <see cref="Pattern.TryGetOrdinaryClauseParameterPatterns"/> but total over mixed
    /// heads: literal items bind nothing, so they contribute no capture,
    /// while binders keep their kind and nested binder groups keep their structural kind
    /// (a sequence pattern stays a sequence pattern, a list pattern a list pattern),
    /// including empty groups. The closed-specification name check consumes only
    /// captures, but single-collecting forwarding also depends on those group boundaries.
    /// Collecting binders in conditional families are host-AST-only; the parser rejects them.
    /// </summary>
    internal static IReadOnlyList<ParameterPattern> BranchBinderParameterPatterns(Pattern pattern)
    {
        // A top-level sequence pattern IS the branch's parameter list; any other top-level
        // pattern is one single parameter position.
        var items = pattern is Pattern.SequenceValue(var topLevelItems) ? topLevelItems : [pattern];
        var patterns = new List<ParameterPattern>(items.Count);
        foreach (var item in items)
        {
            if (TryCreateBinderParameterPattern(item, out var parameterPattern))
                patterns.Add(parameterPattern);
        }

        return patterns;
    }

    private static bool TryCreateBinderParameterPattern(
        Pattern pattern,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out ParameterPattern? parameterPattern)
    {
        FrontEndStack.Ensure();
        switch (pattern)
        {
            case Pattern.Bind binder:
                parameterPattern = new CaptureParameterPattern(binder.Name, binder.NameSpan, binder.ParameterKind)
                {
                    CollectMarkerSpan = binder.CollectMarkerSpan,
                };
                return true;

            case Pattern.SequenceValue sequence:
            {
                var binders = BinderChildPatterns(sequence.Items);
                parameterPattern = new SequenceValueParameterPattern(binders) { Source = BinderGroupSource(sequence.Span, sequence.Items, binders) };
                return true;
            }

            case Pattern.ListValue list:
            {
                var binders = BinderChildPatterns(list.Items);
                parameterPattern = new ListValueParameterPattern(binders) { Source = BinderGroupSource(list.Span, list.Items, binders) };
                return true;
            }

            case Pattern.LitInt:
            case Pattern.LitString:
            case Pattern.LitBool:
                parameterPattern = null;
                return false;

            default:
                throw new InvalidOperationException(
                    $"Unhandled Pattern variant in {nameof(BranchBinderParameterPatterns)}: {pattern.GetType().Name}.");
        }

        static List<ParameterPattern> BinderChildPatterns(IReadOnlyList<Pattern> items)
        {
            var childPatterns = new List<ParameterPattern>(items.Count);
            foreach (var item in items)
            {
                if (TryCreateBinderParameterPattern(item, out var childPattern))
                    childPatterns.Add(childPattern);
            }

            return childPatterns;
        }

        // A literal item has no binder, so a head group that holds one is only part of what was written.
        static PatternGroupSource? BinderGroupSource(SourceSpan? span, IReadOnlyList<Pattern> items, List<ParameterPattern> binders)
            => span is not { } written ? null
                : new(written, binders.Count != items.Count || binders.Exists(static binder => ParameterPattern.GroupSource(binder) is { IsFiltered: true }));
    }

    /// <summary>
    /// A LONE BARE ROW (FWD-02; the alias half decided October 1 2026 as BINDING INDIRECTION). A
    /// NON-ROOT body — a named definition, a clause branch, or an inline block — whose ONE written row
    /// is a bare reference is completed here, never by formula lifting. The row is resolved by
    /// IDENTITY with the one resolution formula lifting uses (<see cref="TryResolveCallable"/>: the
    /// owner walk, the prelude, the opens, or a structural dot path — and through a callable alias to
    /// its normalized target), so the lookup ROUTE never decides anything; and the rule reads whether
    /// that identity DECLARES PARAMETERIZED CALLABLE STRUCTURE
    /// (<see cref="DeclaresParameterizedStructure"/>), never its zero-argument acceptance. Declarations
    /// and opens beside the row do not change what the row means.
    /// <list type="bullet">
    ///   <item><b>Alias (M4★).</b> An OPEN body — no written parameter list, no parameter of its own
    ///   (<c>A = F</c>) — becomes an <see cref="Algorithm.Alias"/> whatever the target's arity: a
    ///   transparent reference when unbraced, a structural forwarding carrier when written in braces or
    ///   beside its own declarations or opens. Nothing is synthesized — no signature, no wrapper call:
    ///   every callable question asked of <c>A</c> later (argument roles, formula lifting, bare
    ///   forwarding, another alias) is answered by the recorded target
    ///   (<see cref="Algorithm.Alias.ResolvedTarget"/>), and the evaluator calls the target itself.
    ///   Every algorithm qualifies: a user algorithm of any arity, any builtin (<c>if</c>, callbacks and
    ///   loops included), any clause family (nameable or not), a Math member, a host operation, and an
    ///   opened, dotted or module member of these — except a cyclic static reference chase (OD-D) and
    ///   assignment deconstruction's hoisted source over a target without parameterized structure.</item>
    ///   <item><b>Bare forwarding.</b> A CLOSED body — a written parameter list (<c>A(p) = F</c>) or a
    ///   clause branch (<c>A(head) = F</c>) — forwards the target the EXISTING bindings of its
    ///   forwarding contract's parameter names (its lifting signature, the target's through an
    ///   alias; <see cref="BareForwardingArgument"/>): by name, never by position; nothing is renamed
    ///   and nothing is added to the closed list; and a target parameter pattern is supplied only by a
    ///   binding that declares the SAME pattern, so a same-named leaf never reshapes an argument. A
    ///   parameter that cannot be supplied is the front-end error
    ///   <see cref="DiagnosticCode.UnforwardableParameter"/>, and a target with no nameable contract
    ///   at all (an unnameable clause family) is <see cref="DiagnosticCode.UnforwardableCallable"/>
    ///   (Q-77, decided October 1 2026) — in both cases the row is left as written. When nothing is
    ///   forwarded to a callee that works with no arguments, the row is its bare name — Q-03's cached
    ///   value read, never an invented call. The explicit call <c>A(p) = F(p)</c> is an ordinary
    ///   written call and never reaches this rule.</item>
    /// </list>
    /// Returns null for every other body (formula lifting, <see cref="LiftSignature"/>): a row with no
    /// static identity (a parameter, an unresolved or ambiguous name, a run-time receiver's member — a
    /// runtime row is classified later, <see cref="RuntimeAliasRow"/>), a closed body whose callee
    /// declares no parameters (a value read), and a bare-forwarding row that forwards nothing.
    /// </summary>
    private static Algorithm? TryCompleteLoneCalleeRow(
        Algorithm.User alg,
        ConditionalBranchContext? branchContext,
        SignatureMap paramMap,
        ForwardableParameters ownForwarding,
        ResolverWalkMemos memos)
    {
        if (!HasLoneBareRowShape(alg))
            return null;

        var row = alg.Output[0];
        if (TryResolveCallable(row, paramMap, memos, out var writtenName) is not { } target)
            return null;

        if (branchContext is null && !alg.HasExplicitParameterList)
        {
            // An inferring body that already owns parameters (none can come from a lone bare
            // reference, but a host tree may carry them) keeps formula lifting.
            if (alg.ParameterPatterns.Count != 0)
                return null;

            // M4★ (ALIAS-UNIFY-1): an OPEN body whose one row is a resolved algorithm REFERENCE is an
            // alias WHATEVER the target's arity — a transparent reference when unbraced, a structural
            // forwarding carrier when written in braces (`Algorithm.Alias.IsReference`). A chain to a
            // runtime-target alias is classified after inference (`RuntimeAliasRow`), and a cyclic
            // static reference chase is no alias (OD-D): it stays an ordinary lazy property.
            if (IsRuntimeTargetEndpoint(target, memos.Run)
                || IsCyclicReferenceChase(alg, row, paramMap, memos))
            {
                return null;
            }

            // Assignment deconstruction's hoisted source keeps its own contract: it is no written
            // definition, so it becomes an alias only of a callable that declares parameterized
            // structure (FWD-02, unchanged) and otherwise stays the ordinary property its targets share.
            if (alg.IsSyntheticDeconstructionPlumbing && !DeclaresParameterizedStructure(target))
                return null;

            // THE ALIAS: the same written declaration, its row kept as written — a block head replaced by
            // the very rewrite its target and structure were read from — and a transparent reference
            // records its static structure (a carrier's is itself).
            var alias = new Algorithm.Alias(alg, WithProcessedBlockHead(row, paramMap, memos))
            {
                ResolvedTargetCell = TargetCellOf(target, memos),
            };
            ReportOutputSpreadMarkerOnAlias(alias, writtenName, target, memos);
            return alias.IsReference
                ? alias with { ResolvedStructureCell = StaticStructureOfRow(row, paramMap, memos) }
                : alias;
        }

        // A CLOSED body keeps FWD-02's bare forwarding, over a callee that declares parameterized
        // structure only: a callee that declares nothing leaves the row its bare name.
        if (!DeclaresParameterizedStructure(target))
            return null;

        // BARE FORWARDING through the target's forwarding contract, which names every parameter it
        // forwards; a target with none names nothing to forward by.
        if (target.Signature.Signature is not { } contract)
        {
            ReportUnforwardableCallable(row, writtenName, target, memos);
            return alg;
        }

        var sources = branchContext is null
            ? BareForwardingSources.OfParameterList(alg.ParameterPatterns)
            : BareForwardingSources.OfBranchHead(branchContext.Pattern);
        var calleePatterns = contract.ParameterPatterns;
        var forwarded = new List<Expr>(calleePatterns.Count);
        Dictionary<ParameterPattern, Expr>? sourceArguments = null;
        List<(ParameterPattern Parameter, bool DifferentPattern)>? unforwardable = null;
        foreach (var parameter in calleePatterns)
        {
            var verdict = BareForwardingArgument(parameter, sources, ownForwarding, ref sourceArguments);
            if (verdict.Argument is { } argument)
                forwarded.Add(argument);
            else if (verdict.Unforwardable)
                (unforwardable ??= []).Add((parameter, verdict.DifferentPattern));
        }

        if (unforwardable is not null)
        {
            ReportUnforwardableParameters(row, writtenName, unforwardable, branchContext?.BranchName, memos);
            return alg;
        }

        // Nothing to forward: every callee parameter is a collector that no binding of its name
        // supplies, so the callee works with no arguments and the row is its bare name.
        if (forwarded.Count == 0)
            return null;

        var arguments = OutputBundle.From(forwarded);
        memos.Run.ChargeImplicitArgumentBundle(arguments.Count);
        memos.Run.Observations?.RecordImplicitArgumentBundleBuilt(arguments.Count);
        // The callee path's block head is processed like the alias row's, so the call reaches the block this pass elaborated.
        // The synthesized call is the body's whole output row: an output-spreading position (R2, R4: a marked call
        // written — or forwarded — inside a bare-forwarding body spreads where it stands).
        return alg with
        {
            Output = [SpreadIfMarked(row, memos.SynthesizedImplicitCall(LoneRowCall(WithProcessedBlockHead(row, paramMap, memos), arguments)), paramMap, memos)],
        };
    }

    /// <summary>The operation's OD-D formation verdict, with no local cycle walk.</summary>
    private static bool IsCyclicReferenceChase(Algorithm.User alg, Expr row, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        var context = memos.Run.Level?.StaticContext ?? throw new InvalidOperationException("Alias formation requires a structural context.");
        return context.Operation.IsCyclic(context.Key, StaticCycleCheck.Formation);
    }



    /// <summary>Q3 selects a written member (its detected input; B3-5★ reads no processed form).</summary>
    private static StaticDeclaration? StructuralMemberAt(Expr.DotCall edge, ResolverLevel? level, StaticCycleCheck check)
    {
        if (level?.StaticContext is not { } context) return null;
        var expression = context.Operation.WrittenExpression(context.Key, edge);
        var selected = context.Operation.Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, context.Key,
            StaticQueryProjection.MemberSelection, stratum: check, node: expression));
        return selected.Kind == StaticFactKind.Structure && selected.Scope is { } key
            ? context.Operation.Declaration(key) : null;
    }

    /// <summary>
    /// A block-headed static member path (<c>{ … }.K</c>) with its block replaced by the block's PROCESSED body —
    /// the very rewrite (the run's region memo) the alias's recorded target and structure were read from — so the
    /// evaluator navigates the block this pass elaborated, never the detector's input (M4★: a member that is a
    /// reference there is an alias, and a formula is lifted). Every other row is returned as written.
    /// </summary>
    private static Expr WithProcessedBlockHead(Expr row, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        FrontEndStack.Ensure();
        if (row is not Expr.DotCall { Args: null } edge)
            return row;
        var target = edge.Target switch
        {
            Expr.AlgorithmExpr block => block with
            {
                Algorithm = ProcessSharedNestedAlgorithm(block.Algorithm, ImportSite.OfBlock(block), paramMap, memos),
            },
            Expr.DotCall { Args: null } inner => WithProcessedBlockHead(inner, paramMap, memos),
            var other => other,
        };
        return ReferenceEquals(target, edge.Target) ? row : edge with { Target = target };
    }

    /// <summary>The call a completed bare-forwarding row makes: the written callee applied to <paramref name="arguments"/>.</summary>
    private static Expr LoneRowCall(Expr row, OutputBundle arguments) => row switch
    {
        Expr.DotCall bareDotCall => bareDotCall with { Args = arguments },
        _ => new Expr.Call(new Expr.Resolve(((Expr.Resolve)row).Name) { Span = row.Span }, arguments) { Span = row.Span },
    };

    /// <summary>
    /// The context-free half of the lone-row rule's eligibility: the body's ONE written row is a bare
    /// name or a bare dot reference (whatever it resolves to; declarations and opens do not count as
    /// rows, while a hoisted deconstruction right-hand side does — <see cref="AstHelpers.WrittenRows"/>
    /// — so a body with a deconstruction beside the bare callee is a formula). A property of the node
    /// alone, so a region key may read it before the body is rewritten.
    /// </summary>
    private static bool HasLoneBareRowShape(Algorithm.User alg)
        => alg.Output.Count == 1
            && alg.Output[0] is Expr.Resolve or Expr.DotCall { Args: null }
            && AstHelpers.WrittenRows(alg).Count == 1;

    /// <summary>
    /// PARAMETERIZED CALLABLE STRUCTURE — the bare-forwarding eligibility of a resolved identity for a
    /// CLOSED body (FWD-02, decided October 1 2026; since M4★ an OPEN body aliases a reference at any
    /// arity): its invocation consumes a supply through declared structure. Every
    /// builtin does (its registry adapter over declared slots, a loop's "at least N" included); every
    /// clause family does (dispatch over its clause heads, whether or not its positions are
    /// nameable); a user algorithm does exactly when it declares at least one parameter pattern once
    /// its signature is complete (written, inferred, or lifted) — a closed body naming a user algorithm
    /// with none forwards nothing and simply reads that value (an open body is its alias). Neither
    /// nameability (an unnameable family is forwardable) nor zero-argument acceptance (a collector-only
    /// <c>Only(*xs)</c> is forwardable) decides. An alias is never asked: identity resolution looks through it to its
    /// normalized target first. "Complete" is the target's FINAL signature (B3-5★: the selected one when this resolution
    /// has not processed the target yet), never its written input. Lean: <c>Algorithm.declaresParameterizedStructure</c>.
    /// </summary>
    private static bool DeclaresParameterizedStructure(AliasTarget target)
        => target.Algorithm switch
        {
            Algorithm.Builtin or Algorithm.Conditional => true,
            Algorithm.User => target.Signature.Signature is { ParameterPatterns.Count: > 0 },
            Algorithm.Alias => false,
        };

    /// <summary>
    /// Whether a static endpoint is a RUNTIME-TARGET body (META-S3-2): an open lone body whose one written row is a runtime
    /// row — an enclosing parameter, a parameter-rooted member path, an <c>.Algorithm</c> link — and whose FINAL signature
    /// declares nothing (B3-5★: a link's selected class), so the rewrite makes it a runtime-target alias, whatever the
    /// order its body is processed in. The row is read as DETECTED: only detection knows that a name is a parameter.
    /// </summary>
    private static bool IsRuntimeTargetEndpoint(AliasTarget target, ResolutionRun run)
        => target.Identity is StaticScopeKey key
            && (run.StructuralOperation!.DetectedView(key) ?? run.StructuralOperation.SourceOf(key))
                is Algorithm.User { HasExplicitParameterList: false, IsSyntheticDeconstructionPlumbing: false } body
            && body.Output.Count == 1
            && AstHelpers.WrittenRows(body).Count == 1
            && AliasTargetRows.IsRuntimeRow(body.Output[0])
            && target.Signature.Signature is { ParameterPatterns.Count: 0 };

    /// <summary>
    /// ONE pattern rebuilt from its own bindings — the argument bare forwarding passes for a
    /// structural pattern the body declares with the same contract: a fixed capture is its binding
    /// (<c>x</c>), a collecting capture re-spreads the items it collected (<c>xs*</c>) at any level,
    /// a sequence pattern rebuilds a sequence and a list pattern a list, of the same shape
    /// (<see cref="BuildPatternArgument"/> with every capture naming its own binding). Lean:
    /// <c>ParameterPattern.sourceArgument</c>.
    /// </summary>
    private static Expr BuildSourceArgument(ParameterPattern pattern, ref Dictionary<ParameterPattern, Expr>? arguments)
        => BuildPatternArgument(
            pattern,
            static capture => capture.Name,
            static capture => capture.Kind == ParameterKind.Collecting,
            ref arguments);

    /// <summary>
    /// What a CLOSED body's own inputs offer BARE FORWARDING: the kind of every TOP-LEVEL capture it
    /// declares (first occurrence of a repeated name wins, as for a caller's own signature), the
    /// contract of every top-level structural pattern it declares that holds no literal (a clause
    /// head item that holds a literal, <c>[0, x]</c>, declares no literal-free pattern), and every
    /// name it binds at any depth — a name bound only inside a structural pattern is an element of
    /// that pattern, never a whole-value parameter. Lean: the <c>own</c> / <c>ownNames</c> inputs of
    /// <c>bareForwardingArguments</c>.
    /// </summary>
    private sealed class BareForwardingSources
    {
        private BareForwardingSources(
            Dictionary<string, ParameterKind> topLevelCaptureKinds,
            HashSet<ParameterPattern> structuralContracts,
            HashSet<string> boundNames)
        {
            TopLevelCaptureKinds = topLevelCaptureKinds;
            StructuralContracts = structuralContracts;
            BoundNames = boundNames;
        }

        public IReadOnlyDictionary<string, ParameterKind> TopLevelCaptureKinds { get; }

        /// <summary>Every literal-free top-level structural pattern, compared by its complete contract.</summary>
        public IReadOnlySet<ParameterPattern> StructuralContracts { get; }

        public IReadOnlySet<string> BoundNames { get; }

        public static BareForwardingSources OfParameterList(IReadOnlyList<ParameterPattern> patterns)
        {
            var boundNames = new HashSet<string>(StringComparer.Ordinal);
            foreach (var capture in ParameterPattern.CapturesExpandingSharedNodesOnce(patterns))
                boundNames.Add(capture.Name);
            return Of(patterns, boundNames);
        }

        public static BareForwardingSources OfBranchHead(Pattern head)
        {
            // A top-level sequence pattern IS the branch's parameter list; any other top-level
            // pattern is one single parameter position.
            var items = head is Pattern.SequenceValue(var topLevelItems) ? topLevelItems : [head];
            var patterns = new List<ParameterPattern>(items.Count);
            // The patterns are read below as contracts only and never leave this class, so a group
            // a host-built head shares along many paths is converted once for the whole head.
            Dictionary<Pattern, ParameterPattern?>? convertedGroups = null;
            foreach (var item in items)
            {
                // An item that holds a literal at any depth declares no literal-free contract.
                if (Pattern.TryCreateOrdinaryClauseParameterPatternKeepingSharing(item, ref convertedGroups, out var pattern))
                    patterns.Add(pattern);
            }

            return Of(patterns, new HashSet<string>(head.BoundNamesExpandingSharedNodesOnce(), StringComparer.Ordinal));
        }

        private static BareForwardingSources Of(IReadOnlyList<ParameterPattern> topLevelPatterns, HashSet<string> boundNames)
        {
            var captureKinds = new Dictionary<string, ParameterKind>(StringComparer.Ordinal);
            var structuralContracts = new HashSet<ParameterPattern>(ParameterPattern.ContractComparer);
            foreach (var pattern in topLevelPatterns)
            {
                if (pattern is CaptureParameterPattern capture)
                    captureKinds.TryAdd(capture.Name, capture.Kind);
                else
                    structuralContracts.Add(pattern);
            }

            return new(captureKinds, structuralContracts, boundNames);
        }
    }

    /// <summary>BARE FORWARDING's verdict for one callee parameter pattern (<see cref="BareForwardingArgument"/>).</summary>
    private readonly record struct BareForwardingVerdict(Expr? Argument, bool Unforwardable, bool DifferentPattern)
    {
        public static BareForwardingVerdict Supplied(Expr argument) => new(argument, Unforwardable: false, DifferentPattern: false);

        /// <summary>A collector that no binding of its name supplies: it receives no argument.</summary>
        public static BareForwardingVerdict Optional => new(null, Unforwardable: false, DifferentPattern: false);

        public static BareForwardingVerdict Unsupplied(bool differentPattern) => new(null, Unforwardable: true, differentPattern);
    }

    /// <summary>
    /// BARE FORWARDING's verdict for ONE callee parameter pattern (FWD-02): the argument that supplies
    /// it from an EXISTING binding, by name; no argument for a collector that nothing of its name
    /// supplies (a collector accepts none); or unforwardable.
    /// <list type="bullet">
    ///   <item>A capture <c>n</c> reads the binding a written <c>n</c> would denote (Q-04): the body's
    ///   own TOP-LEVEL parameter <c>n</c>, else — when the body binds no <c>n</c> at all — the nearest
    ///   enclosing parameter binding (<paramref name="enclosing"/>). A collecting source re-spreads
    ///   into a collecting destination (FWD-01); every other pair passes the binding as ONE argument,
    ///   unchanged (FWD-02's source-kind rule). A body that binds <c>n</c> only INSIDE one of its
    ///   structural patterns holds an element, not a whole-value parameter: unforwardable.</item>
    ///   <item>A structural pattern is supplied only by one of the body's own top-level patterns with
    ///   the SAME contract — kind, shape, names and collectors — rebuilt as itself, never assembled
    ///   from same-named leaves; captured enclosing bindings are plain named values and supply
    ///   none.</item>
    /// </list>
    /// Lean: <c>bareForwardingArgument</c>.
    /// </summary>
    private static BareForwardingVerdict BareForwardingArgument(
        ParameterPattern parameter,
        BareForwardingSources sources,
        ForwardableParameters enclosing,
        ref Dictionary<ParameterPattern, Expr>? arguments)
    {
        if (parameter is CaptureParameterPattern capture)
        {
            if (sources.TopLevelCaptureKinds.TryGetValue(capture.Name, out var ownKind))
                return BareForwardingVerdict.Supplied(ForwardedBinding(capture, ownKind));
            if (sources.BoundNames.Contains(capture.Name))
                return BareForwardingVerdict.Unsupplied(differentPattern: true);
            if (enclosing.TryGetKind(capture.Name, out var enclosingKind))
                return BareForwardingVerdict.Supplied(ForwardedBinding(capture, enclosingKind));
            return capture.Kind == ParameterKind.Collecting
                ? BareForwardingVerdict.Optional
                : BareForwardingVerdict.Unsupplied(differentPattern: false);
        }

        if (sources.StructuralContracts.Contains(parameter))
            return BareForwardingVerdict.Supplied(BuildSourceArgument(parameter, ref arguments));

        var bindsAName = false;
        foreach (var leaf in ParameterPattern.CapturesExpandingSharedNodesOnce([parameter]))
        {
            if (sources.BoundNames.Contains(leaf.Name) || enclosing.Binds(leaf.Name))
            {
                bindsAName = true;
                break;
            }
        }

        return BareForwardingVerdict.Unsupplied(differentPattern: bindsAName);

        static Expr ForwardedBinding(CaptureParameterPattern destination, ParameterKind sourceKind)
            => destination.Kind == ParameterKind.Collecting && sourceKind == ParameterKind.Collecting
                ? new Expr.SequenceSpread(new Expr.Param(destination.Name))
                : new Expr.Param(destination.Name);
    }

    /// <summary>
    /// Reports every callee parameter bare forwarding cannot supply, once per parameter, at the bare
    /// reference (a row inside imported content at the import site). A conditional branch body's own
    /// region keeps each report re-issuable for further families sharing the body (M4).
    /// </summary>
    private static void ReportUnforwardableParameters(
        Expr row,
        string calleeDisplayName,
        IReadOnlyList<(ParameterPattern Parameter, bool DifferentPattern)> unforwardable,
        string? branchName,
        ResolverWalkMemos memos)
    {
        if (memos.Diagnostics is not { } diagnostics)
            return;

        var span = row.Span ?? memos.Run.ImportSite;
        var reported = new HashSet<ParameterPattern>(ParameterPattern.ContractComparer);
        foreach (var (parameter, differentPattern) in unforwardable)
        {
            if (!reported.Add(parameter))
                continue;
            var parameterDisplayName = parameter.DisplayName;

            DiagnosticMessage Format(string? family)
                => FormatUnforwardableParameter(calleeDisplayName, parameterDisplayName, differentPattern, family);
            diagnostics.Add(new Diagnostic(Format(branchName), DiagnosticSeverity.Error, span)
            {
                Code = DiagnosticCode.UnforwardableParameter,
            });
            memos.BranchDiagnosticTemplates?.Add(new BranchDiagnosticTemplate(DiagnosticCode.UnforwardableParameter, Format, span));
        }
    }

    /// <summary>
    /// Wording for <see cref="ReportUnforwardableParameters"/>, parallel to the closed-list wording of
    /// runtime value-demand rejection: what bare forwarding could not supply, why
    /// (the list is closed; nothing is renamed or reshaped), and the two repairs.
    /// </summary>
    private static DiagnosticMessage FormatUnforwardableParameter(
        string calleeDisplayName,
        string parameterDisplayName,
        bool differentPattern,
        string? conditionalBranchName)
    {
        calleeDisplayName = ExprNameRenderer.BoundName(calleeDisplayName);
        parameterDisplayName = ExprNameRenderer.BoundName(parameterDisplayName);
        conditionalBranchName = conditionalBranchName is null ? null : ExprNameRenderer.BoundName(conditionalBranchName);
        if (conditionalBranchName is not null)
        {
            return differentPattern
                ? DiagnosticMessage.JoinLines(
                    $"'{calleeDisplayName}' is forwarded by name here, but the pattern of conditional branch '{conditionalBranchName}' "
                        + $"does not bind its parameter '{parameterDisplayName}' in that form.",
                    "Bare forwarding reuses an existing binding only with the same pattern and never reshapes an argument. "
                        + $"Bind '{parameterDisplayName}' in the branch pattern, or call '{calleeDisplayName}' with explicit arguments.")
                : DiagnosticMessage.JoinLines(
                    $"'{calleeDisplayName}' is forwarded by name here, but its parameter '{parameterDisplayName}' "
                        + $"is not bound by the pattern of conditional branch '{conditionalBranchName}'.",
                    "Bare forwarding reuses an existing binding only under its own name, and conditional branch patterns are closed, "
                        + $"so '{parameterDisplayName}' is neither renamed nor added. Bind '{parameterDisplayName}' in the branch pattern, "
                        + $"or call '{calleeDisplayName}' with explicit arguments.");
        }

        return differentPattern
            ? DiagnosticMessage.JoinLines(
                $"'{calleeDisplayName}' is forwarded by name here, but the enclosing explicit parameter list "
                    + $"does not declare its parameter '{parameterDisplayName}' in that form.",
                "Bare forwarding reuses an existing parameter only with the same pattern and never reshapes an argument. "
                    + $"Declare the parameter '{parameterDisplayName}', or call '{calleeDisplayName}' with explicit arguments.")
            : DiagnosticMessage.JoinLines(
                $"'{calleeDisplayName}' is forwarded by name here, but its parameter '{parameterDisplayName}' "
                    + "is not a parameter of the enclosing explicit parameter list.",
                "Bare forwarding reuses an existing parameter only under its own name, and explicit parameter lists are closed, "
                    + $"so '{parameterDisplayName}' is neither renamed nor added. Declare '{parameterDisplayName}' in the parameter list, "
                    + $"or call '{calleeDisplayName}' with explicit arguments.");
    }

    /// <summary>
    /// Reports a bare-forwarding row whose callable — directly or through an alias — has no forwarding
    /// contract at all (Q-77, decided October 1 2026): an unnameable clause family names no parameter,
    /// so nothing can be forwarded by name. Reported once at the bare reference (a row inside imported
    /// content at the import site); a conditional branch body's region keeps the report re-issuable
    /// for further families sharing the body (M4).
    /// </summary>
    private static void ReportUnforwardableCallable(Expr row, string writtenName, AliasTarget target, ResolverWalkMemos memos)
    {
        if (memos.Diagnostics is not { } diagnostics)
            return;

        var span = row.Span ?? memos.Run.ImportSite;
        var message = FormatUnforwardableCallable(writtenName, target);
        diagnostics.Add(new Diagnostic(message, DiagnosticSeverity.Error, span) { Code = DiagnosticCode.UnforwardableCallable });
        memos.BranchDiagnosticTemplates?.Add(new BranchDiagnosticTemplate(DiagnosticCode.UnforwardableCallable, _ => message, span));
    }

    private static DiagnosticMessage FormatUnforwardableCallable(string writtenName, AliasTarget target)
    {
        var written = ExprNameRenderer.BoundName(writtenName);
        var callable = DescribeCallable(writtenName, target);
        var reason = target.Signature.Unnameable is { } unnameable
            ? FormatUnnameableReason(unnameable)
            : "it declares no parameter names";
        return DiagnosticMessage.JoinLines(
            $"'{written}' is forwarded by name here, but {callable} has no parameter names to forward by: {reason}.",
            "Bare forwarding supplies a callable's parameters from existing bindings of the same names, and literal, structural and binderless clause patterns name nothing. "
                + $"Call '{written}' with explicit arguments.");
    }

    /// <summary>
    /// How a diagnostic names the callable a written reference resolved to: the clause family itself
    /// (<c>clause family 'U'</c>), or, through an alias, both (<c>'UA', an alias of clause family 'U',</c>).
    /// </summary>
    private static string DescribeCallable(string writtenName, AliasTarget target)
    {
        var written = ExprNameRenderer.BoundName(writtenName);
        var kind = target.Algorithm is Algorithm.Conditional ? "clause family " : "";
        if (string.Equals(writtenName, target.DisplayName, StringComparison.Ordinal))
            return $"{kind}'{written}'";
        return $"'{written}', an alias of {kind}'{ExprNameRenderer.BoundName(target.DisplayName)}',";
    }

    /// <summary>
    /// The synthesized forwarding arguments of a lifted call: one slot per callee parameter pattern,
    /// in the callee's declaration order. A PURE function of its inputs — the region memo
    /// <see cref="ResolverWalkMemos.ImplicitArguments"/> shares one result between every lifted
    /// reference to the callee in a rewrite region (FE-2) — so it reads nothing about the reference
    /// site: its nodes are spanless, name only bindings the caller can already reach (its own
    /// parameters, lifted captures included, and — Q-04 — the enclosing parameter bindings
    /// <paramref name="forwardable"/> it reuses), and carry no occurrence identity. A reused
    /// enclosing binding is read through the ordinary captured-parameter read, so the callee receives
    /// the very binding an existing written reference of that name denotes. Forwarding is BY BINDING
    /// NAME: every callee capture receives the caller's binding of its name, so a name the callee
    /// repeats (<c>P(x, x)</c>, <c>P((x, a), x)</c>) receives that one binding at every occurrence —
    /// exactly the call <c>P(x, x)</c> a programmer would write — and the callee's binder then checks
    /// the occurrences as the ordinary independently evaluated argument slots they are (Q-05).
    /// <para>FORWARDING PRESERVES EACH BINDING AND EACH STRUCTURAL KIND (FWD-02, September 2026):
    /// every binding is forwarded as itself — a fixed binding as one <c>Param</c>, a collecting
    /// source into a collecting destination re-spread — never wrapped in a structure of its own;
    /// and a callee structural pattern is rebuilt around those bindings as the SAME kind it
    /// matches (<see cref="BuildPatternArgument"/>): a sequence pattern as a sequence, a list
    /// pattern as a list — never the other kind. So <c>Add((x, y))</c> / <c>A = [Add][0]</c> is
    /// <c>A((x, y)) = [Add((x, y))][0]</c> and <c>Single([x])</c> / <c>B = Single + 0</c> is
    /// <c>B([x]) = Single([x]) + 0</c>. The rebuilt group is the tree the explicit written call
    /// has, so implicit forwarding is observationally the explicit call that writes the same
    /// bindings into the callee's pattern.</para>
    /// </summary>
    private static IReadOnlyList<Expr> BuildImplicitCallArguments(
        IReadOnlyList<ParameterPattern> calleePatterns,
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlyDictionary<string, ParameterKind> sourceBindingKinds,
        ForwardableParameters forwardable)
    {
        TryGetSingleCollectingForwarding(
            callerPatterns,
            calleePatterns,
            out var forwardedCalleeName,
            out var forwardedCallerName);

        // TryGetSingleCollectingForwarding succeeds only when the callee shape
        // contains exactly one capture: a lone collector inside one structural
        // group (a lone TOP-LEVEL collector accepts zero supplied arguments and is
        // never lifted, Q-03). Consequently there is no second callee capture to
        // discriminate here; when forwarding is active, every reachable capture is
        // the forwarded capture. Expressing that invariant directly avoids an
        // equivalent && -> || mutant.
        string MapCaptureName(CaptureParameterPattern capture)
            => forwardedCalleeName is not null ? forwardedCallerName! : capture.Name;

        // A collecting DESTINATION re-spreads the forwarded value only when the
        // SOURCE binding is itself a collecting binding's exact list: then
        // `callee(rest*)` re-supplies exactly the collected items
        // (spread(collect(xs)) = xs). An ordinary source binding always
        // forwards as ONE argument, even into a collecting destination. The
        // source is the caller's own binding, else the enclosing parameter
        // binding it reuses (Q-04); a name bound by neither is about to be
        // lifted as a copy of the callee's own pattern, so its source kind IS
        // the callee kind.
        bool ForwardAsSpread(CaptureParameterPattern calleeCapture)
        {
            var sourceName = MapCaptureName(calleeCapture);
            return sourceBindingKinds.TryGetValue(sourceName, out var sourceKind)
                || forwardable.TryGetKind(sourceName, out sourceKind)
                    ? sourceKind == ParameterKind.Collecting
                    : calleeCapture.Kind == ParameterKind.Collecting;
        }

        Dictionary<ParameterPattern, Expr>? arguments = null;
        return BuildPatternArgumentOutput(calleePatterns, MapCaptureName, ForwardAsSpread, ref arguments);
    }

    private static Expr BuildPatternArgument(
        ParameterPattern pattern,
        Func<CaptureParameterPattern, string> mapCaptureName,
        Func<CaptureParameterPattern, bool> forwardAsSpread,
        ref Dictionary<ParameterPattern, Expr>? arguments)
    {
        FrontEndStack.Ensure();
        // Mapping and source-kind callbacks are fixed for this argument bundle. Sharing a
        // rebuilt value expression preserves all slots and introduces no algorithm scope.
        // Flat capture lists retain their allocation bound: only structural nodes are memoized.
        var isGroup = ParameterPattern.StructuralItems(pattern) is not null;
        if (isGroup && arguments is { } completed && completed.TryGetValue(pattern, out var cached))
            return cached;
        var argument = pattern switch
        {
            // A collecting destination whose source binding is a collecting binding's
            // exact list forwards through explicit spread so the callee's collecting
            // parameter re-collects exactly the caller's items; every other
            // capture forwards as one argument slot.
            CaptureParameterPattern { Kind: ParameterKind.Collecting } collecting
                when forwardAsSpread(collecting) =>
                new Expr.SequenceSpread(new Expr.Param(mapCaptureName(collecting))),
            CaptureParameterPattern capture => new Expr.Param(mapCaptureName(capture)),
            // A forwarded structural pattern is rebuilt as the SAME kind it matches (FWD-02):
            // STRUCTURAL PATTERN DELIMITERS SELECT THE VALUE KIND THEY DESTRUCTURE, so the only
            // argument the callee pattern can open is a value of its own kind, and
            // reconstruction never converts between sequence and list.
            SequenceValueParameterPattern group
                => BuildSequenceArgument(BuildPatternArgumentOutput(group.Items, mapCaptureName, forwardAsSpread, ref arguments)),
            ListValueParameterPattern list => new Expr.ListLiteral(new OutputBundle(
                BuildPatternArgumentOutput(list.Items, mapCaptureName, forwardAsSpread, ref arguments))),
            // The deconstruction unpacking receiver (never written; only a host-built callee can
            // carry one here) opens a list one level at every cardinality, so the exact list of
            // its items is the argument it re-binds exactly.
            UnpackingParameterPattern unpacking => new Expr.ListLiteral(new OutputBundle(
                BuildPatternArgumentOutput(unpacking.Items, mapCaptureName, forwardAsSpread, ref arguments))),
        };
        if (isGroup)
            (arguments ??= new Dictionary<ParameterPattern, Expr>(ReferenceEqualityComparer.Instance)).Add(pattern, argument);
        return argument;
    }

    /// <summary>
    /// A sequence pattern's rebuilt argument: exactly the tree the explicit written group
    /// <c>(e1, …, en)</c> has — <c>()</c> for no items, the one item itself for a lone non-spread
    /// item (a one-slot group IS its content, SYN-06; there is no one-item sequence), and
    /// otherwise a capture of the slots (a spread slot contributes its items). A valid sequence
    /// pattern matched a sequence of zero or at least two elements, so rebuilding a COPIED
    /// pattern reproduces that very sequence; a lone forwarded binding is the explicit call
    /// <c>C((x))</c>, which is <c>C(x)</c>.
    /// </summary>
    private static Expr BuildSequenceArgument(IReadOnlyList<Expr> items)
        => items switch
        {
            [] => new Expr.EmptySequence(0),
            [var only] when only is not Expr.SequenceSpread => only,
            _ => new Expr.Capture(new OutputBundle(items)),
        };

    private static IReadOnlyList<Expr> BuildPatternArgumentOutput(
        IReadOnlyList<ParameterPattern> patterns,
        Func<CaptureParameterPattern, string> mapCaptureName,
        Func<CaptureParameterPattern, bool> forwardAsSpread,
        ref Dictionary<ParameterPattern, Expr>? arguments)
    {
        var output = new List<Expr>(patterns.Count);
        foreach (var pattern in patterns)
            output.Add(BuildPatternArgument(pattern, mapCaptureName, forwardAsSpread, ref arguments));
        return output;
    }

    /// <summary>
    /// The lifting signature of one resolved callable (<see cref="TryResolveLiftable"/>), or — for a
    /// clause family whose clauses do not name every argument position unambiguously — why it has
    /// none (<see cref="Unnameable"/>).
    /// </summary>
    internal sealed record LiftingSignature(CallableSignature? Signature, UnnameableFamily? Unnameable)
    {
        public static LiftingSignature Of(CallableSignature signature) => new(signature, null);
    }

    /// <summary>
    /// Why a clause family has no formula-lifting signature: at <see cref="Position"/> (0-based) no
    /// clause binds a plain parameter, the clauses that do disagree on its name, or the name one
    /// position takes is already another position's (<see cref="OtherPosition"/>).
    /// </summary>
    internal sealed record UnnameableFamily(
        int Position,
        UnnameableFamilyReason Reason,
        IReadOnlyList<string> Names,
        int? OtherPosition = null);

    internal enum UnnameableFamilyReason
    {
        NoName,
        ConflictingNames,
        SharedWithAnotherPosition,
    }

    /// <summary>
    /// A value-role reference's resolved callable as formula lifting reads it: an identity (one per
    /// resolved declaration, whatever spelling reached it), the written name, and its lifting
    /// signature.
    /// </summary>
    private readonly record struct LiftableReference(object Identity, string DisplayName, LiftingSignature Signature)
    {
        /// <summary>The resolved callable, for diagnostics that name what the written reference denotes.</summary>
        public AliasTarget? Callable { get; init; }
    }

    /// <summary>
    /// What the front end knows about the callable a CALLABLE ALIAS resolves to (FWD-02, binding
    /// indirection): the NORMALIZED target — an alias of an alias is its final target — as the ONE
    /// identity resolution found it (<see cref="TryResolveCallable"/>): its <see cref="Identity"/>
    /// (the one formula lifting keys on, so an alias and its target are one callable), its
    /// <see cref="Algorithm"/> as processed (its kind and invocation), its <see cref="Signature"/>
    /// (the lifting signature and forwarding contract, or why an unnameable family has none), the
    /// <see cref="DisplayName"/> the target was written as where the chain ends, whether it is a
    /// Math member or a host operation (<see cref="IsStrictValue"/>: every argument a value role).
    /// That role is decided against the prelude the target was resolved in. Carried on the alias node (<see cref="Algorithm.Alias.ResolvedTarget"/>): static program
    /// structure only — never an activation, a value, or a cache entry.
    /// </summary>
    internal sealed record AliasTarget(
        object Identity,
        string DisplayName,
        Algorithm Algorithm,
        LiftingSignature Signature,
        bool IsStrictValue);

    /// <summary>
    /// THE ONE CALLABLE-IDENTITY RESOLUTION of a written reference (the unified formula-lifting law,
    /// decided September 30 2026; the callable alias, October 1 2026): the callable a reference
    /// resolves to by the language's own resolution order — the owner walk over the document's
    /// properties, then the prelude, then <c>open</c>, or a structural dot path — whatever its category
    /// or the route that reached it, as an identity (one per resolved declaration, whatever spelling
    /// reached it), its processed algorithm (its kind and invocation) and its lifting signature:
    /// <list type="bullet">
    ///   <item>a user algorithm: its parameter patterns, as processed;</item>
    ///   <item>a builtin: its ONE registry signature (<see cref="BuiltinDescriptor.PlainSignature"/>:
    ///   e.g. <c>while(meta step)</c>, <c>repeat(meta step, count)</c>);</item>
    ///   <item>a Math member (alias, <c>Math.X</c>, or opened) or a host operation: its declared
    ///   parameters;</item>
    ///   <item>a member reached through <c>open</c> or a structural dot path: that member's own
    ///   signature, from its PROCESSED provider;</item>
    ///   <item>a clause family: one whole-value slot per top-level position, named by the clauses
    ///   (<see cref="FamilyLiftingSignature"/>), or unnameable;</item>
    ///   <item>a CALLABLE ALIAS: its normalized target, exactly as recorded when the alias was
    ///   elaborated (<see cref="Algorithm.Alias.ResolvedTarget"/>) — one identity, one algorithm, one
    ///   signature: the alias and its target are one callable, so every question formula lifting,
    ///   argument roles, bare forwarding and another alias ask of an alias is answered by its
    ///   target.</item>
    /// </list>
    /// Null for a reference that resolves to nothing static (a parameter, an unresolved name, an
    /// ambiguous open, a run-time receiver's member): a callable known only at run time has no
    /// identity here. <paramref name="writtenName"/> is the reference as written (diagnostics name
    /// it; through an alias the result's <see cref="AliasTarget.DisplayName"/> is the target's).
    ///
    /// <para>B3-5★: the identity is the STATIC one (<see cref="ResolveStaticCallable"/>, read from the input, every
    /// reference row followed to its Q3 endpoint), and an open body's signature is the SELECTED one — so what a reference
    /// denotes, and what it lifts, never depend on which bodies were processed first.</para>
    /// </summary>
    private static AliasTarget? TryResolveCallable(Expr reference, SignatureMap paramMap, ResolverWalkMemos memos, out string writtenName)
        => ResolveStaticCallable(reference, paramMap, memos, out writtenName) is { } callable
            ? TargetOf(callable, memos.Run)
            : null;

    /// <summary>
    /// What the front end records of a static callable (B3-5★): its identity and display name, the algorithm it invokes —
    /// as this resolution processed it once it has, as written until then (its kind is the same either way) — and its
    /// FINAL lifting signature: the selected one for an open body of this resolution, the declared or completed one
    /// otherwise.
    /// </summary>
    private static AliasTarget TargetOf(StaticCallable callable, ResolutionRun run)
    {
        var algorithm = callable.Key is { } key
            ? run.StructuralOperation!.ResolvedView(key) ?? callable.Written
            : callable.Written;
        // Named by the hop that reached it (the spelling of the final written reference), whatever reached the cache first.
        var signature = callable.Key is { } selectedKey && SelectedSignatureOf(selectedKey, callable.DisplayName, run) is { } selected
            ? LiftingSignature.Of(selected)
            : FinalLiftingSignature(callable, callable.DisplayName, run);
        return new AliasTarget(callable.Identity, callable.DisplayName, algorithm, signature, run.Prelude.IsStrictValue(callable.Written));
    }

    /// <summary>Equality of a (reference, name) pair: the algorithm by reference, the name ordinally.</summary>
    private sealed class NamedAlgorithmComparer : IEqualityComparer<(Algorithm Algorithm, string Name)>
    {
        public static readonly NamedAlgorithmComparer Instance = new();

        public bool Equals((Algorithm Algorithm, string Name) x, (Algorithm Algorithm, string Name) y)
            => ReferenceEquals(x.Algorithm, y.Algorithm) && string.Equals(x.Name, y.Name, StringComparison.Ordinal);

        public int GetHashCode((Algorithm Algorithm, string Name) value)
            => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Algorithm), StringComparer.Ordinal.GetHashCode(value.Name));
    }

    /// <summary>
    /// A value-role reference's lifting facts: the projection of <see cref="TryResolveCallable"/>
    /// formula lifting reads (the written name names the reference in diagnostics).
    /// </summary>
    private static LiftableReference? TryResolveLiftable(Expr reference, SignatureMap paramMap, ResolverWalkMemos memos)
        => TryResolveCallable(reference, paramMap, memos, out var writtenName) is { } callable
            ? new LiftableReference(callable.Identity, writtenName, callable.Signature) { Callable = callable }
            : null;

    /// <summary>The lifting signature of an algorithm outside the document's map (cached per algorithm by reference).</summary>
    private static LiftingSignature LiftingSignatureOf(string name, Algorithm algorithm, ResolutionRun run)
    {
        if (run.LiftingSignatures.TryGetValue((algorithm, name), out var cached))
            return cached;

        var signature = algorithm switch
        {
            Algorithm.User user => LiftingSignature.Of(CallableSignature.FromUserAlgorithm(name, user)),
            Algorithm.Builtin(var builtin) => LiftingSignature.Of(BuiltinRegistry.GetBuiltin(builtin).PlainSignature),
            Algorithm.Conditional family => DeriveFamilyLiftingSignature(name, family),
            // An alias's is its target's (an alias with no recorded target declares nothing).
            Algorithm.Alias alias => alias.ResolvedTarget?.Signature ?? LiftingSignature.Of(new CallableSignature(name, [])),
        };
        run.LiftingSignatures.Add((algorithm, name), signature);
        return signature;
    }

    /// <summary>The lifting signature of a clause family (cached per family by reference).</summary>
    private static LiftingSignature FamilyLiftingSignature(string name, Algorithm.Conditional family, ResolutionRun run)
        => LiftingSignatureOf(name, family, run);

    /// <summary>
    /// A CLAUSE FAMILY'S LIFTING SIGNATURE (decided September 30 2026): a family is lifted like every
    /// other callable once its contract is derived from its clauses — ONE WHOLE-VALUE SLOT per
    /// top-level argument position (the family's common arity), passed whole, so the lifted call hands
    /// the family the caller's argument unchanged and dispatch is exactly the explicit call's.
    /// Formula lifting is by binding NAME, so each slot needs one name:
    /// <list type="bullet">
    ///   <item>each clause that binds a PLAIN parameter at a position votes that name; a literal, a
    ///   structural pattern and a binderless group name nothing (they are dispatch detail, never
    ///   leaves of the signature);</item>
    ///   <item>every vote for a position must agree, and every position needs one;</item>
    ///   <item>the names of different positions must be distinct — otherwise by-name lifting would feed
    ///   one binding to independent positions (<c>P(a, 0)</c> / <c>P(0, a)</c> is not <c>P(a, a)</c>).</item>
    /// </list>
    /// Otherwise the family has no lifting signature (<see cref="UnnameableFamily"/>): it stays
    /// explicitly callable, and a formula that would lift it is the front-end error
    /// <see cref="DiagnosticCode.UnliftableClauseFamily"/>. No name is ever invented.
    /// Lean: <c>familyLiftingSignature?</c>.
    /// </summary>
    internal static LiftingSignature DeriveFamilyLiftingSignature(string name, Algorithm.Conditional family)
    {
        static IReadOnlyList<Pattern> Positions(Pattern head) => head is Pattern.SequenceValue(var items) ? items : [head];

        if (family.Branches.Count == 0)
            return new(null, new UnnameableFamily(0, UnnameableFamilyReason.NoName, []));

        var arity = Positions(family.Branches[0].Pattern).Count;
        var names = new string?[arity];
        List<string>?[] conflicts = new List<string>?[arity];
        foreach (var branch in family.Branches)
        {
            var positions = Positions(branch.Pattern);
            if (positions.Count != arity)
                return new(null, new UnnameableFamily(System.Math.Min(arity, positions.Count), UnnameableFamilyReason.NoName, []));

            for (var position = 0; position < arity; position++)
            {
                if (positions[position] is not Pattern.Bind { ParameterKind: ParameterKind.Normal, IsRecoveryPlaceholder: false } binder)
                    continue;
                if (names[position] is null)
                {
                    names[position] = binder.Name;
                }
                else if (names[position] != binder.Name)
                {
                    var voted = conflicts[position] ??= [names[position]!];
                    if (!voted.Contains(binder.Name))
                        voted.Add(binder.Name);
                }
            }
        }

        for (var position = 0; position < arity; position++)
        {
            if (names[position] is null)
                return new(null, new UnnameableFamily(position, UnnameableFamilyReason.NoName, []));
            if (conflicts[position] is { } voted)
                return new(null, new UnnameableFamily(position, UnnameableFamilyReason.ConflictingNames, voted));
        }

        var first = new Dictionary<string, int>(StringComparer.Ordinal);
        for (var position = 0; position < arity; position++)
        {
            if (!first.TryAdd(names[position]!, position))
            {
                return new(null, new UnnameableFamily(
                    position, UnnameableFamilyReason.SharedWithAnotherPosition, [names[position]!], first[names[position]!]));
            }
        }

        return LiftingSignature.Of(new CallableSignature(name, names.Select(static parameter => new CallableParameter(parameter!)).ToArray()));
    }

    /// <summary>
    /// The KIND of the callee a call or dot edge names — never a signature — read STATICALLY (B3-5★,
    /// <see cref="StaticCalleeKindOf"/>): a lone bare row the rewrite makes a callable alias has its endpoint's kind (an
    /// alias's argument roles ARE its target's — no alias-specific role exists), whatever was processed before, so
    /// nothing is ever processed to learn a kind.
    /// </summary>
    private static LiftingCallee ResolveCalleeKind(Expr callee, SignatureMap paramMap, ResolverWalkMemos memos)
        => StaticCalleeKindOf(callee, paramMap, memos);

    /// <summary>
    /// How a dot edge dispatches (<see cref="FormulaLiftingRoles.EdgeKind"/>): the detector's stamped
    /// structural-miss verdict, or — for an unstamped host tree — this pass's own static receiver
    /// resolution (a name through the map and the prelude).
    /// </summary>
    private static DotEdgeKind EdgeKindOf(Expr.DotCall edge, SignatureMap paramMap, ResolverWalkMemos memos)
        => edge.ElaboratedMissSelection is null
            ? EdgeKindOf(edge, paramMap, memos.Run.Prelude)
            : FormulaLiftingRoles.EdgeKind(edge, MissSelectionOf(edge, paramMap, memos));

    /// <summary>
    /// The structural-miss verdict this pass reads for the stamped edge <paramref name="edge"/> where it classifies the
    /// roles of its receiver and arguments: parameter detection's, refined from MAY to MUST where the receiver certainly
    /// lacks the member (M4★). Detection reads a receiver as one the runtime decides when its structure depends on what
    /// only this pass decides: a navigated body whose head an enclosing body may infer (<c>A = x</c>), which this pass's
    /// INPUT already decides, and an <c>.Algorithm</c> link body (<c>A = Mk(x).Algorithm</c>: a calculation when it keeps
    /// a parameter, a runtime reference otherwise), which only its processing decides. So the receiver is read from the
    /// input with nothing processed (<see cref="ReadReceiver"/>), the same whatever was processed before; a link body's
    /// SELECTED class (B3-5★) is read only where a certain miss would give the receiver or an argument a VALUE role
    /// (<see cref="CertainMissDecidesALift"/>: elsewhere MAY and MUST give every slot the same role, and no later pass
    /// tells MAY from MUST — they read NEVER against the rest). A
    /// parameter's member, a runtime reference's and an unresolved name's stay MAY, with nothing read. Never NEVER:
    /// detection's inference reads MAY and MUST alike, and the refinement must not contradict it. ONE answer per edge and
    /// region (<see cref="ResolverWalkMemos.LiftMissSelections"/>), so the dependency walk and the rewrite read the same.
    /// The reports a certain miss makes are decided once resolution has processed every body
    /// (<see cref="ResolutionRun.CommitDeferredChecks"/>).
    /// </summary>
    private static LexicalFallbackSelection MissSelectionOf(Expr.DotCall edge, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        if (edge.ElaboratedMissSelection is not LexicalFallbackSelection.Conditional)
            return edge.ElaboratedMissSelection ?? LexicalFallbackSelection.Conditional;
        memos.LiftMissSelections ??= new(ReferenceEqualityComparer.Instance);
        if (!memos.LiftMissSelections.TryGetValue(edge, out var selection))
        {
            var run = memos.Run;
            var receiver = ReadReceiver(edge.Target, run.Level, paramMap, run, selectedLinks: false);
            if (receiver.Kind == ReceiverReadingKind.Link)
            {
                // B3-5★: a link's class is SELECTED, never processed on demand — the very class the analysis guarded this
                // edge's slots with. A calculation link declares no member, so its miss is certain; a runtime reference's
                // is the runtime's.
                receiver = CertainMissDecidesALift(edge, paramMap, memos)
                    ? ReadReceiver(edge.Target, run.Level, paramMap, run, selectedLinks: true)
                    : default;
            }

            selection = receiver.Lacks(edge.Name, run) ? LexicalFallbackSelection.Always : LexicalFallbackSelection.Conditional;
            memos.LiftMissSelections[edge] = selection;
        }

        return selection;
    }

    /// <summary>
    /// Whether a certain miss of the MAY edge <paramref name="edge"/> would give its receiver or one of its arguments a
    /// VALUE role (<see cref="FormulaLiftingRoles"/>) — the only way its verdict reaches a lift: the fallback call
    /// <c>n(R, args)</c> of a clause family, a Math member, a host operation or a builtin value slot, a dot intrinsic's
    /// VALUE receiver. A user callable or a runtime callee takes the receiver and every argument in a CALLABLE role under
    /// either verdict. The callee is read from this pass's input with nothing processed
    /// (<see cref="StaticFallbackCalleeKind"/>), so asking processes nothing.
    /// </summary>
    private static bool CertainMissDecidesALift(Expr.DotCall edge, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        var run = memos.Run;
        var kind = FormulaLiftingRoles.EdgeKind(edge, LexicalFallbackSelection.Always);
        var callee = kind == DotEdgeKind.Fallback
            ? StaticFallbackCalleeKind(edge.EffectiveLexicalFallback, paramMap, run)
            : LiftingCallee.Dynamic;
        if (FormulaLiftingRoles.ReceiverRole(kind, callee) == LiftingRole.Value)
            return true;
        if (edge.Args is not { } args)
            return false;
        // A MAY edge's receiver is never a marked reference (its stamp is no certain fallback): only its arguments can spread.
        var roles = DotArgumentRolesWithSpreads(edge, kind, callee, StaticLift.None, paramMap, memos, out _);
        for (var i = 0; i < args.Count; i++)
        {
            if (roles[i] == LiftingRole.Value)
                return true;
        }

        return false;
    }

    /// <summary>
    /// The kind of the callee a certain miss of a MAY edge calls (<see cref="CertainMissDecidesALift"/>), read from this
    /// pass's input with nothing processed: the fallback name by the owner walk and the prelude, then the levels' written
    /// opens (<see cref="DirectDeclaration"/>, <see cref="StaticOpenedDeclaration"/>), a body that may become a callable alias
    /// followed to what it invokes (<see cref="StaticInvocationTarget"/>) — an alias's kind is its target's, so the roles
    /// read here are the roles the rewrite reads once it is processed. A parameter is known only at run time.
    /// </summary>
    private static LiftingCallee StaticFallbackCalleeKind(Expr fallback, SignatureMap map, ResolutionRun run)
    {
        if (fallback.UnwrapGraceOperand() is not Expr.Resolve(var name)
            || (DirectDeclaration(name, run.Level, run.Prelude)
                ?? StaticOpenedDeclaration(name, run.Level)) is not { } declared)
        {
            return LiftingCallee.Dynamic;
        }

        var target = StaticInvocationTarget(declared, run).End.Target;
        return LiftingCallee.OfAlgorithm(target, run.Prelude.IsStrictValue(target));
    }

    /// <summary>What <see cref="ReadReceiver"/> found a MAY edge's receiver to be.</summary>
    private enum ReceiverReadingKind
    {
        /// <summary>
        /// Nothing this pass knows: a parameter, a runtime reference, a name nothing static declares, a member a runtime
        /// receiver decides.
        /// </summary>
        Unknown,

        /// <summary>A VALUE — an inner edge whose miss is certain (its fallback call or intrinsic is a calculation) — which declares no member.</summary>
        Value,

        /// <summary>A body whose STRUCTURE is known: its declared members are the receiver's (processing changes no body's members).</summary>
        Structure,

        /// <summary>
        /// An unbraced <c>.Algorithm</c> link body (META-S3-1): a calculation, its own structure, when inference and lifting
        /// leave it a parameter of its own, a runtime reference otherwise — which only its processing decides.
        /// </summary>
        Link,
    }

    /// <summary>
    /// A MAY edge's receiver as <see cref="ReadReceiver"/> read it: the <see cref="Structure"/> of a known one, the
    /// declaration of a <see cref="Link"/> body still to be processed.
    /// </summary>
    private readonly record struct ReceiverReading(ReceiverReadingKind Kind, Algorithm? Structure = null, StaticDeclaration Link = default)
    {
        /// <summary>
        /// Whether the receiver certainly lacks the member <paramref name="name"/>: a value, or a known structure declaring
        /// no such member (nor one only its clause branches declare).
        /// </summary>
        public bool Lacks(string name, ResolutionRun run) => Kind switch
        {
            ReceiverReadingKind.Value => true,
            ReceiverReadingKind.Structure
                => run.StructuralViews.DeclaredMember(Structure!, name) is null && !Structure!.DefinesConditionalBranchProperty(name),
            _ => false,
        };
    }

    /// <summary>
    /// What the receiver <paramref name="receiver"/> of a MAY edge is, read from this pass's INPUT at
    /// <paramref name="level"/> — every declaration as written, a reference followed to its target by the stratified static
    /// chase (<see cref="StaticReferenceStructure"/>), each member path through its receivers' structures — so the reading
    /// is the same whatever was processed before: a name by the owner walk and the prelude, then the levels' written
    /// opens; an inner edge as its own verdict reads (a structural member's structure, a certain miss's value, a MAY edge's
    /// own refinement); a block as written. A body is its own structure — processing changes no body's declared members —
    /// unless it has the one shape implicit-argument resolution turns into a reference rather than a structure
    /// (<see cref="IsUnbracedLoneRowBody"/>): a parameter row or a member path rooted at one is a runtime reference
    /// (unknown), and an <c>.Algorithm</c> link is a <see cref="ReceiverReadingKind.Link"/> — or, with
    /// <paramref name="selectedLinks"/>, what its SELECTED class makes it (B3-5★): a calculation is its own structure (it
    /// declares no member), a runtime reference unknown. Nothing is ever processed to read a receiver.
    /// </summary>
    private static ReceiverReading ReadReceiver(Expr receiver, ResolverLevel? level, SignatureMap map, ResolutionRun run, bool selectedLinks)
    {
        FrontEndStack.Ensure();
        switch (receiver.UnwrapGraceOperand())
        {
            case Expr.Resolve(var name):
                return (DirectDeclaration(name, level, run.Prelude)
                        ?? StaticOpenedDeclaration(name, level)) is { } declared
                    ? ReadDeclaration(declared, run, selectedLinks)
                    : default;

            case Expr.DotCall { Args: null } inner when inner.ElaboratedMissSelection is { } selection:
                if (selection == LexicalFallbackSelection.Always)
                    return new(ReceiverReadingKind.Value);
                if (selection == LexicalFallbackSelection.Never)
                {
                    return StructuralMemberAt(inner, level, StaticCycleCheck.Formation) is { } member
                        ? ReadDeclaration(member, run, selectedLinks)
                        : default;
                }

                // A MAY inner edge is a value exactly when its own receiver certainly lacks its member.
                var innerReceiver = ReadReceiver(inner.Target, level, map, run, selectedLinks);
                return innerReceiver.Kind == ReceiverReadingKind.Link
                    ? innerReceiver
                    : innerReceiver.Lacks(inner.Name, run) ? new(ReceiverReadingKind.Value) : default;

            case Expr.AlgorithmExpr block:
                return new(ReceiverReadingKind.Structure, block.Algorithm);

            default:
                return default;
        }
    }

    /// <summary>The receiver <see cref="ReadReceiver"/> found a declaration to be (its static structure; see there).</summary>
    private static ReceiverReading ReadDeclaration(StaticDeclaration declared, ResolutionRun run, bool selectedLinks)
    {
        if (run.StructuralOperation is { } operation)
        {
            var key = operation.ContextOf(declared.Level?.StaticContext?.Key ?? operation.Queries.Keys.Root, declared.Target);
            var selected = operation.Read(StaticQueryKey.TargetWalk(key, StaticCycleCheck.Formation));
            if (selected.Kind == StaticFactKind.Runtime)
            {
                // Runtime carries a written reference recipe, never a static namespace. Q8 decides whether completing that
                // recipe's signature makes an Algorithm link a calculation (B3-5★: its selected class).
                if (selected.Scope is not { } recipe || operation.SourceOf(recipe) is not Algorithm.User source
                    || source.Output is not [Expr.DotCall { Args: null } edge] || !edge.UsesDotAlgorithmIntrinsic()) return default;
                var link = operation.Declaration(recipe);
                return selectedLinks ? SelectedLinkReading(link, run) : new(ReceiverReadingKind.Link, Link: link);
            }
        }
        if (StaticReferenceStructure(declared, run.StructuralViews, viaOpens: true, StaticCycleCheck.Formation) is not { } structure)
            return default;
        if (structure.Raw && structure.Target is Algorithm.User body && IsUnbracedLoneRowBody(body))
        {
            var row = body.Output[0];
            // A parameter, or a member path rooted at one: a runtime reference, whose members only the run decides.
            if (row is Expr.Param || AliasTargetRows.IsParamHeaded(row))
                return default;
            if (row is Expr.DotCall { Args: null } link && link.UsesDotAlgorithmIntrinsic())
                return selectedLinks ? SelectedLinkReading(structure, run) : new(ReceiverReadingKind.Link, Link: structure);
        }

        return new(ReceiverReadingKind.Structure, structure.Target);
    }

    /// <summary>A link receiver as its SELECTED class reads (B3-5★): a calculation is its own structure, a runtime reference unknown.</summary>
    private static ReceiverReading SelectedLinkReading(StaticDeclaration link, ResolutionRun run)
        => SelectedLinkIsCalculation(LinkKey(link, run), run) ? new(ReceiverReadingKind.Structure, link.Target) : default;

    /// <summary>
    /// Whether the link <paramref name="key"/> is a calculation (B3-5★): its selected signature declares a parameter; a link
    /// an earlier operation completed reads its completed body.
    /// </summary>
    private static bool SelectedLinkIsCalculation(StaticScopeKey key, ResolutionRun run)
        => run.Selected?.TryGetFact(key, out var fact) == true ? fact.IsNonempty : FinalLinkIsCalculation(key, run);

    /// <summary>
    /// The input shape implicit-argument resolution may make a REFERENCE — static or runtime — rather than a structure of
    /// its own: an unbraced open body, with no parameter, declaration or open of its own, whose one written row is that
    /// row (the shape of <c>ElaboratedScopeLookup.WillBeReference</c>, whatever its row).
    /// </summary>
    private static bool IsUnbracedLoneRowBody(Algorithm.User body)
        => !body.IsWrittenBlock
            && !body.HasExplicitParameterList
            && body.ParameterPatterns.Count == 0
            && body.Properties.Count == 0
            && body.Opens.Count == 0
            && !body.IsSyntheticDeconstructionPlumbing
            && !body.IsModuleRoot
            && body.Output.Count == 1
            && AstHelpers.WrittenRows(body).Count == 1;

    /// <summary>What the innermost receiver of the argumentless member path <paramref name="path"/> is (the path itself when it is no such path).</summary>
    private static Expr PathHead(Expr path)
    {
        var head = path.UnwrapGraceOperand();
        while (head is Expr.DotCall { Args: null } step)
            head = step.Target.UnwrapGraceOperand();
        return head;
    }

    private static DotEdgeKind EdgeKindOf(Expr.DotCall edge, SignatureMap paramMap, PreludeContext prelude)
        => FormulaLiftingRoles.EdgeKind(
            edge,
            edge.ElaboratedMissSelection
                ?? edge.GetStructuralMissSelection(edge.Target.UnwrapGraceOperand().ResolveStaticStructuralMemberProvider(
                    name => paramMap.TryGetValue(name, out var entry)
                        ? new(StaticStructuralMemberProviderKind.KnownAlgorithm, entry.Value)
                        : prelude.TryGetMember(name, out var member)
                            ? new(StaticStructuralMemberProviderKind.KnownAlgorithm, member.Value)
                            : new(StaticStructuralMemberProviderKind.LexicalReference))));

    /// <summary>
    /// The cell an alias records its TARGET in (<see cref="AliasTargetCell"/>, M4★): the target's identity and signature are
    /// final when the alias is formed (B3-5★: the endpoint and its selected signature); only the algorithm it invokes can
    /// still be a body this run has not processed, in which case the cell is pending on that body's context and completed
    /// once it is processed. Any other target is final.
    /// </summary>
    private static AliasTargetCell TargetCellOf(AliasTarget target, ResolverWalkMemos memos)
        => target.Identity is StaticScopeKey key
            && memos.Run.StructuralOperation!.ResolvedView(key) is null
                ? memos.Run.PendingTargetOn(target)
                : AliasTargetCell.Of(target);

    /// <summary>Q9 retains the publication cell of the Q3-selected row target.</summary>
    private static AliasStructureCell? StaticStructureOfRow(Expr row, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        var context = memos.Run.Level?.StaticContext ?? throw new InvalidOperationException("Alias structure requires a structural context.");
        var target = context.Operation.Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, context.Key, StaticQueryProjection.RowTarget));
        if (target.Kind != StaticFactKind.Structure || target.Scope is not { } key) return null;
        var source = context.Operation.SourceOf(key);
        // Registry signatures/namespaces are final at admission. Q9 must not wait for a
        // document property loop to process a prelude declaration that loop never owns.
        if (memos.Run.Prelude.IsFinalRegistryAlgorithm(source)
            && context.Operation.Published(key, StaticPublicationStage.Resolved) is null)
        {
            if (context.Operation.DetectedView(key) is null)
                context.Operation.Publish(key, StaticPublicationStage.Detected, source);
            context.Operation.Publish(key, StaticPublicationStage.Resolved, source);
        }
        return context.Operation.StructureCell(key);
    }

    /// <summary>The declaration a recorded entry denotes, as a static chase reads it.</summary>
    private static StaticDeclaration EntryDeclaration(VisibleProperty entry, bool raw)
    {
        var owners = entry.Owners ?? DeclaringOwners.Root;
        return new StaticDeclaration(entry.Value, OpenProviderIdentity.DeclaredIn(entry.Value, owners), owners, entry.Level) { Raw = raw };
    }

    /// <summary>Q3's invocation projection, preserving the written final hop for diagnostics.</summary>
    private static (StaticDeclaration End, string? Through) StaticInvocationTarget(StaticDeclaration start, ResolutionRun run)
    {
        if (!start.Raw) return (start, null);
        var operation = run.StructuralOperation ?? throw new InvalidOperationException("Invocation selection requires a structural operation.");
        var (end, row) = operation.InvocationTarget(start);
        return (end, row is Expr.DotCall dotted ? DottedDisplayName(dotted) : (row as Expr.Resolve)?.Name);
    }

    /// <summary>The written spelling of a dotted callee (<c>Lib.Inc</c>, <c>Math.Abs</c>) for diagnostics, bounded.</summary>
    private static string DottedDisplayName(Expr.DotCall edge)
    {
        FrontEndStack.Ensure();
        return ExprNameRenderer.BoundName(edge.Target.UnwrapGraceOperand() switch
        {
            Expr.Resolve(var head) => head + "." + edge.Name,
            Expr.DotCall { Args: null } inner => DottedDisplayName(inner) + "." + edge.Name,
            _ => edge.Name,
        });
    }

    /// <summary>
    /// Collects the implicit dependencies of a formula's rows: every VALUE-role reference
    /// (<see cref="FormulaLiftingRoles"/>) whose resolved callable has a lifting signature that
    /// REQUIRES supplied arguments (<see cref="RequiresSuppliedArguments"/>), once per resolved
    /// identity. A reference in a CALLABLE role, one to a callable that accepts zero supplied
    /// arguments (a cached read, Q-03), and one to an unnameable family contribute nothing. The walk
    /// is the shared role walk (<see cref="WalkLiftingRoles{TSink}"/>), the one the analysis phase
    /// records equations with.
    /// </summary>
    private static void CollectImplicitDeps(
        Expr expr,
        SignatureMap paramMap,
        HashSet<object> seen,
        List<LiftedDependency> deps,
        LiftingRole role,
        DepsWalkMemo memo)
    {
        var sink = new DependencySink(paramMap, seen, deps, memo);
        WalkLiftingRoles(expr, role, guard: null, ref sink);
    }

    /// <summary>
    /// The rewrite's instantiation of the role walk: a value-role reference lifts its callee's FINAL signature; a dot edge
    /// reads its refined verdict (<see cref="MissSelectionOf"/>, a link's selected class). DAG-safety: every contribution is
    /// identity deduplicated, so a completed node reached again under the same role — the one context dimension that
    /// changes what a node contributes — adds nothing and is skipped; childless leaves decide in place.
    /// </summary>
    private readonly struct DependencySink(SignatureMap paramMap, HashSet<object> seen, List<LiftedDependency> deps, DepsWalkMemo memo)
        : ILiftingWalkSink
    {
        public bool Enter(Expr expr, LiftingRole role, StaticScopeKey? guard)
        {
            if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
                return true;
            var visited = role == LiftingRole.Callable
                ? memo.CalleeVisited ??= new(ReferenceEqualityComparer.Instance)
                : memo.ValueVisited;
            if (visited.Contains(expr))
                return false;
            memo.Observations?.RecordResolverCollectExpansion();
            return true;
        }

        public void Exit(Expr expr, LiftingRole role, StaticScopeKey? guard)
        {
            if (AstTraversalDagSafety.HasTraversableExprChildren(expr))
                (role == LiftingRole.Callable ? memo.CalleeVisited! : memo.ValueVisited).Add(expr);
        }

        public void Reference(Expr reference, StaticScopeKey? guard) => AddLiftedDependency(reference, paramMap, seen, deps, memo);

        public LiftingCallee CalleeKind(Expr callee) => ResolveCalleeKind(callee, paramMap, memo.Walk);

        public DotEdgeKind EdgeKind(Expr.DotCall edge, out DotEdgeKind mayKind, out StaticScopeKey? link)
        {
            mayKind = default;
            link = null;
            return EdgeKindOf(edge, paramMap, memo.Walk);
        }

        public LiftingCallee DotEdgeCallee(Expr.DotCall edge, DotEdgeKind kind) => ImplicitArgumentResolver.DotEdgeCallee(edge, kind, paramMap, memo.Walk);

        public LiftingRole[] ArgumentRoles(LiftingCallee callee, OutputBundle args)
            => ArgumentRolesWithSpreads(callee, args, leadingSlots: 0, leadingPositionsKnown: true, paramMap, memo.Walk, out _);

        public LiftingRole[] DotArgumentRoles(Expr.DotCall edge, DotEdgeKind kind, LiftingCallee callee)
            => DotArgumentRolesWithSpreads(edge, kind, callee, ReceiverLift(edge, kind, callee, paramMap, memo.Walk), paramMap, memo.Walk, out _);
    }

    /// <summary>Adds a value-role reference's callee to the dependencies when it lifts (once per identity).</summary>
    private static void AddLiftedDependency(Expr reference, SignatureMap paramMap, HashSet<object> seen, List<LiftedDependency> deps, DepsWalkMemo memo)
    {
        if (TryResolveLiftable(reference, paramMap, memo.Walk) is { Signature.Signature: { } signature } liftable
            && RequiresSuppliedArguments(signature)
            && seen.Add(liftable.Identity))
        {
            deps.Add(new LiftedDependency(liftable.DisplayName, signature, reference));
        }
    }

    /// <summary>The callee whose slots a non-reference dot edge's receiver and arguments fill.</summary>
    private static LiftingCallee DotEdgeCallee(Expr.DotCall dotCall, DotEdgeKind kind, SignatureMap paramMap, ResolverWalkMemos memos)
        => kind switch
        {
            DotEdgeKind.StructuralMember => ResolveCalleeKind(dotCall with { Args = null }, paramMap, memos),
            DotEdgeKind.Fallback => ResolveCalleeKind(dotCall.EffectiveLexicalFallback, paramMap, memos),
            _ => LiftingCallee.Dynamic,
        };

    /// <summary>
    /// Rewrites every VALUE-role reference whose resolved callable lifts (<see cref="TryResolveLiftable"/>)
    /// into the explicit call that forwards its lifting signature, and processes nested algorithms.
    /// The role of every child is its consumer's (<see cref="FormulaLiftingRoles"/>).
    /// </summary>
    private static Expr RewriteImplicitCalls(
        Expr expr,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        LiftingRole role,
        ResolverWalkMemos memos)
    {
        FrontEndStack.Ensure();
        memos.PinRewriteContext(context);
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr) && expr is not Expr.Resolve)
            return RewriteImplicitCallsCore(expr, paramMap, context, role, memos);
        var rewriteMap = memos.RewriteMapFor(role);
        if (rewriteMap.TryGetValue(expr, out var rewritten)) return rewritten;
        if (AstTraversalDagSafety.HasTraversableExprChildren(expr)) memos.Observations?.RecordResolverRewriteExpansion();
        rewritten = RewriteImplicitCallsCore(expr, paramMap, context, role, memos);
        rewriteMap[expr] = rewritten;
        return rewritten;
    }

    private static Expr RewriteImplicitCallsCore(
        Expr expr,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        LiftingRole role,
        ResolverWalkMemos memos)
    {
        // Every child rewrite is a `with` copy of the node: the record copy carries the span
        // (and every other stored fact) inside the copy constructor, so this calibrated
        // recursion frame holds no span temporaries — see ModuleLoader.ProcessExpr.
        return expr switch
        {
            Expr.Resolve => RewriteBareReference(expr, paramMap, context, role, memos),

            Expr.Call call => RewriteCall(call, paramMap, context, memos),

            Expr.Binary binary => binary with
            {
                Left = RewriteImplicitCalls(binary.Left, paramMap, context, LiftingRole.Value, memos),
                Right = RewriteImplicitCalls(binary.Right, paramMap, context, LiftingRole.Value, memos),
            },

            Expr.Comparison comparison => comparison with
            {
                First = RewriteImplicitCalls(comparison.First, paramMap, context, LiftingRole.Value, memos),
                Links = AstHelpers.RewriteComparisonLinks(
                    comparison.Links,
                    operand => RewriteImplicitCalls(operand, paramMap, context, LiftingRole.Value, memos)),
            },

            Expr.Unary unary => unary with
            {
                Operand = RewriteImplicitCalls(unary.Operand, paramMap, context, LiftingRole.Value, memos),
            },

            // The receiver and every selector slot are VALUE uses (CollectImplicitDeps). A whole selector
            // slot is an output-spreading position (R2); the receiver is one value.
            Expr.Index index => index with
            {
                Target = RewriteImplicitCalls(index.Target, paramMap, context, LiftingRole.Value, memos),
                Selectors = index.Selectors.Select(selector => SpreadIfMarked(
                    selector, RewriteImplicitCalls(selector, paramMap, context, LiftingRole.Value, memos), paramMap, memos)).ToList(),
            },

            // The operand of a written `*` is an output-spreading position (`A(1, 2)*` is `A(1, 2)**`, the
            // chained-spread law); the operand of a spread the front end inserted is the marked call itself.
            Expr.SequenceSpread spread => spread with
            {
                Operand = spread.InsertedFor is null
                    ? SpreadIfMarked(spread.Operand, RewriteImplicitCalls(spread.Operand, paramMap, context, LiftingRole.Value, memos), paramMap, memos)
                    : RewriteImplicitCalls(spread.Operand, paramMap, context, LiftingRole.Value, memos),
            },

            Expr.SequenceConstruct construct => construct with
            {
                Left = RewriteImplicitCalls(construct.Left, paramMap, context, LiftingRole.Value, memos),
                Right = RewriteImplicitCalls(construct.Right, paramMap, context, LiftingRole.Value, memos),
            },

            // A list element and an element of a multi-slot group are output-spreading positions (R2).
            Expr.ListLiteral list => list with
            {
                Items = list.Items.Select(item => SpreadIfMarked(
                    item, RewriteImplicitCalls(item, paramMap, context, LiftingRole.Value, memos), paramMap, memos)).ToList(),
            },

            Expr.DotCall dotCall => RewriteDotCall(dotCall, paramMap, context, role, memos),

            Expr.Grace(var inner, _) => RewriteImplicitCalls(inner, paramMap, context, role, memos),

            Expr.AlgorithmExpr block => block with
            {
                Algorithm = ProcessSharedNestedAlgorithm(block.Algorithm, ImportSite.OfBlock(block), paramMap, memos),
            },

            // A capture element is a value (a capture has no algorithm identity to transport).
            Expr.Capture capture => capture with
            {
                Body = new OutputBundle(capture.Body
                    .Select(row => SpreadIfMarked(row, RewriteImplicitCalls(row, paramMap, context, LiftingRole.Value, memos), paramMap, memos))
                    .ToList()),
            },

            // Intentional leaves: nothing to lift or rewrite. (A Param is an
            // already-elaborated parameter reference; the Resolve arm above
            // handled every liftable name shape.)
            Expr.Num or Expr.Param or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence or Expr.NativeCall => expr,
        };
    }

    /// <summary>
    /// The bare-reference arm of <see cref="RewriteImplicitCallsCore"/>: a VALUE-role reference whose
    /// resolved callable has a lifting signature that REQUIRES supplied arguments lifts to an
    /// explicit implicit-argument call unless the caller's closed explicit parameter list blocks the
    /// forwarding (the reference then stays bare: its run-time zero-argument demand, PAR-04 / Q-15). An unnameable clause family is
    /// reported (<see cref="DiagnosticCode.UnliftableClauseFamily"/>). Every other reference stays
    /// bare — a callable role, a callable that accepts zero supplied arguments (a cached
    /// property-style value demand, Q-03), or a reference with no lifting signature.
    /// </summary>
    private static Expr RewriteBareReference(
        Expr expr,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        LiftingRole role,
        ResolverWalkMemos memos)
    {
        if (role != LiftingRole.Value || TryResolveLiftable(expr, paramMap, memos) is not { } liftable)
            return expr;

        if (TryGetLiftArguments(expr, liftable, context, memos) is not { } implicitArgs)
            return expr;

        // The arguments are the region's one shared bundle for this callee (FE-2); the call node is
        // this reference's own, and its callee keeps the reference's elaboration stamps.
        return memos.SynthesizedImplicitCall(
            new Expr.Call(((Expr.Resolve)expr) with { }, implicitArgs) { Span = expr.Span });
    }

    /// <summary>
    /// The forwarding arguments of one value-role reference that lifts, or null when it does not:
    /// an unnameable family (reported in an inferring body), a callable that accepts zero supplied
    /// arguments (Q-03), or a closed list that cannot supply its parameters (PAR-04; never reported
    /// statically — the bare reference is its run-time demand, Q-15).
    /// </summary>
    private static OutputBundle? TryGetLiftArguments(
        Expr reference,
        LiftableReference liftable,
        ImplicitRewriteContext context,
        ResolverWalkMemos memos)
    {
        if (liftable.Signature.Unnameable is { } unnameable)
        {
            // Only a body that would lift the family reports it — an inferring one. A closed list
            // forwards nothing but same-named existing bindings (PAR-04), and an unnameable family
            // names nothing, so there the reference keeps its ordinary zero-argument demand and
            // runtime checking, exactly as every blocked reference does.
            if (context.ClosedParameterNames is null)
                ReportUnliftableClauseFamily(
                    reference,
                    liftable.DisplayName,
                    liftable.Callable is { } callable && !string.Equals(callable.DisplayName, liftable.DisplayName, StringComparison.Ordinal)
                        ? callable.DisplayName
                        : null,
                    unnameable,
                    memos);
            return null;
        }

        var signature = liftable.Signature.Signature!;
        if (!RequiresSuppliedArguments(signature))
            return null;

        if (ClosedListBlocksLifting(context, signature.ParameterPatterns, memos))
        {
            return null;
        }

        return memos.ImplicitArguments(signature.ParameterPatterns, context);
    }









    /// <summary>
    /// The Call arm of <see cref="RewriteImplicitCallsCore"/>: the callee is CALLABLE, and each
    /// argument slot takes the role the callee's kind gives it (<see cref="FormulaLiftingRoles.ArgumentRoles"/>)
    /// — a user callable's whole argument stays neutral so higher-order references survive
    /// (<c>Twice(A)</c>), while a builtin value slot, a Math or host argument, a family argument, and
    /// every expression NESTED in any argument are values (<c>Twice(A + 0)</c> lifts <c>A</c>).
    /// A Math member's arguments are VALUE roles like any other (no static strict-value demand since Q-15).
    /// </summary>
    private static Expr RewriteCall(
        Expr.Call call,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        ResolverWalkMemos memos)
    {
        var newFunc = RewriteImplicitCalls(call.Function, paramMap, context, LiftingRole.Callable, memos);
        var callee = ResolveCalleeKind(call.Function, paramMap, memos);
        // A slot this pass spreads — a written marked call, or a marked reference formula lifting calls — makes later
        // positions unknown, as a written `*` does (the role walk reads the same ArgumentRolesWithSpreads, so the analysis
        // selected the signatures these roles lift); every predicted lift is checked against the call built below.
        var roles = ArgumentRolesWithSpreads(
            callee, call.Args, leadingSlots: 0, leadingPositionsKnown: true, paramMap, memos, out var lifts, report: true);
        var newArgs = new List<Expr>(call.Args.Count);
        for (var i = 0; i < call.Args.Count; i++)
        {
            // A LAZY slot (a branch of `if`) is rewritten exactly like any other — lifting is blind
            // to laziness; whether the lifted call ever runs is the evaluator's demand (Q-15). Inline,
            // so the calibrated recursion adds no frame per argument level. A whole argument slot of
            // any callee is an output-spreading position (no exemption, R2).
            var processed = RewriteImplicitCalls(call.Args[i], paramMap, context, roles[i], memos);
            if (lifts is not null)
                RequirePredictedLift(call.Args[i], processed, lifts[i]);
            newArgs.Add(SpreadIfMarked(call.Args[i], processed, paramMap, memos));
        }

        return new Expr.Call(newFunc, new OutputBundle(newArgs)) { Span = call.Span };
    }

    /// <summary>
    /// The DotCall arm of <see cref="RewriteImplicitCallsCore"/>. A STRUCTURAL dotted callable in a
    /// value role (<c>Lib.Inc</c>, <c>Math.Pow</c>) lifts like a bare reference, from its member's
    /// own signature; its receiver is navigated. Otherwise the edge's receiver and arguments take the
    /// roles of its dispatch (<see cref="FormulaLiftingRoles.ReceiverRole"/>): the <c>string</c>
    /// intrinsic converts its receiver's value; a selected fallback is the call <c>F(receiver, args)</c>
    /// (dotted-call equivalence holds through elaboration, so <c>R.F(args)</c> and <c>F(R, args)</c>
    /// infer alike); a structural member call's arguments are that member's slots; a runtime receiver
    /// decides nothing statically. A Math member's receiver and arguments are VALUE roles (no static
    /// strict-value demand since Q-15). The stored lexical fallback is a Resolve/Param leaf; <c>with</c> carries it.
    /// </summary>
    private static Expr RewriteDotCall(
        Expr.DotCall dotCall,
        SignatureMap paramMap,
        ImplicitRewriteContext context,
        LiftingRole role,
        ResolverWalkMemos memos)
    {
        // A miss detection left to the runtime receiver: the checks that wait on it are decided once this run has
        // processed every body, from the receiver as it then stands (ProvisionalMiss, ResolutionRun.CommitDeferredChecks);
        // the edge carries the verdict the rewrite reads (MissSelectionOf).
        if (dotCall.ProvisionalMiss is { } provisional)
        {
            var edge = dotCall;
            var level = memos.Run.Level;
            provisional.Register(() => ReadReceiver(edge.Target, level, paramMap, memos.Run, selectedLinks: true).Lacks(edge.Name, memos.Run));
            memos.Run.Await(provisional);
        }

        // Output spreading decides on the WRITTEN edge (its detector stamp), never on the verdict refined below.
        var written = dotCall;
        if (dotCall.ElaboratedMissSelection is LexicalFallbackSelection.Conditional
            && MissSelectionOf(dotCall, paramMap, memos) is LexicalFallbackSelection.Always)
        {
            dotCall = dotCall with { ElaboratedMissSelection = LexicalFallbackSelection.Always };
        }

        var kind = EdgeKindOf(dotCall, paramMap, memos);
        if (dotCall.Args is null && kind == DotEdgeKind.StructuralMember)
        {
            if (role == LiftingRole.Value
                && TryResolveLiftable(dotCall, paramMap, memos) is { } liftable
                && TryGetLiftArguments(dotCall, liftable, context, memos) is { } liftedArgs)
            {
                return memos.SynthesizedImplicitCall(dotCall with
                {
                    Target = RewriteImplicitCalls(dotCall.Target, paramMap, context, LiftingRole.Callable, memos),
                    Args = liftedArgs,
                });
            }

            return dotCall with
            {
                Target = RewriteImplicitCalls(dotCall.Target, paramMap, context, LiftingRole.Callable, memos),
            };
        }

        var callee = DotEdgeCallee(dotCall, kind, paramMap, memos);
        // A receiver formula lifting calls for a marked declaration is a spread slot too (D2): decided on the written edge.
        var receiverLift = ReceiverLift(written, kind, callee, paramMap, memos);
        OutputBundle? newArgs = null;
        if (dotCall.Args is { } dotArgs)
        {
            var roles = DotArgumentRolesWithSpreads(dotCall, kind, callee, receiverLift, paramMap, memos, out var lifts, report: true);
            var rewrittenArgs = new List<Expr>(dotArgs.Count);
            for (var i = 0; i < dotArgs.Count; i++)
            {
                var processed = RewriteImplicitCalls(dotArgs[i], paramMap, context, roles[i], memos);
                if (lifts is not null)
                    RequirePredictedLift(dotArgs[i], processed, lifts[i]);
                rewrittenArgs.Add(SpreadIfMarked(dotArgs[i], processed, paramMap, memos));
            }

            newArgs = new OutputBundle(rewrittenArgs);
        }

        var rewritten = dotCall with
        {
            Target = RewriteImplicitCalls(
                dotCall.Target, paramMap, context, FormulaLiftingRoles.ReceiverRole(kind, callee), memos),
            Args = newArgs,
        };
        RequirePredictedLift(written.Target, rewritten.Target, receiverLift);
        // The receiver of an extension-call edge is an output-spreading position (R2). A WRITTEN marked call there was
        // lowered by parameter detection, where the names are ordered (D1); a marked reference this pass lifted makes the
        // edge the call `F(R(…)*, args)` here, exactly as the parser lowers a written `R*.F(args)`.
        return LowerLiftedMarkedReceiver(written, rewritten, paramMap, memos) ?? rewritten;
    }

    /// <summary>
    /// Reports a value-role reference to a clause family formula lifting cannot name
    /// (<see cref="DeriveFamilyLiftingSignature"/>), once per reference, at the reference (a
    /// reference inside imported content at the import site). The family stays explicitly callable.
    /// A conditional branch body's own region keeps the report re-issuable for further families
    /// sharing the body (M4).
    /// </summary>
    private static void ReportUnliftableClauseFamily(Expr reference, string displayName, string? aliasedFamily, UnnameableFamily unnameable, ResolverWalkMemos memos)
    {
        if (memos.Diagnostics is not { } diagnostics)
            return;
        memos.UnliftableFamilyDiagnosticVisits ??= new(ReferenceEqualityComparer.Instance);
        if (!memos.UnliftableFamilyDiagnosticVisits.Add(reference))
            return;

        var span = reference.Span ?? memos.Run.ImportSite;
        // The reason belongs to the callable identity; the name belongs to this occurrence.
        // A shared family may be exposed by several bindings in the same resolution run.
        var message = FormatUnliftableClauseFamily(displayName, aliasedFamily, unnameable);
        diagnostics.Add(new Diagnostic(message, DiagnosticSeverity.Error, span) { Code = DiagnosticCode.UnliftableClauseFamily });
        memos.BranchDiagnosticTemplates?.Add(new BranchDiagnosticTemplate(DiagnosticCode.UnliftableClauseFamily, _ => message, span));
    }

    private static DiagnosticMessage FormatUnliftableClauseFamily(string displayName, string? aliasedFamily, UnnameableFamily unnameable)
    {
        var family = ExprNameRenderer.BoundName(displayName);
        var callable = aliasedFamily is null
            ? $"clause family '{family}'"
            : $"'{family}', an alias of clause family '{ExprNameRenderer.BoundName(aliasedFamily)}',";
        return DiagnosticMessage.JoinLines(
            $"'{family}' is used as a value here, but {callable} has no formula-lifting signature: {FormatUnnameableReason(unnameable)}.",
            "Formula lifting forwards arguments by parameter name, and literal, structural and binderless clause patterns name nothing. "
                + $"Call '{family}' with explicit arguments, or bind that position with one plain parameter name in the clauses that bind it.");
    }

    /// <summary>Why a clause family names no argument position unambiguously (<see cref="UnnameableFamily"/>), in KatLang terms.</summary>
    private static string FormatUnnameableReason(UnnameableFamily unnameable)
    {
        var position = (unnameable.Position + 1).ToString(System.Globalization.CultureInfo.InvariantCulture);
        return unnameable.Reason switch
        {
            UnnameableFamilyReason.ConflictingNames
                => $"its clauses name argument position {position} differently ({FormatQuotedNameList(unnameable.Names)})",
            UnnameableFamilyReason.SharedWithAnotherPosition
                => $"argument positions {(unnameable.OtherPosition!.Value + 1).ToString(System.Globalization.CultureInfo.InvariantCulture)} and {position} "
                    + $"would both be named {FormatQuotedNameList(unnameable.Names)}",
            _ => $"no clause binds argument position {position} with a plain parameter",
        };
    }


    /// <summary>
    /// Region-memoized nested-algorithm processing: two distinct <see cref="Expr.AlgorithmExpr"/>
    /// wrappers over ONE shared algorithm resolve it once (the whole region shares one final
    /// signature map).
    /// </summary>
    private static Algorithm ProcessSharedNestedAlgorithm(
        Algorithm alg,
        SourceSpan? importSite,
        SignatureMap paramMap,
        ResolverWalkMemos memos)
    {
        memos.Algorithms ??= new(ReferenceEqualityComparer.Instance);
        if (!memos.Algorithms.TryGetValue(alg, out var processed))
        {
            using var site = memos.Run.EnterImportSite(importSite);
            processed = ProcessAlgorithm(
                alg, paramMap, memos.NestedForwarding, isRoot: false, memos.Observations, memos.Diagnostics, branchContext: null, memos.Run);
            memos.Algorithms[alg] = processed;
        }

        return processed;
    }

    /// <summary>
    /// Processes an argument bundle of an OPEN TARGET (never a formula row): each slot recurses into
    /// nested algorithms only. An open target is navigation, resolved statically with fresh maps —
    /// nothing in it is a formula, so nothing in it lifts (see <see cref="ProcessOpenExprCore"/>).
    /// </summary>
    private static OutputBundle ProcessArgumentBundle(
        OutputBundle args,
        SignatureMap paramMap,
        ResolverWalkMemos memos)
        => new(args.Select(argExpr => ProcessExprNested(argExpr, paramMap, memos)).ToList());

    /// <summary>
    /// Processes an expression inside an OPEN TARGET: recurse into nested algorithms only. Open
    /// targets are navigation, never formulas, so no reference in one lifts; every formula row goes
    /// through <see cref="RewriteImplicitCalls"/>, whose roles come from
    /// <see cref="FormulaLiftingRoles"/>.
    /// </summary>
    private static Expr ProcessExprNested(
        Expr expr,
        SignatureMap paramMap,
        ResolverWalkMemos memos)
    {
        FrontEndStack.Ensure();
        // DAG-safety: one rewrite per shared node reference per open-target region; the memo
        // returns the same rewritten node for every later reach.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return ProcessExprNestedCore(expr, paramMap, memos);

        memos.NestedRewrites ??= new(ReferenceEqualityComparer.Instance);
        if (memos.NestedRewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        memos.Observations?.RecordResolverRewriteExpansion();
        rewritten = ProcessExprNestedCore(expr, paramMap, memos);
        memos.NestedRewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr ProcessExprNestedCore(
        Expr expr,
        SignatureMap paramMap,
        ResolverWalkMemos memos)
    {
        return expr switch
        {
            Expr.AlgorithmExpr block => block with
            {
                Algorithm = ProcessSharedNestedAlgorithm(block.Algorithm, ImportSite.OfBlock(block), paramMap, memos),
            },
            Expr.Capture capture => capture with
            {
                Body = new OutputBundle(
                    capture.Body.Select(row => ProcessExprNested(row, paramMap, memos)).ToList()),
            },
            Expr.Call call => call with
            {
                Function = ProcessExprNested(call.Function, paramMap, memos),
                Args = ProcessArgumentBundle(call.Args, paramMap, memos),
            },
            Expr.Binary binary => binary with
            {
                Left = ProcessExprNested(binary.Left, paramMap, memos),
                Right = ProcessExprNested(binary.Right, paramMap, memos),
            },
            Expr.Comparison comparison => comparison with
            {
                First = ProcessExprNested(comparison.First, paramMap, memos),
                Links = AstHelpers.RewriteComparisonLinks(comparison.Links, operand => ProcessExprNested(operand, paramMap, memos)),
            },
            Expr.Unary unary => unary with { Operand = ProcessExprNested(unary.Operand, paramMap, memos) },
            Expr.Index index => index with
            {
                Target = ProcessExprNested(index.Target, paramMap, memos),
                Selectors = index.Selectors.Select(selector => ProcessExprNested(selector, paramMap, memos)).ToList(),
            },
            Expr.SequenceSpread spread => spread with { Operand = ProcessExprNested(spread.Operand, paramMap, memos) },
            Expr.SequenceConstruct construct => construct with
            {
                Left = ProcessExprNested(construct.Left, paramMap, memos),
                Right = ProcessExprNested(construct.Right, paramMap, memos),
            },
            Expr.ListLiteral list => list with { Items = list.Items.Select(item => ProcessExprNested(item, paramMap, memos)).ToList() },
            // `with` keeps the stored dot-edge facts (member span, lexical fallback).
            Expr.DotCall dotCall => dotCall with
            {
                Target = ProcessExprNested(dotCall.Target, paramMap, memos),
                Args = dotCall.Args is { } da ? ProcessArgumentBundle(da, paramMap, memos) : null,
            },
            Expr.Grace(var inner, _) => ProcessExprNested(inner, paramMap, memos),
            // Intentional leaves: an open target's names are navigation, never lifted.
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral
                or Expr.EmptySequence or Expr.NativeCall => expr,
        };
    }
}
