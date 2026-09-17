namespace KatLang;

/// <summary>
/// Walks a parsed AST and classifies identifiers as parameters vs. algorithm references.
/// For each algorithm scope, identifiers not matching any local property name
    /// or any property name visible from a parent scope or any opened algorithm are converted from
    /// <see cref="Expr.Resolve"/> to <see cref="Expr.Param"/>, and added to the algorithm's
    /// <see cref="Algorithm.Parameters"/> list.
///
/// Lean spec anchor: <c>shouldTreatAsImplicitParam</c> — uses the full ownership-first
/// lookup order (local → parent chain → opens) to determine if a name is an implicit parameter.
/// No casing restriction: any unknown identifier becomes an implicit parameter, regardless of case.
///
/// <para><b>Internal by design (v0.8.187):</b> this is ONE stage of the authoritative
/// front-end pipeline (<see cref="FrontEndPipeline"/>), not a host-composable API.
/// A host that ran only detection (and implicit-argument resolution) obtained an AST
/// whose <see cref="Property.Exposure"/> metadata was never finalized by
/// <see cref="PropertyExposureResolver"/>, and the evaluator trusts that stored flag —
/// so the partial composition observably diverged from engine-parsed source
/// (see <c>FrontEndElaborationBoundaryTests</c>). Hosts elaborate through
/// <see cref="Parser.Parse(string)"/> / <see cref="Parser.ParseAsync"/> or run through
/// <see cref="KatLangEngine"/>, which always execute the complete pass sequence.</para>
/// </summary>
internal static class ParameterDetector
{
    /// <summary>
    /// Processes a root algorithm, detecting and classifying parameters throughout the tree.
    /// Returns a new AST with correct <see cref="Expr.Param"/> nodes and populated
    /// <see cref="Algorithm.Parameters"/> lists, along with any diagnostics (e.g. free
    /// identifiers in conditional branch bodies that violate the full-input-specification rule).
    ///
    /// <para><b>Host-AST contract:</b> the root may be a preconstructed (host-built) AST.
    /// A non-recursive structural preflight runs BEFORE this pass's recursive rewriting
    /// walk: a tree whose structural depth exceeds
    /// <see cref="EvaluationLimits.MaxSupportedAstDepth"/> — the shared fat-frame
    /// elaboration ceiling, measured with a ≥2x stack margin for this pass on the
    /// documented 1 MiB thread baseline — or a cyclic node graph is rejected with a
    /// placeholder root and one structured diagnostic instead of overflowing the
    /// process stack. Roots reaching this pass through the front-end pipeline are
    /// already gated and pass unchanged.</para>
    ///
    /// <para><b>Shared subtrees (acyclic DAGs) are legal and DAG-safe:</b> a node referenced
    /// from several parents elaborates exactly like the equivalent duplicated tree, but every
    /// walk of this pass is reference-identity memoized per constant-context region, so
    /// traversal work is bounded by the DISTINCT reachable nodes, never by the number of
    /// root-to-node paths, and rewritten output preserves the input's sharing instead of
    /// expanding it into a tree. The memos are run-local (created per detection, garbage
    /// afterwards); grace-weight accumulation stays per semantic occurrence through memoized
    /// per-visit weight effects. The one deliberate per-NODE (rather than per-path) behavior is diagnostic
    /// multiplicity: an erroneous shared node is diagnosed once, not once per path.</para>
    /// </summary>
    public static (Algorithm Root, IReadOnlyList<Diagnostic> Diagnostics) Detect(Algorithm root)
    {
        if (AstStructuralPreflight.Check(
                root,
                EvaluationLimits.MaxSupportedAstDepth,
                AstConsumerProfile.FullyRecursive) is { } structuralRejection)
        {
            return (
                new Algorithm.User(null, [], [], [], []),
                [AstStructuralPreflight.ToParseDiagnostic(
                    structuralRejection, EvaluationLimits.MaxSupportedAstDepth)]);
        }

        var detected = DetectPrevalidated(root);

        // Unlike the full front-end pipeline, this standalone single-pass entry
        // point does not subsequently run PropertyExposureResolver: the returned
        // tree keeps the exposure values it was given.
        return detected;
    }

    /// <summary>
    /// The detection core behind <see cref="Detect"/>, without the structural
    /// preflight. Only for callers that ALREADY gated the tree at the shared
    /// elaboration ceiling (the front-end pipeline's common gate); it must never
    /// become reachable with an unvalidated host tree.
    ///
    /// <para>When <paramref name="hostOperations"/> is supplied, detection resolves
    /// names against that configuration's extended signature-only prelude, so a
    /// referenced host operation name resolves like <c>Math</c> instead of becoming an
    /// implicit parameter — the front-end half of the runtime prelude's name-level
    /// agreement.</para>
    /// </summary>
    internal static (Algorithm Root, IReadOnlyList<Diagnostic> Diagnostics) DetectPrevalidated(
        Algorithm root,
        HostOperations? hostOperations = null,
        FrontEndTraversalObservations? observations = null,
        GraceOrigins? graceOrigins = null)
    {
        var diagnostics = new List<Diagnostic>();
        var preludeAlgorithm = hostOperations?.SemanticPreludeAlgorithm
            ?? BuiltinRegistry.CreateSemanticPreludeAlgorithm();
        var preludeScope = ElaboratedScopeLookup.CreateScope(preludeAlgorithm, observations: observations);
        var processed = ProcessAlgorithm(
            root,
            preludeScope,
            capturedParameters: ParameterOwnership.Empty,
            diagnostics,
            observations,
            new DetectionRun { ProgramRoot = root, GraceOrigins = graceOrigins });
        return (processed, diagnostics);
    }

    /// <summary>
    /// Selects bindings once implicit forwarding has completed the owner signatures.
    /// Retains those signatures and their ordering/pattern/provenance metadata exactly;
    /// this is selection of established bindings, not another inference pass. Restoring
    /// synthesized calls lets the resolver rebuild forwarding under the selected bindings.
    /// Uses the ordinary region memos and owner construction, including deferred branches.
    /// The caller has already applied the pipeline's structural preflight.
    /// </summary>
    internal static (Algorithm Root, IReadOnlyList<Diagnostic> Diagnostics, bool Changed) CompleteOwnership(
        Algorithm root,
        ImplicitArgumentResolver.ResolutionOrigins origins,
        HostOperations? hostOperations = null,
        DeferredBranchContext? branchContext = null,
        FrontEndTraversalObservations? observations = null)
    {
        var diagnostics = new List<Diagnostic>();
        var run = new DetectionRun
        {
            ImplicitCallOrigins = origins.ImplicitCalls,
            GraceOrigins = origins.Grace,
            // A whole-program completion re-enters at the program root; a deferred branch
            // completion re-enters at that branch body, which is a nested (called) owner.
            ProgramRoot = branchContext is null ? root : null,
        };
        Algorithm processed;
        if (branchContext is not null)
        {
            processed = ProcessConditionalBranchBody(
                root, branchContext.ParentScope, new HashSet<string>(branchContext.BinderNames),
                branchContext.BranchName, branchContext.CapturedParameters, diagnostics, observations, run);
        }
        else
        {
            var prelude = hostOperations?.SemanticPreludeAlgorithm ?? BuiltinRegistry.CreateSemanticPreludeAlgorithm();
            processed = ProcessAlgorithm(root, ElaboratedScopeLookup.CreateScope(prelude, observations: observations),
                ParameterOwnership.Empty, diagnostics, observations, run);
        }
        return (processed, diagnostics, run.OwnershipChanged);
    }

    private static Algorithm ProcessAlgorithm(
        Algorithm alg,
        ElaboratedPropertyScope parentScope,
        ParameterOwnership capturedParameters,
        List<Diagnostic>? diagnostics,
        FrontEndTraversalObservations? observations,
        DetectionRun run)
    {
        if (alg is Algorithm.Builtin)
            return alg;

        if (alg is Algorithm.Conditional conditional)
            return ProcessConditionalProperty(
                conditional, "<anonymous>", parentScope, capturedParameters, diagnostics, observations, run);

        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is already a
        // fully-formed elaboration leaf: an explicit N-capture sequence-value pattern, no
        // opens, no properties, and an output that is exactly the single bound target name.
        // Its only required elaboration is rewriting that bound Resolve to a Param. Running
        // it through the general path builds an O(N) param-name set, param-order list,
        // parameter-ownership map, and MergeParameterPatterns per helper, so a wide
        // deconstruction is O(N^2) across its N sibling helpers. This leaf path is O(1) in
        // the capture count and produces the identical elaborated helper.
        if (alg is Algorithm.User { AssignmentDeconstructionTarget: not null } deconstructionHelper)
            return RewriteAssignmentDeconstructionHelperOutput(deconstructionHelper);

        var newOpens = ProcessOpenExprs(alg.Opens, parentScope, diagnostics, observations, run);
        var algWithProcessedOpens = alg with { Opens = newOpens };
        var scope = ElaboratedScopeLookup.CreateScope(algWithProcessedOpens, parentScope);

        var paramNames = new HashSet<string>(alg.Params);
        var paramOrder = new List<string>(alg.Params);
        var graceWeights = new Dictionary<string, int>();
        var hasExplicitParameterList = alg.ExplicitParameterPatterns.Count > 0;

        // The program root is never called: its signature (unresolved root names, and names
        // forwarding lifted into it) binds nothing, so this level is recorded as the
        // never-called owner of its bindings (see ParameterOwnership) — reference
        // classification still captures them, callable-binding decisions never do.
        var isProgramRoot = ReferenceEquals(alg, run.ProgramRoot);

        // The parameter bindings in force while this body's OWN rows are collected: the
        // inherited ones plus this algorithm's written parameters, all owned by THIS level.
        // Ordinary nested algorithms close over already-known outer params: those rewrite to
        // Expr.Param but must not become new local params.
        var boundParameters = capturedParameters.Extend(scope, alg.Params, isProgramRoot);

        // Static-open ownership (F2): the head name of every open target is classified by the
        // SAME owner walk as every other bare-name occurrence, against the bindings established
        // BEFORE this body's rows are read — written parameters, captured ancestor parameters
        // and binders, and on a completion run the completed signature. A parameter-owned head
        // is not an open target: it elaborates to Expr.Param and is reported, and the scope is
        // rebuilt over the corrected list so a farther same-named declaration can never provide
        // names through it — not to the closed-list check, not to inference, not to the editor.
        var ownedOpens = ClassifyOpenTargetHeads(
            newOpens, scope, boundParameters, diagnostics, run, reclassifyParameterHeads: true);
        if (!ReferenceEquals(ownedOpens, newOpens))
        {
            newOpens = ownedOpens;
            algWithProcessedOpens = alg with { Opens = newOpens };
            scope = ElaboratedScopeLookup.CreateScope(algWithProcessedOpens, parentScope);
            boundParameters = capturedParameters.Extend(scope, alg.Params, isProgramRoot);
        }

        // Every row this body WRITES: its output rows plus each hoisted assignment-
        // deconstruction right-hand side (see WrittenRows) — the right-hand side obeys this
        // body's closed-input rule and seeds this body's implicit parameters like any row.
        var writtenRows = AstHelpers.WrittenRows(alg);

        ImplicitParameterOccurrenceRecorder? provenanceRecorder = null;
        if (hasExplicitParameterList)
        {
            ReportUndeclaredExplicitParameterNames(writtenRows, scope, boundParameters, diagnostics, observations);
        }
        else if (run.ImplicitCallOrigins is null)
        {
            provenanceRecorder = new ImplicitParameterOccurrenceRecorder(scope, boundParameters);
            CollectFreeParams(
                writtenRows, scope, boundParameters, paramNames, paramOrder, graceWeights,
                FreeNameCollection.ImplicitSignature,
                provenanceRecorder,
                new FreeNameWalkMemo(observations));

            if (graceWeights.Count > 0)
                ApplyGraceReordering(paramOrder, graceWeights);
        }

        // The bindings in force inside this body: every inferred parameter is now known, and
        // all of them are owned by THIS level. One object serves both the rewrite of this
        // body's own rows and every nested descent, because a nested body sees exactly the
        // same bindings with exactly the same owners.
        // Collection only adds names; Grace changes their order, not this map's contents.
        // Reuse the established map when no names were inferred, including completion runs.
        var bodyParameters = paramOrder.Count == alg.Parameters.Count
            ? boundParameters
            : capturedParameters.Extend(scope, paramOrder, isProgramRoot);

        // Static-open ownership (F2), inferred bindings: a head this body's own rows just
        // promoted to an implicit parameter (`open Lib` beside `Lib.X` with no visible `Lib`)
        // is parameter-owned by exactly the same rule. Such a head resolved to nothing during
        // collection (an inferred name has no visible property, and open-head lookup is the
        // direct chain), so the scope's providers are unchanged: only the stored target and
        // the report change. Heads already classified above are not reported twice.
        if (!ReferenceEquals(bodyParameters, boundParameters))
        {
            var reclassifiedOpens = ClassifyOpenTargetHeads(
                newOpens, scope, bodyParameters, diagnostics, run, reclassifyParameterHeads: false);
            if (!ReferenceEquals(reclassifiedOpens, newOpens))
            {
                newOpens = reclassifiedOpens;
                algWithProcessedOpens = alg with { Opens = newOpens };
            }
        }

        // Process properties recursively (each property body is an algorithm scope).
        // Two properties may legally share ONE value algorithm by reference (host-built
        // trees, and module elaboration splicing one cached module at several load
        // sites); the per-loop reference memo processes such a shared value once —
        // context is constant across the loop (same scope, same captured names, same
        // diagnostics sink), so the results coincide, and the sharing is preserved in
        // the detected tree. Conditional values are exempt: their branch diagnostics
        // cite the property NAME, which differs per referencing property.
        Dictionary<Algorithm, Algorithm>? processedSharedValues =
            alg.Properties.Count > 1 ? new(ReferenceEqualityComparer.Instance) : null;
        var newProperties = new List<Property>(alg.Properties.Count);
        foreach (var prop in alg.Properties)
        {
            if (prop.Value is Algorithm.User { IsAssignmentDeconstructionSource: true })
            {
                // Hoisted deconstruction right-hand side: its rows were collected with this
                // body's rows above and are rewritten with them below (never as a nested
                // scope of its own, which would make its free names ITS parameters).
                newProperties.Add(prop);
            }
            else if (prop.Value is Algorithm.Conditional condAlg)
            {
                newProperties.Add(prop.WithValue(ProcessConditionalProperty(
                    condAlg, prop.Name, scope, bodyParameters, diagnostics, observations, run)));
            }
            else if (processedSharedValues is null)
            {
                newProperties.Add(prop.WithValue(ProcessAlgorithm(
                    prop.Value,
                    scope,
                    bodyParameters,
                    diagnostics,
                    observations,
                    run)));
            }
            else
            {
                if (!processedSharedValues.TryGetValue(prop.Value, out var processedBody))
                {
                    processedBody = ProcessAlgorithm(
                        prop.Value,
                        scope,
                        bodyParameters,
                        diagnostics,
                        observations,
                        run);
                    processedSharedValues[prop.Value] = processedBody;
                }

                newProperties.Add(prop.WithValue(processedBody));
            }
        }

        // Rewrite Resolve → Param for detected parameters. ONE reference memo spans all
        // output rows: they share this exact rewrite context, so a node shared between
        // rows (or reached twice within one row) rewrites once. The memo also carries
        // this level's Grace-effect policy (F10): under a closed explicit list nothing
        // is inferred, so no marker can reorder anything; otherwise a marker is
        // effective exactly on the names this level binds as its own parameters
        // (paramNames — the inferred signature, retained on a completion run).
        var rewriteMemo = new RewriteWalkMemo(
            run,
            observations,
            diagnostics,
            hasExplicitParameterList ? GraceEffectPolicy.ClosedExplicitList : GraceEffectPolicy.ImplicitSignature,
            paramNames,
            scope,
            provenanceRecorder?.DotMembers);
        var rewrittenOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
            rewrittenOutput.Add(RewriteParams(expr, scope, bodyParameters, rewriteMemo));
        AstHelpers.RewriteDeconstructionSourceRows(
            alg, newProperties, expr => RewriteParams(expr, scope, bodyParameters, rewriteMemo));

        var parameterized = run.ImplicitCallOrigins is null
            ? algWithProcessedOpens.WithParams(paramOrder, provenanceRecorder?.Provenance)
            : algWithProcessedOpens;
        return parameterized with
        {
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

    /// <summary>
    /// Elaborates one clause family (a property whose value is an
    /// <see cref="Algorithm.Conditional"/>) branch by branch under the
    /// full-input-specification rule of <see cref="ProcessConditionalBranchBody"/>. This is
    /// the ONE owner of that per-branch dispatch: <see cref="ProcessAlgorithm"/>'s property
    /// loop and <see cref="ProcessConditionalBranchBody"/>'s own property loop both route
    /// conditional values here, so a family declared inside a branch body is elaborated
    /// exactly like one declared in any other body (its binders become
    /// <see cref="Expr.Param"/>, its undeclared names are reported).
    /// General algorithm descent also routes host-built root/expression conditionals here.
    /// Previously it returned the family untouched, leaving its binders as bare resolves
    /// that later bound whatever outer name happened to match. Parsed families have no family-level opens;
    /// host-built families may have them and retain that parent scope for their branches.
    /// </summary>
    private static Algorithm.Conditional ProcessConditionalProperty(
        Algorithm.Conditional condAlg,
        string propertyName,
        ElaboratedPropertyScope scope,
        ParameterOwnership capturedParameters,
        List<Diagnostic>? diagnostics,
        FrontEndTraversalObservations? observations,
        DetectionRun run)
    {
        var newOpens = ProcessOpenExprs(condAlg.Opens, scope, diagnostics, observations, run);
        var processedConditional = condAlg with { Opens = newOpens };
        var branchParentScope = newOpens.Count == 0
            ? scope
            : ElaboratedScopeLookup.CreateScope(processedConditional, scope);

        // Static-open ownership (F2) for a host-built family's own open list (parsed families
        // own no opens): the family binds nothing itself, so its heads are classified against
        // the captured bindings from the family's level outward.
        if (newOpens.Count > 0)
        {
            var ownedOpens = ClassifyOpenTargetHeads(
                newOpens, branchParentScope, capturedParameters, diagnostics, run, reclassifyParameterHeads: true);
            if (!ReferenceEquals(ownedOpens, newOpens))
            {
                newOpens = ownedOpens;
                processedConditional = condAlg with { Opens = newOpens };
                branchParentScope = ElaboratedScopeLookup.CreateScope(processedConditional, scope);
            }
        }

        // Process each conditional branch body with the full-input-specification rule:
        // - Pattern binder names are rewritten to Expr.Param (resolved via valEnv at runtime)
        // - NO other free identifiers become implicit parameters
        // - The branch body's Params list is empty (bindings come from pattern matching)
        var processedBranches = new List<CondBranch>(condAlg.Branches.Count);
        foreach (var branch in condAlg.Branches)
        {
            var binderNames = new HashSet<string>(branch.Pattern.BoundNames());
            if (branch.Body.DeferredRegion is { } region)
            {
                // Even a body with no provisional reference to the lifted name must carry
                // the completed owner chain: its loaded source may reference it later.
                if (run.ImplicitCallOrigins is not null)
                    run.OwnershipChanged = true;
                // B2c: a deferred module region. The body's modules — and with them its full
                // elaboration and every diagnostic that could depend on their members — wait
                // for the branch to be selected. Eagerly the body is elaborated PROVISIONALLY:
                // the same walk with the diagnostics sink withheld, so binder and
                // ancestor-parameter references become Params (what the exposure summary
                // channel needs to classify the family soundly) while no undeclared-identifier
                // diagnostic can be raised against names a deferred module may provide. This
                // pass's output view of the placeholder carries the region forked with this
                // exact context for the demand-time run — one view per family occurrence, so
                // a placeholder reached under two contexts yields two independent regions.
                var provisionalBody = ProcessConditionalBranchBody(
                    branch.Body,
                    branchParentScope,
                    binderNames,
                    propertyName,
                    capturedParameters,
                    diagnostics: null,
                    observations,
                    run);
                processedBranches.Add(new CondBranch(branch.Pattern, provisionalBody with
                {
                    DeferredRegion = region.WithDetection(new DeferredBranchContext(
                        branchParentScope,
                        new HashSet<string>(binderNames),
                        propertyName,
                        capturedParameters)),
                }));
                continue;
            }

            var processedBody = ProcessConditionalBranchBody(
                branch.Body,
                branchParentScope,
                binderNames,
                propertyName,
                capturedParameters,
                diagnostics,
                observations,
                run);
            processedBranches.Add(new CondBranch(branch.Pattern, processedBody));
        }

        return processedConditional with { Branches = processedBranches };
    }

    /// <summary>
    /// The detection context of one deferred module region (B2c): exactly what
    /// <see cref="ProcessConditionalBranchBody"/> received when the eager walk reached the
    /// branch, so the demand-time run elaborates the loaded body under the same scope chain,
    /// binder names, family name, and captured ancestor parameter bindings — the last WITH
    /// their owning levels, so the deferred elaboration makes the same ownership decisions
    /// the eager provisional one did.
    /// </summary>
    internal sealed record DeferredBranchContext(
        ElaboratedPropertyScope ParentScope,
        IReadOnlySet<string> BinderNames,
        string BranchName,
        ParameterOwnership CapturedParameters);

    /// <summary>
    /// Demand-time detection of a deferred region's LOADED body: the ordinary branch-body
    /// walk, with diagnostics — the closed-branch rule and every nested closed-list check
    /// now run against the real module members.
    /// </summary>
    internal static Algorithm ElaborateDeferredBranch(
        Algorithm loadedBody,
        DeferredBranchContext context,
        List<Diagnostic> diagnostics,
        FrontEndTraversalObservations? observations = null,
        GraceOrigins? graceOrigins = null)
        => ProcessConditionalBranchBody(
            loadedBody,
            context.ParentScope,
            new HashSet<string>(context.BinderNames),
            context.BranchName,
            context.CapturedParameters,
            diagnostics,
            observations,
            new DetectionRun { GraceOrigins = graceOrigins });

    /// <summary>
    /// Records the diagnostic-only origin of each implicit parameter at the
    /// exact moment <see cref="CollectFreeParams(Expr, ElaboratedPropertyScope, HashSet{string}, HashSet{string}, List{string}, Dictionary{string, int}, FreeNameCollection, ImplicitParameterOccurrenceRecorder?)"/>
    /// first promotes the unresolved name: its first semantic source
    /// occurrence span (the same occurrence order the inference itself uses)
    /// and a conservative near-miss suggestion computed against the SAME
    /// elaborated scope the promotion decision consulted. Purely observational:
    /// it changes nothing about which names are promoted or their order.
    /// </summary>
    private sealed class ImplicitParameterOccurrenceRecorder
    {
        // Suggestions are best-effort diagnostics. Provenance remains complete,
        // but cap edit-distance/candidate enumeration for adversarial bodies
        // containing hundreds of distinct unresolved names.
        private const int MaxSuggestionAttempts = 64;

        private readonly ElaboratedPropertyScope _scope;
        private readonly ParameterOwnership _parameters;
        private Dictionary<string, ImplicitParameterProvenance>? _provenance;
        private int _suggestionAttempts;

        /// <summary>
        /// The dot edge whose member/fallback occurrence is being collected,
        /// when its receiver is a statically known algorithm that provably
        /// lacks the member (the edge's fallback is then the selected
        /// resolution); null for bare-name occurrences and for receivers with
        /// no statically known algorithm. Save/restore via
        /// <see cref="EnterDotMemberContext"/> so nested (host-built) fallback
        /// shapes cannot leak the context.
        /// </summary>
        private KnownReceiverMember? _dotMember;

        public ImplicitParameterOccurrenceRecorder(ElaboratedPropertyScope scope, ParameterOwnership parameters)
        {
            _scope = scope;
            _parameters = parameters;
        }

        public IReadOnlyDictionary<string, ImplicitParameterProvenance>? Provenance => _provenance;

        public Dictionary<Expr.DotCall, ImplicitParameterProvenance>? DotMembers { get; private set; }

        public KnownReceiverMember? EnterDotMemberContext(KnownReceiverMember? dotMember)
        {
            var previous = _dotMember;
            _dotMember = dotMember;
            return previous;
        }

        public void ExitDotMemberContext(KnownReceiverMember? previous) => _dotMember = previous;

        public void RecordFirstOccurrence(string name, Expr occurrence)
        {
            _provenance ??= new Dictionary<string, ImplicitParameterProvenance>(StringComparer.Ordinal);
            if (_provenance.ContainsKey(name))
                return;

            // The occurrence is the member of a dot edge on a known receiver
            // only when it IS that edge's member name (the elaborated fallback
            // identity carries the member's own spelling; a host-built fallback
            // naming something else is an ordinary bare occurrence). The receiver
            // is described exactly as the evaluator's dot-call context describes
            // it, rendered lazily here — once per promoted name, never per edge.
            DotMemberReceiver? receiver = null;
            DotMemberFallbackOrigin? origin = null;
            if (_dotMember is { } dotMember && string.Equals(dotMember.MemberName, name, StringComparison.Ordinal))
            {
                var description = ExprNameRenderer.Render(dotMember.ReceiverExpr, ExprNameMode.Open);
                receiver = new DotMemberReceiver(
                    dotMember.Algorithm,
                    IsDottedNamePath(dotMember.ReceiverExpr)
                        && !description.EndsWith(ExprNameRenderer.TruncationMarker, StringComparison.Ordinal)
                            ? description : null);
                origin = new DotMemberFallbackOrigin(description);
            }

            var suggestion = _suggestionAttempts++ < MaxSuggestionAttempts
                ? NameSuggestions.SuggestVisibleName(
                    name,
                    _scope,
                    _parameters,
                    receiver)
                : null;
            var provenance = new ImplicitParameterProvenance(name, occurrence.Span, suggestion, origin);
            _provenance[name] = provenance;
            if (origin is not null && _dotMember is { } member)
                (DotMembers ??= new(ReferenceEqualityComparer.Instance))[member.Edge] = provenance;
        }

        /// <summary>
        /// True when the receiver is spelled as a dotted name path the user can
        /// write a member after (<c>Math</c>, <c>Lib.Sub</c>), so a member
        /// suggestion can be offered as <c>Math.Ceil</c>; an inline block or
        /// any other receiver shape keeps the bare member suggestion.
        /// </summary>
        private static bool IsDottedNamePath(Expr receiver)
        {
            while (true)
            {
                switch (receiver)
                {
                    case Expr.Resolve:
                        return true;
                    case Expr.DotCall { Args: null } edge:
                        receiver = edge.Target;
                        continue;
                    default:
                        return false;
                }
            }
        }
    }

    /// <summary>
    /// A dot edge whose receiver is a statically known algorithm that lacks the
    /// member: the receiver's algorithm (its structural members are the member
    /// suggestion surface), the written receiver expression (rendered for the
    /// diagnostic only when a provenance note is actually recorded), and the
    /// member name the fallback occurrence must carry to count as this edge's.
    /// </summary>
    private readonly record struct KnownReceiverMember(Algorithm Algorithm, Expr ReceiverExpr, string MemberName, Expr.DotCall Edge);

    /// <summary>
    /// Diagnostic source survives only between the two detection passes, never on the
    /// executable AST. Resolve/Param leaves retain identity through implicit resolution;
    /// a lifted call is restored to that leaf through ResolutionOrigins.ImplicitCalls.
    /// </summary>
    internal sealed class GraceOrigins
    {
        public readonly Dictionary<Expr, Expr.Grace> Occurrences = new(ReferenceEqualityComparer.Instance);
    }

    /// <summary>
    /// Run-scoped state of ONE detection (a <see cref="DetectPrevalidated"/> or
    /// <see cref="ElaborateDeferredBranch"/> call), threaded through every algorithm-processing
    /// path so a node reached through several paths of a shared (acyclic) host tree is
    /// elaborated once per SEMANTIC REGION rather than once per path (M4). Run-local: created
    /// per detection, garbage afterwards — never static, never ambient.
    /// </summary>
    private sealed class DetectionRun
    {
        // Non-null only at the completion boundary. Read-only for this run; every memo is
        // still local to its ownership region, so shared nodes cannot reuse another owner's
        // selection. Existing Param nodes retain their classification.
        public IReadOnlyDictionary<Expr, Expr>? ImplicitCallOrigins;
        public GraceOrigins? GraceOrigins;
        public bool OwnershipChanged;
        /// <summary>
        /// The PROGRAM ROOT this run entered at (by reference), or null for a run that enters
        /// at a nested owner (a deferred branch body). The root is never called, so its
        /// signature is recorded as the never-called owner of its bindings (see
        /// <see cref="ParameterOwnership"/>): reference classification still captures them,
        /// callable-binding decisions — the static open-target head classification — never do.
        /// </summary>
        public Algorithm? ProgramRoot;
        /// <summary>
        /// Conditional branch bodies elaborated so far, by <see cref="BranchBodyRegionKey"/>.
        /// A branch body's rewrite depends on exactly the key's dimensions (parent scope,
        /// binder names, captured names, and whether diagnostics are reported); the family's
        /// NAME only words the body's closed-branch diagnostics, so a second family sharing
        /// the body reuses the rewrite and REPLAYS those diagnostics under its own name (see
        /// <see cref="BranchBodyRegion.UndeclaredNames"/>). Diagnostics of nodes nested inside
        /// the body do not mention the family and are reported once per region, exactly like
        /// every other shared node within one diagnostic context.
        /// </summary>
        public Dictionary<BranchBodyRegionKey, BranchBodyRegion>? BranchBodyRegions;
    }

    /// <summary>
    /// The minimal complete semantic context of one conditional branch-body elaboration:
    /// body and parent scope by REFERENCE, binder and captured names by CONTENT, plus the
    /// reporting mode (a provisional, diagnostic-free elaboration of a deferred module region
    /// never stands in for a reporting one).
    /// </summary>
    private sealed record BranchBodyRegionKey(
        Algorithm Body,
        ElaboratedPropertyScope ParentScope,
        string BinderNames,
        string CapturedNames,
        bool ReportsDiagnostics)
    {
        public bool Equals(BranchBodyRegionKey? other)
            => other is not null
                && ReferenceEquals(Body, other.Body)
                && ReferenceEquals(ParentScope, other.ParentScope)
                && BinderNames == other.BinderNames
                && CapturedNames == other.CapturedNames
                && ReportsDiagnostics == other.ReportsDiagnostics;

        public override int GetHashCode()
            => HashCode.Combine(
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Body),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(ParentScope),
                BinderNames,
                CapturedNames,
                ReportsDiagnostics);
    }

    /// <summary>
    /// A completed branch-body region: the rewritten body, and the closed-branch undeclared
    /// identifiers it reported (name and first-occurrence span) — the one diagnostic whose
    /// wording names the family, re-issued for every further family that shares the body.
    /// </summary>
    private sealed record BranchBodyRegion(Algorithm Rewritten, IReadOnlyList<(string Name, SourceSpan Span)>? UndeclaredNames);

    /// <summary>
    /// Reference-identity memo state for ONE <see cref="CollectFreeParams(IReadOnlyList{Expr}, ElaboratedPropertyScope, ParameterOwnership, HashSet{string}, List{string}, Dictionary{string, int}, FreeNameCollection, ImplicitParameterOccurrenceRecorder?, FreeNameWalkMemo)"/>
    /// walk (one algorithm's collection region — scope, bound names, target sets, mode and
    /// recorder are all constant for the walk's lifetime). A legal shared (acyclic) subtree is
    /// expanded once; a later reach of the same node reference re-applies only the node's
    /// memoized per-visit GRACE-WEIGHT EFFECT, because weight accumulation is the one
    /// per-occurrence-additive fact of this walk — every other contribution (name sets,
    /// first-occurrence order, provenance) is idempotent, so skipping the re-walk preserves
    /// exactly the semantics of the equivalent duplicated tree. An effect retains the ORDERED
    /// composition of the walk's per-occurrence int-saturating additions; a net sum is not
    /// sufficient because saturation makes mixed positive/negative additions non-associative.
    /// </summary>
    private sealed class FreeNameWalkMemo(FrontEndTraversalObservations? observations)
    {
        /// <summary>
        /// Completed nodes → their per-visit grace-weight effect (<c>null</c> = no weight
        /// contribution, the overwhelmingly common case). Completion-marked: a node appears
        /// only after its subtree finished, so an (illegal, preflight-rejected) cycle keeps
        /// today's non-terminating behavior instead of silently truncating the walk.
        /// </summary>
        public readonly Dictionary<Expr, Dictionary<string, GraceWeightEffect>?> CompletedVectors =
            new(ReferenceEqualityComparer.Instance);

        /// <summary>
        /// One slot per in-progress memoizable node on the recursion path (LIFO). Every weight
        /// application lands in the walk's <c>graceWeights</c> AND in every open slot, so when a
        /// node completes, its slot holds exactly its subtree's per-visit contribution.
        /// </summary>
        public readonly List<Dictionary<string, GraceWeightEffect>?> OpenSlots = [];

        public readonly FrontEndTraversalObservations? Observations = observations;
    }

    /// <summary>
    /// Compact composition of an ordered sequence of int-saturating grace additions.
    /// Every such sequence is a clamped translation; the arbitrary-precision offset avoids
    /// overflowing while a shared diamond composes one effect exponentially many times.
    /// </summary>
    private readonly record struct GraceWeightEffect(
        System.Numerics.BigInteger Offset,
        int Minimum,
        int Maximum)
    {
        public static GraceWeightEffect Addition(System.Numerics.BigInteger amount)
            => new(amount, int.MinValue, int.MaxValue);

        public int Apply(int value)
        {
            var shifted = value + Offset;
            if (shifted <= Minimum)
                return Minimum;
            if (shifted >= Maximum)
                return Maximum;
            return (int)shifted;
        }

        /// <summary>Returns the effect of applying this effect, then <paramref name="next"/>.</summary>
        public GraceWeightEffect Then(GraceWeightEffect next)
        {
            var minimum = next.Apply(Minimum);
            var maximum = next.Apply(Maximum);
            return minimum == maximum
                ? new GraceWeightEffect(0, minimum, maximum)
                : new GraceWeightEffect(Offset + next.Offset, minimum, maximum);
        }
    }

    /// <summary>
    /// Reference-identity memo state for ONE <see cref="RewriteParams"/> region:
    /// an algorithm's output rows or a conditional branch body. Both use the same
    /// owner-aware rewrite. The rewrite context (parameter ownership, scope) is constant
    /// for the region, so an original node reference maps to exactly one rewritten node: shared
    /// input rewrites once and stays shared in the output. <see cref="Algorithms"/> additionally
    /// memoizes the region's nested-algorithm processing so two distinct
    /// <see cref="Expr.AlgorithmExpr"/> wrappers over ONE shared algorithm elaborate it once.
    /// The region's diagnostics sink travels with the memo: a brace block in expression
    /// position (an output row, a call argument, a capture element) is a scope-owning body
    /// under the same rules as the enclosing one, so its closed explicit lists and clause
    /// families report undeclared identifiers exactly as they would at the root. The memo
    /// keeps that per NODE within the region — a shared block reports once.
    /// </summary>
    private sealed class RewriteWalkMemo(
        DetectionRun run,
        FrontEndTraversalObservations? observations,
        List<Diagnostic>? diagnostics,
        GraceEffectPolicy gracePolicy = GraceEffectPolicy.NotReported,
        IReadOnlySet<string>? ownParameterNames = null,
        ElaboratedPropertyScope? level = null,
        IReadOnlyDictionary<Expr.DotCall, ImplicitParameterProvenance>? dotMembers = null)
    {
        public readonly Dictionary<Expr, Expr> Rewrites = new(ReferenceEqualityComparer.Instance);
        public readonly HashSet<Expr> ReportedGrace = new(ReferenceEqualityComparer.Instance);

        public readonly IReadOnlyDictionary<Expr.DotCall, ImplicitParameterProvenance>? DotMembers = dotMembers;

        public Dictionary<Algorithm, Algorithm>? Algorithms;

        public readonly DetectionRun Run = run;

        public readonly FrontEndTraversalObservations? Observations = observations;

        public readonly List<Diagnostic>? Diagnostics = diagnostics;

        /// <summary>How this region reports Grace markers that cannot reorder anything.</summary>
        public readonly GraceEffectPolicy GracePolicy = gracePolicy;

        /// <summary>
        /// The names the region's algorithm binds as ITS OWN parameters — for an
        /// implicit-signature body exactly the names its collection inferred (on a
        /// completion run, the retained signature). Grace is effective on precisely
        /// these occurrences, because they are the ones the collection reordered.
        /// </summary>
        public readonly IReadOnlySet<string>? OwnParameterNames = ownParameterNames;

        /// <summary>The region's own scope level, so an owned parameter can be told apart from a captured one.</summary>
        public readonly ElaboratedPropertyScope? Level = level;
    }

    /// <summary>
    /// Whether a rewrite region reports a Grace marker that cannot reorder anything
    /// (F10): Grace is meaningful ONLY on a bare-name occurrence that implicit-signature
    /// collection promoted to a parameter of the enclosing algorithm — that is the one
    /// place its weight is consumed (<see cref="CollectFreeParams"/>, then
    /// <see cref="ApplyGraceReordering"/>). Every other occurrence is silently inert
    /// without this report: a name already bound before collection (an explicit or
    /// captured parameter, a visible property, a builtin, an opened name), a dot member
    /// that always resolves structurally, and every occurrence under a closed explicit
    /// parameter list, which infers nothing.
    /// </summary>
    private enum GraceEffectPolicy
    {
        /// <summary>
        /// A conditional branch body: the parser already rejects every written Grace in
        /// it, so the detector strips the marker for recovery without a second report.
        /// </summary>
        NotReported,

        /// <summary>A body inferring its implicit signature: effective exactly on the names it inferred.</summary>
        ImplicitSignature,

        /// <summary>A body under a closed explicit parameter list: nothing is inferred, so no Grace is effective.</summary>
        ClosedExplicitList,
    }

    /// <summary>
    /// Reference-identity memo state for ONE open-target region
    /// (<see cref="ProcessOpenExprs"/> over one algorithm's open list). The region runs two
    /// distinct walks over the same nodes — <see cref="ProcessOpenExpr(Expr, ElaboratedPropertyScope, List{Diagnostic}?, OpenWalkMemo)"/>
    /// (open-form rewriting) and <see cref="ProcessExpr"/>
    /// (transparent argument/capture rewriting) — with different results for the same node, so
    /// each keeps its own map; both contexts are constant for the region (the open-parent
    /// prelude scope, empty captured names, one diagnostics sink). The two algorithm maps stay
    /// separate for the same reason: the open walk elaborates nested algorithms WITH the
    /// diagnostics sink, the transparent walk without one.
    /// </summary>
    private sealed class OpenWalkMemo(DetectionRun run, FrontEndTraversalObservations? observations)
    {
        public readonly Dictionary<Expr, Expr> OpenRewrites = new(ReferenceEqualityComparer.Instance);

        public Dictionary<Expr, Expr>? TransparentRewrites;

        public Dictionary<Algorithm, Algorithm>? OpenAlgorithms;

        public Dictionary<Algorithm, Algorithm>? TransparentAlgorithms;

        public readonly DetectionRun Run = run;

        public readonly FrontEndTraversalObservations? Observations = observations;
    }

    /// <summary>
    /// Reference-identity memo for ONE <see cref="FindResolveSpan(IReadOnlyList{Expr}, string, ResolveSpanSearchMemo)"/>
    /// search (one free name): subtrees proven to contain no occurrence of THAT name are never
    /// re-searched through a second shared reference. A found span short-circuits the whole
    /// search, so only no-hit subtrees are recorded.
    /// </summary>
    private sealed class ResolveSpanSearchMemo(FrontEndTraversalObservations? observations)
    {
        public readonly HashSet<Expr> NoHit = new(ReferenceEqualityComparer.Instance);

        public readonly FrontEndTraversalObservations? Observations = observations;
    }

    /// <summary>
    /// Applies one grace-weight amount for <paramref name="name"/> to the walk's accumulated
    /// weights (int-saturating, exactly once per semantic occurrence) and composes it into every
    /// open memo slot, so each in-progress ancestor retains the subtree's ordered effect.
    /// </summary>
    private static void AddGraceWeight(
        Dictionary<string, int> graceWeights,
        FreeNameWalkMemo memo,
        string name,
        System.Numerics.BigInteger amount)
    {
        var addition = GraceWeightEffect.Addition(amount);
        graceWeights[name] = addition.Apply(graceWeights.GetValueOrDefault(name));
        for (var i = 0; i < memo.OpenSlots.Count; i++)
        {
            var slot = memo.OpenSlots[i] ??= new Dictionary<string, GraceWeightEffect>(StringComparer.Ordinal);
            slot[name] = slot.TryGetValue(name, out var previous)
                ? previous.Then(addition)
                : addition;
        }
    }

    /// <summary>Re-applies a completed node's per-visit weight effect for one more reach.</summary>
    private static void ApplyGraceVector(
        Dictionary<string, GraceWeightEffect>? vector,
        Dictionary<string, int> graceWeights,
        FreeNameWalkMemo memo)
    {
        if (vector is null)
            return;

        foreach (var (name, effect) in vector)
        {
            graceWeights[name] = effect.Apply(graceWeights.GetValueOrDefault(name));
            for (var i = 0; i < memo.OpenSlots.Count; i++)
            {
                var slot = memo.OpenSlots[i] ??= new Dictionary<string, GraceWeightEffect>(StringComparer.Ordinal);
                slot[name] = slot.TryGetValue(name, out var previous)
                    ? previous.Then(effect)
                    : effect;
            }
        }
    }

    /// <summary>
    /// Cheap elaboration of a synthetic assignment-deconstruction helper. The general
    /// <see cref="ProcessAlgorithm"/> path would rewrite the helper's output <see cref="Expr.Resolve"/>
    /// to an <see cref="Expr.Param"/> (the target is one of the helper's explicit captures), so this
    /// does exactly that and nothing else. The helper carries no free identifiers, no opens, and no
    /// nested algorithms, so no scope, param-name set, or pattern merge is needed — only the output
    /// rewrite. Every output slot of such a helper is a bare reference to a bound capture by
    /// construction (see <c>Parser.AddDeconstructionProperties</c>), so the rewrite is unconditional.
    /// </summary>
    private static Algorithm RewriteAssignmentDeconstructionHelperOutput(Algorithm.User helper)
    {
        var rewrittenOutput = new List<Expr>(helper.Output.Count);
        foreach (var expr in helper.Output)
            rewrittenOutput.Add(expr is Expr.Resolve resolve ? new Expr.Param(resolve.Name) { Span = expr.Span } : expr);
        return helper with { Output = rewrittenOutput };
    }

    private static IReadOnlyList<Expr> ProcessOpenExprs(
        IReadOnlyList<Expr> opens,
        ElaboratedPropertyScope parentScope,
        List<Diagnostic>? diagnostics,
        FrontEndTraversalObservations? observations,
        DetectionRun run)
    {
        if (opens.Count == 0)
            return opens;

        // The detection's prelude scope is the chain root, since every chain of
        // this detection starts at the prelude scope DetectPrevalidated created.
        // Anchoring open-target processing on it (rather than allocating a second
        // prelude) also keeps the host-operation extended prelude — when one is
        // configured — in force for open targets.
        var openParentScope = parentScope.Root;
        var memo = new OpenWalkMemo(run, observations);
        var processed = new List<Expr>(opens.Count);
        foreach (var open in opens)
            processed.Add(ProcessOpenExpr(open, openParentScope, diagnostics, memo));
        return processed;
    }

    /// <summary>
    /// Static-open ownership (SYN-03 / F2): classifies the HEAD NAME of every open target in
    /// one algorithm's open list by THE owner walk
    /// (<see cref="ElaboratedScopeLookup.SelectOwnedDeclaration"/>) from the opening
    /// algorithm's own level outward, exactly as <see cref="ShouldRewriteAsParam"/> classifies
    /// every other bare-name occurrence. The head is the innermost name of a core open form —
    /// the bare name of <c>open Lib</c>, or <c>Root</c> in <c>open Root.Sub.Leaf</c>; every
    /// other form (an inline block, a capture, a spread, a call-like dot edge) has no lexical
    /// head and passes through unchanged to its own validation.
    ///
    /// <para><c>open</c> is STATIC, and the nearest established binding owns the name. When the
    /// walk selects a parameter — written, inferred, lifted, collecting, grouped, a branch
    /// binder, or any of these captured from an enclosing owner — that parameter owns the head,
    /// and a parameter cannot be opened: the head elaborates to <see cref="Expr.Param"/>, which
    /// is not an open form in either engine (<c>IsCoreOpenForm</c> / Lean
    /// <c>Expr.openForm?</c>), so no evaluation of the elaborated or recovery tree can reach a
    /// farther same-named declaration, and the front end reports
    /// <see cref="DiagnosticCode.OpenTargetIsParameter"/> at the head's own span. Nothing is
    /// evaluated dynamically and nothing searches farther outward: whether a farther
    /// <c>Lib</c> exists changes neither the verdict nor the report. The walk receives the
    /// CALLABLE bindings (<see cref="ParameterOwnership.CallableBindings"/>), so the never-called
    /// program root's phantom signature decides nothing here (see F1: a root name nothing
    /// resolves is reported by evaluation as the unresolved root input it is, not as a
    /// parameter that cannot be opened).</para>
    ///
    /// <para><paramref name="reclassifyParameterHeads"/> re-verifies heads an EARLIER run
    /// already elaborated to <see cref="Expr.Param"/> (a completion run re-enters on the
    /// discovery run's tree, and the pipeline keeps only the latest run's diagnostics): a head
    /// the completed bindings still own as a parameter is reported again, and one they no
    /// longer own is restored to its written <see cref="Expr.Resolve"/>. The same region's
    /// second pass (after inference added names) passes <c>false</c>, so a head classified by
    /// the first pass is never reported twice within one run.</para>
    ///
    /// <para>Returns the same list instance when nothing changed. A shared open-target node
    /// reached twice within one list rewrites once and is reported once (reference-identity
    /// memo per region), and rewriting allocates only the rewritten spine: sharing outside the
    /// spine is preserved.</para>
    /// </summary>
    private static IReadOnlyList<Expr> ClassifyOpenTargetHeads(
        IReadOnlyList<Expr> opens,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        List<Diagnostic>? diagnostics,
        DetectionRun run,
        bool reclassifyParameterHeads)
    {
        if (opens.Count == 0)
            return opens;

        var callableBindings = parameters.CallableBindings;
        List<Expr>? classified = null;
        Dictionary<Expr, Expr>? rewrites = null;
        for (var i = 0; i < opens.Count; i++)
        {
            var open = opens[i];
            var head = OpenTargetHead(open);
            // A new Expr variant must be classified here as a lexical open head or an
            // intentional no-head form (a skipped name-like head would be a bypass).
            string? headName = head switch
            {
                Expr.Resolve resolve => resolve.Name,
                Expr.Param parameter => reclassifyParameterHeads ? parameter.Name : null,

                // Intentional no-head forms: an inline algorithm or capture owns no lexical
                // head (inline targets are separate owner regions), an argument-bearing dot
                // edge, a spread, a join, a list, a literal, an operator form, a call, a
                // native call, and a Grace wrapper are never lexical heads — the parser and
                // open-form validation reject the illegal ones with their own diagnostics.
                Expr.AlgorithmExpr or Expr.Capture or Expr.DotCall or Expr.SequenceSpread
                    or Expr.SequenceConstruct or Expr.ListLiteral or Expr.Call or Expr.Num
                    or Expr.StringLiteral or Expr.EmptySequence or Expr.NativeCall
                    or Expr.Unary or Expr.Binary or Expr.Index or Expr.Grace => null,
            };

            var rewritten = open;
            if (headName is not null)
            {
                // The membership test is the same pure fast path ShouldRewriteAsParam uses: the
                // walk can only select a parameter for a name some level binds.
                var parameterOwned = parameters.Contains(headName)
                    && ElaboratedScopeLookup.SelectOwnedDeclaration(scope, headName, callableBindings).Kind
                        == OwnedDeclarationKind.Parameter;

                if (parameterOwned)
                {
                    if (rewrites is null || !rewrites.TryGetValue(open, out var memoized))
                    {
                        if (head is Expr.Resolve)
                        {
                            rewritten = ReplaceOpenTargetHead(open, new Expr.Param(headName) { Span = head.Span });
                            run.OwnershipChanged = true;
                        }

                        diagnostics?.Add(CreateOpenTargetIsParameterDiagnostic(open, headName, head.Span ?? open.Span));
                        if (opens.Count > 1)
                            (rewrites ??= new(ReferenceEqualityComparer.Instance))[open] = rewritten;
                    }
                    else
                    {
                        rewritten = memoized;
                    }
                }
                else if (head is Expr.Param)
                {
                    // A parameter head of an earlier run that the completed bindings no longer
                    // own: restore the written lexical reference (same span) and let ordinary
                    // open resolution decide.
                    if (rewrites is null || !rewrites.TryGetValue(open, out var memoized))
                    {
                        rewritten = ReplaceOpenTargetHead(open, new Expr.Resolve(headName) { Span = head.Span });
                        run.OwnershipChanged = true;
                        if (opens.Count > 1)
                            (rewrites ??= new(ReferenceEqualityComparer.Instance))[open] = rewritten;
                    }
                    else
                    {
                        rewritten = memoized;
                    }
                }
            }

            if (classified is null && !ReferenceEquals(rewritten, open))
            {
                classified = new List<Expr>(opens.Count);
                for (var j = 0; j < i; j++)
                    classified.Add(opens[j]);
            }

            classified?.Add(rewritten);
        }

        return classified ?? opens;
    }

    /// <summary>
    /// The lexical head of a core open form: the target itself for a bare name, or the
    /// innermost receiver of an argumentless dot path (<c>Root</c> in <c>Root.Sub.Leaf</c>).
    /// Iterative over the dot spine; an argument-bearing edge is not an open form and stops
    /// the descent (the edge itself is then returned and classified as no head).
    /// </summary>
    private static Expr OpenTargetHead(Expr open)
    {
        while (open is Expr.DotCall { Args: null } dotCall)
            open = dotCall.Target;
        return open;
    }

    /// <summary>
    /// Rebuilds the argumentless dot spine of <paramref name="open"/> over a new head,
    /// keeping every stored dot-edge fact (member span, fallback identity, span) and
    /// allocating only the spine. Iterative, mirroring <see cref="OpenTargetHead"/>.
    /// </summary>
    private static Expr ReplaceOpenTargetHead(Expr open, Expr newHead)
    {
        List<Expr.DotCall>? spine = null;
        while (open is Expr.DotCall { Args: null } dotCall)
        {
            (spine ??= []).Add(dotCall);
            open = dotCall.Target;
        }

        var rebuilt = newHead;
        if (spine is not null)
        {
            for (var i = spine.Count - 1; i >= 0; i--)
                rebuilt = spine[i] with { Target = rebuilt };
        }

        return rebuilt;
    }

    private static Diagnostic CreateOpenTargetIsParameterDiagnostic(Expr open, string headName, SourceSpan? span)
        => new(
            FormatOpenTargetIsParameter(Evaluator.OpenExprName(open), headName),
            DiagnosticSeverity.Error,
            span ?? new SourceSpan(0, 0, 0, 0))
        {
            Code = DiagnosticCode.OpenTargetIsParameter,
        };

    /// <summary>
    /// Wording for <see cref="DiagnosticCode.OpenTargetIsParameter"/>: both facts the user
    /// needs — the name resolves to a parameter, and a parameter is not a static open target —
    /// plus the two repairs, in KatLang terms and without implementation vocabulary.
    /// </summary>
    private static string FormatOpenTargetIsParameter(string targetName, string headName)
        => string.Join(
            Environment.NewLine,
            targetName == headName
                ? $"Cannot open '{headName}': '{headName}' refers to a parameter, and a parameter cannot be used as an open target."
                : $"Cannot open '{targetName}': its first name '{headName}' refers to a parameter, and a parameter cannot be used as an open target.",
            $"'open' is resolved statically and never looks past the parameter for another declaration named '{headName}'. Open a declared algorithm instead, or access the parameter's members directly (for example {headName}.Member).");

    private static Expr ProcessOpenExpr(
        Expr expr,
        ElaboratedPropertyScope openParentScope,
        List<Diagnostic>? diagnostics,
        OpenWalkMemo memo)
    {
        // DAG-safety: a shared node reference rewrites once per open-target region;
        // the memo returns the same rewritten node for every later reach, preserving
        // the input's sharing. Childless leaves skip the memo (they cannot multiply
        // paths and re-process in O(1)).
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return ProcessOpenExprCore(expr, openParentScope, diagnostics, memo);

        if (memo.OpenRewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        memo.Observations?.RecordDetectorRewriteExpansion();
        rewritten = ProcessOpenExprCore(expr, openParentScope, diagnostics, memo);
        memo.OpenRewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr ProcessOpenExprCore(
        Expr expr,
        ElaboratedPropertyScope openParentScope,
        List<Diagnostic>? diagnostics,
        OpenWalkMemo memo)
    {
        return expr switch
        {
            // An open target has no parameter inference to reorder, so a
            // grace annotation is meaningless here. The parser rejects and
            // unwraps written ones; a host-built tree is unwrapped the same
            // way so no Grace can survive elaboration in any position.
            Expr.Grace(var gracedTarget, _) => ProcessOpenExpr(gracedTarget, openParentScope, diagnostics, memo),

            Expr.AlgorithmExpr(var algorithm) => new Expr.AlgorithmExpr(
                ProcessSharedOpenAlgorithm(algorithm, openParentScope, diagnostics, memo)) { Span = expr.Span },

            // A capture target owns no scope: its rows are processed in the
            // open-target parent scope (the pre-split transparent wrapper
            // added only an empty lookup level here).
            Expr.Capture(var captureBody) => new Expr.Capture(new OutputBundle(
                captureBody.Select(row => ProcessExpr(row, openParentScope, memo)).ToList()))
            { Span = expr.Span },

            // `with` keeps the stored dot-edge facts (member span). Open
            // targets are ordinary structural paths, so the fallback
            // identity is inert here, but the detector is the
            // normalization owner: every DotCall it emits carries an
            // EXPLICIT fallback (null is only a host-construction
            // shorthand for Resolve(Name)).
            Expr.DotCall dotCall => dotCall with
            {
                Target = ProcessOpenExpr(dotCall.Target, openParentScope, diagnostics, memo),
                Args = dotCall.Args is { } dotArgs
                    ? new OutputBundle(dotArgs.Select(argExpr => ProcessExpr(argExpr, openParentScope, memo)).ToList())
                    : null,
                LexicalFallback = ProcessOpenExpr(
                    dotCall.EffectiveLexicalFallback, openParentScope, diagnostics, memo),
            },

            Expr.SequenceSpread(var operand) => new Expr.SequenceSpread(
                ProcessOpenExpr(operand, openParentScope, diagnostics, memo))
            {
                Span = expr.Span,
                SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
            },

            Expr.SequenceConstruct(var left, var right) => new Expr.SequenceConstruct(
                ProcessOpenExpr(left, openParentScope, diagnostics, memo),
                ProcessOpenExpr(right, openParentScope, diagnostics, memo)) { Span = expr.Span },

            Expr.ListLiteral(var items) => new Expr.ListLiteral(
                items.Select(item => ProcessOpenExpr(item, openParentScope, diagnostics, memo)).ToList())
            { Span = expr.Span },

            Expr.Call(var function, var args) => new Expr.Call(
                ProcessOpenExpr(function, openParentScope, diagnostics, memo),
                new OutputBundle(args.Select(argExpr => ProcessExpr(argExpr, openParentScope, memo)).ToList())) { Span = expr.Span },

            // Intentional leaves: name/literal leaves carry no nested algorithm
            // to process (a bare Resolve IS the ordinary open-target form), and
            // operator forms are never valid open targets — the evaluator's
            // open-form validation rejects them (BadOpenForm) — so a host-built
            // one passes through unprocessed like a leaf.
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral or Expr.EmptySequence
                or Expr.NativeCall or Expr.Unary or Expr.Binary or Expr.Index => expr,
        };
    }

    /// <summary>
    /// Region-memoized inline-algorithm processing for the open-target walk: two
    /// distinct <see cref="Expr.AlgorithmExpr"/> wrappers over ONE shared algorithm
    /// elaborate it once per open-target region.
    /// </summary>
    private static Algorithm ProcessSharedOpenAlgorithm(
        Algorithm algorithm,
        ElaboratedPropertyScope openParentScope,
        List<Diagnostic>? diagnostics,
        OpenWalkMemo memo)
    {
        memo.OpenAlgorithms ??= new(ReferenceEqualityComparer.Instance);
        if (!memo.OpenAlgorithms.TryGetValue(algorithm, out var processedAlgorithm))
        {
            processedAlgorithm = ProcessAlgorithm(
                algorithm, openParentScope, ParameterOwnership.Empty, diagnostics, memo.Observations, memo.Run);
            memo.OpenAlgorithms[algorithm] = processedAlgorithm;
        }

        return processedAlgorithm;
    }

    /// <summary>
    /// Processes a conditional branch body under the full-input-specification rule:
    /// - Pattern binder names are rewritten to <see cref="Expr.Param"/> (resolved via valEnv at runtime).
    /// - No other free identifiers become implicit parameters.
    /// - The branch body's <see cref="Algorithm.Parameters"/> list is empty.
    /// - The body's own `open` list is elaborated (branch-owned opens, see
    ///   SEMANTIC-ALIGNMENT.md), and nested algorithms within the body — brace blocks,
    ///   property values, and nested clause families alike — are processed normally.
    ///
    /// This enforces the invariant that conditional branch inputs come ONLY from the
    /// branch pattern. Free identifiers in the body that are not pattern-bound must
    /// resolve through ordinary lexical / property / open / builtin lookup.
    /// Any free identifier that would be an implicit parameter (not visible in any scope)
    /// is reported as a compile-time error.
    /// </summary>
    private static Algorithm ProcessConditionalBranchBody(
        Algorithm body,
        ElaboratedPropertyScope parentScope,
        HashSet<string> binderNames,
        string branchName,
        ParameterOwnership capturedParameters,
        List<Diagnostic>? diagnostics,
        FrontEndTraversalObservations? observations,
        DetectionRun run)
    {
        // M4: one elaboration per (body, semantic region). A body shared by several families
        // — or a family reached from several parents of a shared host tree — is rewritten once
        // per distinct parent scope, binder set, captured set, and reporting mode; a later
        // reach reuses the rewritten body (sharing preserved in the output) and re-issues only
        // the closed-branch diagnostics, which are the one thing that names THIS family.
        //
        // The captured dimension stays the NAME SET even though ownership decisions also read
        // the owning LEVEL of each name: a scope level is allocated once per descent step and
        // every use of that instance carries the one ownership object built beside it, so the
        // parent scope — already in the key by reference identity — determines the owner map.
        // Two contexts that agree on the parent scope instance cannot disagree on owners.
        var regionKey = new BranchBodyRegionKey(
            body,
            parentScope,
            FrontEndRegionKeys.NameSet(binderNames),
            FrontEndRegionKeys.NameSet(capturedParameters.Names),
            ReportsDiagnostics: diagnostics is not null);
        var regions = run.BranchBodyRegions ??= new();
        if (regions.TryGetValue(regionKey, out var completedRegion))
        {
            ReplayUndeclaredNames(completedRegion, branchName, diagnostics);
            return completedRegion.Rewritten;
        }

        observations?.RecordDetectorBranchBodyRegionExpansion();

        // A branch body owns its `open` list exactly like every other algorithm body, so its
        // targets are elaborated here — an inline open block's members get their own
        // parameter detection — and the body scope is created over the PROCESSED opens,
        // exactly as ProcessAlgorithm does for ordinary bodies.
        var newOpens = ProcessOpenExprs(body.Opens, parentScope, diagnostics, observations, run);
        var bodyWithProcessedOpens = body with { Opens = newOpens };
        var bodyScope = ElaboratedScopeLookup.CreateScope(bodyWithProcessedOpens, parentScope);

        // The branch's pattern binders are owned by the branch BODY level, exactly like an
        // ordinary algorithm's parameters are owned by its own level. In invalid same-owner
        // collisions, recovery selects the binder for direct and nested references alike;
        // declaration validity is checked after signature completion.
        var bodyParameters = capturedParameters.Extend(bodyScope, binderNames);

        // Static-open ownership (F2): a branch body's own open heads are classified against
        // its binders and captured ancestor parameters exactly like an ordinary body's (see
        // ProcessAlgorithm); a branch body infers nothing, so this is its only pass.
        var ownedOpens = ClassifyOpenTargetHeads(
            newOpens, bodyScope, bodyParameters, diagnostics, run, reclassifyParameterHeads: true);
        if (!ReferenceEquals(ownedOpens, newOpens))
        {
            newOpens = ownedOpens;
            bodyWithProcessedOpens = body with { Opens = newOpens };
            bodyScope = ElaboratedScopeLookup.CreateScope(bodyWithProcessedOpens, parentScope);
            bodyParameters = capturedParameters.Extend(bodyScope, binderNames);
        }

        // Every row this branch body WRITES, hoisted deconstruction right-hand sides
        // included (see WrittenRows): they obey the same full-input-specification rule.
        var writtenRows = AstHelpers.WrittenRows(body);

        // Detect free identifiers that would be implicit parameters — these are
        // forbidden in conditional branch bodies (full-input-specification rule).
        List<(string Name, SourceSpan Span)>? undeclaredNames = null;
        if (diagnostics is not null)
        {
            var freeNames = new HashSet<string>();
            var freeOrder = new List<string>();
            var dummyWeights = new Dictionary<string, int>();
            CollectFreeParams(
                writtenRows,
                bodyScope,
                bodyParameters,
                freeNames,
                freeOrder,
                dummyWeights,
                FreeNameCollection.DeclaredNameCheck,
                recorder: null,
                new FreeNameWalkMemo(observations));
            foreach (var freeName in freeOrder)
            {
                // Find the span for the first occurrence of this free identifier
                var span = FindResolveSpan(writtenRows, freeName, new ResolveSpanSearchMemo(observations))
                    ?? new SourceSpan(0, 0, 0, 0);
                (undeclaredNames ??= []).Add((freeName, span));
                diagnostics.Add(CreateConditionalBranchUndeclaredIdentifierDiagnostic(freeName, branchName, span));
            }
        }

        // Process nested properties normally. As in ProcessAlgorithm's property loop,
        // non-conditional values share one constant context across this branch body
        // (body scope, captured names, diagnostics sink), so a value algorithm referenced
        // by several properties must be processed once and stay shared. Conditional values
        // remain occurrence-specific because their branch diagnostics cite prop.Name.
        Dictionary<Algorithm, Algorithm>? processedSharedValues =
            body.Properties.Count > 1 ? new(ReferenceEqualityComparer.Instance) : null;
        var newProperties = new List<Property>(body.Properties.Count);
        foreach (var prop in body.Properties)
        {
            Algorithm processedProp;
            if (prop.Value is Algorithm.User { IsAssignmentDeconstructionSource: true })
            {
                // Hoisted deconstruction right-hand side: collected with the body's rows
                // above and rewritten with them below (see WrittenRows).
                newProperties.Add(prop);
                continue;
            }

            if (prop.Value is Algorithm.Conditional nestedCondAlg)
            {
                processedProp = ProcessConditionalProperty(
                    nestedCondAlg, prop.Name, bodyScope, bodyParameters, diagnostics, observations, run);
            }
            else if (processedSharedValues is null)
            {
                processedProp = ProcessAlgorithm(
                    prop.Value,
                    bodyScope,
                    bodyParameters,
                    diagnostics,
                    observations,
                    run);
            }
            else if (!processedSharedValues.TryGetValue(prop.Value, out processedProp!))
            {
                processedProp = ProcessAlgorithm(
                    prop.Value,
                    bodyScope,
                    bodyParameters,
                    diagnostics,
                    observations,
                    run);
                processedSharedValues[prop.Value] = processedProp;
            }

            newProperties.Add(prop.WithValue(processedProp));
        }

        // The shared owner walk selects both branch binders and ancestor parameters.
        // Process nested blocks/calls normally for their own parameter detection.
        // ONE reference memo spans the branch body's rows (constant rewrite context).
        var rewriteMemo = new RewriteWalkMemo(run, observations, diagnostics);
        var rewrittenOutput = new List<Expr>(body.Output.Count);
        foreach (var expr in body.Output)
            rewrittenOutput.Add(RewriteParams(expr, bodyScope, bodyParameters, rewriteMemo));
        AstHelpers.RewriteDeconstructionSourceRows(
            body, newProperties, expr => RewriteParams(expr, bodyScope, bodyParameters, rewriteMemo));

        var rewritten = bodyWithProcessedOpens with
        {
            Parameters = [],  // No implicit params — bindings come from pattern matching
            Properties = newProperties,
            Output = rewrittenOutput,
        };
        // Admitted only after the whole body completed (the structural preflight guarantees
        // acyclic inputs, so the body can never be reached again while in flight).
        regions[regionKey] = new BranchBodyRegion(rewritten, undeclaredNames);
        return rewritten;
    }

    /// <summary>
    /// Re-issues a completed region's closed-branch diagnostics for a further family that
    /// shares the body: same identifiers, same spans, worded with THIS family's name — so
    /// diagnostic multiplicity per family is exactly what elaborating the body again would
    /// produce, without re-walking it, and independent of which family was reached first.
    /// </summary>
    private static void ReplayUndeclaredNames(BranchBodyRegion region, string branchName, List<Diagnostic>? diagnostics)
    {
        if (diagnostics is null || region.UndeclaredNames is null)
            return;

        foreach (var (name, span) in region.UndeclaredNames)
            diagnostics.Add(CreateConditionalBranchUndeclaredIdentifierDiagnostic(name, branchName, span));
    }

    private static Diagnostic CreateConditionalBranchUndeclaredIdentifierDiagnostic(string identifierName, string branchName, SourceSpan span)
        => new(
            FormatConditionalBranchUndeclaredIdentifier(identifierName, branchName),
            DiagnosticSeverity.Error,
            span)
        {
            Code = DiagnosticCode.UndeclaredIdentifier,
        };

    private static string FormatConditionalBranchUndeclaredIdentifier(string identifierName, string branchName)
        => string.Join(
            Environment.NewLine,
            $"Identifier '{identifierName}' is used in conditional branch '{branchName}', but it is not declared in the branch pattern.",
            "If you want to use a parameter, declare it in the pattern, for example: `A(y) = y`.");

    private static string FormatExplicitParameterUndeclaredIdentifier(string identifierName)
        => string.Join(
            Environment.NewLine,
            $"Identifier '{identifierName}' is used in an explicitly parameterized algorithm, but it is not declared in the parameter list.",
            "Explicit parameter lists are closed. Declare the parameter explicitly or define a visible property/opened name.");

    private static void ReportUndeclaredExplicitParameterNames(
        IReadOnlyList<Expr> output,
        ElaboratedPropertyScope scope,
        ParameterOwnership boundParameters,
        List<Diagnostic>? diagnostics,
        FrontEndTraversalObservations? observations = null)
    {
        if (diagnostics is null)
            return;

        var freeNames = new HashSet<string>();
        var freeOrder = new List<string>();
        var dummyWeights = new Dictionary<string, int>();
        CollectFreeParams(
            output, scope, boundParameters, freeNames, freeOrder, dummyWeights,
            FreeNameCollection.DeclaredNameCheck,
            recorder: null,
            new FreeNameWalkMemo(observations));

        foreach (var freeName in freeOrder)
        {
            var span = FindResolveSpan(output, freeName, new ResolveSpanSearchMemo(observations));
            diagnostics.Add(new Diagnostic(
                FormatExplicitParameterUndeclaredIdentifier(freeName),
                DiagnosticSeverity.Error,
                span ?? new SourceSpan(0, 0, 0, 0))
            {
                Code = DiagnosticCode.UndeclaredIdentifier,
            });
        }
    }

    /// <summary>
    /// The purpose a free-name collection serves — the two purposes act on
    /// DIFFERENT dependency strengths for a dot edge's lexical fallback:
    /// <list type="bullet">
    /// <item><see cref="ImplicitSignature"/> constructs an implicit
    /// parameter list, a MAY-selection question: whenever the fallback CAN be
    /// selected at runtime, its callable identity must be representable in
    /// the signature, so the fallback name participates (see
    /// <see cref="LexicalFallbackSelection"/>).</item>
    /// <item><see cref="DeclaredNameCheck"/> REJECTS programs (the closed
    /// explicit-parameter-list rule and the conditional-branch
    /// full-input-specification rule). A conditional fallback name is not a
    /// definite dependency — the program stays runtime-valid through the
    /// structural arm (`Get(obj) = obj.size` with a member-bearing runtime
    /// receiver never selects the fallback) — so charging it here would
    /// reject working programs. The checks therefore take no fallback
    /// contribution, exactly like dependency/exposure analysis charges only
    /// must-selected fallbacks.</item>
    /// </list>
    /// </summary>
    private enum FreeNameCollection
    {
        ImplicitSignature,
        DeclaredNameCheck,
    }

    /// <summary>
    /// Collects identifiers that are free (not defined as properties in any visible scope).
    /// Preserves order of first appearance.
    /// </summary>
    private static void CollectFreeParams(
        IReadOnlyList<Expr> exprs,
        ElaboratedPropertyScope scope,
        ParameterOwnership boundParameters,
        HashSet<string> paramNames,
        List<string> paramOrder,
        Dictionary<string, int> graceWeights,
        FreeNameCollection mode,
        ImplicitParameterOccurrenceRecorder? recorder,
        FreeNameWalkMemo memo)
    {
        foreach (var expr in exprs)
            CollectFreeParams(expr, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
    }

    private static void CollectFreeParams(
        Expr expr,
        ElaboratedPropertyScope scope,
        ParameterOwnership boundParameters,
        HashSet<string> paramNames,
        List<string> paramOrder,
        Dictionary<string, int> graceWeights,
        FreeNameCollection mode,
        ImplicitParameterOccurrenceRecorder? recorder,
        FreeNameWalkMemo memo)
    {
        // DAG-safety: a shared node reference is expanded once per collection walk. Every
        // contribution of a completed subtree except grace weight is idempotent (name sets,
        // first-occurrence order, provenance all dedup by name), so a later reach re-applies
        // only the memoized per-visit ordered weight effect — exactly the effect walking the
        // equivalent duplicated tree would have. Childless leaves skip the memo (O(1) each).
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
        {
            CollectFreeParamsCore(expr, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
            return;
        }

        if (memo.CompletedVectors.TryGetValue(expr, out var vector))
        {
            ApplyGraceVector(vector, graceWeights, memo);
            return;
        }

        memo.Observations?.RecordDetectorCollectExpansion();
        memo.OpenSlots.Add(null);
        var slotIndex = memo.OpenSlots.Count - 1;
        CollectFreeParamsCore(expr, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
        var completedVector = memo.OpenSlots[slotIndex];
        memo.OpenSlots.RemoveAt(slotIndex);
        memo.CompletedVectors[expr] = completedVector;
    }

    private static void CollectFreeParamsCore(
        Expr expr,
        ElaboratedPropertyScope scope,
        ParameterOwnership boundParameters,
        HashSet<string> paramNames,
        List<string> paramOrder,
        Dictionary<string, int> graceWeights,
        FreeNameCollection mode,
        ImplicitParameterOccurrenceRecorder? recorder,
        FreeNameWalkMemo memo)
    {
        switch (expr)
        {
            case Expr.Grace(var graceOperand, var graceWeight):
            {
                // Grace decorates exactly ONE bare name occurrence. Stacked
                // wrappers on the SAME occurrence accumulate their weights.
                // Repeated prefix/postfix markers use this same arithmetic in
                // every context, including before a dot (`a~~.t` is ordinary
                // postfix Grace with weight +2). Grace never distributes a
                // weight through a compound expression: source validation
                // rejects complex operands, and a host-built one is handled
                // defensively by collecting its names WITHOUT any reordering
                // weight.
                // A host-built AST can carry arbitrary int weights on stacked wrappers.
                // Sum the one-occurrence amount without overflowing before the ordered,
                // saturating GraceWeightEffect sees it; source `~` markers are only +/-1,
                // so this widens host robustness without changing surface-language behavior.
                var accumulatedWeight = new System.Numerics.BigInteger(graceWeight);
                var gracedCore = graceOperand;
                while (gracedCore is Expr.Grace(var deeperOperand, var deeperWeight))
                {
                    accumulatedWeight += deeperWeight;
                    gracedCore = deeperOperand;
                }

                if (gracedCore is Expr.Resolve(var gracedName))
                {
                    if (!IsBoundName(gracedName, scope, boundParameters) && gracedName.Length > 0)
                    {
                        if (paramNames.Add(gracedName))
                        {
                            paramOrder.Add(gracedName);
                            recorder?.RecordFirstOccurrence(gracedName, gracedCore);
                        }
                        // Accumulate weight (multiple references sum up). Routed through the
                        // memo so in-progress ancestors record it in their per-visit effects.
                        AddGraceWeight(graceWeights, memo, gracedName, accumulatedWeight);
                    }
                }
                else
                {
                    CollectFreeParams(gracedCore, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                }

                break;
            }

            case Expr.Resolve(var name):
                if (!IsBoundName(name, scope, boundParameters) && name.Length > 0)
                {
                    if (paramNames.Add(name))
                    {
                        paramOrder.Add(name);
                        recorder?.RecordFirstOccurrence(name, expr);
                    }
                }
                break;

            case Expr.Binary(_, var left, var right):
                CollectFreeParams(left, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                CollectFreeParams(right, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.Unary(_, var operand):
                CollectFreeParams(operand, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.Index(var target, var selector):
                CollectFreeParams(target, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                CollectFreeParams(selector, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.SequenceSpread(var operand):
                CollectFreeParams(operand, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectFreeParams(left, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                CollectFreeParams(right, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.ListLiteral(var items):
                // List-literal elements are transparent to the enclosing
                // parameter scope, like spread operands and sequence joins.
                foreach (var item in items)
                    CollectFreeParams(item, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.DotCall dotCall:
                // Occurrence order is the language's ordinary semantic source
                // order: receiver, member, then written arguments. The member
                // spelling contributes a free-name occurrence through the
                // stored lexical-fallback identity only when that fallback MAY
                // be selected at runtime. This participation question is
                // independent of runtime fallback invocation, which later calls
                // `t(receiver, args...)`; executable argument assembly does not
                // reorder the enclosing algorithm's signature. Thus `a.t(b)`
                // contributes `a, t, b`, while the direct call `t(a)` keeps its
                // own source order `t, a`.
                CollectFreeParams(dotCall.Target, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);

                // A statically impossible fallback — a guaranteed structural
                // member, a conditional-branch member (a local-only ERROR at
                // runtime, never a fallback), or the dot-only `string`
                // intrinsic — contributes no member occurrence. The
                // DeclaredNameCheck mode likewise takes no fallback
                // contribution because a conditional fallback is not a
                // definite dependency (see FreeNameCollection).
                if (mode == FreeNameCollection.ImplicitSignature)
                {
                    var receiverProvider = ResolveDotCallReceiverProvider(dotCall, scope, boundParameters);
                    if (dotCall.GetLexicalFallbackSelection(receiverProvider) != LexicalFallbackSelection.Never)
                    {
                        // While collecting the member/fallback occurrence, the
                        // recorder knows the receiver's statically known
                        // algorithm (when there is one — a KnownAlgorithm
                        // receiver reaching this branch provably LACKS the
                        // member, so the fallback is its selected resolution)
                        // so a provenance note recorded here can name the
                        // receiver and rank its structural members as
                        // suggestion candidates. Diagnostic-only: the
                        // collection itself is unchanged.
                        var previousReceiver = recorder?.EnterDotMemberContext(
                            receiverProvider.Kind == StaticStructuralMemberProviderKind.KnownAlgorithm
                                ? new KnownReceiverMember(
                                    receiverProvider.Algorithm!,
                                    dotCall.Target.UnwrapGraceOperand(),
                                    dotCall.Name,
                                    dotCall)
                                : null);
                        CollectFreeParams(dotCall.EffectiveLexicalFallback, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                        recorder?.ExitDotMemberContext(previousReceiver);
                    }
                }
                if (dotCall.Args is { } dotArgs)
                    CollectFreeParams(dotArgs, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.Capture(var captureBody):
                // Captures are transparent: free identifiers bubble up to the
                // enclosing param scope.
                CollectFreeParams(captureBody, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.AlgorithmExpr:
                // Scope-owning algorithm expressions own their names — don't collect.
                break;

            case Expr.Call(var func, var args):
                CollectFreeParams(func, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                // Argument bundles are transparent: free identifiers inside
                // argument slots belong to the enclosing algorithm. (A brace
                // block argument is an AlgorithmExpr slot and owns its names.)
                CollectFreeParams(args, scope, boundParameters, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            // Intentional leaves with no free-name occurrences: literals, the
            // empty sequence, already-elaborated parameter references, and
            // native-call bodies (whose argument names are parameter
            // references by construction).
            case Expr.Num:
            case Expr.Param:
            case Expr.StringLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                break;

            // Runtime exhaustiveness guard (statement-form collector, which the
            // closed Expr hierarchy cannot make compiler-exhaustive — see
            // AstWalker.VisitExpr): a new Expr variant must be classified above
            // rather than silently contributing no free names (which would
            // silently change the inferred implicit-parameter signature).
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ParameterDetector)}.{nameof(CollectFreeParams)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a collected case or an intentional leaf.");
        }
    }

    /// <summary>
    /// The receiver provider of one dot edge at implicit-signature collection
    /// time, resolving a lexical-reference receiver through the SAME
    /// elaborated scope the collection itself uses; the caller applies the
    /// shared MAY-selection law to it. The receiver's provider mirrors the
    /// receiver occurrence's own elaboration fate, and it must do so through the
    /// SAME owner walk that decides it: a name the walk selects a parameter for —
    /// or one nothing declares and no open provides, which is therefore about to
    /// be inferred as a parameter — is a runtime value; a name the walk selects a
    /// property for, or exactly one open provides, is that property's statically
    /// known algorithm; an ambiguous opened name stays an unresolved reference.
    /// Reusing <see cref="ElaboratedScopeLookup.SelectOwnedDeclaration"/> here is
    /// what keeps receiver classification from drifting away from
    /// <see cref="ShouldRewriteAsParam"/>. The Never/Conditional/Always mapping
    /// itself is the shared <see cref="AstHelpers.GetLexicalFallbackSelection"/>
    /// law, and a chained receiver (<c>Lib.Sub</c> in <c>Lib.Sub.Q</c>) is
    /// navigated structurally by the shared compositional classification
    /// (<see cref="AstHelpers.ResolveStaticStructuralMemberProvider"/>, the
    /// static twin of the evaluator's receiver resolution) — this method only
    /// supplies the detector's resolution power for the bare names it meets,
    /// exactly like the editor's provider resolution.
    /// </summary>
    private static StaticStructuralMemberProvider ResolveDotCallReceiverProvider(
        Expr.DotCall dotCall,
        ElaboratedPropertyScope scope,
        ParameterOwnership boundParameters)
        => dotCall.Target.UnwrapGraceOperand().ResolveStaticStructuralMemberProvider(
            name => ResolveReceiverNameProvider(name, scope, boundParameters));

    private static StaticStructuralMemberProvider ResolveReceiverNameProvider(
        string name,
        ElaboratedPropertyScope scope,
        ParameterOwnership boundParameters)
    {
        var owned = ElaboratedScopeLookup.SelectOwnedDeclaration(scope, name, boundParameters);
        if (owned.TryGetParameter(out _))
            return new(StaticStructuralMemberProviderKind.RuntimeParameter);

        if (owned.TryGetProperty(out _, out var hit))
            return new(StaticStructuralMemberProviderKind.KnownAlgorithm, hit.Property.Value);

        // Undecided by ownership: the ordinary open fallback, and — when
        // that provides nothing either — the name this collection is
        // about to promote to an implicit parameter.
        var openHits = ElaboratedScopeLookup.LookupOpenPropertyMatches(scope, name);
        return openHits.Count switch
        {
            0 => new(StaticStructuralMemberProviderKind.RuntimeParameter),
            1 => new(StaticStructuralMemberProviderKind.KnownAlgorithm, openHits[0].Property.Value),
            _ => new(StaticStructuralMemberProviderKind.LexicalReference),
        };
    }

    /// <summary>
    /// Reorders parameters based on accumulated grace weights.
    /// Positive weight moves rightward, negative weight moves leftward.
    /// Each swap consumes one unit of weight. Movement stops at list boundaries
    /// or when blocked by a neighbor with equal or more extreme weight.
    /// </summary>
    private static void ApplyGraceReordering(
        List<string> paramOrder,
        Dictionary<string, int> graceWeights)
    {
        var weights = paramOrder.Select(n =>
            graceWeights.TryGetValue(n, out var w) ? w : 0).ToArray();

        for (var i = 0; i < paramOrder.Count; i++)
        {
            var idx = i;
            while (true)
            {
                if (weights[idx] == 0) break;

                if (weights[idx] > 0) // postfix: move right
                {
                    if (idx < paramOrder.Count - 1 && weights[idx + 1] < weights[idx])
                    {
                        weights[idx]--;
                        (paramOrder[idx], paramOrder[idx + 1]) = (paramOrder[idx + 1], paramOrder[idx]);
                        (weights[idx], weights[idx + 1]) = (weights[idx + 1], weights[idx]);
                        idx++;
                        continue;
                    }
                    break;
                }

                if (weights[idx] < 0) // prefix: move left
                {
                    if (idx > 0 && weights[idx - 1] > weights[idx])
                    {
                        weights[idx]++;
                        (paramOrder[idx], paramOrder[idx - 1]) = (paramOrder[idx - 1], paramOrder[idx]);
                        (weights[idx], weights[idx - 1]) = (weights[idx - 1], weights[idx]);
                        idx--;
                        continue;
                    }
                    break;
                }
            }
        }
    }

    // ── F10: a Grace marker that cannot reorder anything ────────────────────

    /// <summary>
    /// Reports a written Grace marker that has no effect (see
    /// <see cref="GraceEffectPolicy"/>): its bare-name occurrence never contributed a
    /// weight to this level's implicit-signature collection, so the marker looks
    /// meaningful and silently does nothing. Consulted from the rewrite pass — once per
    /// occurrence per region through the rewrite memo, on every detection run — for a
    /// standalone occurrence (<paramref name="memberEdge"/> null) and for a dot member's
    /// prefix Grace, whose edge verdict decides whether the fallback occurrence could
    /// participate at all. The reason names what fixed the binding, derived from the
    /// SAME owner walk that classifies the occurrence
    /// (<see cref="ElaboratedScopeLookup.SelectOwnedDeclaration"/>), so the report and
    /// the editor's resolution cannot disagree. A host-built compound operand is not a
    /// name occurrence and is left to the collection's defensive handling.
    /// </summary>
    private static void ReportIneffectiveGrace(
        Expr graceNode,
        Expr gracedCore,
        (Expr.DotCall Edge, LexicalFallbackSelection Selection)? memberEdge,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        RewriteWalkMemo memo)
    {
        if (memo.Diagnostics is null
            || memo.GracePolicy == GraceEffectPolicy.NotReported
            || gracedCore is not Expr.Resolve(var name))
            return;

        string reason;
        if (memberEdge is { Selection: LexicalFallbackSelection.Never } edge)
        {
            reason = string.Equals(edge.Edge.Name, "string", StringComparison.Ordinal)
                ? "'.string' is the dot-only intrinsic, so this occurrence never joins the implicit parameters"
                : $"the member '{name}' always resolves structurally on its receiver, so this occurrence never joins the implicit parameters";
        }
        else if (memo.GracePolicy == GraceEffectPolicy.ImplicitSignature
            && memo.OwnParameterNames?.Contains(name) == true)
        {
            // Effective: the occurrence was inferred into this level's own signature and
            // reordered there. Nothing to report.
            return;
        }
        else
        {
            reason = DescribeFixedGraceBinding(name, scope, parameters, memo);
        }

        // A shared marker can be reached as a bare occurrence and through several
        // dot edges. Observe each edge's selection even after a rewrite memo hit,
        // but report the same source node at most once in this region.
        if (!memo.ReportedGrace.Add(graceNode))
            return;

        memo.Diagnostics.Add(new Diagnostic(
            FormatIneffectiveGrace(name, reason),
            DiagnosticSeverity.Error,
            graceNode.Span ?? gracedCore.Span ?? new SourceSpan(0, 0, 0, 0))
        {
            Code = DiagnosticCode.InvalidGraceMarker,
        });
    }

    /// <summary>
    /// Why an occurrence's binding was already fixed before this level's collection ran,
    /// in KatLang terms, from the owner walk and the open providers.
    /// </summary>
    private static string DescribeFixedGraceBinding(
        string name,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        RewriteWalkMemo memo)
    {
        var owned = ElaboratedScopeLookup.SelectOwnedDeclaration(scope, name, parameters);
        if (owned.TryGetParameter(out var parameterOwner))
        {
            return ReferenceEquals(parameterOwner, memo.Level)
                ? "it already resolves to an explicit parameter"
                : "it already resolves to a parameter of an enclosing algorithm";
        }

        if (owned.TryGetProperty(out var propertyOwner, out _))
        {
            // The prelude is the outermost property level of the owner walk.
            return propertyOwner.Parent is null
                ? $"it already resolves to the builtin '{name}'"
                : "it already resolves to a property";
        }

        if (ElaboratedScopeLookup.LookupOpenPropertyMatches(scope, name).Count > 0)
            return "it already resolves to an opened property";

        return "the enclosing explicit parameter list fixes the parameter order, so nothing is inferred";
    }

    internal static string FormatIneffectiveGrace(string name, string reason)
        => $"Grace has no effect on '{name}' because {reason}. Grace `~` only reorders the implicit parameters an algorithm infers from its free names; remove the marker.";

    /// <summary>
    /// THE parameter-classification decision: whether this bare-name occurrence
    /// elaborates to <see cref="Expr.Param"/> (a runtime parameter read) rather
    /// than staying an <see cref="Expr.Resolve"/> lexical property reference.
    ///
    /// <para>It is exactly the shared owner walk
    /// (<see cref="ElaboratedScopeLookup.SelectOwnedDeclaration"/>) reading
    /// <see cref="OwnedDeclarationKind.Parameter"/>: the first owning scope that
    /// declares the name decides; invalid same-owner ties select the parameter for
    /// recovery. A parameter of the algorithm being rewritten decides at once (it
    /// owns the walk's first level), a captured ancestor parameter beats a
    /// property owned by any FARTHER scope — the root, the prelude, or any level
    /// beyond the capturing one — and a nearer property still wins in invalid recovery source.
    /// Nothing here consults <c>open</c>: a name the walk leaves undecided is
    /// handed to the ordinary open/prelude fallback by staying a Resolve.</para>
    ///
    /// <para>The membership test is a pure fast path — the walk can only answer
    /// Parameter for a name some level binds — and keeps the common
    /// non-parameter occurrence at one dictionary probe.</para>
    /// </summary>
    private static bool ShouldRewriteAsParam(
        string name,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters)
        => parameters.Contains(name)
            && ElaboratedScopeLookup.SelectOwnedDeclaration(scope, name, parameters).Kind
                == OwnedDeclarationKind.Parameter;

    /// <summary>
    /// Rewrites owned parameter references in ordinary and conditional bodies using the
    /// same owner walk. Signature inference and closed-branch diagnostics precede this step.
    /// Also recursively processes nested algorithms.
    /// </summary>
    private static Expr RewriteParams(
        Expr expr,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        RewriteWalkMemo memo)
    {
        // Resolve leaves can rewrite to newly allocated Params and therefore must be memoized
        // to preserve leaf sharing. Other childless leaves return themselves unchanged.
        var hasTraversableChildren = AstTraversalDagSafety.HasTraversableExprChildren(expr);
        if (!hasTraversableChildren && expr is not Expr.Resolve)
            return RewriteParamsCore(expr, scope, parameters, memo);

        if (memo.Rewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        if (hasTraversableChildren)
            memo.Observations?.RecordDetectorRewriteExpansion();
        rewritten = RewriteParamsCore(expr, scope, parameters, memo);
        memo.Rewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr RewriteParamsCore(
        Expr expr,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        RewriteWalkMemo memo)
    {
        if (memo.Run.ImplicitCallOrigins?.TryGetValue(expr, out var original) == true)
            expr = original;
        if (memo.Run.ImplicitCallOrigins is not null
            && memo.Run.GraceOrigins?.Occurrences.TryGetValue(expr, out var sourceGrace) == true)
            ReportIneffectiveGrace(sourceGrace, sourceGrace.UnwrapGraceOperand(), null, scope, parameters, memo);
        return expr switch
        {
            Expr.Grace grace => RewriteGrace(grace, scope, parameters, memo),

            Expr.Resolve(var name) when ShouldRewriteAsParam(name, scope, parameters)
                => RewriteResolveAsParam(name, expr.Span, memo),

            Expr.Binary(var op, var left, var right) => new Expr.Binary(op,
                RewriteParams(left, scope, parameters, memo),
                RewriteParams(right, scope, parameters, memo)) { Span = expr.Span },

            Expr.Unary(var op, var operand) => new Expr.Unary(op,
                RewriteParams(operand, scope, parameters, memo)) { Span = expr.Span },

            Expr.Index(var target, var selector) => new Expr.Index(
                RewriteParams(target, scope, parameters, memo),
                RewriteParams(selector, scope, parameters, memo)) { Span = expr.Span },

            Expr.SequenceSpread(var operand) => new Expr.SequenceSpread(
                RewriteParams(operand, scope, parameters, memo))
            {
                Span = expr.Span,
                SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
            },

            Expr.SequenceConstruct(var left, var right) => new Expr.SequenceConstruct(
                RewriteParams(left, scope, parameters, memo),
                RewriteParams(right, scope, parameters, memo)) { Span = expr.Span },

            Expr.ListLiteral(var items) => new Expr.ListLiteral(
                RewriteParams(items, scope, parameters, memo)) { Span = expr.Span },

            Expr.DotCall dotCall => RewriteDotCall(dotCall, scope, parameters, memo),

            Expr.AlgorithmExpr(var alg) => new Expr.AlgorithmExpr(
                RewriteSharedAlgorithm(alg, scope, parameters, memo)) { Span = expr.Span },

            // Captures are transparent: rewrite rows in the enclosing param scope.
            Expr.Capture(var captureBody) => new Expr.Capture(
                RewriteParams(captureBody, scope, parameters, memo)) { Span = expr.Span },

            // Argument bundles own no scope: slots rewrite in the enclosing
            // param context. (A brace block argument is an AlgorithmExpr
            // slot and processes as an independent algorithm.)
            Expr.Call call => RewriteCall(call, scope, parameters, memo),

            // Intentional leaves: a Resolve that failed the guarded parameter
            // test above stays an ordinary lexical reference, and the
            // remaining leaves contain no parameter references to rewrite.
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral
                or Expr.EmptySequence or Expr.NativeCall => expr,
        };
    }

    private static Expr RewriteCall(
        Expr.Call call,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        RewriteWalkMemo memo)
    {
        // Keep the established argument-before-callee rewrite order: both sides can
        // report diagnostics and update the region's shared-node metadata.
        var rewrittenArgs = RewriteParams(call.Args, scope, parameters, memo);
        return new Expr.Call(
            RewriteParams(call.Function, scope, parameters, memo), rewrittenArgs) { Span = call.Span };
    }

    /// <summary>Rewrites every slot of a scope-less bundle (capture rows, list elements, argument slots) in the enclosing param context.</summary>
    private static OutputBundle RewriteParams(
        OutputBundle bundle,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        RewriteWalkMemo memo)
    {
        var rewrittenSlots = new List<Expr>(bundle.Count);
        foreach (var slot in bundle)
            rewrittenSlots.Add(RewriteParams(slot, scope, parameters, memo));
        return new OutputBundle(rewrittenSlots);
    }

    private static Expr RewriteResolveAsParam(string name, SourceSpan? span, RewriteWalkMemo memo)
    {
        memo.Run.OwnershipChanged = true;
        return new Expr.Param(name) { Span = span };
    }

    /// <summary>
    /// The Grace arm of <see cref="RewriteParamsCore"/>. Ordinary collection consumed the
    /// weight of an EFFECTIVE marker — one on a bare name this level inferred as its own
    /// parameter. A marker that could not reorder anything is reported here (F10,
    /// <see cref="ReportIneffectiveGrace"/>): this pass runs on every detection run, so
    /// the report survives ownership completion, which replays rewriting but never
    /// inference. The wrapper is stripped either way; stacked wrappers on the one
    /// occurrence are unwrapped together so the occurrence is examined — and reported —
    /// exactly once. (In a conditional body the parser already diagnosed Grace; that
    /// region's policy strips it for recovery without a second report.)
    /// </summary>
    private static Expr RewriteGrace(
        Expr.Grace grace,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        RewriteWalkMemo memo)
    {
        var gracedCore = grace.UnwrapGraceOperand();
        ReportIneffectiveGrace(grace, gracedCore, memberEdge: null, scope, parameters, memo);
        var rewrittenGrace = RewriteParams(gracedCore, scope, parameters, memo);
        if (memo.Run.ImplicitCallOrigins is null
            && memo.Run.GraceOrigins is { } origins
            && gracedCore is Expr.Resolve)
        {
            // Keep this written occurrence distinct from an ungraced reference
            // sharing its operand in a host DAG. Repeated reaches of the Grace
            // node still reuse this copy through the ordinary rewrite memo.
            rewrittenGrace = rewrittenGrace with { };
            origins.Occurrences.Add(rewrittenGrace, grace);
        }
        return rewrittenGrace;
    }

    /// <summary>
    /// The DotCall arm of <see cref="RewriteParamsCore"/>. Argument bundles own no scope:
    /// slots rewrite in the enclosing param context. The stored lexical-fallback identity
    /// rewrites by the SAME rule as a bare callee name (Resolve → Param when the member is
    /// a known local or captured parameter) — including a fallback name the collection
    /// itself just inferred because the fallback may be selected at runtime.
    /// </summary>
    private static Expr RewriteDotCall(
        Expr.DotCall dotCall,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        RewriteWalkMemo memo)
    {
        var rewrittenArgs = dotCall.Args is { } dotArgs
            ? RewriteParams(dotArgs, scope, parameters, memo)
            : null;

        // The scope-aware selection verdict this walk already derives for
        // implicit-signature collection (CollectFreeParams), stamped on the
        // edge so the scope-free exposure walk charges a parameter-naming
        // fallback exactly when the runtime may take it
        // (AstHelpers.LexicalFallbackMayBeSelected).
        var selection = dotCall.GetLexicalFallbackSelection(
            ResolveDotCallReceiverProvider(dotCall, scope, parameters));

        // Prefix member Grace (`recv.~t`) decorates the fallback occurrence. It
        // is effective only when that occurrence joined this level's inferred
        // signature — which a member that always resolves structurally (or the
        // dot-only `.string` intrinsic) never does — so it is examined here with
        // the edge's own verdict (F10) and stripped like every other marker. A
        // graced receiver (`a~.t`) is an ordinary bare-name occurrence and takes
        // the Grace arm through the Target rewrite below.
        var fallback = dotCall.EffectiveLexicalFallback;
        var memberGrace = fallback as Expr.Grace;
        if (memberGrace is null && memo.Run.GraceOrigins is { } graceOrigins)
            graceOrigins.Occurrences.TryGetValue(fallback, out memberGrace);
        if (memberGrace is not null)
        {
            var memberCore = memberGrace.UnwrapGraceOperand();
            ReportIneffectiveGrace(memberGrace, memberCore, (dotCall, selection), scope, parameters, memo);
        }

        // The promotion note this collection recorded for the edge's fallback
        // occurrence travels on the rewritten edge, so the post-exposure
        // finalizer can re-examine the edge against the completed tree. A
        // completion run records nothing and keeps the note the input edge
        // already carries.
        return dotCall with
        {
            Target = RewriteParams(dotCall.Target, scope, parameters, memo),
            Args = rewrittenArgs,
            LexicalFallback = RewriteParams(fallback, scope, parameters, memo),
            ElaboratedFallbackSelection = selection,
            InferredFallbackProvenance = memo.DotMembers is { } dotMembers && dotMembers.TryGetValue(dotCall, out var provenance)
                ? provenance
                : dotCall.InferredFallbackProvenance,
        };
    }

    /// <summary>
    /// Region-memoized nested-algorithm processing for the rewrite walk: two distinct
    /// <see cref="Expr.AlgorithmExpr"/> wrappers over ONE shared algorithm elaborate it once.
    /// </summary>
    private static Algorithm RewriteSharedAlgorithm(
        Algorithm alg,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        RewriteWalkMemo memo)
    {
        memo.Algorithms ??= new(ReferenceEqualityComparer.Instance);
        if (!memo.Algorithms.TryGetValue(alg, out var processedAlg))
        {
            processedAlg = ProcessAlgorithm(
                alg, scope, parameters, memo.Diagnostics, memo.Observations, memo.Run);
            memo.Algorithms[alg] = processedAlg;
        }

        return processedAlg;
    }

    /// <summary>
    /// Processes transparent expressions inside an open target (capture rows, list elements,
    /// argument slots). Open-target regions always start with empty parameter ownership;
    /// only their nested algorithms introduce parameters.
    /// </summary>
    private static Expr ProcessExpr(
        Expr expr,
        ElaboratedPropertyScope scope,
        OpenWalkMemo memo)
    {
        // DAG-safety: one rewrite per shared node reference per open-target region. The
        // transparent walk keeps its own map — the same node can also be reached by
        // ProcessOpenExpr, whose open-form rewriting legitimately differs.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return ProcessExprCore(expr, scope, memo);

        memo.TransparentRewrites ??= new(ReferenceEqualityComparer.Instance);
        if (memo.TransparentRewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        memo.Observations?.RecordDetectorRewriteExpansion();
        rewritten = ProcessExprCore(expr, scope, memo);
        memo.TransparentRewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr ProcessExprCore(
        Expr expr,
        ElaboratedPropertyScope scope,
        OpenWalkMemo memo)
    {
        return expr switch
        {
            Expr.Grace(var inner, _) => ProcessExpr(inner, scope, memo),
            Expr.AlgorithmExpr(var alg) => new Expr.AlgorithmExpr(
                ProcessSharedTransparentAlgorithm(alg, scope, memo)) { Span = expr.Span },
            Expr.Capture(var captureBody) => new Expr.Capture(new OutputBundle(
                captureBody.Select(row => ProcessExpr(row, scope, memo)).ToList()))
            { Span = expr.Span },
            Expr.Call(var func, var args) => new Expr.Call(
                ProcessExpr(func, scope, memo),
                new OutputBundle(args.Select(argExpr => ProcessExpr(argExpr, scope, memo)).ToList())) { Span = expr.Span },
            Expr.Binary(var op, var l, var r) => new Expr.Binary(op,
                ProcessExpr(l, scope, memo),
                ProcessExpr(r, scope, memo)) { Span = expr.Span },
            Expr.Unary(var op, var operand) => new Expr.Unary(op,
                ProcessExpr(operand, scope, memo)) { Span = expr.Span },
            Expr.Index(var t, var s) => new Expr.Index(
                ProcessExpr(t, scope, memo),
                ProcessExpr(s, scope, memo)) { Span = expr.Span },
            Expr.SequenceSpread(var operand) => new Expr.SequenceSpread(
                ProcessExpr(operand, scope, memo))
            {
                Span = expr.Span,
                SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
            },
            Expr.SequenceConstruct(var l, var r) => new Expr.SequenceConstruct(
                ProcessExpr(l, scope, memo),
                ProcessExpr(r, scope, memo)) { Span = expr.Span },
            Expr.ListLiteral(var items) => new Expr.ListLiteral(
                items.Select(item => ProcessExpr(item, scope, memo)).ToList())
            { Span = expr.Span },
            // The detector is the normalization owner: every DotCall it emits
            // carries an EXPLICIT fallback identity (null is only a
            // host-construction shorthand for Resolve(Name)).
            Expr.DotCall dotCall => dotCall with
            {
                Target = ProcessExpr(dotCall.Target, scope, memo),
                Args = dotCall.Args is { } da
                    ? new OutputBundle(da.Select(argExpr => ProcessExpr(argExpr, scope, memo)).ToList())
                    : null,
                LexicalFallback = ProcessExpr(
                    dotCall.EffectiveLexicalFallback, scope, memo),
            },
            // Intentional leaves: bare references and literals rewrite nothing
            // in a transparent context (parameter classification happened in
            // the owning algorithm's collection walk).
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral
                or Expr.EmptySequence or Expr.NativeCall => expr,
        };
    }

    /// <summary>
    /// Region-memoized nested-algorithm processing for the transparent open-region walk:
    /// two distinct <see cref="Expr.AlgorithmExpr"/> wrappers over ONE shared algorithm
    /// elaborate it once (constant region context — same scope, same captured-name content,
    /// no diagnostics sink on this path, exactly as before).
    /// </summary>
    private static Algorithm ProcessSharedTransparentAlgorithm(
        Algorithm alg,
        ElaboratedPropertyScope scope,
        OpenWalkMemo memo)
    {
        memo.TransparentAlgorithms ??= new(ReferenceEqualityComparer.Instance);
        if (!memo.TransparentAlgorithms.TryGetValue(alg, out var processed))
        {
            processed = ProcessAlgorithm(alg, scope, ParameterOwnership.Empty, diagnostics: null, memo.Observations, memo.Run);
            memo.TransparentAlgorithms[alg] = processed;
        }

        return processed;
    }

    /// <summary>
    /// Whether the name is already bound and therefore must NOT be promoted to a
    /// new implicit parameter: a parameter binding is in scope, or lexical lookup
    /// finds a property (direct or open-provided). This is the PROMOTION question
    /// and is deliberately independent of the ownership question — which of the
    /// two bindings a bound name selects is <see cref="ShouldRewriteAsParam"/>.
    /// </summary>
    private static bool IsBoundName(
        string name,
        ElaboratedPropertyScope scope,
        ParameterOwnership boundParameters)
        => boundParameters.Contains(name) || HasVisiblePropertyName(scope, name);

    private static bool HasVisiblePropertyName(ElaboratedPropertyScope scope, string name)
        => ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope, name).Count > 0;

    /// <summary>
    /// Finds the <see cref="SourceSpan"/> of the first <see cref="Expr.Resolve"/> with the given name
    /// in a list of expressions. Used for error reporting on free identifiers in conditional branches.
    /// </summary>
    private static SourceSpan? FindResolveSpan(IReadOnlyList<Expr> exprs, string name, ResolveSpanSearchMemo memo)
    {
        foreach (var expr in exprs)
        {
            var span = FindResolveSpan(expr, name, memo);
            if (span is not null) return span;
        }
        return null;
    }

    private static SourceSpan? FindResolveSpan(Expr expr, string name, ResolveSpanSearchMemo memo)
    {
        // DAG-safety: a shared subtree proven free of the searched name is skipped through
        // every later reference (a hit ends the whole search, so only no-hit subtrees are
        // recorded). Childless leaves are decided in place.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return FindResolveSpanCore(expr, name, memo);

        if (memo.NoHit.Contains(expr))
            return null;

        memo.Observations?.RecordDetectorSpanSearchExpansion();
        var span = FindResolveSpanCore(expr, name, memo);
        if (span is null)
            memo.NoHit.Add(expr);
        return span;
    }

    private static SourceSpan? FindResolveSpanCore(Expr expr, string name, ResolveSpanSearchMemo memo)
    {
        return expr switch
        {
            Expr.Resolve(var n) when n == name => expr.Span,
            Expr.Grace(var inner, _) => FindResolveSpan(inner, name, memo),
            Expr.Binary(_, var l, var r) => FindResolveSpan(l, name, memo) ?? FindResolveSpan(r, name, memo),
            Expr.Unary(_, var operand) => FindResolveSpan(operand, name, memo),
            Expr.Index(var t, var s) => FindResolveSpan(t, name, memo) ?? FindResolveSpan(s, name, memo),
            Expr.SequenceConstruct(var l, var r) => FindResolveSpan(l, name, memo) ?? FindResolveSpan(r, name, memo),
            Expr.SequenceSpread(var operand) => FindResolveSpan(operand, name, memo),
            Expr.ListLiteral(var items) => FindResolveSpan(items, name, memo),
            Expr.DotCall d => FindResolveSpan(d.Target, name, memo)
                ?? (d.Args is not null ? FindResolveSpan(d.Args, name, memo) : null),
            Expr.AlgorithmExpr(var alg) => FindResolveSpan(alg.Output, name, memo),
            Expr.Capture(var captureBody) => FindResolveSpan(captureBody, name, memo),
            Expr.Call(var f, var args) => FindResolveSpan(f, name, memo) ?? FindResolveSpan(args, name, memo),
            // Intentional misses: a Resolve spelling a different name (the
            // guarded arm above is the hit case) and leaves that contain no
            // written Resolve occurrence.
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral
                or Expr.EmptySequence or Expr.NativeCall => null,
        };
    }
}
