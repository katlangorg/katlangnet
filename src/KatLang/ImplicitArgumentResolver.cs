namespace KatLang;

/// <summary>
/// Rewrites bare references to algorithms with parameters into explicit <see cref="Expr.Call"/> nodes,
/// lifting their parameters into the enclosing algorithm's <see cref="Algorithm.Parameters"/> list.
/// Must run after <see cref="ParameterDetector"/>.
///
/// <para><b>Internal by design (v0.8.187):</b> this is ONE stage of the authoritative
/// front-end pipeline (<see cref="FrontEndPipeline"/>), not a host-composable API — its
/// output still lacks the <see cref="PropertyExposureResolver"/> finalization the
/// evaluator's stored-exposure checks rely on (see
/// <c>FrontEndElaborationBoundaryTests</c>). Hosts elaborate through
/// <see cref="Parser.Parse(string)"/> / <see cref="Parser.ParseAsync"/> or run through
/// <see cref="KatLangEngine"/>, which always execute the complete pass sequence.</para>
/// </summary>
internal static class ImplicitArgumentResolver
{
    /// <summary>
    /// Processes a root algorithm, resolving all implicit arguments throughout the tree.
    /// Returns a new AST where every bare reference to an algorithm with parameters
    /// has been rewritten into an explicit call with lifted parameters.
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
    public static Algorithm Resolve(Algorithm root)
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

        return ResolvePrevalidated(root);
    }

    /// <summary>
    /// The resolution core behind <see cref="Resolve"/>, without the structural
    /// preflight. Only for callers that ALREADY gated the tree at the shared
    /// elaboration ceiling (the front-end pipeline's common gate); it must never
    /// become reachable with an unvalidated host tree.
    /// </summary>
    internal static Algorithm ResolvePrevalidated(
        Algorithm root,
        FrontEndTraversalObservations? observations = null,
        List<Diagnostic>? diagnostics = null)
    {
        return ProcessAlgorithm(
            root,
            parentParamMap: new Dictionary<string, CallableSignature>(),
            isRoot: true,
            observations,
            diagnostics,
            branchContext: null,
            new ResolutionRun());
    }

    /// <summary>
    /// Run-scoped state of ONE resolution (a <see cref="ResolvePrevalidated"/> or
    /// <see cref="ElaborateDeferredBranch"/> call), threaded through every algorithm-processing
    /// path so an algorithm reached through several paths of a shared (acyclic) host tree —
    /// a property value shared by several properties, a block literal reached from several
    /// rows, a conditional branch body shared by several families — is rewritten once per
    /// SEMANTIC REGION rather than once per path (M4). Run-local: created per resolution,
    /// garbage afterwards — never static, never ambient.
    /// </summary>
    private sealed class ResolutionRun
    {
        /// <summary>
        /// Nested algorithms rewritten so far, by <see cref="AlgorithmRegionKey"/>. A family's
        /// NAME only words a branch body's blocked strict-value diagnostics, so a second
        /// family sharing the body reuses the rewrite and REPLAYS those diagnostics under its
        /// own name (see <see cref="AlgorithmRegion.DiagnosticTemplates"/>).
        /// </summary>
        public Dictionary<AlgorithmRegionKey, AlgorithmRegion>? AlgorithmRegions;

        /// <summary>
        /// The free reference names of every algorithm node computed so far (a pure function
        /// of the node — see <see cref="FreeReferenceNames"/>), by node reference.
        /// </summary>
        public Dictionary<Algorithm, IReadOnlySet<string>>? FreeReferenceNames;
    }

    /// <summary>
    /// The minimal complete semantic context of one nested-algorithm rewrite: the node by
    /// REFERENCE; the <see cref="SignatureSnapshot"/> of the signatures its FREE reference
    /// names see in the visible map (every signature the rewrite can read — the subtree's own
    /// bindings shadow the map, open targets use fresh maps, stored dot-edge fallbacks are
    /// never rewritten); for a conditional branch body the closed binder specification the
    /// pattern imposes, by CONTENT (<see cref="FrontEndRegionKeys.ClosedBranchSpecification"/>);
    /// and the reporting mode. Two reaches with equal keys observe identical inputs, whatever
    /// path led to them and whatever else the property loop rewrote in between.
    /// </summary>
    private sealed record AlgorithmRegionKey(
        Algorithm Node,
        SignatureSnapshot Snapshot,
        string? ClosedSpecification,
        bool ReportsDiagnostics)
    {
        public bool Equals(AlgorithmRegionKey? other)
            => other is not null
                && ReferenceEquals(Node, other.Node)
                && Snapshot.Equals(other.Snapshot)
                && ClosedSpecification == other.ClosedSpecification
                && ReportsDiagnostics == other.ReportsDiagnostics;

        public override int GetHashCode()
            => HashCode.Combine(
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Node),
                Snapshot.GetHashCode(),
                ClosedSpecification,
                ReportsDiagnostics);
    }

    /// <summary>
    /// The signature-map footprint of one algorithm: for each of its free reference names
    /// (sorted), the signature object the visible map holds for it — by REFERENCE, since the
    /// property loop replaces a rewritten sibling's signature object — or null when the map
    /// has no entry (a prelude name, an open-provided name, or an unresolved one).
    /// </summary>
    private sealed class SignatureSnapshot : IEquatable<SignatureSnapshot>
    {
        private readonly string[] _names;
        private readonly CallableSignature?[] _signatures;
        private readonly int _hash;

        private SignatureSnapshot(string[] names, CallableSignature?[] signatures)
        {
            _names = names;
            _signatures = signatures;
            var hash = new HashCode();
            for (var i = 0; i < names.Length; i++)
            {
                hash.Add(names[i], StringComparer.Ordinal);
                hash.Add(signatures[i] is { } signature ? System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(signature) : 0);
            }

            _hash = hash.ToHashCode();
        }

        public static SignatureSnapshot Capture(IReadOnlySet<string> freeNames, Dictionary<string, CallableSignature> visibleParamMap)
        {
            var names = freeNames.Order(StringComparer.Ordinal).ToArray();
            var signatures = new CallableSignature?[names.Length];
            for (var i = 0; i < names.Length; i++)
                signatures[i] = visibleParamMap.TryGetValue(names[i], out var signature) ? signature : null;
            return new SignatureSnapshot(names, signatures);
        }

        public bool Equals(SignatureSnapshot? other)
        {
            if (other is null || other._names.Length != _names.Length)
                return false;

            for (var i = 0; i < _names.Length; i++)
            {
                if (!string.Equals(_names[i], other._names[i], StringComparison.Ordinal)
                    || !ReferenceEquals(_signatures[i], other._signatures[i]))
                    return false;
            }

            return true;
        }

        public override bool Equals(object? obj) => obj is SignatureSnapshot other && Equals(other);

        public override int GetHashCode() => _hash;
    }

    /// <summary>
    /// A completed algorithm region: the rewritten algorithm and, for a conditional branch
    /// body, the blocked strict-value forwarding diagnostics its own output rewrite reported
    /// — the one diagnostic whose wording names the family — as re-issuable templates.
    /// </summary>
    private sealed record AlgorithmRegion(Algorithm Rewritten, IReadOnlyList<BlockedForwardingTemplate>? DiagnosticTemplates);

    /// <summary>One blocked strict-value forwarding report, minus the family name that words it.</summary>
    private readonly record struct BlockedForwardingTemplate(
        string ReferenceDisplayName,
        IReadOnlyList<string> MissingParameterNames,
        SourceSpan Span);

    /// <summary>
    /// The FREE reference names of an algorithm's subtree: every <see cref="Expr.Resolve"/>
    /// name in its output rows and property values (recursively) that the subtree does not
    /// bind itself (a body's property names bind for everything inside it; parameters and
    /// binders are already <see cref="Expr.Param"/>s). These are exactly the names whose
    /// visible-map signatures the rewrite of the subtree can read — bare and called
    /// references, the alias and canonical <c>Math</c> shadow checks, and the sibling-order
    /// channel's shadow predicate all probe the map by a written name — while open targets
    /// (rewritten with fresh maps) and stored dot-edge fallbacks (never rewritten) read
    /// nothing. A pure function of the node: memoized per run, and reference-visited per
    /// subtree so a shared expression contributes its names once.
    /// </summary>
    private static IReadOnlySet<string> FreeReferenceNames(Algorithm algorithm, ResolutionRun run)
    {
        var memo = run.FreeReferenceNames ??= new(ReferenceEqualityComparer.Instance);
        if (memo.TryGetValue(algorithm, out var cached))
            return cached;

        var names = new HashSet<string>(StringComparer.Ordinal);
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
                break;
            }

            case Algorithm.Conditional conditional:
                foreach (var branch in conditional.Branches)
                    names.UnionWith(FreeReferenceNames(branch.Body, run));
                break;

            case Algorithm.Builtin:
                break;

            default:
                throw new InvalidOperationException(
                    $"Unhandled Algorithm variant in {nameof(ImplicitArgumentResolver)}.{nameof(FreeReferenceNames)}: {algorithm.GetType().Name}.");
        }

        memo[algorithm] = names;
        return names;
    }

    private static void CollectReferenceNames(Expr expr, HashSet<string> names, HashSet<Expr> visited, ResolutionRun run)
    {
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

            case Expr.Unary(_, var operand):
                CollectReferenceNames(operand, names, visited, run);
                break;

            case Expr.Index(var target, var selector):
                CollectReferenceNames(target, names, visited, run);
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
                // receiver is a name); the stored lexical fallback is never rewritten.
                CollectReferenceNames(dotCall.Target, names, visited, run);
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
            case Expr.EmptySequence:
            case Expr.NativeCall:
                break;

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr variant must be
            // classified above rather than silently keeping its names out of the region key.
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
    /// (Math) argument bundles, which are ordinary value positions of the SAME caller.
    ///
    /// <para>Bundling the four values is deliberate: they are one semantic unit, and the
    /// defect this record replaces was exactly a call site that supplied two of them
    /// degenerately and silently defaulted the other two away
    /// (see <see cref="ProcessValueDemandingArgumentBundle"/>).</para>
    /// </summary>
    /// <param name="CallerParameterPatterns">
    /// The enclosing algorithm's parameter patterns — the forwarding SOURCE shape.
    /// </param>
    /// <param name="SourceBindingKinds">
    /// Caller capture name to binding kind, so re-spread decisions read the source binding
    /// (see <see cref="BuildSourceBindingKinds"/>).
    /// </param>
    /// <param name="RequireExistingParameters">
    /// True inside an algorithm whose explicit parameter list is CLOSED: nothing may be lifted
    /// that would need a capture the list does not already declare.
    /// </param>
    /// <param name="ExistingParameterNames">
    /// The closed list's declared capture names; consulted only when
    /// <paramref name="RequireExistingParameters"/> is true.
    /// </param>
    /// <param name="ConditionalBranchName">
    /// Non-null when the closed specification is a conditional BRANCH PATTERN rather than a
    /// written explicit parameter list: the family's property name, used only to word the
    /// blocked strict-value diagnostic in the branch's own terms.
    /// </param>
    /// <remarks>
    /// A reference type, allocated EXACTLY ONCE per rewrite region and forwarded by reference
    /// through the whole walk: that makes the region's memo-soundness guard one reference
    /// comparison (<see cref="ResolverWalkMemos.PinRewriteContext"/>) instead of a per-node
    /// field-by-field comparison, and keeps the recursion spine passing one reference rather
    /// than copying four values.
    /// </remarks>
    private sealed record ImplicitRewriteContext(
        IReadOnlyList<ParameterPattern> CallerParameterPatterns,
        IReadOnlyDictionary<string, ParameterKind> SourceBindingKinds,
        bool RequireExistingParameters,
        IReadOnlySet<string>? ExistingParameterNames,
        string? ConditionalBranchName = null);

    /// <summary>
    /// The conditional branch a body belongs to, threaded into
    /// <see cref="ProcessAlgorithm"/> so the body resolves under the CLOSED branch-pattern
    /// rule: its pattern binders are its only inputs, exactly like a written explicit
    /// parameter list, and its <see cref="Algorithm.Parameters"/> stay empty.
    /// </summary>
    private sealed record ConditionalBranchContext(string BranchName, Pattern Pattern);

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
        List<Diagnostic>? diagnostics)
    {
        private ImplicitRewriteContext? _pinnedRewriteContext;

        /// <summary>The resolution this region belongs to (its algorithm region memo).</summary>
        public readonly ResolutionRun Run = run;

        /// <summary>
        /// Non-null only for a conditional branch body's own output-rewrite region: the
        /// templates of the blocked strict-value reports it issues, kept on the region so a
        /// further family sharing the body re-issues them under its own name (M4).
        /// </summary>
        public List<BlockedForwardingTemplate>? BranchDiagnosticTemplates;

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
        /// Nodes whose strict-value diagnostic walk has completed in this region. Kept
        /// separate from rewrite maps so a neutral-first memo hit can replay diagnostic
        /// observation once without changing or duplicating the rewritten node.
        /// </summary>
        public HashSet<Expr>? StrictValueDiagnosticVisits;

        public readonly FrontEndTraversalObservations? Observations = observations;

        /// <summary>
        /// The pass-wide diagnostic sink, threaded beside <see cref="Observations"/> so
        /// every region of one resolution appends to the SAME list. Null for the
        /// standalone entry points that only rewrite. A blocked lift returns the same
        /// reference either way, so rewrite maps never depend on this field; the separate
        /// strict-visit set above tracks the reporting side effect.
        /// </summary>
        public readonly List<Diagnostic>? Diagnostics = diagnostics;

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

        public Dictionary<Expr, Expr> RewriteMapFor(bool inCallPosition)
            => inCallPosition
                ? CalleeRewrites ??= new(ReferenceEqualityComparer.Instance)
                : ValueRewrites ??= new(ReferenceEqualityComparer.Instance);

        public bool TryBeginStrictValueDiagnosticVisit(Expr expr)
        {
            if (Diagnostics is null)
                return false;

            StrictValueDiagnosticVisits ??= new(ReferenceEqualityComparer.Instance);
            return StrictValueDiagnosticVisits.Add(expr);
        }
    }

    /// <summary>
    /// Reference-identity memo for ONE implicit-dependency collection region (one algorithm's
    /// output rows; the signature map and the shared seen/deps accumulators are constant).
    /// Every contribution is seen-set deduplicated, so a revisit of a completed node — split
    /// by call position, which changes what a node contributes — adds nothing and is skipped.
    /// </summary>
    private sealed class DepsWalkMemo(FrontEndTraversalObservations? observations)
    {
        public readonly HashSet<Expr> ValueVisited = new(ReferenceEqualityComparer.Instance);

        public HashSet<Expr>? CalleeVisited;

        public readonly FrontEndTraversalObservations? Observations = observations;
    }

    /// <summary>
    /// Builds a map from property name to its parameter-pattern signature for one level of properties.
    /// </summary>
    private static Dictionary<string, CallableSignature> BuildPropertyParamMap(
        IReadOnlyList<Property> properties)
    {
        var map = new Dictionary<string, CallableSignature>();
        foreach (var prop in properties)
            map[prop.Name] = CallableSignature.FromAlgorithm(prop.Name, prop.Value);
        return map;
    }

    /// <summary>
    /// Processes an algorithm: topologically sorts its properties, recursively processes each,
    /// then collects implicit deps and rewrites the algorithm's own output. Every NESTED
    /// algorithm — a property value, a block literal, an open target, a conditional branch
    /// body — goes through the run's region memo (M4): one rewrite per
    /// <see cref="AlgorithmRegionKey"/>, sharing preserved in the output, and a branch body's
    /// family-worded diagnostics replayed for every further family that shares it.
    /// </summary>
    private static Algorithm ProcessAlgorithm(
        Algorithm alg,
        Dictionary<string, CallableSignature> parentParamMap,
        bool isRoot,
        FrontEndTraversalObservations? observations,
        List<Diagnostic>? diagnostics,
        ConditionalBranchContext? branchContext,
        ResolutionRun run)
    {
        if (alg is Algorithm.Builtin)
            return alg;

        if (alg is Algorithm.Conditional conditional)
            return ProcessConditionalProperty(conditional, "<anonymous>", parentParamMap, observations, diagnostics, run);

        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is a fully-elaborated
        // leaf: its output is a single bound Param (rewritten by ParameterDetector), it has no
        // properties or opens, and its explicit N-capture pattern lifts nothing. The general path
        // would still build an O(N) existing-parameter set and source-binding-kind map per helper —
        // O(N^2) across a wide deconstruction's N helpers — only to rewrite an output that has no
        // implicit calls. Returning it unchanged is O(1) and identical.
        if (alg is Algorithm.User { IsAssignmentDeconstructionHelper: true })
            return alg;

        // The root is processed exactly once and keeps its bare-root rule; nothing shares it.
        if (isRoot)
            return ProcessUserAlgorithm(alg, parentParamMap, isRoot: true, observations, diagnostics, branchContext: null, run, diagnosticTemplates: null);

        var regionKey = new AlgorithmRegionKey(
            alg,
            SignatureSnapshot.Capture(FreeReferenceNames(alg, run), parentParamMap),
            branchContext is null ? null : FrontEndRegionKeys.ClosedBranchSpecification(branchContext.Pattern),
            ReportsDiagnostics: diagnostics is not null);
        var regions = run.AlgorithmRegions ??= new();
        if (regions.TryGetValue(regionKey, out var completedRegion))
        {
            if (branchContext is not null)
                ReplayBranchDiagnostics(completedRegion, branchContext.BranchName, diagnostics);
            return completedRegion.Rewritten;
        }

        if (branchContext is null)
            observations?.RecordResolverAlgorithmRegionExpansion();
        else
            observations?.RecordResolverBranchBodyRegionExpansion();

        var diagnosticTemplates = branchContext is not null && diagnostics is not null
            ? new List<BlockedForwardingTemplate>()
            : null;
        var rewritten = ProcessUserAlgorithm(alg, parentParamMap, isRoot: false, observations, diagnostics, branchContext, run, diagnosticTemplates);
        // Admitted only after the whole body completed (acyclic by the structural preflight).
        regions[regionKey] = new AlgorithmRegion(rewritten, diagnosticTemplates);
        return rewritten;
    }

    private static Algorithm ProcessUserAlgorithm(
        Algorithm alg,
        Dictionary<string, CallableSignature> parentParamMap,
        bool isRoot,
        FrontEndTraversalObservations? observations,
        List<Diagnostic>? diagnostics,
        ConditionalBranchContext? branchContext,
        ResolutionRun run,
        List<BlockedForwardingTemplate>? diagnosticTemplates)
    {
        var newOpens = ProcessOpenExprs(alg.Opens, observations, run);

        // Build local param map
        var localParamMap = BuildPropertyParamMap(alg.Properties);
        // The sibling-order channel consults the same Math-alias shadow knowledge
        // this pass's own visibleParamMap carries (ancestor property names here,
        // sibling names inside the builder), so dependency ordering and the
        // rewriting below cannot disagree about which calls are alias calls.
        // This pass consumes ONLY the dependency/order channel: the builder's
        // recursive property-summary channel belongs to the exposure resolver
        // and is deliberately never computed here (M17).
        var dependencyGraph = alg is Algorithm.User userAlgorithm
            ? PropertyDependencyGraphBuilder.BuildDependencyOrder(
                userAlgorithm,
                preludeNameShadowedByCaller: parentParamMap.ContainsKey,
                observations)
            : PropertyDependencyGraph.Empty;

        // Visible map = parent + local (local overrides). When there are no local properties —
        // the common leaf case, e.g. every simple property value `A = expr` — nothing overrides
        // the parent map and the per-property loop below (the only writer of visibleParamMap) is
        // empty, so the parent map is shared instead of copied. Cloning this O(P) parent map once
        // per leaf property is what made this pass O(P^2) in the property count.
        Dictionary<string, CallableSignature> visibleParamMap;
        if (localParamMap.Count == 0)
        {
            visibleParamMap = parentParamMap;
        }
        else
        {
            visibleParamMap = new Dictionary<string, CallableSignature>(parentParamMap);
            foreach (var (k, v) in localParamMap)
                visibleParamMap[k] = v;
        }

        // Topological sort of properties
        var topoOrder = dependencyGraph.TopologicalOrder;

        // Process properties in topological order
        var processedProperties = new Property[alg.Properties.Count];
        foreach (var idx in topoOrder)
        {
            var prop = alg.Properties[idx];

            if (prop.Value is Algorithm.User { IsAssignmentDeconstructionSource: true })
            {
                // Hoisted deconstruction right-hand side: written as rows of THIS body, so it
                // is rewritten in the output phase below with this body's own context and
                // acquires no parameters of its own (see RewriteDeconstructionSourceRows).
                processedProperties[idx] = prop;
            }
            else if (prop.Value is Algorithm.Conditional condAlg)
            {
                processedProperties[idx] = prop.WithValue(ProcessConditionalProperty(
                    condAlg, prop.Name, visibleParamMap, observations, diagnostics, run));
            }
            else
            {
                // visibleParamMap is UPDATED after each processed property, so a value shared
                // by two properties could observe different sibling signatures if it were
                // reached between two writes it depends on. The run's region memo keys each
                // value on the signatures its FREE names actually see (M4), so a shared value
                // rewrites once per distinct observation and never once per referencing
                // property — and the dependency order above processes every referenced
                // sibling first, so within an acyclic property graph every reach observes the
                // same, final signatures.
                var processedBody = ProcessAlgorithm(
                    prop.Value, visibleParamMap, isRoot: false, observations, diagnostics, branchContext: null, run);

                // Update param maps with the processed, potentially augmented signature.
                var processedSignature = CallableSignature.FromAlgorithm(prop.Name, processedBody);
                localParamMap[prop.Name] = processedSignature;
                visibleParamMap[prop.Name] = processedSignature;

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
        };

        if (alg.ExplicitParameterPatterns.Count > 0 || branchContext is not null)
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
            var closedExistingParams = branchContext is null
                ? new HashSet<string>(alg.Params)
                : new HashSet<string>(branchContext.Pattern.BoundNames());
            var explicitContext = new ImplicitRewriteContext(
                closedPatterns,
                BuildSourceBindingKinds(closedPatterns),
                RequireExistingParameters: true,
                closedExistingParams,
                branchContext?.BranchName);
            var newOutput = new List<Expr>(alg.Output.Count);
            foreach (var expr in alg.Output)
            {
                newOutput.Add(
                    RewriteImplicitCalls(
                        expr,
                        visibleParamMap,
                        explicitContext,
                        inCallPosition: false,
                        walkMemos));
            }

            AstHelpers.RewriteDeconstructionSourceRows(
                alg,
                newProperties,
                expr => RewriteImplicitCalls(expr, visibleParamMap, explicitContext, inCallPosition: false, walkMemos));

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
        var deps = new List<(string Name, CallableSignature Signature)>();
        var seen = new HashSet<string>();
        var depsMemo = new DepsWalkMemo(observations);
        foreach (var expr in AstHelpers.WrittenRows(
            alg, isRoot ? expr => !ShouldPreserveBareRootResolve(expr, visibleParamMap, isRoot: true) : null))
        {
            CollectImplicitDeps(expr, visibleParamMap, seen, deps, inCallPosition: false, depsMemo);
        }

        // Compute lifted parameter patterns: existing patterns first, then new
        // dependency captures with their recursive shape preserved.
        var existingParams = new HashSet<string>(alg.Params);
        var newPatterns = new List<ParameterPattern>(alg.ParameterPatterns);
        foreach (var (_, signature) in deps)
        {
            if (CanForwardSingleCollectingStream(alg.ParameterPatterns, signature.ParameterPatterns))
                continue;

            foreach (var pattern in signature.ParameterPatterns)
            {
                var missingPattern = MissingCapturePattern(pattern, existingParams);
                if (missingPattern is null)
                    continue;

                newPatterns.Add(missingPattern);
                foreach (var capture in missingPattern.Captures)
                    existingParams.Add(capture.Name);
            }
        }

        // Rewrite output expressions. Source binding kinds come from the
        // LIFTED pattern list: a callee name missing from the original caller
        // parameters binds through the capture lifted above (possibly by an
        // earlier dependency with a different kind), and that lifted capture
        // is the forwarding source.
        var liftedContext = new ImplicitRewriteContext(
            alg.ParameterPatterns,
            BuildSourceBindingKinds(newPatterns),
            RequireExistingParameters: false,
            ExistingParameterNames: null);
        var rewrittenOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
        {
            rewrittenOutput.Add(
                ShouldPreserveBareRootResolve(expr, visibleParamMap, isRoot)
                    ? expr
                    : RewriteImplicitCalls(
                        expr,
                        visibleParamMap,
                        liftedContext,
                        inCallPosition: false,
                        walkMemos));
        }

        AstHelpers.RewriteDeconstructionSourceRows(
            alg,
            newProperties,
            expr => RewriteImplicitCalls(expr, visibleParamMap, liftedContext, inCallPosition: false, walkMemos));

        return alg.WithParameterPatterns(newPatterns) with
        {
            Opens = newOpens,
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

    private static IReadOnlyList<Expr> ProcessOpenExprs(
        IReadOnlyList<Expr> opens,
        FrontEndTraversalObservations? observations,
        ResolutionRun run)
    {
        if (opens.Count == 0)
            return opens;

        // One memo bundle per open-target region: every walk below runs with a fresh EMPTY
        // signature map, so the region's rewrite context is constant regardless of which
        // fresh map instance a call site allocates.
        var memos = new ResolverWalkMemos(run, observations, diagnostics: null);
        var processed = new List<Expr>(opens.Count);
        foreach (var open in opens)
            processed.Add(ProcessOpenExpr(open, memos));
        return processed;
    }

    private static Algorithm.Conditional ProcessConditionalProperty(
        Algorithm.Conditional conditional,
        string propertyName,
        Dictionary<string, CallableSignature> parentParamMap,
        FrontEndTraversalObservations? observations,
        List<Diagnostic>? diagnostics,
        ResolutionRun run)
    {
        var newOpens = ProcessOpenExprs(conditional.Opens, observations, run);
        var branches = new List<CondBranch>(conditional.Branches.Count);
        foreach (var branch in conditional.Branches)
        {
            if (DeferredModuleRegions.TryGet(branch.Body, out var region))
            {
                // B2c: a deferred module region is not resolved eagerly (its provisional body
                // is never evaluated, and resolving it could only report false forwarding
                // refusals against names a deferred module provides). The region records the
                // visible signature map as it stands HERE — a snapshot, since the property loop
                // keeps extending the map — and is re-keyed by this region's own output body.
                var placeholder = branch.Body with { };
                DeferredModuleRegions.Register(
                    placeholder,
                    region.WithResolution(new DeferredBranchContext(
                        new Dictionary<string, CallableSignature>(parentParamMap),
                        propertyName,
                        branch.Pattern)));
                branches.Add(new CondBranch(branch.Pattern, placeholder));
                continue;
            }

            // M4: the body is rewritten through the run's region memo — once per (body,
            // free-name signature snapshot, closed binder specification, reporting mode). A
            // body shared by several families under one region is rewritten once (sharing
            // preserved in the output) and only its blocked-forwarding diagnostics, the one
            // thing that names THIS family, are re-issued for the later families.
            var body = ProcessAlgorithm(
                branch.Body, parentParamMap, isRoot: false, observations, diagnostics,
                new ConditionalBranchContext(propertyName, branch.Pattern), run);
            branches.Add(new CondBranch(branch.Pattern, body));
        }

        return conditional with { Opens = newOpens, Branches = branches };
    }

    /// <summary>
    /// Re-issues a completed region's blocked strict-value reports for a further family that
    /// shares the body — same references, same missing names, same spans, worded with THIS
    /// family's name — so per-family diagnostic multiplicity matches a fresh rewrite without
    /// performing one, independent of which family was reached first.
    /// </summary>
    private static void ReplayBranchDiagnostics(AlgorithmRegion region, string branchName, List<Diagnostic>? diagnostics)
    {
        if (diagnostics is null || region.DiagnosticTemplates is null)
            return;

        foreach (var template in region.DiagnosticTemplates)
        {
            diagnostics.Add(new Diagnostic(
                FormatBlockedStrictValueForwarding(template.ReferenceDisplayName, template.MissingParameterNames, branchName),
                DiagnosticSeverity.Error,
                template.Span)
            {
                Code = DiagnosticCode.UndeclaredIdentifier,
            });
        }
    }

    /// <summary>
    /// The resolution context of one deferred module region (B2c): the visible signature map
    /// exactly as the eager walk saw it at the branch, plus the closed branch-pattern
    /// specification, so the demand-time run rewrites the detected body under the same
    /// forwarding rules.
    /// </summary>
    internal sealed record DeferredBranchContext(
        IReadOnlyDictionary<string, CallableSignature> ParentParamMap,
        string BranchName,
        Pattern Pattern);

    /// <summary>
    /// Demand-time implicit-argument resolution of a deferred region's DETECTED body: the
    /// ordinary closed-branch rewrite, with diagnostics.
    /// </summary>
    internal static Algorithm ElaborateDeferredBranch(
        Algorithm detectedBody,
        DeferredBranchContext context,
        List<Diagnostic> diagnostics,
        FrontEndTraversalObservations? observations = null)
        => ProcessAlgorithm(
            detectedBody,
            new Dictionary<string, CallableSignature>(context.ParentParamMap),
            isRoot: false,
            observations,
            diagnostics,
            new ConditionalBranchContext(context.BranchName, context.Pattern),
            new ResolutionRun());

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
        switch (expr)
        {
            case Expr.AlgorithmExpr(var algorithm):
                return new Expr.AlgorithmExpr(
                    ProcessSharedNestedAlgorithm(algorithm, new Dictionary<string, CallableSignature>(), memos))
                {
                    Span = expr.Span,
                };

            case Expr.Capture(var captureBody):
                // Capture targets own no scope; rows recurse without lifting,
                // with a fresh signature map like every other open target.
                return new Expr.Capture(new OutputBundle(
                    captureBody
                        .Select(row => ProcessExprNested(row, new Dictionary<string, CallableSignature>(), memos))
                        .ToList()))
                {
                    Span = expr.Span,
                };

            case Expr.DotCall dotCall:
                // `with` keeps the stored dot-edge facts (member span, lexical
                // fallback) intact.
                return dotCall with
                {
                    Target = ProcessOpenExpr(dotCall.Target, memos),
                    Args = dotCall.Args is { } dotArgs
                        ? ProcessArgumentBundle(dotArgs, new Dictionary<string, CallableSignature>(), memos)
                        : null,
                };

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    ProcessOpenExpr(operand, memos))
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    ProcessOpenExpr(left, memos),
                    ProcessOpenExpr(right, memos)) { Span = expr.Span };

            case Expr.ListLiteral(var items):
                return new Expr.ListLiteral(
                    items.Select(item => ProcessOpenExpr(item, memos)).ToList()) { Span = expr.Span };

            case Expr.Call(var function, var args):
                return new Expr.Call(
                    ProcessOpenExpr(function, memos),
                    ProcessArgumentBundle(args, new Dictionary<string, CallableSignature>(), memos)) { Span = expr.Span };

            // Intentional leaves: name/literal leaves carry no nested algorithm
            // to process (a bare Resolve IS the ordinary open-target form);
            // Grace cannot survive parameter detection, which runs first, so a
            // host-supplied wrapper passes through untouched; and operator
            // forms are never valid open targets — the evaluator's open-form
            // validation rejects them (BadOpenForm) — so a host-built one
            // passes through unprocessed like a leaf.
            case Expr.Resolve:
            case Expr.Param:
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
            case Expr.Grace:
            case Expr.Unary:
            case Expr.Binary:
            case Expr.Index:
                return expr;

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently passing
            // through.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ImplicitArgumentResolver)}.{nameof(ProcessOpenExpr)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a recursive rewrite case or an intentional leaf.");
        }
    }

    private static bool ShouldPreserveBareRootResolve(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        bool isRoot)
        => isRoot
            && expr is Expr.Resolve(var name)
            && paramMap.TryGetValue(name, out var ps)
            && ps.Parameters.Count > 0;

    private static ParameterPattern? MissingCapturePattern(
        ParameterPattern pattern,
        IReadOnlySet<string> existingParams)
    {
        switch (pattern)
        {
            case CaptureParameterPattern capture:
                return existingParams.Contains(capture.Name) ? null : capture;

            case SequenceValueParameterPattern group:
            {
                var missingItems = new List<ParameterPattern>(group.Items.Count);
                foreach (var item in group.Items)
                {
                    var missingItem = MissingCapturePattern(item, existingParams);
                    if (missingItem is not null)
                        missingItems.Add(missingItem);
                }

                return missingItems.Count == 0
                    ? null
                    : new SequenceValueParameterPattern(missingItems);
            }

            default:
                return null;
        }
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

    private static bool TryGetSingleForwardableCalleeStream(
        IReadOnlyList<ParameterPattern> patterns,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CaptureParameterPattern? capture)
    {
        if (TryGetSingleTopLevelCollectingCapture(patterns, out capture))
            return true;

        if (patterns.Count == 1
            && patterns[0] is SequenceValueParameterPattern { Items.Count: 1 } group
            && group.Items[0] is CaptureParameterPattern { Kind: ParameterKind.Collecting } groupedCollecting)
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

    private static bool CanBuildImplicitCallArgumentsFromExistingParameters(
        IReadOnlyList<ParameterPattern> calleePatterns,
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlySet<string> existingParameterNames)
        => MissingClosedListForwardingNames(calleePatterns, callerPatterns, existingParameterNames).Count == 0;

    /// <summary>
    /// The callee capture names a CLOSED explicit parameter list cannot supply — the
    /// witness form of <see cref="CanBuildImplicitCallArgumentsFromExistingParameters"/>,
    /// which is now that predicate's only implementation. Forwarding availability and the
    /// names blamed for its absence therefore cannot drift apart: the caller's own
    /// forwarded collecting stream satisfies EVERY capture (so it yields no names at all),
    /// and otherwise a capture is missing exactly when the closed list does not declare it.
    /// <para>Order is <see cref="ParameterPattern.FlattenCaptures"/> order — the callee's
    /// own declaration order — deduplicated first-occurrence-wins, so a diagnostic built
    /// from it is stable and never hash-ordered.</para>
    /// </summary>
    private static IReadOnlyList<string> MissingClosedListForwardingNames(
        IReadOnlyList<ParameterPattern> calleePatterns,
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlySet<string> existingParameterNames)
    {
        // A single forwarded collecting stream re-supplies the callee's whole parameter
        // shape by binding KIND, not by name, so nothing is missing even though the names
        // differ. Consulting the same helper the forwarding builder uses keeps fixed and
        // collecting bindings from ever being judged interchangeable here.
        if (CanForwardSingleCollectingStream(callerPatterns, calleePatterns))
            return [];

        List<string>? missing = null;
        foreach (var capture in ParameterPattern.FlattenCaptures(calleePatterns))
        {
            if (existingParameterNames.Contains(capture.Name))
                continue;

            missing ??= [];
            if (!missing.Contains(capture.Name, StringComparer.Ordinal))
                missing.Add(capture.Name);
        }

        return missing ?? (IReadOnlyList<string>)[];
    }

    /// <summary>
    /// The CLOSED-explicit-parameter-list gate, in one place: inside an algorithm that wrote
    /// its own parameter list, a bare parameterized reference may lift only when every capture
    /// the synthesized argument list would need is already declared by that list (or is the
    /// caller's own forwarded collecting stream). Lifting anything else would invent a
    /// parameter the programmer never wrote — and, worse, silently bind an ancestor's.
    ///
    /// <para>Every liftable arm of <see cref="RewriteImplicitCallsCore"/> consults THIS
    /// helper with the region's <see cref="ImplicitRewriteContext"/>, so no expression
    /// position — value-demanding Math arguments included — can be reached under a
    /// weaker gate than the rows around it.</para>
    /// </summary>
    private static bool ClosedListBlocksLifting(
        ImplicitRewriteContext context,
        IReadOnlyList<ParameterPattern> calleePatterns)
        => context.RequireExistingParameters
            && (context.ExistingParameterNames is null
                || !CanBuildImplicitCallArgumentsFromExistingParameters(
                    calleePatterns,
                    context.CallerParameterPatterns,
                    context.ExistingParameterNames));

    /// <summary>
    /// Reports a STATICALLY IMPOSSIBLE strict value demand: a registry-proven
    /// value-demanding consumer requires this reference's produced value, the reference
    /// resolves to a callable with implicit parameters, and
    /// <see cref="ClosedListBlocksLifting"/> just refused the forwarding that would supply
    /// them. Nothing later in the pipeline can rescue such a position — evaluation would
    /// demand the value with zero arguments and fail — so the front end says so, naming
    /// what the programmer can act on.
    ///
    /// <para>Called ONLY from the arms that already decided to leave the reference bare,
    /// and only while <c>inStrictValueDemand</c> holds. Both halves matter: outside a
    /// proven strict-value position the same blocked reference is a legal higher-order
    /// reference (<c>F(x) = A</c>, <c>Apply(A)</c>), and outside a blocked lift there is
    /// nothing wrong at all.</para>
    ///
    /// <para>Conservative by construction — it reports only what it can name. A context
    /// with no recorded <see cref="ImplicitRewriteContext.ExistingParameterNames"/> blocks
    /// lifting without identifying a closed list, so it yields no diagnostic and the
    /// program keeps its ordinary runtime checking.</para>
    /// </summary>
    /// <param name="referenceDisplayName">
    /// The written callable the program can act on (<c>A</c>, the alias <c>abs</c>, the
    /// canonical <c>Math.Abs</c>) — never the consuming native's own declared argument
    /// name, which belongs to the consumer and not to this failure.
    /// </param>
    private static void ReportBlockedStrictValueForwarding(
        Expr reference,
        string referenceDisplayName,
        IReadOnlyList<ParameterPattern> calleePatterns,
        ImplicitRewriteContext context,
        ResolverWalkMemos memos)
    {
        if (memos.Diagnostics is not { } diagnostics || context.ExistingParameterNames is null)
            return;

        var missing = MissingClosedListForwardingNames(
            calleePatterns, context.CallerParameterPatterns, context.ExistingParameterNames);
        if (missing.Count == 0)
            return;

        var span = reference.Span ?? new SourceSpan(0, 0, 0, 0);
        diagnostics.Add(new Diagnostic(
            FormatBlockedStrictValueForwarding(referenceDisplayName, missing, context.ConditionalBranchName),
            DiagnosticSeverity.Error,
            span)
        {
            Code = DiagnosticCode.UndeclaredIdentifier,
        });
        // A conditional branch body's own region keeps the report re-issuable for further
        // families sharing the body (M4; see ConditionalBranchContext.DiagnosticTemplates).
        memos.BranchDiagnosticTemplates?.Add(new BlockedForwardingTemplate(referenceDisplayName, missing, span));
    }

    /// <summary>
    /// Wording for <see cref="ReportBlockedStrictValueForwarding"/>, deliberately parallel
    /// to parameter detection's directly-written counterparts ("Identifier 'z' is used in an
    /// explicitly parameterized algorithm, but it is not declared in the parameter list" /
    /// "Identifier 'z' is used in conditional branch 'F', but it is not declared in the branch
    /// pattern"): the same closed-specification rule, reached one level of indirection away
    /// because the missing name is required by the REFERENCED callable rather than written here.
    /// </summary>
    private static string FormatBlockedStrictValueForwarding(
        string referenceDisplayName,
        IReadOnlyList<string> missingParameterNames,
        string? conditionalBranchName)
    {
        var names = FormatQuotedNameList(missingParameterNames);
        var noun = missingParameterNames.Count == 1 ? "parameter" : "parameters";
        if (conditionalBranchName is not null)
        {
            return string.Join(
                Environment.NewLine,
                $"'{referenceDisplayName}' is required as a value here, but producing that value needs the implicit {noun} {names}, "
                    + $"which the pattern of conditional branch '{conditionalBranchName}' does not bind.",
                $"Conditional branch patterns are closed, so {names} cannot be inferred here. Declare {names} in the branch pattern, "
                    + $"or call '{referenceDisplayName}' with explicit arguments.");
        }

        return string.Join(
            Environment.NewLine,
            $"'{referenceDisplayName}' is required as a value here, but producing that value needs the implicit {noun} {names}, "
                + "which the enclosing explicit parameter list does not declare.",
            $"Explicit parameter lists are closed, so {names} cannot be inferred here. Declare {names} in the parameter list, "
                + $"call '{referenceDisplayName}' with explicit arguments, or remove the explicit parameter list.");
    }

    private static string FormatQuotedNameList(IReadOnlyList<string> values)
        => values.Count switch
        {
            0 => string.Empty,
            1 => $"'{values[0]}'",
            2 => $"'{values[0]}' and '{values[1]}'",
            _ => string.Join(", ", values.Take(values.Count - 1).Select(value => $"'{value}'")) + $", and '{values[^1]}'",
        };

    /// <summary>
    /// Maps every caller-side capture name (top-level and nested) to its
    /// binding kind. Implicit forwarding consults this map so the decision to
    /// re-spread a forwarded value is made from the SOURCE binding, never from
    /// the destination parameter kind alone.
    /// </summary>
    private static Dictionary<string, ParameterKind> BuildSourceBindingKinds(
        IEnumerable<ParameterPattern> callerPatterns)
    {
        var kinds = new Dictionary<string, ParameterKind>(StringComparer.Ordinal);
        foreach (var capture in ParameterPattern.FlattenCaptures(callerPatterns))
            kinds.TryAdd(capture.Name, capture.Kind);
        return kinds;
    }

    /// <summary>
    /// The binder shape of a conditional branch pattern as caller parameter patterns — the
    /// forwarding SOURCE shape of a branch body, mirroring
    /// <see cref="Pattern.TryGetOrdinaryClauseParameterPatterns"/> but total over mixed
    /// heads: literal items bind nothing, so they contribute no capture,
    /// while binders keep their kind and nested binder groups keep their sequence-value
    /// structure, including empty groups. The closed-specification name check consumes only
    /// captures, but single-collecting forwarding also depends on those group boundaries.
    /// Collecting binders in conditional families are host-AST-only; the parser rejects them.
    /// </summary>
    private static IReadOnlyList<ParameterPattern> BranchBinderParameterPatterns(Pattern pattern)
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
        switch (pattern)
        {
            case Pattern.Bind binder:
                parameterPattern = new CaptureParameterPattern(binder.Name, binder.NameSpan, binder.ParameterKind)
                {
                    CollectMarkerSpan = binder.CollectMarkerSpan,
                };
                return true;

            case Pattern.SequenceValue(var items):
            {
                var childPatterns = new List<ParameterPattern>(items.Count);
                foreach (var item in items)
                {
                    if (TryCreateBinderParameterPattern(item, out var childPattern))
                        childPatterns.Add(childPattern);
                }

                parameterPattern = new SequenceValueParameterPattern(childPatterns);
                return true;
            }

            case Pattern.LitInt:
            case Pattern.LitString:
                parameterPattern = null;
                return false;

            default:
                throw new InvalidOperationException(
                    $"Unhandled Pattern variant in {nameof(BranchBinderParameterPatterns)}: {pattern.GetType().Name}.");
        }
    }

    private static IReadOnlyList<Expr> BuildImplicitCallArguments(
        IReadOnlyList<ParameterPattern> calleePatterns,
        IReadOnlyList<ParameterPattern> callerPatterns,
        IReadOnlyDictionary<string, ParameterKind> sourceBindingKinds)
    {
        TryGetSingleCollectingForwarding(
            callerPatterns,
            calleePatterns,
            out var forwardedCalleeName,
            out var forwardedCallerName);

        // TryGetSingleCollectingForwarding succeeds only when the callee shape
        // contains exactly one capture: either a lone top-level collector or a
        // lone collector inside one sequence-value group. Consequently there is
        // no second callee capture to discriminate here; when forwarding is
        // active, every reachable capture is the forwarded capture. Expressing
        // that invariant directly avoids an equivalent && -> || mutant.
        string MapCaptureName(CaptureParameterPattern capture)
            => forwardedCalleeName is not null ? forwardedCallerName! : capture.Name;

        // A collecting DESTINATION re-spreads the forwarded value only when the
        // SOURCE binding is itself a collecting binding's exact list: then
        // `callee(rest*)` re-supplies exactly the collected items
        // (spread(collect(xs)) = xs). An ordinary source binding always
        // forwards as ONE argument, even into a collecting destination. A name
        // absent from the caller's bindings is about to be lifted as a copy
        // of the callee's own pattern, so its source kind IS the callee kind.
        bool ForwardAsSpread(CaptureParameterPattern calleeCapture)
            => sourceBindingKinds.TryGetValue(MapCaptureName(calleeCapture), out var sourceKind)
                ? sourceKind == ParameterKind.Collecting
                : calleeCapture.Kind == ParameterKind.Collecting;

        return calleePatterns
            .Select(pattern => BuildPatternArgument(pattern, MapCaptureName, ForwardAsSpread))
            .ToList();
    }

    private static Expr BuildPatternArgument(
        ParameterPattern pattern,
        Func<CaptureParameterPattern, string> mapCaptureName,
        Func<CaptureParameterPattern, bool> forwardAsSpread)
    {
        return pattern switch
        {
            // A collecting destination whose source binding is a collecting binding's
            // exact list forwards through explicit spread so the callee's collecting
            // parameter re-collects exactly the caller's items; every other
            // capture forwards as one argument slot.
            CaptureParameterPattern { Kind: ParameterKind.Collecting } collecting
                when forwardAsSpread(collecting) =>
                new Expr.SequenceSpread(new Expr.Param(mapCaptureName(collecting))),
            CaptureParameterPattern capture => new Expr.Param(mapCaptureName(capture)),
            // A forwarded sequence-value pattern groups its item arguments as one
            // written capture boundary — a value grouping, not a scope.
            SequenceValueParameterPattern group => new Expr.Capture(new OutputBundle(
                BuildPatternArgumentOutput(group.Items, mapCaptureName, forwardAsSpread))),
            _ => throw new InvalidOperationException("Unknown parameter pattern."),
        };
    }

    private static IReadOnlyList<Expr> BuildPatternArgumentOutput(
        IReadOnlyList<ParameterPattern> patterns,
        Func<CaptureParameterPattern, string> mapCaptureName,
        Func<CaptureParameterPattern, bool> forwardAsSpread)
        => patterns
            .Select(pattern => BuildPatternArgument(pattern, mapCaptureName, forwardAsSpread))
            .ToList();

    /// <summary>
    /// Collects implicit dependencies from an expression: bare <see cref="Expr.Resolve"/> nodes
    /// pointing to algorithms with parameters in the visible scope.
    /// </summary>
    private static void CollectImplicitDeps(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        HashSet<string> seen,
        List<(string Name, CallableSignature Signature)> deps,
        bool inCallPosition,
        DepsWalkMemo memo)
    {
        // DAG-safety: every contribution of this walk is seen-set deduplicated, so a
        // completed node reference reached again — under the same call-position flavor,
        // which is the one context dimension that changes what a node contributes — adds
        // nothing and is skipped. Childless leaves decide in place.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
        {
            CollectImplicitDepsCore(expr, paramMap, seen, deps, inCallPosition, memo);
            return;
        }

        var visited = inCallPosition
            ? memo.CalleeVisited ??= new(ReferenceEqualityComparer.Instance)
            : memo.ValueVisited;
        if (visited.Contains(expr))
            return;

        memo.Observations?.RecordResolverCollectExpansion();
        CollectImplicitDepsCore(expr, paramMap, seen, deps, inCallPosition, memo);
        visited.Add(expr);
    }

    private static void CollectImplicitDepsCore(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        HashSet<string> seen,
        List<(string Name, CallableSignature Signature)> deps,
        bool inCallPosition,
        DepsWalkMemo memo)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (inCallPosition)
                    break;

                if (paramMap.TryGetValue(name, out var ps))
                {
                    if (ps.Parameters.Count > 0 && seen.Add(name))
                        deps.Add((name, ps));
                }
                else if (expr.TryGetRegistryProvenMathAliasFacts(paramMap.ContainsKey, out var bareAliasFacts)
                    && seen.Add(bareAliasFacts.CanonicalKey))
                {
                    // A bare Math ALIAS in value position lifts exactly like the
                    // bare canonical `Math.X` spelling (the DotCall arm below),
                    // from the same registry facts. The canonical key dedups the
                    // two spellings into ONE lifted dependency. Any visible user
                    // property — even a zero-parameter one — shadows the alias
                    // through the paramMap branch above.
                    //
                    // The resolver's shadow predicate for every Math-shape
                    // classification (this arm, the alias-call arms, and the
                    // canonical `Math.X` arms) is `paramMap.ContainsKey`: the map
                    // carries every visible user property — local or ancestor —
                    // and a parameter reference is an Expr.Param after detection,
                    // so a surviving bare Expr.Resolve outside the map can only
                    // resolve to the prelude. A user-defined `sin` or `Math`
                    // therefore stays an ordinary neutral callable/container.
                    deps.Add((bareAliasFacts.CanonicalKey, bareAliasFacts.Signature));
                }
                break;

            case Expr.Call(var func, var callArgs) call:
                // func: if it's a direct Resolve, it's explicitly called - mark as call position.
                // Otherwise recurse normally (e.g. Prop target is not in call position).
                if (func is Expr.Resolve)
                {
                    CollectImplicitDeps(func, paramMap, seen, deps, inCallPosition: true, memo);

                    // A Math-alias call has the SAME registry-proven strict-value
                    // argument contract as the written `Math.X(...)` dot shape
                    // (the DotCall arm below), classified by the shared alias-call
                    // twin: its argument slots are ordinary value positions and
                    // contribute implicit dependencies. Ordinary neutral call
                    // arguments contribute none.
                    if (call.HasRegistryProvenStrictValueArguments(paramMap.ContainsKey))
                    {
                        CollectArgumentImplicitDeps(callArgs, paramMap, seen, deps, memo);
                    }
                }
                else
                {
                    CollectImplicitDeps(func, paramMap, seen, deps, inCallPosition: false, memo);
                }
                break;

            case Expr.Binary(_, var left, var right):
                CollectImplicitDeps(left, paramMap, seen, deps, false, memo);
                CollectImplicitDeps(right, paramMap, seen, deps, false, memo);
                break;

            case Expr.Unary(_, var operand):
                CollectImplicitDeps(operand, paramMap, seen, deps, false, memo);
                break;

            case Expr.Index(var target, var selector):
                CollectImplicitDeps(target, paramMap, seen, deps, false, memo);
                CollectImplicitDeps(selector, paramMap, seen, deps, false, memo);
                break;

            case Expr.SequenceSpread(var operand):
                CollectImplicitDeps(operand, paramMap, seen, deps, false, memo);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectImplicitDeps(left, paramMap, seen, deps, false, memo);
                CollectImplicitDeps(right, paramMap, seen, deps, false, memo);
                break;

            case Expr.ListLiteral(var listItems):
                foreach (var item in listItems)
                    CollectImplicitDeps(item, paramMap, seen, deps, false, memo);
                break;

            case Expr.DotCall dotCall:
                if (!inCallPosition
                    && TryGetBareBuiltinCallableSignature(dotCall, paramMap, out var callableKey, out var signature))
                {
                    if (seen.Add(callableKey))
                        deps.Add((callableKey, signature));
                }

                // DotCall target is in algorithm position (resolveAlg, not eval).
                CollectImplicitDeps(dotCall.Target, paramMap, seen, deps, inCallPosition: true, memo);
                if (dotCall.Args is { } dotArgs
                    && dotCall.HasRegistryProvenStrictValueArguments(paramMap.ContainsKey))
                {
                    CollectArgumentImplicitDeps(dotArgs, paramMap, seen, deps, memo);
                }
                break;

            case Expr.Grace(var inner, _):
                CollectImplicitDeps(inner, paramMap, seen, deps, inCallPosition, memo);
                break;

            case Expr.AlgorithmExpr or Expr.Capture:
                // A scoped block owns its names; a capture suppresses callable
                // lifting for everything inside it (pre-split behavior for
                // grouped expressions). Neither contributes deps here.
                break;

            // Intentional leaves: no bare callable references to lift.
            case Expr.Num:
            case Expr.Param:
            case Expr.StringLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                break;

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently
            // contributing no implicit dependencies.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ImplicitArgumentResolver)}.{nameof(CollectImplicitDeps)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a collected case or an intentional leaf.");
        }
    }

    private static void CollectArgumentImplicitDeps(
        OutputBundle args,
        Dictionary<string, CallableSignature> paramMap,
        HashSet<string> seen,
        List<(string Name, CallableSignature Signature)> deps,
        DepsWalkMemo memo)
    {
        foreach (var argExpr in args)
            CollectImplicitDeps(argExpr, paramMap, seen, deps, inCallPosition: false, memo);
    }

    /// <summary>
    /// Rewrites bare <see cref="Expr.Resolve"/> nodes into <see cref="Expr.Call"/> nodes
    /// with lifted parameters. Also recursively processes nested algorithms.
    /// </summary>
    /// <param name="inStrictValueDemand">
    /// True while this position's produced value is required by a registry-proven
    /// value-demanding consumer — set by
    /// <see cref="ProcessValueDemandingArgumentBundle"/> and carried down only through
    /// positions that compute that same value (operands, index parts, sequence/list
    /// elements, a nested value-demanding bundle). It is DROPPED wherever the walk leaves
    /// that obligation: call/dot-call targets (algorithm position), neutral argument
    /// bundles, capture rows, and nested algorithms. The flag never changes a rewrite —
    /// only whether a refused lift is additionally REPORTED (see
    /// <see cref="ReportBlockedStrictValueForwarding"/>), so it is not part of the rewrite
    /// memo key. A separate strict-visit set makes that reporting side effect independent of
    /// whether a neutral reach populated the rewrite memo first.
    /// </param>
    private static Expr RewriteImplicitCalls(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        ImplicitRewriteContext context,
        bool inCallPosition,
        ResolverWalkMemos memos,
        bool inStrictValueDemand = false)
    {
        // DAG-safety: one rewrite per shared node reference per (region, call position); the
        // memo returns the same rewritten node for every later reach, preserving the input's
        // sharing (see ResolverWalkMemos). A Resolve leaf participates because value-position
        // resolution may replace it with a fresh Call. Node plus call position is a complete
        // key only while the region rewrites under ONE caller context — pinned here, not
        // assumed.
        memos.PinRewriteContext(context);

        var hasTraversableChildren = AstTraversalDagSafety.HasTraversableExprChildren(expr);
        if (!hasTraversableChildren && expr is not Expr.Resolve)
            return RewriteImplicitCallsCore(expr, paramMap, context, inCallPosition, memos, inStrictValueDemand);

        var observeStrictValueDemand = inStrictValueDemand
            && memos.TryBeginStrictValueDiagnosticVisit(expr);
        var rewriteMap = memos.RewriteMapFor(inCallPosition);
        if (rewriteMap.TryGetValue(expr, out var rewritten))
        {
            // The cached rewrite is still authoritative. Re-enter the existing traversal
            // only for its first strict diagnostic observation; descendants use the same
            // independent visit set, so each shared written occurrence reports at most once.
            if (observeStrictValueDemand)
                _ = RewriteImplicitCallsCore(expr, paramMap, context, inCallPosition, memos, inStrictValueDemand: true);
            return rewritten;
        }

        if (hasTraversableChildren)
            memos.Observations?.RecordResolverRewriteExpansion();
        rewritten = RewriteImplicitCallsCore(
            expr, paramMap, context, inCallPosition, memos, observeStrictValueDemand);
        rewriteMap[expr] = rewritten;
        return rewritten;
    }

    private static Expr RewriteImplicitCallsCore(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        ImplicitRewriteContext context,
        bool inCallPosition,
        ResolverWalkMemos memos,
        bool inStrictValueDemand)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (!inCallPosition
                    && paramMap.TryGetValue(name, out var ps)
                    && ps.Parameters.Count > 0)
                {
                    if (ClosedListBlocksLifting(context, ps.ParameterPatterns))
                    {
                        if (inStrictValueDemand)
                            ReportBlockedStrictValueForwarding(expr, name, ps.ParameterPatterns, context, memos);
                        return expr;
                    }

                    var implicitArgs = OutputBundle.From(BuildImplicitCallArguments(
                        ps.ParameterPatterns, context.CallerParameterPatterns, context.SourceBindingKinds));
                    return new Expr.Call(new Expr.Resolve(name) { Span = expr.Span }, implicitArgs) { Span = expr.Span };
                }

                // Bare Math ALIAS in value position: lift exactly like the bare
                // canonical `Math.X` arm below, from the same registry facts.
                // The constant (`pi`) carries no facts and stays a bare reference.
                if (!inCallPosition
                    && expr.TryGetRegistryProvenMathAliasFacts(paramMap.ContainsKey, out var bareAliasFacts))
                {
                    if (ClosedListBlocksLifting(context, bareAliasFacts.Signature.ParameterPatterns))
                    {
                        if (inStrictValueDemand)
                        {
                            ReportBlockedStrictValueForwarding(
                                expr, bareAliasFacts.SpelledName, bareAliasFacts.Signature.ParameterPatterns, context, memos);
                        }

                        return expr;
                    }

                    var aliasArgs = OutputBundle.From(BuildImplicitCallArguments(
                        bareAliasFacts.Signature.ParameterPatterns, context.CallerParameterPatterns, context.SourceBindingKinds));
                    return new Expr.Call(new Expr.Resolve(name) { Span = expr.Span }, aliasArgs) { Span = expr.Span };
                }
                return expr;

            case Expr.Call(var func, var args) call:
                // If func is a direct Resolve, leave it (explicitly called).
                // Otherwise recurse into func normally.
                var newFunc = func is Expr.Resolve
                    ? func
                    : RewriteImplicitCalls(func, paramMap, context, inCallPosition: false, memos);

                // A Math-alias call shares the written `Math.X(...)` dot shape's
                // registry-proven strict-value argument contract (the DotCall arm
                // below), classified by the shared alias-call twin: its argument
                // slots are ordinary value positions and lift. Every other call
                // keeps NEUTRAL argument processing so bare higher-order
                // references survive.
                var newArgs = call.HasRegistryProvenStrictValueArguments(paramMap.ContainsKey)
                    ? ProcessValueDemandingArgumentBundle(args, paramMap, context, memos)
                    : ProcessArgumentBundle(args, paramMap, memos);
                return new Expr.Call(newFunc, newArgs) { Span = expr.Span };

            case Expr.Binary(var op, var left, var right):
                return new Expr.Binary(op,
                    RewriteImplicitCalls(left, paramMap, context, false, memos, inStrictValueDemand),
                    RewriteImplicitCalls(right, paramMap, context, false, memos, inStrictValueDemand)) { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op, RewriteImplicitCalls(operand, paramMap, context, false, memos, inStrictValueDemand)) { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    RewriteImplicitCalls(target, paramMap, context, false, memos, inStrictValueDemand),
                    RewriteImplicitCalls(selector, paramMap, context, false, memos, inStrictValueDemand)) { Span = expr.Span };

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    RewriteImplicitCalls(operand, paramMap, context, false, memos, inStrictValueDemand))
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    RewriteImplicitCalls(left, paramMap, context, false, memos, inStrictValueDemand),
                    RewriteImplicitCalls(right, paramMap, context, false, memos, inStrictValueDemand)) { Span = expr.Span };

            case Expr.ListLiteral(var listItems):
                return new Expr.ListLiteral(
                    listItems.Select(item => RewriteImplicitCalls(item, paramMap, context, false, memos, inStrictValueDemand)).ToList())
                { Span = expr.Span };

            case Expr.DotCall(var target, var name, null)
                when !inCallPosition
                    && TryGetBareBuiltinCallableSignature(expr, paramMap, out var bareBuiltinKey, out var builtinSignature):
                if (ClosedListBlocksLifting(context, builtinSignature.ParameterPatterns))
                {
                    if (inStrictValueDemand)
                    {
                        ReportBlockedStrictValueForwarding(
                            expr, bareBuiltinKey, builtinSignature.ParameterPatterns, context, memos);
                    }

                    return expr;
                }

                var liftedDotArgs = OutputBundle.From(BuildImplicitCallArguments(
                    builtinSignature.ParameterPatterns, context.CallerParameterPatterns, context.SourceBindingKinds));
                return ((Expr.DotCall)expr) with
                {
                    Target = RewriteImplicitCalls(target, paramMap, context, inCallPosition: true, memos),
                    Args = liftedDotArgs,
                };

            case Expr.DotCall dotCall:
                // DotCall target is in algorithm position (resolveAlg, not eval).
                // The stored lexical fallback is a Resolve/Param leaf and needs
                // no implicit-call rewriting; `with` carries it forward.
                return dotCall with
                {
                    Target = RewriteImplicitCalls(dotCall.Target, paramMap, context, inCallPosition: true, memos),
                    Args = dotCall.Args is { } dotArgs
                        ? dotCall.HasRegistryProvenStrictValueArguments(paramMap.ContainsKey)
                            ? ProcessValueDemandingArgumentBundle(dotArgs, paramMap, context, memos)
                            : ProcessArgumentBundle(dotArgs, paramMap, memos)
                        : null,
                };

            case Expr.Grace(var inner, _):
                return RewriteImplicitCalls(inner, paramMap, context, inCallPosition, memos, inStrictValueDemand);

            case Expr.AlgorithmExpr(var alg):
                return new Expr.AlgorithmExpr(
                    ProcessSharedNestedAlgorithm(alg, paramMap, memos)) { Span = expr.Span };

            case Expr.Capture(var captureBody):
                // Capture rows recurse without lifting at this level, exactly as
                // the pre-split transparent group algorithm's rows did.
                return new Expr.Capture(new OutputBundle(
                    captureBody.Select(row => ProcessExprNested(row, paramMap, memos)).ToList()))
                { Span = expr.Span };

            // Intentional leaves: nothing to lift or rewrite. (A Param is an
            // already-elaborated parameter reference; the guarded Resolve arms
            // above handled every liftable name shape.)
            case Expr.Num:
            case Expr.Param:
            case Expr.StringLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                return expr;

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently keeping
            // bare param-bearing references inside it unlifted.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ImplicitArgumentResolver)}.{nameof(RewriteImplicitCalls)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a recursive rewrite case or an intentional leaf.");
        }
    }

    /// <summary>
    /// Processes an argument bundle without lifting at this level: each slot
    /// recurses into nested algorithms only, exactly like every other
    /// transparent expression context (capture rows, list elements). Bare
    /// higher-order references such as <c>Apply(Increment)</c> therefore stay
    /// bare argument slots.
    /// </summary>
    private static OutputBundle ProcessArgumentBundle(
        OutputBundle args,
        Dictionary<string, CallableSignature> paramMap,
        ResolverWalkMemos memos)
        => new(args.Select(argExpr => ProcessExprNested(argExpr, paramMap, memos)).ToList());

    /// <summary>
    /// Region-memoized nested-algorithm processing for transparent contexts and value
    /// positions: two distinct <see cref="Expr.AlgorithmExpr"/> wrappers over ONE shared
    /// algorithm resolve it once (the whole region shares one final signature map).
    /// </summary>
    private static Algorithm ProcessSharedNestedAlgorithm(
        Algorithm alg,
        Dictionary<string, CallableSignature> paramMap,
        ResolverWalkMemos memos)
    {
        memos.Algorithms ??= new(ReferenceEqualityComparer.Instance);
        if (!memos.Algorithms.TryGetValue(alg, out var processed))
        {
            processed = ProcessAlgorithm(
                alg, paramMap, isRoot: false, memos.Observations, memos.Diagnostics, branchContext: null, memos.Run);
            memos.Algorithms[alg] = processed;
        }

        return processed;
    }

    /// <summary>
    /// Processes an argument bundle whose consumer is VALUE-DEMANDING: each
    /// slot is an ordinary value position, so bare references to callables
    /// with parameters lift to implicit calls exactly as they would in any
    /// other value position (binary operands, output rows). This is the
    /// deliberate counterpart of <see cref="ProcessArgumentBundle"/>:
    /// ordinary call arguments stay NEUTRAL (no lifting) because an arbitrary
    /// callee may consume an argument on the higher-order algorithm channel,
    /// and lifting would destroy the bare reference. Value-context processing
    /// is a property of the consumer, not of the argument.
    ///
    /// <para>The current value-demanding consumer is the Math member family in
    /// BOTH of its spellings — the written <c>Math.X(...)</c> dot shape
    /// (<see cref="AstHelpers.HasRegistryProvenStrictValueArguments(Expr.DotCall, Func{string, bool}?)"/>)
    /// and an unshadowed prelude-alias call
    /// (<see cref="AstHelpers.HasRegistryProvenStrictValueArguments(Expr.Call, Func{string, bool}?)"/>),
    /// which resolve to the same <see cref="MathCallableFacts"/>: the builtin registry proves every
    /// Math member consumes strictly numeric values, so no higher-order
    /// channel exists to preserve. Other strict builtins (<c>sum</c>,
    /// <c>count</c>, ...) do NOT currently receive value-context lifting —
    /// their unresolved-reference arguments surface as runtime errors instead
    /// (a documented consistency gap; widening lifting to them would be a new
    /// observable semantic surface and is deliberately left as future
    /// work).</para>
    ///
    /// <para><b>Value-demanding is WHERE lifting happens, never HOW.</b> The consumer's
    /// registry-proven strict-value contract decides only that these slots are value
    /// positions; the rewriting itself must then be the ordinary one, under the ENCLOSING
    /// algorithm's <see cref="ImplicitRewriteContext"/> — the same caller parameter patterns,
    /// the same source binding kinds, and the same closed-explicit-list gate as the rows
    /// around the Math call. This method therefore forwards <paramref name="context"/>
    /// unchanged and holds no configuration of its own. Erasing it (as an earlier revision
    /// did, to let a region's value-demanding memo entries unify) made a semantically neutral
    /// <c>Math.Abs(...)</c> wrapper change elaboration: forwarding spread was decided from the
    /// CALLEE's kind, forwarded under the CALLEE's capture name, and a closed explicit
    /// parameter list silently acquired an ancestor's parameter.</para>
    /// </summary>
    private static OutputBundle ProcessValueDemandingArgumentBundle(
        OutputBundle args,
        Dictionary<string, CallableSignature> paramMap,
        ImplicitRewriteContext context,
        ResolverWalkMemos memos)
    {
        var rewritten = new List<Expr>(args.Count);
        foreach (var argExpr in args)
            rewritten.Add(RewriteImplicitCalls(
                argExpr, paramMap, context, inCallPosition: false, memos, inStrictValueDemand: true));

        return new OutputBundle(rewritten);
    }

    private static bool TryGetBareBuiltinCallableSignature(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out string? callableKey,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out CallableSignature? signature)
    {
        // `Math~.Pow` reaches this same structural arm: its ordinary receiver
        // Grace is consumed by parameter detection before implicit-call
        // rewriting, so Grace cannot change registry facts. The bare reference
        // is the argumentless canonical shape, classified by the shared helper.
        if (expr is Expr.DotCall { Args: null } dotCall
            && dotCall.TryGetRegistryProvenCanonicalMathFacts(paramMap.ContainsKey, out var facts)
            && facts.Signature.Parameters.Count > 0)
        {
            // The canonical spelling and its prelude alias use the SAME
            // descriptor-projected identity and signature. Do not reconstruct
            // the key from text here: that would create a second convention
            // capable of drifting from MathCallableFacts.CanonicalKey.
            callableKey = facts.CanonicalKey;
            signature = facts.Signature;
            return true;
        }

        callableKey = null;
        signature = null;
        return false;
    }

    /// <summary>
    /// Processes an expression in a transparent context (capture rows, list
    /// elements, argument slots): recurse into nested algorithms only (no
    /// lifting at this level).
    /// </summary>
    private static Expr ProcessExprNested(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        ResolverWalkMemos memos)
    {
        // DAG-safety: one rewrite per shared node reference per region's transparent
        // context; the memo returns the same rewritten node for every later reach.
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
        Dictionary<string, CallableSignature> paramMap,
        ResolverWalkMemos memos)
    {
        return expr switch
        {
            Expr.AlgorithmExpr(var alg) => new Expr.AlgorithmExpr(
                ProcessSharedNestedAlgorithm(alg, paramMap, memos)) { Span = expr.Span },
            Expr.Capture(var captureBody) => new Expr.Capture(new OutputBundle(
                captureBody.Select(row => ProcessExprNested(row, paramMap, memos)).ToList()))
            { Span = expr.Span },
            Expr.Call(var func, var args) => new Expr.Call(
                ProcessExprNested(func, paramMap, memos),
                ProcessArgumentBundle(args, paramMap, memos)) { Span = expr.Span },
            Expr.Binary(var op, var l, var r) => new Expr.Binary(op,
                ProcessExprNested(l, paramMap, memos),
                ProcessExprNested(r, paramMap, memos)) { Span = expr.Span },
            Expr.Unary(var op, var operand) => new Expr.Unary(op,
                ProcessExprNested(operand, paramMap, memos)) { Span = expr.Span },
            Expr.Index(var t, var s) => new Expr.Index(
                ProcessExprNested(t, paramMap, memos),
                ProcessExprNested(s, paramMap, memos)) { Span = expr.Span },
            Expr.SequenceSpread(var operand) => new Expr.SequenceSpread(
                ProcessExprNested(operand, paramMap, memos))
            {
                Span = expr.Span,
                SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
            },
            Expr.SequenceConstruct(var l, var r) => new Expr.SequenceConstruct(
                ProcessExprNested(l, paramMap, memos),
                ProcessExprNested(r, paramMap, memos)) { Span = expr.Span },
            Expr.ListLiteral(var items) => new Expr.ListLiteral(
                items.Select(item => ProcessExprNested(item, paramMap, memos)).ToList())
            { Span = expr.Span },
            // `with` keeps the stored dot-edge facts (member span, lexical
            // fallback) — a positional rebuild here silently dropped the
            // elaborated fallback identity inside argument bundles, capture
            // rows, and list elements.
            Expr.DotCall dotCall => dotCall with
            {
                Target = ProcessExprNested(dotCall.Target, paramMap, memos),
                Args = dotCall.Args is { } da ? ProcessArgumentBundle(da, paramMap, memos) : null,
            },
            Expr.Grace(var inner, _) => ProcessExprNested(inner, paramMap, memos),
            // Intentional leaves: bare references stay bare in transparent
            // contexts (no lifting at this level, so higher-order references
            // such as Apply(Increment) survive), and literals carry nothing to
            // process.
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral
                or Expr.EmptySequence or Expr.NativeCall => expr,
            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently skipping
            // nested-algorithm processing.
            _ => throw new InvalidOperationException(
                $"Unhandled Expr variant in {nameof(ImplicitArgumentResolver)}.{nameof(ProcessExprNested)}: {expr.GetType().Name}. " +
                "Classify the new variant explicitly as a recursive rewrite case or an intentional leaf."),
        };
    }
}
