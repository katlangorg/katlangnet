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
        FrontEndTraversalObservations? observations = null)
    {
        return ProcessAlgorithm(
            root, parentParamMap: new Dictionary<string, CallableSignature>(), isRoot: true, observations);
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
        IReadOnlySet<string>? ExistingParameterNames);

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
    /// shared in the output.
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
    private sealed class ResolverWalkMemos(FrontEndTraversalObservations? observations)
    {
        private ImplicitRewriteContext? _pinnedRewriteContext;

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

        public readonly FrontEndTraversalObservations? Observations = observations;

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
    /// then collects implicit deps and rewrites the algorithm's own output.
    /// </summary>
    private static Algorithm ProcessAlgorithm(
        Algorithm alg,
        Dictionary<string, CallableSignature> parentParamMap,
        bool isRoot = false,
        FrontEndTraversalObservations? observations = null)
    {
        if (alg is Algorithm.Builtin)
            return alg;

        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is a fully-elaborated
        // leaf: its output is a single bound Param (rewritten by ParameterDetector), it has no
        // properties or opens, and its explicit N-capture pattern lifts nothing. The general path
        // would still build an O(N) existing-parameter set and source-binding-kind map per helper —
        // O(N^2) across a wide deconstruction's N helpers — only to rewrite an output that has no
        // implicit calls. Returning it unchanged is O(1) and identical.
        if (alg is Algorithm.User { IsAssignmentDeconstructionHelper: true })
            return alg;

        var newOpens = ProcessOpenExprs(alg.Opens, observations);

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

            if (prop.Value is Algorithm.Conditional condAlg)
            {
                // Process each conditional branch body
                var processedBranches = new List<CondBranch>(condAlg.Branches.Count);
                foreach (var branch in condAlg.Branches)
                {
                    var processedBody = ProcessAlgorithm(branch.Body, visibleParamMap, isRoot: false, observations);
                    processedBranches.Add(new CondBranch(branch.Pattern, processedBody));
                }
                var processedCond = new Algorithm.Conditional(
                    condAlg.Parent, condAlg.Opens, processedBranches);
                processedProperties[idx] = prop.WithValue(processedCond);
            }
            else
            {
                // NOTE: property VALUES are deliberately NOT reference-deduplicated in this
                // pass (unlike ParameterDetector's property loop): visibleParamMap is UPDATED
                // after each processed property, so two properties sharing one value algorithm
                // may legitimately observe different sibling signatures. See the front-end
                // DAG-safety notes in SEMANTIC-ALIGNMENT.md for the residual complexity this
                // leaves on shared property values.
                var processedBody = ProcessAlgorithm(prop.Value, visibleParamMap, isRoot: false, observations);

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
        var walkMemos = new ResolverWalkMemos(observations);

        if (alg.ExplicitParameterPatterns.Count > 0)
        {
            var explicitExistingParams = new HashSet<string>(alg.Params);
            var explicitContext = new ImplicitRewriteContext(
                alg.ParameterPatterns,
                BuildSourceBindingKinds(alg.ParameterPatterns),
                RequireExistingParameters: true,
                explicitExistingParams);
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
        foreach (var expr in alg.Output)
        {
            if (ShouldPreserveBareRootResolve(expr, visibleParamMap, isRoot))
                continue;

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

        return alg.WithParameterPatterns(newPatterns) with
        {
            Opens = newOpens,
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

    private static IReadOnlyList<Expr> ProcessOpenExprs(
        IReadOnlyList<Expr> opens,
        FrontEndTraversalObservations? observations)
    {
        if (opens.Count == 0)
            return opens;

        // One memo bundle per open-target region: every walk below runs with a fresh EMPTY
        // signature map, so the region's rewrite context is constant regardless of which
        // fresh map instance a call site allocates.
        var memos = new ResolverWalkMemos(observations);
        var processed = new List<Expr>(opens.Count);
        foreach (var open in opens)
            processed.Add(ProcessOpenExpr(open, memos));
        return processed;
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
    {
        if (CanForwardSingleCollectingStream(callerPatterns, calleePatterns))
            return true;

        foreach (var capture in ParameterPattern.FlattenCaptures(calleePatterns))
        {
            if (!existingParameterNames.Contains(capture.Name))
                return false;
        }

        return true;
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
    private static Expr RewriteImplicitCalls(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        ImplicitRewriteContext context,
        bool inCallPosition,
        ResolverWalkMemos memos)
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
            return RewriteImplicitCallsCore(expr, paramMap, context, inCallPosition, memos);

        var rewriteMap = memos.RewriteMapFor(inCallPosition);
        if (rewriteMap.TryGetValue(expr, out var rewritten))
            return rewritten;

        if (hasTraversableChildren)
            memos.Observations?.RecordResolverRewriteExpansion();
        rewritten = RewriteImplicitCallsCore(expr, paramMap, context, inCallPosition, memos);
        rewriteMap[expr] = rewritten;
        return rewritten;
    }

    private static Expr RewriteImplicitCallsCore(
        Expr expr,
        Dictionary<string, CallableSignature> paramMap,
        ImplicitRewriteContext context,
        bool inCallPosition,
        ResolverWalkMemos memos)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (!inCallPosition
                    && paramMap.TryGetValue(name, out var ps)
                    && ps.Parameters.Count > 0)
                {
                    if (ClosedListBlocksLifting(context, ps.ParameterPatterns))
                        return expr;

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
                        return expr;

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
                    RewriteImplicitCalls(left, paramMap, context, false, memos),
                    RewriteImplicitCalls(right, paramMap, context, false, memos)) { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op, RewriteImplicitCalls(operand, paramMap, context, false, memos)) { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    RewriteImplicitCalls(target, paramMap, context, false, memos),
                    RewriteImplicitCalls(selector, paramMap, context, false, memos)) { Span = expr.Span };

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    RewriteImplicitCalls(operand, paramMap, context, false, memos))
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    RewriteImplicitCalls(left, paramMap, context, false, memos),
                    RewriteImplicitCalls(right, paramMap, context, false, memos)) { Span = expr.Span };

            case Expr.ListLiteral(var listItems):
                return new Expr.ListLiteral(
                    listItems.Select(item => RewriteImplicitCalls(item, paramMap, context, false, memos)).ToList())
                { Span = expr.Span };

            case Expr.DotCall(var target, var name, null)
                when !inCallPosition
                    && TryGetBareBuiltinCallableSignature(expr, paramMap, out _, out var builtinSignature):
                if (ClosedListBlocksLifting(context, builtinSignature.ParameterPatterns))
                    return expr;

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
                return RewriteImplicitCalls(inner, paramMap, context, inCallPosition, memos);

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
            processed = ProcessAlgorithm(alg, paramMap, isRoot: false, memos.Observations);
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
            rewritten.Add(RewriteImplicitCalls(argExpr, paramMap, context, inCallPosition: false, memos));

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
