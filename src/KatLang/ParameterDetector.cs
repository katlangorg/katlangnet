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
        // point does not subsequently run PropertyExposureResolver. Its
        // returned tree's current exposure values are therefore the final
        // values a direct evaluator call will observe; release any suggestion
        // gates against that exact tree rather than leaving otherwise-valid
        // structural/open suggestions permanently pending.
        FinalPropertyExposure.MarkTreeFinal(detected.Root);
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
        FrontEndTraversalObservations? observations = null)
    {
        var diagnostics = new List<Diagnostic>();
        var preludeAlgorithm = hostOperations?.SemanticPreludeAlgorithm
            ?? BuiltinRegistry.CreateSemanticPreludeAlgorithm();
        FinalPropertyExposure.MarkTreeFinal(preludeAlgorithm);
        var preludeScope = ElaboratedScopeLookup.CreateScope(preludeAlgorithm, observations: observations);
        var processed = ProcessAlgorithm(
            root,
            preludeScope,
            capturedParamNames: [],
            diagnostics,
            observations);
        return (processed, diagnostics);
    }

    private static Algorithm ProcessAlgorithm(
        Algorithm alg,
        ElaboratedPropertyScope parentScope,
        HashSet<string> capturedParamNames,
        List<Diagnostic>? diagnostics = null,
        FrontEndTraversalObservations? observations = null)
    {
        if (alg is Algorithm.Builtin)
            return alg;

        if (alg is Algorithm.Conditional conditional)
            return ProcessConditionalProperty(
                conditional, "<anonymous>", parentScope, capturedParamNames, diagnostics, observations);

        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is already a
        // fully-formed elaboration leaf: an explicit N-capture sequence-value pattern, no
        // opens, no properties, and an output that is exactly the single bound target name.
        // Its only required elaboration is rewriting that bound Resolve to a Param. Running
        // it through the general path builds an O(N) param-name set, param-order list,
        // captured-name union, and MergeParameterPatterns per helper, so a wide
        // deconstruction is O(N^2) across its N sibling helpers. This leaf path is O(1) in
        // the capture count and produces the identical elaborated helper.
        if (alg is Algorithm.User { IsAssignmentDeconstructionHelper: true } deconstructionHelper)
            return RewriteAssignmentDeconstructionHelperOutput(deconstructionHelper);

        var newOpens = ProcessOpenExprs(alg.Opens, parentScope, diagnostics, observations);
        var algWithProcessedOpens = alg with { Opens = newOpens };
        var scope = ElaboratedScopeLookup.CreateScope(algWithProcessedOpens, parentScope);

        var paramNames = new HashSet<string>(alg.Params);
        var paramOrder = new List<string>(alg.Params);
        var graceWeights = new Dictionary<string, int>();
        var hasExplicitParameterList = alg.ExplicitParameterPatterns.Count > 0;

        // Ordinary nested algorithms close over already-known outer params.
        // These should rewrite to Expr.Param but must not become new local params.
        var boundNames = UnionNames(capturedParamNames, alg.Params);

        ImplicitParameterOccurrenceRecorder? provenanceRecorder = null;
        if (hasExplicitParameterList)
        {
            ReportUndeclaredExplicitParameterNames(alg.Output, scope, boundNames, diagnostics, observations);
        }
        else
        {
            provenanceRecorder = new ImplicitParameterOccurrenceRecorder(
                scope,
                alg.Params,
                capturedParamNames);
            CollectFreeParams(
                alg.Output, scope, boundNames, paramNames, paramOrder, graceWeights,
                FreeNameCollection.ImplicitSignature,
                provenanceRecorder,
                new FreeNameWalkMemo(observations));

            if (graceWeights.Count > 0)
                ApplyGraceReordering(paramOrder, graceWeights);
        }

        var nestedCapturedParamNames = UnionNames(capturedParamNames, paramOrder);

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
            if (prop.Value is Algorithm.Conditional condAlg)
            {
                newProperties.Add(prop.WithValue(ProcessConditionalProperty(
                    condAlg, prop.Name, scope, nestedCapturedParamNames, diagnostics, observations)));
            }
            else if (processedSharedValues is null)
            {
                newProperties.Add(prop.WithValue(ProcessAlgorithm(
                    prop.Value,
                    scope,
                    nestedCapturedParamNames,
                    diagnostics,
                    observations)));
            }
            else
            {
                if (!processedSharedValues.TryGetValue(prop.Value, out var processedBody))
                {
                    processedBody = ProcessAlgorithm(
                        prop.Value,
                        scope,
                        nestedCapturedParamNames,
                        diagnostics,
                        observations);
                    processedSharedValues[prop.Value] = processedBody;
                }

                newProperties.Add(prop.WithValue(processedBody));
            }
        }

        // Rewrite Resolve → Param for detected parameters. ONE reference memo spans all
        // output rows: they share this exact rewrite context, so a node shared between
        // rows (or reached twice within one row) rewrites once.
        var rewriteMemo = new RewriteWalkMemo(observations, diagnostics);
        var rewrittenOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
            rewrittenOutput.Add(RewriteParams(expr, paramNames, scope, capturedParamNames, rewriteMemo));

        return algWithProcessedOpens.WithParams(paramOrder, provenanceRecorder?.Provenance) with
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
        HashSet<string> capturedParamNames,
        List<Diagnostic>? diagnostics,
        FrontEndTraversalObservations? observations)
    {
        var newOpens = ProcessOpenExprs(condAlg.Opens, scope, diagnostics, observations);
        var processedConditional = condAlg with { Opens = newOpens };
        var branchParentScope = newOpens.Count == 0
            ? scope
            : ElaboratedScopeLookup.CreateScope(processedConditional, scope);

        // Process each conditional branch body with the full-input-specification rule:
        // - Pattern binder names are rewritten to Expr.Param (resolved via valEnv at runtime)
        // - NO other free identifiers become implicit parameters
        // - The branch body's Params list is empty (bindings come from pattern matching)
        var processedBranches = new List<CondBranch>(condAlg.Branches.Count);
        foreach (var branch in condAlg.Branches)
        {
            var binderNames = new HashSet<string>(branch.Pattern.BoundNames());
            var processedBody = ProcessConditionalBranchBody(
                branch.Body,
                branchParentScope,
                binderNames,
                propertyName,
                capturedParamNames,
                diagnostics,
                observations);
            processedBranches.Add(new CondBranch(branch.Pattern, processedBody));
        }

        return processedConditional with { Branches = processedBranches };
    }

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
        private readonly IReadOnlyCollection<string> _localParameterNames;
        private readonly IReadOnlyCollection<string> _capturedParameterNames;
        private Dictionary<string, ImplicitParameterProvenance>? _provenance;
        private int _suggestionAttempts;

        /// <summary>
        /// The statically known receiver algorithm while collecting inside a
        /// dot edge's member/fallback occurrence; null for bare-name
        /// occurrences and for receivers with no statically known algorithm.
        /// Save/restore via <see cref="EnterDotMemberContext"/> so nested
        /// (host-built) fallback shapes cannot leak the context.
        /// </summary>
        private Algorithm? _dotMemberReceiver;

        public ImplicitParameterOccurrenceRecorder(
            ElaboratedPropertyScope scope,
            IReadOnlyCollection<string> localParameterNames,
            IReadOnlyCollection<string> capturedParameterNames)
        {
            _scope = scope;
            _localParameterNames = localParameterNames;
            _capturedParameterNames = capturedParameterNames;
        }

        public IReadOnlyDictionary<string, ImplicitParameterProvenance>? Provenance => _provenance;

        public Algorithm? EnterDotMemberContext(Algorithm? knownReceiver)
        {
            var previous = _dotMemberReceiver;
            _dotMemberReceiver = knownReceiver;
            return previous;
        }

        public void ExitDotMemberContext(Algorithm? previous) => _dotMemberReceiver = previous;

        public void RecordFirstOccurrence(string name, Expr occurrence)
        {
            _provenance ??= new Dictionary<string, ImplicitParameterProvenance>(StringComparer.Ordinal);
            if (_provenance.ContainsKey(name))
                return;

            var suggestion = _suggestionAttempts++ < MaxSuggestionAttempts
                ? NameSuggestions.SuggestVisibleName(
                    name,
                    _scope,
                    _localParameterNames,
                    _capturedParameterNames,
                    _dotMemberReceiver)
                : null;
            _provenance[name] = new ImplicitParameterProvenance(name, occurrence.Span, suggestion);
        }
    }

    /// <summary>
    /// Reference-identity memo state for ONE <see cref="CollectFreeParams(IReadOnlyList{Expr}, ElaboratedPropertyScope, HashSet{string}, HashSet{string}, List{string}, Dictionary{string, int}, FreeNameCollection, ImplicitParameterOccurrenceRecorder?, FreeNameWalkMemo)"/>
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
    /// Reference-identity memo state for ONE detector rewrite region — a
    /// <see cref="RewriteParams(Expr, HashSet{string}, ElaboratedPropertyScope, HashSet{string}, RewriteWalkMemo)"/>
    /// walk over one algorithm's output rows, or a
    /// <see cref="RewriteBinderRefs(Expr, HashSet{string}, ElaboratedPropertyScope, HashSet{string}, RewriteWalkMemo)"/>
    /// walk over one conditional branch body. The rewrite context (name sets, scope) is constant
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
    private sealed class RewriteWalkMemo(FrontEndTraversalObservations? observations, List<Diagnostic>? diagnostics)
    {
        public readonly Dictionary<Expr, Expr> Rewrites = new(ReferenceEqualityComparer.Instance);

        public Dictionary<Algorithm, Algorithm>? Algorithms;

        public readonly FrontEndTraversalObservations? Observations = observations;

        public readonly List<Diagnostic>? Diagnostics = diagnostics;
    }

    /// <summary>
    /// Reference-identity memo state for ONE open-target region
    /// (<see cref="ProcessOpenExprs"/> over one algorithm's open list). The region runs two
    /// distinct walks over the same nodes — <see cref="ProcessOpenExpr(Expr, ElaboratedPropertyScope, List{Diagnostic}?, OpenWalkMemo)"/>
    /// (open-form rewriting) and <see cref="ProcessExpr(Expr, ElaboratedPropertyScope, HashSet{string}, OpenWalkMemo)"/>
    /// (transparent argument/capture rewriting) — with different results for the same node, so
    /// each keeps its own map; both contexts are constant for the region (the open-parent
    /// prelude scope, empty captured names, one diagnostics sink). The two algorithm maps stay
    /// separate for the same reason: the open walk elaborates nested algorithms WITH the
    /// diagnostics sink, the transparent walk without one.
    /// </summary>
    private sealed class OpenWalkMemo(FrontEndTraversalObservations? observations)
    {
        public readonly Dictionary<Expr, Expr> OpenRewrites = new(ReferenceEqualityComparer.Instance);

        public Dictionary<Expr, Expr>? TransparentRewrites;

        public Dictionary<Algorithm, Algorithm>? OpenAlgorithms;

        public Dictionary<Algorithm, Algorithm>? TransparentAlgorithms;

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
        FrontEndTraversalObservations? observations)
    {
        if (opens.Count == 0)
            return opens;

        // The detection's prelude scope is the chain root, since every chain of
        // this detection starts at the prelude scope DetectPrevalidated created.
        // Anchoring open-target processing on it (rather than allocating a second
        // prelude) also keeps the host-operation extended prelude — when one is
        // configured — in force for open targets.
        var openParentScope = parentScope.Root;
        var memo = new OpenWalkMemo(observations);
        var processed = new List<Expr>(opens.Count);
        foreach (var open in opens)
            processed.Add(ProcessOpenExpr(open, openParentScope, diagnostics, memo));
        return processed;
    }

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
        switch (expr)
        {
            case Expr.Grace(var gracedTarget, _):
                // An open target has no parameter inference to reorder, so a
                // grace annotation is meaningless here. The parser rejects and
                // unwraps written ones; a host-built tree is unwrapped the same
                // way so no Grace can survive elaboration in any position.
                return ProcessOpenExpr(gracedTarget, openParentScope, diagnostics, memo);

            case Expr.AlgorithmExpr(var algorithm):
            {
                memo.OpenAlgorithms ??= new(ReferenceEqualityComparer.Instance);
                if (!memo.OpenAlgorithms.TryGetValue(algorithm, out var processedAlgorithm))
                {
                    processedAlgorithm = ProcessAlgorithm(
                        algorithm, openParentScope, [], diagnostics, memo.Observations);
                    memo.OpenAlgorithms[algorithm] = processedAlgorithm;
                }

                return new Expr.AlgorithmExpr(processedAlgorithm) { Span = expr.Span };
            }

            case Expr.Capture(var captureBody):
                // A capture target owns no scope: its rows are processed in the
                // open-target parent scope (the pre-split transparent wrapper
                // added only an empty lookup level here).
                return new Expr.Capture(new OutputBundle(
                    captureBody.Select(row => ProcessExpr(row, openParentScope, [], memo)).ToList()))
                { Span = expr.Span };

            case Expr.DotCall dotCall:
                // `with` keeps the stored dot-edge facts (member span). Open
                // targets are ordinary structural paths, so the fallback
                // identity is inert here, but the detector is the
                // normalization owner: every DotCall it emits carries an
                // EXPLICIT fallback (null is only a host-construction
                // shorthand for Resolve(Name)).
                return dotCall with
                {
                    Target = ProcessOpenExpr(dotCall.Target, openParentScope, diagnostics, memo),
                    Args = dotCall.Args is { } dotArgs
                        ? new OutputBundle(dotArgs.Select(argExpr => ProcessExpr(argExpr, openParentScope, [], memo)).ToList())
                        : null,
                    LexicalFallback = ProcessOpenExpr(
                        dotCall.EffectiveLexicalFallback, openParentScope, diagnostics, memo),
                };

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    ProcessOpenExpr(operand, openParentScope, diagnostics, memo))
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    ProcessOpenExpr(left, openParentScope, diagnostics, memo),
                    ProcessOpenExpr(right, openParentScope, diagnostics, memo)) { Span = expr.Span };

            case Expr.ListLiteral(var items):
                return new Expr.ListLiteral(
                    items.Select(item => ProcessOpenExpr(item, openParentScope, diagnostics, memo)).ToList())
                { Span = expr.Span };

            case Expr.Call(var function, var args):
                return new Expr.Call(
                    ProcessOpenExpr(function, openParentScope, diagnostics, memo),
                    new OutputBundle(args.Select(argExpr => ProcessExpr(argExpr, openParentScope, [], memo)).ToList())) { Span = expr.Span };

            // Intentional leaves: name/literal leaves carry no nested algorithm
            // to process (a bare Resolve IS the ordinary open-target form), and
            // operator forms are never valid open targets — the evaluator's
            // open-form validation rejects them (BadOpenForm) — so a host-built
            // one passes through unprocessed like a leaf.
            case Expr.Resolve:
            case Expr.Param:
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
            case Expr.Unary:
            case Expr.Binary:
            case Expr.Index:
                return expr;

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above (recursive rewrite or
            // intentional leaf) rather than silently passing through.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ParameterDetector)}.{nameof(ProcessOpenExpr)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a recursive rewrite case or an intentional leaf.");
        }
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
        HashSet<string> capturedParamNames,
        List<Diagnostic>? diagnostics,
        FrontEndTraversalObservations? observations = null)
    {
        // A branch body owns its `open` list exactly like every other algorithm body, so its
        // targets are elaborated here — an inline open block's members get their own
        // parameter detection — and the body scope is created over the PROCESSED opens,
        // exactly as ProcessAlgorithm does for ordinary bodies.
        var newOpens = ProcessOpenExprs(body.Opens, parentScope, diagnostics, observations);
        var bodyWithProcessedOpens = body with { Opens = newOpens };
        var bodyScope = ElaboratedScopeLookup.CreateScope(bodyWithProcessedOpens, parentScope);

        var bodyCapturedParamNames = UnionNames(capturedParamNames, binderNames);

        // Detect free identifiers that would be implicit parameters — these are
        // forbidden in conditional branch bodies (full-input-specification rule).
        if (diagnostics is not null)
        {
            var freeNames = new HashSet<string>();
            var freeOrder = new List<string>();
            var dummyWeights = new Dictionary<string, int>();
            CollectFreeParams(
                body.Output,
                bodyScope,
                bodyCapturedParamNames,
                freeNames,
                freeOrder,
                dummyWeights,
                FreeNameCollection.DeclaredNameCheck,
                recorder: null,
                new FreeNameWalkMemo(observations));
            foreach (var freeName in freeOrder)
            {
                // Find the span for the first occurrence of this free identifier
                var span = FindResolveSpan(body.Output, freeName, new ResolveSpanSearchMemo(observations));
                diagnostics.Add(new Diagnostic(
                    FormatConditionalBranchUndeclaredIdentifier(freeName, branchName),
                    DiagnosticSeverity.Error,
                    span ?? new SourceSpan(0, 0, 0, 0))
                {
                    Code = DiagnosticCode.UndeclaredIdentifier,
                });
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
            if (prop.Value is Algorithm.Conditional nestedCondAlg)
            {
                processedProp = ProcessConditionalProperty(
                    nestedCondAlg, prop.Name, bodyScope, bodyCapturedParamNames, diagnostics, observations);
            }
            else if (processedSharedValues is null)
            {
                processedProp = ProcessAlgorithm(
                    prop.Value,
                    bodyScope,
                    bodyCapturedParamNames,
                    diagnostics,
                    observations);
            }
            else if (!processedSharedValues.TryGetValue(prop.Value, out processedProp!))
            {
                processedProp = ProcessAlgorithm(
                    prop.Value,
                    bodyScope,
                    bodyCapturedParamNames,
                    diagnostics,
                    observations);
                processedSharedValues[prop.Value] = processedProp;
            }

            newProperties.Add(prop.WithValue(processedProp));
        }

        // Rewrite only binder names Resolve → Param; leave all others as-is.
        // Process nested blocks/calls normally for their own parameter detection.
        // ONE reference memo spans the branch body's rows (constant rewrite context).
        var rewriteMemo = new RewriteWalkMemo(observations, diagnostics);
        var rewrittenOutput = new List<Expr>(body.Output.Count);
        foreach (var expr in body.Output)
            rewrittenOutput.Add(RewriteBinderRefs(expr, binderNames, bodyScope, capturedParamNames, rewriteMemo));

        return bodyWithProcessedOpens with
        {
            Parameters = [],  // No implicit params — bindings come from pattern matching
            Properties = newProperties,
            Output = rewrittenOutput,
        };
    }

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
        HashSet<string> boundNames,
        List<Diagnostic>? diagnostics,
        FrontEndTraversalObservations? observations = null)
    {
        if (diagnostics is null)
            return;

        var freeNames = new HashSet<string>();
        var freeOrder = new List<string>();
        var dummyWeights = new Dictionary<string, int>();
        CollectFreeParams(
            output, scope, boundNames, freeNames, freeOrder, dummyWeights,
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
    /// Rewrites <see cref="Expr.Resolve"/> → <see cref="Expr.Param"/> ONLY for pattern binder names.
    /// Other identifiers remain as <see cref="Expr.Resolve"/> (lexical lookup at runtime).
    /// Grace wrappers are stripped (they should not appear in conditional bodies, but handle gracefully).
    /// Nested algorithms are processed via <see cref="ProcessAlgorithm"/> for their own scope.
    /// </summary>
    private static Expr RewriteBinderRefs(
        Expr expr,
        HashSet<string> binderNames,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames,
        RewriteWalkMemo memo)
    {
        // A Resolve leaf may itself be replaced by a fresh Param, so it participates in the
        // rewrite memo even though it has no children; otherwise a shared input leaf would
        // become several output objects. Other childless leaves return themselves.
        var hasTraversableChildren = AstTraversalDagSafety.HasTraversableExprChildren(expr);
        if (!hasTraversableChildren && expr is not Expr.Resolve)
            return RewriteBinderRefsCore(expr, binderNames, scope, capturedParamNames, memo);

        if (memo.Rewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        if (hasTraversableChildren)
            memo.Observations?.RecordDetectorRewriteExpansion();
        rewritten = RewriteBinderRefsCore(expr, binderNames, scope, capturedParamNames, memo);
        memo.Rewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr RewriteBinderRefsCore(
        Expr expr,
        HashSet<string> binderNames,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames,
        RewriteWalkMemo memo)
    {
        switch (expr)
        {
            case Expr.Grace(var inner, _):
                // Grace in conditional branch body is a parse error (already reported).
                // Strip it here for error recovery so downstream processing doesn't crash.
                return RewriteBinderRefs(inner, binderNames, scope, capturedParamNames, memo);

            case Expr.Resolve(var name) when ShouldRewriteAsParam(name, binderNames, scope, capturedParamNames):
                return new Expr.Param(name) { Span = expr.Span };

            case Expr.Binary(var op, var left, var right):
                return new Expr.Binary(op,
                    RewriteBinderRefs(left, binderNames, scope, capturedParamNames, memo),
                    RewriteBinderRefs(right, binderNames, scope, capturedParamNames, memo)) { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op, RewriteBinderRefs(operand, binderNames, scope, capturedParamNames, memo)) { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    RewriteBinderRefs(target, binderNames, scope, capturedParamNames, memo),
                    RewriteBinderRefs(selector, binderNames, scope, capturedParamNames, memo)) { Span = expr.Span };

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    RewriteBinderRefs(operand, binderNames, scope, capturedParamNames, memo))
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    RewriteBinderRefs(left, binderNames, scope, capturedParamNames, memo),
                    RewriteBinderRefs(right, binderNames, scope, capturedParamNames, memo)) { Span = expr.Span };

            case Expr.ListLiteral(var items):
                return new Expr.ListLiteral(
                    items.Select(item => RewriteBinderRefs(item, binderNames, scope, capturedParamNames, memo)).ToList())
                { Span = expr.Span };

            case Expr.DotCall dotCall:
            {
                // Argument bundles own no scope: slots rewrite in the enclosing
                // binder scope, exactly like capture rows. The stored
                // lexical-fallback identity rewrites by the SAME rule as a bare
                // callee name (Resolve → Param when the member is a known
                // binder).
                OutputBundle? rewrittenArgs = null;
                if (dotCall.Args is { } dotArgs)
                {
                    var rewrittenSlots = new List<Expr>(dotArgs.Count);
                    foreach (var argExpr in dotArgs)
                        rewrittenSlots.Add(RewriteBinderRefs(argExpr, binderNames, scope, capturedParamNames, memo));
                    rewrittenArgs = new OutputBundle(rewrittenSlots);
                }

                return dotCall with
                {
                    Target = RewriteBinderRefs(dotCall.Target, binderNames, scope, capturedParamNames, memo),
                    Args = rewrittenArgs,
                    LexicalFallback = RewriteBinderRefs(dotCall.EffectiveLexicalFallback, binderNames, scope, capturedParamNames, memo),
                };
            }

            case Expr.AlgorithmExpr(var alg):
            {
                memo.Algorithms ??= new(ReferenceEqualityComparer.Instance);
                if (!memo.Algorithms.TryGetValue(alg, out var processedAlg))
                {
                    processedAlg = ProcessAlgorithm(
                        alg, scope, UnionNames(capturedParamNames, binderNames), memo.Diagnostics, memo.Observations);
                    memo.Algorithms[alg] = processedAlg;
                }

                return new Expr.AlgorithmExpr(processedAlg) { Span = expr.Span };
            }

            case Expr.Capture(var captureBody):
                {
                    // Captures are transparent: rows rewrite in the enclosing
                    // binder scope (no scope of their own, no properties).
                    var rewrittenRows = new List<Expr>(captureBody.Count);
                    foreach (var row in captureBody)
                        rewrittenRows.Add(RewriteBinderRefs(row, binderNames, scope, capturedParamNames, memo));
                    return new Expr.Capture(new OutputBundle(rewrittenRows)) { Span = expr.Span };
                }

            case Expr.Call(var func, var args):
            {
                // Argument bundles own no scope: slots rewrite in the enclosing
                // binder scope.
                var rewrittenArgs = new List<Expr>(args.Count);
                foreach (var argExpr in args)
                    rewrittenArgs.Add(RewriteBinderRefs(argExpr, binderNames, scope, capturedParamNames, memo));
                return new Expr.Call(
                    RewriteBinderRefs(func, binderNames, scope, capturedParamNames, memo),
                    new OutputBundle(rewrittenArgs)) { Span = expr.Span };
            }

            // Intentional leaves: a Resolve that failed the guarded binder test
            // above stays an ordinary lexical reference, and the remaining
            // leaves contain no binder references to rewrite.
            case Expr.Resolve:
            case Expr.Param:
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                return expr;

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently keeping
            // binder references inside it unrewritten.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ParameterDetector)}.{nameof(RewriteBinderRefs)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a recursive rewrite case or an intentional leaf.");
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
        HashSet<string> extraBoundNames,
        HashSet<string> paramNames,
        List<string> paramOrder,
        Dictionary<string, int> graceWeights,
        FreeNameCollection mode,
        ImplicitParameterOccurrenceRecorder? recorder,
        FreeNameWalkMemo memo)
    {
        foreach (var expr in exprs)
            CollectFreeParams(expr, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
    }

    private static void CollectFreeParams(
        Expr expr,
        ElaboratedPropertyScope scope,
        HashSet<string> extraBoundNames,
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
            CollectFreeParamsCore(expr, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
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
        CollectFreeParamsCore(expr, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
        var completedVector = memo.OpenSlots[slotIndex];
        memo.OpenSlots.RemoveAt(slotIndex);
        memo.CompletedVectors[expr] = completedVector;
    }

    private static void CollectFreeParamsCore(
        Expr expr,
        ElaboratedPropertyScope scope,
        HashSet<string> extraBoundNames,
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
                    if (!IsBoundName(gracedName, scope, extraBoundNames) && gracedName.Length > 0)
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
                    CollectFreeParams(gracedCore, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                }

                break;
            }

            case Expr.Resolve(var name):
                if (!IsBoundName(name, scope, extraBoundNames) && name.Length > 0)
                {
                    if (paramNames.Add(name))
                    {
                        paramOrder.Add(name);
                        recorder?.RecordFirstOccurrence(name, expr);
                    }
                }
                break;

            case Expr.Binary(_, var left, var right):
                CollectFreeParams(left, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                CollectFreeParams(right, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.Unary(_, var operand):
                CollectFreeParams(operand, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.Index(var target, var selector):
                CollectFreeParams(target, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                CollectFreeParams(selector, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.SequenceSpread(var operand):
                CollectFreeParams(operand, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectFreeParams(left, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                CollectFreeParams(right, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.ListLiteral(var items):
                // List-literal elements are transparent to the enclosing
                // parameter scope, like spread operands and sequence joins.
                foreach (var item in items)
                    CollectFreeParams(item, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
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
                CollectFreeParams(dotCall.Target, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);

                // A statically impossible fallback — a guaranteed structural
                // member, a conditional-branch member (a local-only ERROR at
                // runtime, never a fallback), or the dot-only `string`
                // intrinsic — contributes no member occurrence. The
                // DeclaredNameCheck mode likewise takes no fallback
                // contribution because a conditional fallback is not a
                // definite dependency (see FreeNameCollection).
                if (mode == FreeNameCollection.ImplicitSignature)
                {
                    var receiverProvider = ResolveDotCallReceiverProvider(dotCall, scope, extraBoundNames);
                    if (dotCall.GetLexicalFallbackSelection(receiverProvider) != LexicalFallbackSelection.Never)
                    {
                        // While collecting the member/fallback occurrence, the
                        // recorder knows the receiver's statically known
                        // algorithm (when there is one) so a provenance note
                        // recorded here can rank the receiver's structural
                        // members as suggestion candidates. Diagnostic-only:
                        // the collection itself is unchanged.
                        var previousReceiver = recorder?.EnterDotMemberContext(
                            receiverProvider.Kind == StaticStructuralMemberProviderKind.KnownAlgorithm
                                ? receiverProvider.Algorithm
                                : null);
                        CollectFreeParams(dotCall.EffectiveLexicalFallback, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                        recorder?.ExitDotMemberContext(previousReceiver);
                    }
                }
                if (dotCall.Args is { } dotArgs)
                    CollectFreeParams(dotArgs, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.Capture(var captureBody):
                // Captures are transparent: free identifiers bubble up to the
                // enclosing param scope.
                CollectFreeParams(captureBody, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                break;

            case Expr.AlgorithmExpr:
                // Scope-owning algorithm expressions own their names — don't collect.
                break;

            case Expr.Call(var func, var args):
                CollectFreeParams(func, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
                // Argument bundles are transparent: free identifiers inside
                // argument slots belong to the enclosing algorithm. (A brace
                // block argument is an AlgorithmExpr slot and owns its names.)
                CollectFreeParams(args, scope, extraBoundNames, paramNames, paramOrder, graceWeights, mode, recorder, memo);
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

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently
            // contributing no free names (which would silently change the
            // inferred implicit-parameter signature).
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
    /// shared MAY-selection law to it. The receiver's
    /// provider mirrors the receiver occurrence's own elaboration fate:
    /// a name that will elaborate to a parameter (unbound and therefore
    /// inferred, or a known parameter name not shadowed by a visible
    /// non-prelude property — the <see cref="ShouldRewriteAsParam"/>
    /// decision) is a runtime value; a name resolving to exactly one visible
    /// property is that property's statically known algorithm; an ambiguous
    /// name stays an unresolved reference. The Never/Conditional/Always
    /// mapping itself is the shared
    /// <see cref="AstHelpers.GetLexicalFallbackSelection"/> law — this
    /// method only supplies the detector's resolution power, exactly like
    /// the editor's provider resolution.
    /// </summary>
    private static StaticStructuralMemberProvider ResolveDotCallReceiverProvider(
        Expr.DotCall dotCall,
        ElaboratedPropertyScope scope,
        HashSet<string> extraBoundNames)
    {
        var receiver = dotCall.Target.UnwrapGraceOperand();
        var provider = receiver.GetStaticStructuralMemberProvider();
        if (provider.Kind == StaticStructuralMemberProviderKind.LexicalReference
            && receiver is Expr.Resolve(var receiverName))
        {
            provider = ResolveReceiverNameProvider(receiverName, scope, extraBoundNames);
        }

        return provider;
    }

    private static StaticStructuralMemberProvider ResolveReceiverNameProvider(
        string name,
        ElaboratedPropertyScope scope,
        HashSet<string> extraBoundNames)
    {
        if (!IsBoundName(name, scope, extraBoundNames)
            || (extraBoundNames.Contains(name) && !HasVisibleNonPreludePropertyName(scope, name)))
        {
            return new(StaticStructuralMemberProviderKind.RuntimeParameter);
        }

        var hits = ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope, name);
        return hits.Count == 1
            ? new(StaticStructuralMemberProviderKind.KnownAlgorithm, hits[0].Property.Value)
            : new(StaticStructuralMemberProviderKind.LexicalReference);
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

    private static HashSet<string> UnionNames(HashSet<string> baseNames, IEnumerable<string> extraNames)
    {
        var names = new HashSet<string>(baseNames);
        foreach (var extraName in extraNames)
            names.Add(extraName);
        return names;
    }

    private static bool ShouldRewriteAsParam(
        string name,
        HashSet<string> localParamNames,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames)
        => localParamNames.Contains(name)
            || (capturedParamNames.Contains(name) && !HasVisibleNonPreludePropertyName(scope, name));

    /// <summary>
    /// Rewrites <see cref="Expr.Resolve"/> to <see cref="Expr.Param"/> for detected parameter names.
    /// Also recursively processes nested algorithms.
    /// </summary>
    private static Expr RewriteParams(
        Expr expr,
        HashSet<string> paramNames,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames,
        RewriteWalkMemo memo)
    {
        // Resolve leaves can rewrite to newly allocated Params and therefore must be memoized
        // to preserve leaf sharing. Other childless leaves return themselves unchanged.
        var hasTraversableChildren = AstTraversalDagSafety.HasTraversableExprChildren(expr);
        if (!hasTraversableChildren && expr is not Expr.Resolve)
            return RewriteParamsCore(expr, paramNames, scope, capturedParamNames, memo);

        if (memo.Rewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        if (hasTraversableChildren)
            memo.Observations?.RecordDetectorRewriteExpansion();
        rewritten = RewriteParamsCore(expr, paramNames, scope, capturedParamNames, memo);
        memo.Rewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr RewriteParamsCore(
        Expr expr,
        HashSet<string> paramNames,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames,
        RewriteWalkMemo memo)
    {
        switch (expr)
        {
            case Expr.Grace(var inner, _):
                // Strip Grace wrapper — weight has been consumed during collection
                return RewriteParams(inner, paramNames, scope, capturedParamNames, memo);

            case Expr.Resolve(var name) when ShouldRewriteAsParam(name, paramNames, scope, capturedParamNames):
                return new Expr.Param(name) { Span = expr.Span };

            case Expr.Binary(var op, var left, var right):
                return new Expr.Binary(op,
                    RewriteParams(left, paramNames, scope, capturedParamNames, memo),
                    RewriteParams(right, paramNames, scope, capturedParamNames, memo)) { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op, RewriteParams(operand, paramNames, scope, capturedParamNames, memo)) { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    RewriteParams(target, paramNames, scope, capturedParamNames, memo),
                    RewriteParams(selector, paramNames, scope, capturedParamNames, memo)) { Span = expr.Span };

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    RewriteParams(operand, paramNames, scope, capturedParamNames, memo))
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    RewriteParams(left, paramNames, scope, capturedParamNames, memo),
                    RewriteParams(right, paramNames, scope, capturedParamNames, memo)) { Span = expr.Span };

            case Expr.ListLiteral(var items):
                return new Expr.ListLiteral(
                    items.Select(item => RewriteParams(item, paramNames, scope, capturedParamNames, memo)).ToList())
                { Span = expr.Span };

            case Expr.DotCall dotCall:
            {
                // Argument bundles own no scope: slots rewrite in the enclosing
                // param context. The stored lexical-fallback identity rewrites
                // by the SAME rule as a bare callee name (Resolve → Param when
                // the member is a known local or captured parameter) —
                // including a fallback name the collection itself just
                // inferred because the fallback may be selected at runtime.
                OutputBundle? rewrittenArgs = null;
                if (dotCall.Args is { } dotArgs)
                {
                    var rewrittenSlots = new List<Expr>(dotArgs.Count);
                    foreach (var argExpr in dotArgs)
                        rewrittenSlots.Add(RewriteParams(argExpr, paramNames, scope, capturedParamNames, memo));
                    rewrittenArgs = new OutputBundle(rewrittenSlots);
                }

                return dotCall with
                {
                    Target = RewriteParams(dotCall.Target, paramNames, scope, capturedParamNames, memo),
                    Args = rewrittenArgs,
                    LexicalFallback = RewriteParams(dotCall.EffectiveLexicalFallback, paramNames, scope, capturedParamNames, memo),
                };
            }

            case Expr.AlgorithmExpr(var alg):
            {
                memo.Algorithms ??= new(ReferenceEqualityComparer.Instance);
                if (!memo.Algorithms.TryGetValue(alg, out var processedAlg))
                {
                    processedAlg = ProcessAlgorithm(
                        alg, scope, UnionNames(capturedParamNames, paramNames), memo.Diagnostics, memo.Observations);
                    memo.Algorithms[alg] = processedAlg;
                }

                return new Expr.AlgorithmExpr(processedAlg) { Span = expr.Span };
            }

            case Expr.Capture(var captureBody):
                {
                    // Captures are transparent: rewrite rows in the enclosing param scope.
                    var rewrittenRows = new List<Expr>(captureBody.Count);
                    foreach (var row in captureBody)
                        rewrittenRows.Add(RewriteParams(row, paramNames, scope, capturedParamNames, memo));
                    return new Expr.Capture(new OutputBundle(rewrittenRows)) { Span = expr.Span };
                }

            case Expr.Call(var func, var args):
            {
                // Argument bundles own no scope: slots rewrite in the enclosing
                // param context. (A brace block argument is an AlgorithmExpr
                // slot and processes as an independent algorithm.)
                var rewrittenArgs = new List<Expr>(args.Count);
                foreach (var argExpr in args)
                    rewrittenArgs.Add(RewriteParams(argExpr, paramNames, scope, capturedParamNames, memo));
                return new Expr.Call(
                    RewriteParams(func, paramNames, scope, capturedParamNames, memo),
                    new OutputBundle(rewrittenArgs)) { Span = expr.Span };
            }

            // Intentional leaves: a Resolve that failed the guarded parameter
            // test above stays an ordinary lexical reference, and the
            // remaining leaves contain no parameter references to rewrite.
            case Expr.Resolve:
            case Expr.Param:
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                return expr;

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently keeping
            // detected parameter references inside it unrewritten.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ParameterDetector)}.{nameof(RewriteParams)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a recursive rewrite case or an intentional leaf.");
        }
    }

    /// <summary>
    /// Processes an expression in a transparent context (capture rows, list elements,
    /// argument slots): just recurse into nested algorithms.
    /// </summary>
    private static Expr ProcessExpr(
        Expr expr,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames,
        OpenWalkMemo memo)
    {
        // DAG-safety: one rewrite per shared node reference per open-target region. The
        // transparent walk keeps its own map — the same node can also be reached by
        // ProcessOpenExpr, whose open-form rewriting legitimately differs.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return ProcessExprCore(expr, scope, capturedParamNames, memo);

        memo.TransparentRewrites ??= new(ReferenceEqualityComparer.Instance);
        if (memo.TransparentRewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        memo.Observations?.RecordDetectorRewriteExpansion();
        rewritten = ProcessExprCore(expr, scope, capturedParamNames, memo);
        memo.TransparentRewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr ProcessExprCore(
        Expr expr,
        ElaboratedPropertyScope scope,
        HashSet<string> capturedParamNames,
        OpenWalkMemo memo)
    {
        return expr switch
        {
            Expr.Grace(var inner, _) => ProcessExpr(inner, scope, capturedParamNames, memo),
            Expr.AlgorithmExpr(var alg) => new Expr.AlgorithmExpr(
                ProcessSharedTransparentAlgorithm(alg, scope, capturedParamNames, memo)) { Span = expr.Span },
            Expr.Capture(var captureBody) => new Expr.Capture(new OutputBundle(
                captureBody.Select(row => ProcessExpr(row, scope, capturedParamNames, memo)).ToList()))
            { Span = expr.Span },
            Expr.Call(var func, var args) => new Expr.Call(
                ProcessExpr(func, scope, capturedParamNames, memo),
                new OutputBundle(args.Select(argExpr => ProcessExpr(argExpr, scope, capturedParamNames, memo)).ToList())) { Span = expr.Span },
            Expr.Binary(var op, var l, var r) => new Expr.Binary(op,
                ProcessExpr(l, scope, capturedParamNames, memo),
                ProcessExpr(r, scope, capturedParamNames, memo)) { Span = expr.Span },
            Expr.Unary(var op, var operand) => new Expr.Unary(op,
                ProcessExpr(operand, scope, capturedParamNames, memo)) { Span = expr.Span },
            Expr.Index(var t, var s) => new Expr.Index(
                ProcessExpr(t, scope, capturedParamNames, memo),
                ProcessExpr(s, scope, capturedParamNames, memo)) { Span = expr.Span },
            Expr.SequenceSpread(var operand) => new Expr.SequenceSpread(
                ProcessExpr(operand, scope, capturedParamNames, memo))
            {
                Span = expr.Span,
                SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
            },
            Expr.SequenceConstruct(var l, var r) => new Expr.SequenceConstruct(
                ProcessExpr(l, scope, capturedParamNames, memo),
                ProcessExpr(r, scope, capturedParamNames, memo)) { Span = expr.Span },
            Expr.ListLiteral(var items) => new Expr.ListLiteral(
                items.Select(item => ProcessExpr(item, scope, capturedParamNames, memo)).ToList())
            { Span = expr.Span },
            // The detector is the normalization owner: every DotCall it emits
            // carries an EXPLICIT fallback identity (null is only a
            // host-construction shorthand for Resolve(Name)).
            Expr.DotCall dotCall => dotCall with
            {
                Target = ProcessExpr(dotCall.Target, scope, capturedParamNames, memo),
                Args = dotCall.Args is { } da
                    ? new OutputBundle(da.Select(argExpr => ProcessExpr(argExpr, scope, capturedParamNames, memo)).ToList())
                    : null,
                LexicalFallback = ProcessExpr(
                    dotCall.EffectiveLexicalFallback, scope, capturedParamNames, memo),
            },
            // Intentional leaves: bare references and literals rewrite nothing
            // in a transparent context (parameter classification happened in
            // the owning algorithm's collection walk).
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral
                or Expr.EmptySequence or Expr.NativeCall => expr,
            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently skipping
            // nested-algorithm processing.
            _ => throw new InvalidOperationException(
                $"Unhandled Expr variant in {nameof(ParameterDetector)}.{nameof(ProcessExpr)}: {expr.GetType().Name}. " +
                "Classify the new variant explicitly as a recursive rewrite case or an intentional leaf."),
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
        HashSet<string> capturedParamNames,
        OpenWalkMemo memo)
    {
        memo.TransparentAlgorithms ??= new(ReferenceEqualityComparer.Instance);
        if (!memo.TransparentAlgorithms.TryGetValue(alg, out var processed))
        {
            processed = ProcessAlgorithm(alg, scope, capturedParamNames, diagnostics: null, memo.Observations);
            memo.TransparentAlgorithms[alg] = processed;
        }

        return processed;
    }

    private static bool IsBoundName(
        string name,
        ElaboratedPropertyScope scope,
        HashSet<string> extraBoundNames)
        => extraBoundNames.Contains(name) || HasVisiblePropertyName(scope, name);

    private static bool HasVisiblePropertyName(ElaboratedPropertyScope scope, string name)
        => ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope, name).Count > 0;

    /// <summary>
    /// Whether a visible property hit can shadow a captured ancestor PARAMETER
    /// of the same name. Only a NON-PRELUDE hit can: the prelude is the scope
    /// chain's root (<see cref="ElaboratedPropertyScope.Root"/>), always FARTHER than
    /// any capturing algorithm's parameter, so ownership-first resolution
    /// selects the parameter over every prelude property — builtins and the
    /// prelude's <see cref="Algorithm.User"/>-valued members (<c>Math</c>, host
    /// operations, and the Math member aliases such as <c>sin</c> and
    /// <c>pi</c>) uniformly. <c>F(pi) = {pi + 1}</c> therefore binds the
    /// parameter, not <c>Math.Pi</c>. The first direct hit in the
    /// ownership-first walk decides (mirroring
    /// <see cref="ElaboratedScopeLookup.LookupLexicalPropertyMatches"/>); a
    /// direct hit at any nearer level, and any open-provided hit, may win at
    /// runtime and keeps the name a lexical reference.
    /// </summary>
    private static bool HasVisibleNonPreludePropertyName(ElaboratedPropertyScope scope, string name)
    {
        if (ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, name) is { } directHit)
        {
            var preludeScope = scope.Root;
            return preludeScope.Properties.Count == 0
                || !ReferenceEquals(directHit.Owner, preludeScope.Properties[0].Owner);
        }

        return ElaboratedScopeLookup.LookupOpenPropertyMatches(scope, name).Count > 0;
    }

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
            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently reporting
            // "no occurrence" for identifiers written inside it.
            _ => throw new InvalidOperationException(
                $"Unhandled Expr variant in {nameof(ParameterDetector)}.{nameof(FindResolveSpan)}: {expr.GetType().Name}. " +
                "Classify the new variant explicitly as a searched case or an intentional miss."),
        };
    }
}
