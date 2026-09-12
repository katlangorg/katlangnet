namespace KatLang;

internal static class PropertyExposureResolver
{
    internal sealed class AnalysisSummary
    {
        public static AnalysisSummary Empty { get; } = new([]);

        public AnalysisSummary(IEnumerable<string> requiredAncestorOwnedParameterNames)
        {
            RequiredAncestorOwnedParameterNames = new HashSet<string>(requiredAncestorOwnedParameterNames, StringComparer.Ordinal);
        }

        public HashSet<string> RequiredAncestorOwnedParameterNames { get; }

        public bool RequiresAncestorOwnedParameters => RequiredAncestorOwnedParameterNames.Count > 0;

        public bool SetEquals(AnalysisSummary other)
            => RequiredAncestorOwnedParameterNames.SetEquals(other.RequiredAncestorOwnedParameterNames);
    }

    /// <summary>
    /// Shared subtrees (acyclic DAGs) are legal and DAG-safe: exposure classification of a
    /// node referenced from several parents matches the equivalent duplicated tree (summary
    /// seeds are name SETS, so multiplicities never mattered), while the rewrite walk is
    /// reference-identity memoized per constant-context region — work is bounded by the
    /// DISTINCT reachable nodes per exposure round, never the number of root-to-node paths,
    /// and the rewritten output preserves sharing within a scope. Each round has one
    /// completed-summary memo (see <see cref="PropertyDependencyGraphBuilder.SummaryMemo"/>)
    /// plus per-region rewrite memos. Removing open providers can require another round
    /// to widen a provisional structural-winner proof; signatures are never reinferred.
    /// </summary>
    public static Algorithm Resolve(Algorithm root)
        => Resolve(root, observations: null);

    internal static Algorithm Resolve(Algorithm root, FrontEndTraversalObservations? observations)
        => ResolveInScope(root, new Dictionary<string, AnalysisSummary>(StringComparer.Ordinal),
            ElaboratedScopeLookup.CreateScope(BuiltinRegistry.CreateSemanticPreludeAlgorithm()), observations);

    private static Algorithm ResolveInScope(
        Algorithm root,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        ElaboratedPropertyScope parentScope,
        FrontEndTraversalObservations? observations)
    {
        while (true)
        {
            var run = new ExposureRun();
            root = ProcessAlgorithm(root, visiblePropertySummaries,
                new PropertyDependencyGraphBuilder.SummaryMemo(), observations, parentScope, run);
            // Exposure can remove an opened receiver, revealing a different ancestor
            // provider. Recheck Never proofs against the classified tree before trusting
            // them. Only widen proofs, never infer parameters or rewrite forwarding here:
            // each non-final round removes a Never proof or demotes an exported property.
            if (!run.FallbackWidened && !(run.ExposureChanged && run.HasOpens && run.HasNeverFallback))
                return root;
        }
    }

    private sealed class ExposureRun
    {
        public bool ExposureChanged;
        public bool FallbackWidened;
        public bool HasOpens;
        public bool HasNeverFallback;
        public readonly FallbackProofScan DeferredProofs = new();
    }

    // A deferred body's provisional capture summary needs revisiting only if it
    // contains a structural-winner proof. Keep ordinary load-only regions lazy;
    // scanning shared syntax is bounded by nodes, not paths through the DAG.
    private sealed class FallbackProofScan : AstWalker
    {
        private readonly Dictionary<Algorithm, bool> _algorithms = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<Expr, bool> _expressions = new(ReferenceEqualityComparer.Instance);
        private bool _found;
        protected override bool VisitsExplicitParameterDeclarations => false;

        public bool Contains(Algorithm algorithm)
        {
            _found = false;
            VisitAlgorithm(algorithm);
            return _found;
        }

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            if (_algorithms.TryGetValue(algorithm, out var found)) { _found |= found; return; }
            var outer = _found;
            _found = false;
            base.VisitAlgorithm(algorithm);
            _algorithms[algorithm] = _found;
            _found |= outer;
        }

        public override void VisitExpr(Expr expr)
        {
            if (_expressions.TryGetValue(expr, out var found)) { _found |= found; return; }
            var outer = _found;
            _found = expr is Expr.DotCall { ElaboratedFallbackSelection: LexicalFallbackSelection.Never } dot
                && !dot.UsesOrdinaryDotStringIntrinsic();
            base.VisitExpr(expr);
            _expressions[expr] = _found;
            _found |= outer;
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
    /// <see cref="Expr.Param"/> references, and neither is owned by the declaring body).
    /// Exported-ness is thus a fact about the property's VALUE — evaluable wherever the
    /// property can be reached — never about where the declaration is written. WHERE it can
    /// be reached from is decided structurally by lookup, not here: a conditional family
    /// exposes no structural members, so nothing declared in a branch body is reachable BY
    /// NAME from outside the conditional (the evaluator, the front-end lookup, the editor, and
    /// Lean all deny that at the family and report it as
    /// <see cref="PropertyExposure.LocalOnlyConditionalAlgorithm"/>, which is a family-level
    /// error reason this pass never assigns). Inside the branch — and on the algorithm channel,
    /// for anything the branch itself hands out — a branch declaration therefore behaves
    /// exactly like the same declaration in a parameterized body: a self-contained
    /// branch-local library is openable and dot-accessible by every body nested in the
    /// branch, while a binder-capturing member stays local-only for the same reason a
    /// parameter-capturing one does.
    /// </summary>
    private static PropertyExposure ClassifyDeclaredProperty(AnalysisSummary summary)
        => summary.RequiresAncestorOwnedParameters
            ? PropertyExposure.LocalOnlyCapturedAncestorParameters
            : PropertyExposure.Exported;

    /// <summary>
    /// Reference-identity memo state for ONE exposure rewrite region — one user algorithm's
    /// opens/output/property-value processing (the final visible summaries are fixed before
    /// any of it runs), or one conditional's open list. Shared expressions rewrite once and
    /// stay shared; <see cref="Algorithms"/> memoizes nested-algorithm processing (property
    /// values and <see cref="Expr.AlgorithmExpr"/> contents run under the identical context:
    /// the final summaries), so two properties or wrappers sharing ONE algorithm classify it
    /// once. The resolution-wide summary memo rides along so nested regions keep sharing
    /// completed summaries. Conditional BRANCH bodies go through the same
    /// <see cref="Algorithms"/> memo (M4): this pass reads nothing about a branch but its
    /// body and the region's final visible summaries — binder references already arrived
    /// as <see cref="Expr.Param"/>s from parameter detection — so a body shared by several
    /// families in one region is classified once and stays one rewritten object.
    /// </summary>
    private sealed class ExposureWalkMemos(
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations,
        ElaboratedPropertyScope scope,
        ExposureRun run)
    {
        public Dictionary<Expr, Expr>? Rewrites;

        public Dictionary<Algorithm, Algorithm>? Algorithms;

        public readonly PropertyDependencyGraphBuilder.SummaryMemo SummaryMemo = summaryMemo;

        public readonly FrontEndTraversalObservations? Observations = observations;

        public readonly ElaboratedPropertyScope Scope = scope;

        public readonly ExposureRun Run = run;
    }

    private static Algorithm ProcessAlgorithm(
        Algorithm algorithm,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations,
        ElaboratedPropertyScope parentScope,
        ExposureRun run)
        => algorithm switch
        {
            Algorithm.User user => ProcessUserAlgorithm(
                user,
                visiblePropertySummaries,
                summaryMemo,
                observations,
                parentScope,
                run),
            // A family reached outside any region (a host root, or a deferred branch's own
            // demand-time elaboration) opens a region of its own.
            Algorithm.Conditional conditional => ProcessConditionalAlgorithm(
                conditional,
                visiblePropertySummaries,
                new ExposureWalkMemos(summaryMemo, observations, parentScope, run)),
            _ => algorithm,
        };

    private static Algorithm ProcessUserAlgorithm(
        Algorithm.User algorithm,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations,
        ElaboratedPropertyScope parentScope,
        ExposureRun run)
    {
        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is a fully-elaborated
        // leaf: no properties, no opens, and an output that is exactly its own bound Param. It
        // captures no ancestor-owned parameter, so it needs no exposure rewriting. The general
        // path would still analyze and rewrite it per helper for no observable effect.
        if (algorithm is Algorithm.User { IsAssignmentDeconstructionHelper: true })
            return algorithm;

        observations?.RecordExposureAlgorithmExpansion();
        run.HasOpens |= algorithm.Opens.Count != 0;

        // The summary channel is the ONLY builder data this pass consumes: what ancestors own
        // is not an input to it (a captured parameter is reported by name regardless), so no
        // ancestor-owned or locally-owned name context is threaded here (M17).
        var summaryGraph = PropertyDependencyGraphBuilder.BuildSummaries(
            algorithm,
            summaryMemo,
            observations);

        var currentPropertySummaries = new Dictionary<string, AnalysisSummary>(StringComparer.Ordinal);
        foreach (var property in algorithm.Properties)
            currentPropertySummaries[property.Name] = AnalysisSummary.Empty;

        // The summary graph already centralizes the stable per-property seed facts:
        // direct required ancestor-owned names plus summary edges to visible names and sibling properties.
        // What still changes here is each property's accumulated RequiredAncestorOwnedParameterNames
        // after following sibling summary edges through the current local summary map. That closure can
        // be transitive or cyclic, including cases where nested local properties create summary-sibling
        // cycles even though the direct sibling dependency graph is empty, so the exposure pass still
        // needs a local least-fixed-point before rewriting children with the final visible summaries.
        while (true)
        {
            var visibleForChildren = MergeVisiblePropertySummaries(visiblePropertySummaries, currentPropertySummaries);
            var nextPropertySummaries = new Dictionary<string, AnalysisSummary>(StringComparer.Ordinal);
            for (var propertyIndex = 0; propertyIndex < algorithm.Properties.Count; propertyIndex++)
            {
                var property = algorithm.Properties[propertyIndex];
                nextPropertySummaries[property.Name] = SummarizePropertyDependencies(
                    summaryGraph,
                    propertyIndex,
                    visibleForChildren,
                    currentPropertySummaries);
            }

            if (SummariesEqual(currentPropertySummaries, nextPropertySummaries))
            {
                currentPropertySummaries = nextPropertySummaries;
                break;
            }

            currentPropertySummaries = nextPropertySummaries;
        }

        var finalVisiblePropertySummaries = MergeVisiblePropertySummaries(visiblePropertySummaries, currentPropertySummaries);
        // Properties and output share one lexical scope and summary context. Inline
        // open providers below have their own memo because they resolve at global scope.
        var memos = new ExposureWalkMemos(summaryMemo, observations,
            ElaboratedScopeLookup.CreateScope(algorithm, parentScope), run);
        var rewrittenProperties = new List<Property>(algorithm.Properties.Count);
        for (var propertyIndex = 0; propertyIndex < algorithm.Properties.Count; propertyIndex++)
        {
            var property = algorithm.Properties[propertyIndex];
            var rewrittenPropertyValue = ProcessSharedNestedAlgorithm(
                property.Value,
                finalVisiblePropertySummaries,
                memos);

            var exposure = ClassifyDeclaredProperty(currentPropertySummaries[property.Name]);
            run.ExposureChanged |= exposure != property.Exposure;

            var rewrittenProperty = new Property(property.Name, rewrittenPropertyValue, property.IsPublic, exposure)
            {
                DeclarationSpans = property.DeclarationSpans
            };
            // Suggestion collection runs before this authoritative pass. Record
            // the final classification against both the property record lookup
            // originally saw and the rewritten record returned to consumers.
            FinalPropertyExposure.Link(property, rewrittenProperty);
            FinalPropertyExposure.RecordIfTracked(property, exposure);
            FinalPropertyExposure.RecordIfTracked(rewrittenProperty, exposure);
            rewrittenProperties.Add(rewrittenProperty);
        }

        var rewrittenOpens = RewriteExprList(
            algorithm.Opens,
            finalVisiblePropertySummaries,
            new ExposureWalkMemos(summaryMemo, observations, parentScope.Root, run));
        var rewrittenOutput = RewriteExprList(
            algorithm.Output,
            finalVisiblePropertySummaries,
            memos);

        return algorithm with
        {
            Opens = rewrittenOpens,
            Properties = rewrittenProperties,
            Output = OutputBundle.From(rewrittenOutput),
        };
    }

    /// <summary>
    /// Region-memoized nested-algorithm processing (property values,
    /// <see cref="Expr.AlgorithmExpr"/> contents, and conditional branch bodies share the
    /// identical region context — the region's final visible summaries). A nested USER
    /// algorithm opens its own region below (its own final summaries); a nested FAMILY has
    /// no summaries of its own, so its branch bodies stay in this region and share its memo.
    /// </summary>
    private static Algorithm ProcessSharedNestedAlgorithm(
        Algorithm algorithm,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        ExposureWalkMemos memos)
    {
        memos.Algorithms ??= new(ReferenceEqualityComparer.Instance);
        if (!memos.Algorithms.TryGetValue(algorithm, out var rewritten))
        {
            rewritten = algorithm is Algorithm.Conditional conditional
                ? ProcessConditionalAlgorithm(conditional, visiblePropertySummaries, memos)
                : ProcessAlgorithm(
                    algorithm,
                    visiblePropertySummaries,
                    memos.SummaryMemo,
                    memos.Observations,
                    memos.Scope,
                    memos.Run);
            memos.Algorithms[algorithm] = rewritten;
        }

        return rewritten;
    }

    private static AnalysisSummary SummarizePropertyDependencies(
        PropertyDependencySummaryGraph summaryGraph,
        int propertyIndex,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        IReadOnlyDictionary<string, AnalysisSummary> currentPropertySummaries)
    {
        var node = summaryGraph[propertyIndex];
        var requiredAncestorOwnedParameterNames = new HashSet<string>(
            node.RequiredAncestorOwnedParameterNames,
            StringComparer.Ordinal);

        foreach (var dependencyName in node.SummaryVisiblePropertyDependencyNames)
        {
            if (visiblePropertySummaries.TryGetValue(dependencyName, out var summary))
                requiredAncestorOwnedParameterNames.UnionWith(summary.RequiredAncestorOwnedParameterNames);
        }

        foreach (var dependencyIndex in node.SummarySiblingDependencyIndices)
        {
            var dependencyName = summaryGraph.Properties[dependencyIndex].Name;
            if (currentPropertySummaries.TryGetValue(dependencyName, out var summary))
                requiredAncestorOwnedParameterNames.UnionWith(summary.RequiredAncestorOwnedParameterNames);
        }

        return requiredAncestorOwnedParameterNames.Count == 0
            ? AnalysisSummary.Empty
            : new AnalysisSummary(requiredAncestorOwnedParameterNames);
    }

    private static Algorithm ProcessConditionalAlgorithm(
        Algorithm.Conditional algorithm,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        ExposureWalkMemos memos)
    {
        memos.Run.HasOpens |= algorithm.Opens.Count != 0;
        var branchMemos = algorithm.Opens.Count == 0 ? memos
            : new ExposureWalkMemos(memos.SummaryMemo, memos.Observations,
                ElaboratedScopeLookup.CreateScope(algorithm, memos.Scope), memos.Run);
        // Family-owned opens exist in host trees only (parsed families own none; the branch
        // bodies own theirs). They are rewritten like any open list: an open target's nested
        // algorithms classify under the one rule exactly like every other body.
        var rewrittenOpens = RewriteExprList(
            algorithm.Opens,
            visiblePropertySummaries,
            new ExposureWalkMemos(memos.SummaryMemo, memos.Observations, memos.Scope.Root, memos.Run));

        var rewrittenBranches = new List<CondBranch>(algorithm.Branches.Count);
        foreach (var branch in algorithm.Branches)
        {
            if (DeferredModuleRegions.TryGet(branch.Body, out var region))
            {
                // B2c: a deferred module region is not materialized eagerly (its provisional
                // body is never evaluated; the FAMILY's classification reads the
                // provisional body's captures through the summary channel above). The region
                // records the visible summaries and is re-keyed by this region's output body.
                // Keep provisional fallback proofs sound too: a cached enclosing property
                // uses this body's capture summary before demand-time module loading.
                var placeholder = memos.Run.DeferredProofs.Contains(branch.Body)
                    ? ProcessSharedNestedAlgorithm(branch.Body, visiblePropertySummaries, branchMemos)
                    : branch.Body with { };
                DeferredModuleRegions.Register(
                    placeholder,
                    region.WithExposure(new DeferredBranchContext(visiblePropertySummaries, branchMemos.Scope)));
                rewrittenBranches.Add(new CondBranch(branch.Pattern, placeholder));
                continue;
            }

            // A branch body is processed exactly like any nested body under the one
            // classification rule (ClassifyDeclaredProperty): its pattern binders are inputs
            // only the family's call binds and arrive as Expr.Param references the body does
            // not own, so a declaration that depends on one is local-only for the same reason
            // a parameter-capturing declaration is, while a self-contained one is Exported —
            // openable, dot-accessible, and hand-out-able within the branch, and unreachable
            // by name from outside it because the family exposes no structural members.
            // Bodies ARE reference-deduplicated within the region (M4): the rewrite reads only
            // the body and the region's final visible summaries, so a body shared by several
            // families — or by a family and a property — classifies once and stays shared.
            var rewrittenBody = ProcessSharedNestedAlgorithm(
                branch.Body,
                visiblePropertySummaries,
                branchMemos);

            rewrittenBranches.Add(new CondBranch(branch.Pattern, rewrittenBody));
        }

        return algorithm with
        {
            Opens = rewrittenOpens,
            Branches = rewrittenBranches,
        };
    }

    /// <summary>
    /// The exposure context of one deferred module region (B2c): the final visible summaries
    /// the eager walk held at the branch, so the demand-time run classifies the resolved body
    /// under the same ancestor facts.
    /// </summary>
    internal sealed record DeferredBranchContext(
        IReadOnlyDictionary<string, AnalysisSummary> VisiblePropertySummaries,
        ElaboratedPropertyScope? ParentScope = null);

    /// <summary>
    /// Demand-time exposure classification of a deferred region's RESOLVED body — the
    /// ordinary body walk under the ONE rule (<see cref="ClassifyDeclaredProperty"/>).
    /// </summary>
    internal static Algorithm ElaborateDeferredBranch(
        Algorithm resolvedBody,
        DeferredBranchContext context,
        FrontEndTraversalObservations? observations = null)
        => ResolveInScope(
            resolvedBody,
            context.VisiblePropertySummaries,
            context.ParentScope ?? ElaboratedScopeLookup.CreateScope(BuiltinRegistry.CreateSemanticPreludeAlgorithm()),
            observations);

    private static IReadOnlyList<Expr> RewriteExprList(
        IReadOnlyList<Expr> expressions,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        ExposureWalkMemos memos)
    {
        var rewritten = new List<Expr>(expressions.Count);
        foreach (var expression in expressions)
        {
            rewritten.Add(RewriteExpr(
                expression,
                visiblePropertySummaries,
                memos));
        }

        return rewritten;
    }

    // Expression descent exists to reach nested algorithms — block literals and
    // call/dot-call argument bundles — so their properties receive exposure
    // classifications too. Outside those nested algorithm replacements, each
    // expression keeps the same shape and metadata.
    private static Expr RewriteExpr(
        Expr expr,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        ExposureWalkMemos memos)
    {
        // DAG-safety: one rewrite per shared node reference per region; the memo returns
        // the same rewritten node for every later reach, preserving the input's sharing.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return RewriteExprCore(expr, visiblePropertySummaries, memos);

        memos.Rewrites ??= new(ReferenceEqualityComparer.Instance);
        if (memos.Rewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        memos.Observations?.RecordExposureRewriteExpansion();
        rewritten = RewriteExprCore(expr, visiblePropertySummaries, memos);
        memos.Rewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr RewriteExprCore(
        Expr expr,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        ExposureWalkMemos memos)
    {
        switch (expr)
        {
            case Expr.Grace grace:
            {
                // Defensive only — parameter detection strips every grace
                // before exposure resolution runs; `with` keeps the stored
                // grace facts for host-built trees.
                var rewrittenInner = RewriteExpr(
                    grace.Inner,
                    visiblePropertySummaries,
                    memos);
                return grace with { Inner = rewrittenInner };
            }

            case Expr.Unary(var op, var operand):
            {
                var rewrittenOperand = RewriteExpr(
                    operand,
                    visiblePropertySummaries,
                    memos);
                return new Expr.Unary(op, rewrittenOperand) { Span = expr.Span };
            }

            case Expr.Binary(var op, var left, var right):
            {
                var rewrittenLeft = RewriteExpr(
                    left,
                    visiblePropertySummaries,
                    memos);
                var rewrittenRight = RewriteExpr(
                    right,
                    visiblePropertySummaries,
                    memos);
                return new Expr.Binary(op, rewrittenLeft, rewrittenRight) { Span = expr.Span };
            }

            case Expr.Index(var target, var selector):
            {
                var rewrittenTarget = RewriteExpr(
                    target,
                    visiblePropertySummaries,
                    memos);
                var rewrittenSelector = RewriteExpr(
                    selector,
                    visiblePropertySummaries,
                    memos);
                return new Expr.Index(rewrittenTarget, rewrittenSelector) { Span = expr.Span };
            }

            case Expr.SequenceSpread(var operand):
            {
                var rewrittenOperand = RewriteExpr(
                    operand,
                    visiblePropertySummaries,
                    memos);
                return new Expr.SequenceSpread(rewrittenOperand)
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };
            }

            case Expr.SequenceConstruct(var left, var right):
            {
                var rewrittenLeft = RewriteExpr(
                    left,
                    visiblePropertySummaries,
                    memos);
                var rewrittenRight = RewriteExpr(
                    right,
                    visiblePropertySummaries,
                    memos);
                return new Expr.SequenceConstruct(rewrittenLeft, rewrittenRight) { Span = expr.Span };
            }

            case Expr.ListLiteral(var items):
            {
                var rewrittenItems = new List<Expr>(items.Count);
                foreach (var item in items)
                {
                    rewrittenItems.Add(RewriteExpr(
                        item,
                        visiblePropertySummaries,
                        memos));
                }

                return new Expr.ListLiteral(rewrittenItems) { Span = expr.Span };
            }

            case Expr.AlgorithmExpr(var algorithm):
            {
                var rewrittenAlgorithm = ProcessSharedNestedAlgorithm(
                    algorithm,
                    visiblePropertySummaries,
                    memos);
                return new Expr.AlgorithmExpr(rewrittenAlgorithm) { Span = expr.Span };
            }

            case Expr.Capture(var captureBody):
            {
                // A capture owns no names and no properties, so its rows rewrite
                // with the same visible summaries — the exact effect the
                // pre-split transparent wrapper had through ProcessAlgorithm.
                var rewrittenRows = new List<Expr>(captureBody.Count);
                foreach (var row in captureBody)
                {
                    rewrittenRows.Add(RewriteExpr(
                        row,
                        visiblePropertySummaries,
                        memos));
                }

                return new Expr.Capture(new OutputBundle(rewrittenRows)) { Span = expr.Span };
            }

            case Expr.Call(var function, var args):
            {
                var rewrittenFunction = RewriteExpr(
                    function,
                    visiblePropertySummaries,
                    memos);
                // Argument bundles own no scope: slots rewrite in the enclosing
                // context, exactly like capture rows.
                var rewrittenArgs = new List<Expr>(args.Count);
                foreach (var argExpr in args)
                {
                    rewrittenArgs.Add(RewriteExpr(
                        argExpr,
                        visiblePropertySummaries,
                        memos));
                }

                return new Expr.Call(rewrittenFunction, new OutputBundle(rewrittenArgs)) { Span = expr.Span };
            }

            case Expr.DotCall(var target, _, var argsOpt):
            {
                var rewrittenTarget = RewriteExpr(
                    target,
                    visiblePropertySummaries,
                    memos);
                OutputBundle? rewrittenArgs = null;
                if (argsOpt is not null)
                {
                    var rewrittenSlots = new List<Expr>(argsOpt.Count);
                    foreach (var argExpr in argsOpt)
                    {
                        rewrittenSlots.Add(RewriteExpr(
                            argExpr,
                            visiblePropertySummaries,
                            memos));
                    }

                    rewrittenArgs = new OutputBundle(rewrittenSlots);
                }

                // `with` keeps the stored dot-edge facts (member span, lexical
                // fallback) intact.
                return ((Expr.DotCall)expr) with
                {
                    Target = rewrittenTarget,
                    Args = rewrittenArgs,
                    ElaboratedFallbackSelection = RecheckFallbackSelection((Expr.DotCall)expr, memos),
                };
            }

            // Intentional leaves: no nested algorithm to reach, so the
            // expression keeps its exact shape and metadata.
            case Expr.Resolve:
            case Expr.Param:
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                return expr;

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently skipping
            // exposure classification for algorithms nested inside it.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(PropertyExposureResolver)}.{nameof(RewriteExpr)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a recursive rewrite case or an intentional leaf.");
        }
    }

    private static LexicalFallbackSelection? RecheckFallbackSelection(Expr.DotCall dotCall, ExposureWalkMemos memos)
    {
        if (dotCall.ElaboratedFallbackSelection != LexicalFallbackSelection.Never)
            return dotCall.ElaboratedFallbackSelection;

        memos.Run.HasNeverFallback = true;
        var receiver = dotCall.Target.UnwrapGraceOperand().ResolveStaticStructuralMemberProvider(name =>
        {
            // Resolve/Param ownership is already elaborated. Resolve uses the same
            // direct-then-open lookup as the evaluator; missing/ambiguous names cannot
            // establish a structural winner. No source inference is performed here.
            var hits = ElaboratedScopeLookup.LookupLexicalPropertyMatches(memos.Scope, name);
            return hits.Count == 1
                ? new(StaticStructuralMemberProviderKind.KnownAlgorithm, hits[0].Property.Value)
                : new StaticStructuralMemberProvider(StaticStructuralMemberProviderKind.LexicalReference);
        });
        var selection = dotCall.GetLexicalFallbackSelection(receiver);
        memos.Run.FallbackWidened |= selection != LexicalFallbackSelection.Never;
        return selection;
    }

    private static IReadOnlyDictionary<string, AnalysisSummary> MergeVisiblePropertySummaries(
        IReadOnlyDictionary<string, AnalysisSummary> ancestorSummaries,
        IReadOnlyDictionary<string, AnalysisSummary> localSummaries)
    {
        // A nested algorithm with no local properties — the common leaf case, e.g. every simple
        // property value `A = expr` — adds nothing, so the ancestor map is shared as-is instead
        // of being copied. Cloning this O(P) sibling-summary map once per sibling property is what
        // made the exposure pass O(P^2) in the property count (a 10k-property source spent seconds
        // and gigabytes here). The merged map is only ever READ downstream, so sharing it is safe.
        if (localSummaries.Count == 0)
            return ancestorSummaries;

        var merged = new Dictionary<string, AnalysisSummary>(ancestorSummaries, StringComparer.Ordinal);
        foreach (var (name, summary) in localSummaries)
            merged[name] = summary;
        return merged;
    }

    private static bool SummariesEqual(
        IReadOnlyDictionary<string, AnalysisSummary> left,
        IReadOnlyDictionary<string, AnalysisSummary> right)
    {
        if (left.Count != right.Count)
            return false;

        foreach (var (name, leftSummary) in left)
        {
            if (!right.TryGetValue(name, out var rightSummary) || !leftSummary.SetEquals(rightSummary))
                return false;
        }

        return true;
    }
}
