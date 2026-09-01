namespace KatLang;

internal static class PropertyExposureResolver
{
    private sealed class AnalysisSummary
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
    /// DISTINCT reachable nodes, never the number of root-to-node paths, and the rewritten
    /// output preserves the input's sharing. Memos are run-local: one resolution creates one
    /// completed-summary memo (see <see cref="PropertyDependencyGraphBuilder.SummaryMemo"/>)
    /// plus per-region rewrite memos, all garbage afterwards.
    /// </summary>
    public static Algorithm Resolve(Algorithm root)
        => Resolve(root, observations: null);

    internal static Algorithm Resolve(Algorithm root, FrontEndTraversalObservations? observations)
        => ProcessAlgorithm(
            root,
            visiblePropertySummaries: new Dictionary<string, AnalysisSummary>(StringComparer.Ordinal),
            insideConditionalAlgorithm: false,
            // ONE completed-summary memo per resolution: every BuildSummaries call below
            // shares it, so a context-independent descendant summary is computed once per
            // resolution instead of once per ancestor level (M17).
            new PropertyDependencyGraphBuilder.SummaryMemo(),
            observations);

    /// <summary>
    /// Reference-identity memo state for ONE exposure rewrite region — one user algorithm's
    /// opens/output/property-value processing (the final visible summaries are fixed before
    /// any of it runs), or one conditional's open list. Shared expressions rewrite once and
    /// stay shared; <see cref="Algorithms"/> memoizes nested-algorithm processing (property
    /// values and <see cref="Expr.AlgorithmExpr"/> contents run under the identical context:
    /// final summaries, the same conditional flag), so two properties or wrappers sharing
    /// ONE algorithm classify it once. The resolution-wide summary memo rides along so
    /// nested regions keep sharing completed summaries. Conditional BRANCH bodies are
    /// deliberately not memoized here: they re-process per branch (their summary work still
    /// deduplicates through the resolution memo).
    /// </summary>
    private sealed class ExposureWalkMemos(
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations)
    {
        public Dictionary<Expr, Expr>? Rewrites;

        public Dictionary<Algorithm, Algorithm>? Algorithms;

        public readonly PropertyDependencyGraphBuilder.SummaryMemo SummaryMemo = summaryMemo;

        public readonly FrontEndTraversalObservations? Observations = observations;
    }

    private static Algorithm ProcessAlgorithm(
        Algorithm algorithm,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        bool insideConditionalAlgorithm,
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations)
        => algorithm switch
        {
            Algorithm.User user => ProcessUserAlgorithm(
                user,
                visiblePropertySummaries,
                insideConditionalAlgorithm,
                summaryMemo,
                observations),
            Algorithm.Conditional conditional => ProcessConditionalAlgorithm(
                conditional,
                visiblePropertySummaries,
                insideConditionalAlgorithm,
                summaryMemo,
                observations),
            _ => algorithm,
        };

    private static Algorithm ProcessUserAlgorithm(
        Algorithm.User algorithm,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        bool insideConditionalAlgorithm,
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations)
    {
        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is a fully-elaborated
        // leaf: no properties, no opens, and an output that is exactly its own bound Param. It
        // captures no ancestor-owned parameter, so it needs no exposure rewriting. The general
        // path would still analyze and rewrite it per helper for no observable effect.
        if (algorithm is Algorithm.User { IsAssignmentDeconstructionHelper: true })
            return algorithm;

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
        // ONE memo bundle spans this algorithm's property-value processing AND its
        // opens/output rewrite below: all of it runs under the identical, already-final
        // context (finalVisiblePropertySummaries, the flag).
        var memos = new ExposureWalkMemos(summaryMemo, observations);
        var rewrittenProperties = new List<Property>(algorithm.Properties.Count);
        for (var propertyIndex = 0; propertyIndex < algorithm.Properties.Count; propertyIndex++)
        {
            var property = algorithm.Properties[propertyIndex];
            var rewrittenPropertyValue = ProcessSharedNestedAlgorithm(
                property.Value,
                finalVisiblePropertySummaries,
                insideConditionalAlgorithm,
                memos);

            var exposure = insideConditionalAlgorithm
                ? PropertyExposure.LocalOnlyConditionalAlgorithm
                : currentPropertySummaries[property.Name].RequiresAncestorOwnedParameters
                    ? PropertyExposure.LocalOnlyCapturedAncestorParameters
                    : PropertyExposure.Exported;

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
            insideConditionalAlgorithm,
            memos);
        var rewrittenOutput = RewriteExprList(
            algorithm.Output,
            finalVisiblePropertySummaries,
            insideConditionalAlgorithm,
            memos);

        return algorithm with
        {
            Opens = rewrittenOpens,
            Properties = rewrittenProperties,
            Output = OutputBundle.From(rewrittenOutput),
        };
    }

    /// <summary>
    /// Region-memoized nested-algorithm processing (property values and
    /// <see cref="Expr.AlgorithmExpr"/> contents share the identical region context —
    /// exactly as before).
    /// </summary>
    private static Algorithm ProcessSharedNestedAlgorithm(
        Algorithm algorithm,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        bool insideConditionalAlgorithm,
        ExposureWalkMemos memos)
    {
        memos.Algorithms ??= new(ReferenceEqualityComparer.Instance);
        if (!memos.Algorithms.TryGetValue(algorithm, out var rewritten))
        {
            rewritten = ProcessAlgorithm(
                algorithm,
                visiblePropertySummaries,
                insideConditionalAlgorithm,
                memos.SummaryMemo,
                memos.Observations);
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
        bool insideConditionalAlgorithm,
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations)
    {
        var rewrittenOpens = RewriteExprList(
            algorithm.Opens,
            visiblePropertySummaries,
            insideConditionalAlgorithm,
            new ExposureWalkMemos(summaryMemo, observations));

        var rewrittenBranches = new List<CondBranch>(algorithm.Branches.Count);
        foreach (var branch in algorithm.Branches)
        {
            // Branch bodies are deliberately NOT reference-deduplicated: each body
            // re-processes per branch (this pass threads no binder-name context — the
            // builder's summary channel applies binder names itself, and everything inside a
            // conditional classifies LocalOnlyConditionalAlgorithm regardless).
            var rewrittenBody = ProcessAlgorithm(
                branch.Body,
                visiblePropertySummaries,
                insideConditionalAlgorithm: true,
                summaryMemo,
                observations);

            rewrittenBranches.Add(new CondBranch(branch.Pattern, rewrittenBody));
        }

        return algorithm with
        {
            Opens = rewrittenOpens,
            Branches = rewrittenBranches,
        };
    }

    private static IReadOnlyList<Expr> RewriteExprList(
        IReadOnlyList<Expr> expressions,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        bool insideConditionalAlgorithm,
        ExposureWalkMemos memos)
    {
        var rewritten = new List<Expr>(expressions.Count);
        foreach (var expression in expressions)
        {
            rewritten.Add(RewriteExpr(
                expression,
                visiblePropertySummaries,
                insideConditionalAlgorithm,
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
        bool insideConditionalAlgorithm,
        ExposureWalkMemos memos)
    {
        // DAG-safety: one rewrite per shared node reference per region; the memo returns
        // the same rewritten node for every later reach, preserving the input's sharing.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return RewriteExprCore(expr, visiblePropertySummaries, insideConditionalAlgorithm, memos);

        memos.Rewrites ??= new(ReferenceEqualityComparer.Instance);
        if (memos.Rewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        memos.Observations?.RecordExposureRewriteExpansion();
        rewritten = RewriteExprCore(expr, visiblePropertySummaries, insideConditionalAlgorithm, memos);
        memos.Rewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr RewriteExprCore(
        Expr expr,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        bool insideConditionalAlgorithm,
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
                    insideConditionalAlgorithm,
                    memos);
                return grace with { Inner = rewrittenInner };
            }

            case Expr.Unary(var op, var operand):
            {
                var rewrittenOperand = RewriteExpr(
                    operand,
                    visiblePropertySummaries,
                    insideConditionalAlgorithm,
                    memos);
                return new Expr.Unary(op, rewrittenOperand) { Span = expr.Span };
            }

            case Expr.Binary(var op, var left, var right):
            {
                var rewrittenLeft = RewriteExpr(
                    left,
                    visiblePropertySummaries,
                    insideConditionalAlgorithm,
                    memos);
                var rewrittenRight = RewriteExpr(
                    right,
                    visiblePropertySummaries,
                    insideConditionalAlgorithm,
                    memos);
                return new Expr.Binary(op, rewrittenLeft, rewrittenRight) { Span = expr.Span };
            }

            case Expr.Index(var target, var selector):
            {
                var rewrittenTarget = RewriteExpr(
                    target,
                    visiblePropertySummaries,
                    insideConditionalAlgorithm,
                    memos);
                var rewrittenSelector = RewriteExpr(
                    selector,
                    visiblePropertySummaries,
                    insideConditionalAlgorithm,
                    memos);
                return new Expr.Index(rewrittenTarget, rewrittenSelector) { Span = expr.Span };
            }

            case Expr.SequenceSpread(var operand):
            {
                var rewrittenOperand = RewriteExpr(
                    operand,
                    visiblePropertySummaries,
                    insideConditionalAlgorithm,
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
                    insideConditionalAlgorithm,
                    memos);
                var rewrittenRight = RewriteExpr(
                    right,
                    visiblePropertySummaries,
                    insideConditionalAlgorithm,
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
                        insideConditionalAlgorithm,
                        memos));
                }

                return new Expr.ListLiteral(rewrittenItems) { Span = expr.Span };
            }

            case Expr.AlgorithmExpr(var algorithm):
            {
                var rewrittenAlgorithm = ProcessSharedNestedAlgorithm(
                    algorithm,
                    visiblePropertySummaries,
                    insideConditionalAlgorithm,
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
                        insideConditionalAlgorithm,
                        memos));
                }

                return new Expr.Capture(new OutputBundle(rewrittenRows)) { Span = expr.Span };
            }

            case Expr.Call(var function, var args):
            {
                var rewrittenFunction = RewriteExpr(
                    function,
                    visiblePropertySummaries,
                    insideConditionalAlgorithm,
                    memos);
                // Argument bundles own no scope: slots rewrite in the enclosing
                // context, exactly like capture rows.
                var rewrittenArgs = new List<Expr>(args.Count);
                foreach (var argExpr in args)
                {
                    rewrittenArgs.Add(RewriteExpr(
                        argExpr,
                        visiblePropertySummaries,
                        insideConditionalAlgorithm,
                        memos));
                }

                return new Expr.Call(rewrittenFunction, new OutputBundle(rewrittenArgs)) { Span = expr.Span };
            }

            case Expr.DotCall(var target, _, var argsOpt):
            {
                var rewrittenTarget = RewriteExpr(
                    target,
                    visiblePropertySummaries,
                    insideConditionalAlgorithm,
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
                            insideConditionalAlgorithm,
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
