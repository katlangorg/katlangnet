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

    public static Algorithm Resolve(Algorithm root)
        => ProcessAlgorithm(
            root,
            visiblePropertySummaries: new Dictionary<string, AnalysisSummary>(StringComparer.Ordinal),
            ancestorOwnedNames: CreateNameSet(),
            locallyOwnedNames: CreateNameSet(),
            insideConditionalAlgorithm: false);

    private static Algorithm ProcessAlgorithm(
        Algorithm algorithm,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        HashSet<string> ancestorOwnedNames,
        HashSet<string> locallyOwnedNames,
        bool insideConditionalAlgorithm)
        => algorithm switch
        {
            Algorithm.User user => ProcessUserAlgorithm(
                user,
                visiblePropertySummaries,
                ancestorOwnedNames,
                locallyOwnedNames,
                insideConditionalAlgorithm),
            Algorithm.Conditional conditional => ProcessConditionalAlgorithm(
                conditional,
                visiblePropertySummaries,
                ancestorOwnedNames,
                locallyOwnedNames,
                insideConditionalAlgorithm),
            _ => algorithm,
        };

    private static Algorithm ProcessUserAlgorithm(
        Algorithm.User algorithm,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        HashSet<string> ancestorOwnedNames,
        HashSet<string> locallyOwnedNames,
        bool insideConditionalAlgorithm)
    {
        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is a fully-elaborated
        // leaf: no properties, no opens, and an output that is exactly its own bound Param. It
        // captures no ancestor-owned parameter, so it needs no exposure rewriting. The general
        // path would build an O(N) owned-name union from its N-capture pattern per helper —
        // O(N^2) across a wide deconstruction's N helpers — for no observable effect.
        if (algorithm is Algorithm.User { IsAssignmentDeconstructionHelper: true })
            return algorithm;

        var dependencyGraph = PropertyDependencyGraphBuilder.Build(
            algorithm,
            ancestorOwnedNames,
            locallyOwnedNames);
        var ownedHere = UnionNames(locallyOwnedNames, algorithm.Params);
        var ancestorOwnedForChildren = UnionNames(ancestorOwnedNames, ownedHere);

        var currentPropertySummaries = new Dictionary<string, AnalysisSummary>(StringComparer.Ordinal);
        foreach (var property in algorithm.Properties)
            currentPropertySummaries[property.Name] = AnalysisSummary.Empty;

        // PropertyDependencyGraph already centralizes the stable per-property seed facts:
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
                    dependencyGraph,
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
        var rewrittenProperties = new List<Property>(algorithm.Properties.Count);
        for (var propertyIndex = 0; propertyIndex < algorithm.Properties.Count; propertyIndex++)
        {
            var property = algorithm.Properties[propertyIndex];
            var rewrittenPropertyValue = ProcessAlgorithm(
                property.Value,
                finalVisiblePropertySummaries,
                ancestorOwnedForChildren,
                CreateNameSet(),
                insideConditionalAlgorithm);

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
            ancestorOwnedForChildren,
            insideConditionalAlgorithm);
        var rewrittenOutput = RewriteExprList(
            algorithm.Output,
            finalVisiblePropertySummaries,
            ancestorOwnedForChildren,
            insideConditionalAlgorithm);

        return algorithm with
        {
            Opens = rewrittenOpens,
            Properties = rewrittenProperties,
            Output = OutputBundle.From(rewrittenOutput),
        };
    }

    private static AnalysisSummary SummarizePropertyDependencies(
        PropertyDependencyGraph dependencyGraph,
        int propertyIndex,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        IReadOnlyDictionary<string, AnalysisSummary> currentPropertySummaries)
    {
        var node = dependencyGraph[propertyIndex];
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
            var dependencyName = dependencyGraph.Properties[dependencyIndex].Name;
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
        HashSet<string> ancestorOwnedNames,
        HashSet<string> locallyOwnedNames,
        bool insideConditionalAlgorithm)
    {
        var ancestorOwnedForChildren = UnionNames(ancestorOwnedNames, locallyOwnedNames);

        var rewrittenOpens = RewriteExprList(
            algorithm.Opens,
            visiblePropertySummaries,
            ancestorOwnedForChildren,
            insideConditionalAlgorithm);

        var rewrittenBranches = new List<CondBranch>(algorithm.Branches.Count);
        foreach (var branch in algorithm.Branches)
        {
            var binderNames = CreateNameSet(branch.Pattern.BoundNames());
            var rewrittenBody = ProcessAlgorithm(
                branch.Body,
                visiblePropertySummaries,
                ancestorOwnedForChildren,
                binderNames,
                insideConditionalAlgorithm: true);

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
        HashSet<string> ancestorOwnedForChildren,
        bool insideConditionalAlgorithm)
    {
        var rewritten = new List<Expr>(expressions.Count);
        foreach (var expression in expressions)
        {
            rewritten.Add(RewriteExpr(
                expression,
                visiblePropertySummaries,
                ancestorOwnedForChildren,
                insideConditionalAlgorithm));
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
        HashSet<string> ancestorOwnedForChildren,
        bool insideConditionalAlgorithm)
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
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                return grace with { Inner = rewrittenInner };
            }

            case Expr.Unary(var op, var operand):
            {
                var rewrittenOperand = RewriteExpr(
                    operand,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                return new Expr.Unary(op, rewrittenOperand) { Span = expr.Span };
            }

            case Expr.Binary(var op, var left, var right):
            {
                var rewrittenLeft = RewriteExpr(
                    left,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                var rewrittenRight = RewriteExpr(
                    right,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                return new Expr.Binary(op, rewrittenLeft, rewrittenRight) { Span = expr.Span };
            }

            case Expr.Index(var target, var selector):
            {
                var rewrittenTarget = RewriteExpr(
                    target,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                var rewrittenSelector = RewriteExpr(
                    selector,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                return new Expr.Index(rewrittenTarget, rewrittenSelector) { Span = expr.Span };
            }

            case Expr.SequenceSpread(var operand):
            {
                var rewrittenOperand = RewriteExpr(
                    operand,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
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
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                var rewrittenRight = RewriteExpr(
                    right,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
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
                        ancestorOwnedForChildren,
                        insideConditionalAlgorithm));
                }

                return new Expr.ListLiteral(rewrittenItems) { Span = expr.Span };
            }

            case Expr.AlgorithmExpr(var algorithm):
            {
                var rewrittenAlgorithm = ProcessAlgorithm(
                    algorithm,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    CreateNameSet(),
                    insideConditionalAlgorithm);
                return new Expr.AlgorithmExpr(rewrittenAlgorithm) { Span = expr.Span };
            }

            case Expr.Capture(var captureBody):
            {
                // A capture owns no names and no properties, so its rows rewrite
                // with the same visible summaries and owned-name context — the
                // exact effect the pre-split transparent wrapper had through
                // ProcessAlgorithm.
                var rewrittenRows = new List<Expr>(captureBody.Count);
                foreach (var row in captureBody)
                {
                    rewrittenRows.Add(RewriteExpr(
                        row,
                        visiblePropertySummaries,
                        ancestorOwnedForChildren,
                        insideConditionalAlgorithm));
                }

                return new Expr.Capture(new OutputBundle(rewrittenRows)) { Span = expr.Span };
            }

            case Expr.Call(var function, var args):
            {
                var rewrittenFunction = RewriteExpr(
                    function,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                // Argument bundles own no scope: slots rewrite in the enclosing
                // context, exactly like capture rows.
                var rewrittenArgs = new List<Expr>(args.Count);
                foreach (var argExpr in args)
                {
                    rewrittenArgs.Add(RewriteExpr(
                        argExpr,
                        visiblePropertySummaries,
                        ancestorOwnedForChildren,
                        insideConditionalAlgorithm));
                }

                return new Expr.Call(rewrittenFunction, new OutputBundle(rewrittenArgs)) { Span = expr.Span };
            }

            case Expr.DotCall(var target, _, var argsOpt):
            {
                var rewrittenTarget = RewriteExpr(
                    target,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                OutputBundle? rewrittenArgs = null;
                if (argsOpt is not null)
                {
                    var rewrittenSlots = new List<Expr>(argsOpt.Count);
                    foreach (var argExpr in argsOpt)
                    {
                        rewrittenSlots.Add(RewriteExpr(
                            argExpr,
                            visiblePropertySummaries,
                            ancestorOwnedForChildren,
                            insideConditionalAlgorithm));
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

    private static HashSet<string> CreateNameSet(IEnumerable<string>? names = null)
        => names is null
            ? new HashSet<string>(StringComparer.Ordinal)
            : new HashSet<string>(names, StringComparer.Ordinal);

    private static HashSet<string> UnionNames(IEnumerable<string> left, IEnumerable<string> right)
    {
        var names = CreateNameSet(left);
        names.UnionWith(right);
        return names;
    }
}
