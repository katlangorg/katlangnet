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

    private sealed record RewriteResult(Algorithm Algorithm, AnalysisSummary Summary);

    private sealed record ExprRewriteResult(Expr Expr, AnalysisSummary Summary);

    public static Algorithm Resolve(Algorithm root)
        => ProcessAlgorithm(
            root,
            visiblePropertySummaries: new Dictionary<string, AnalysisSummary>(StringComparer.Ordinal),
            ancestorOwnedNames: CreateNameSet(),
            locallyOwnedNames: CreateNameSet(),
            insideConditionalAlgorithm: false).Algorithm;

    private static RewriteResult ProcessAlgorithm(
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
            _ => new RewriteResult(algorithm, AnalysisSummary.Empty),
        };

    private static RewriteResult ProcessUserAlgorithm(
        Algorithm.User algorithm,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        HashSet<string> ancestorOwnedNames,
        HashSet<string> locallyOwnedNames,
        bool insideConditionalAlgorithm)
    {
        var dependencyGraph = PropertyDependencyGraphBuilder.Build(
            algorithm,
            ancestorOwnedNames,
            locallyOwnedNames);
        var ownedHere = UnionNames(locallyOwnedNames, algorithm.Params);
        var ancestorOwnedForChildren = UnionNames(ancestorOwnedNames, ownedHere);
        var summaryOwnedHere = algorithm.IsParametrized
            ? ownedHere
            : UnionNames(ownedHere, ancestorOwnedNames);

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

            rewrittenProperties.Add(new Property(property.Name, rewrittenPropertyValue.Algorithm, property.IsPublic, exposure)
            {
                DeclarationSpans = property.DeclarationSpans
            });
        }

        var rewrittenOpens = RewriteExprList(
            algorithm.Opens,
            finalVisiblePropertySummaries,
            summaryOwnedHere,
            ancestorOwnedForChildren,
            insideConditionalAlgorithm);
        var rewrittenOutput = RewriteExprList(
            algorithm.Output,
            finalVisiblePropertySummaries,
            summaryOwnedHere,
            ancestorOwnedForChildren,
            insideConditionalAlgorithm);

        var rewrittenAlgorithm = algorithm with
        {
            Opens = rewrittenOpens.Select(result => result.Expr).ToList(),
            Properties = rewrittenProperties,
            Output = rewrittenOutput.Select(result => result.Expr).ToList(),
        };

        return new RewriteResult(
            rewrittenAlgorithm,
            MergeSummaries(rewrittenOpens.Concat(rewrittenOutput).Select(result => result.Summary)));
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

    private static RewriteResult ProcessConditionalAlgorithm(
        Algorithm.Conditional algorithm,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        HashSet<string> ancestorOwnedNames,
        HashSet<string> locallyOwnedNames,
        bool insideConditionalAlgorithm)
    {
        var ownedHere = CreateNameSet(locallyOwnedNames);
        var ancestorOwnedForChildren = UnionNames(ancestorOwnedNames, ownedHere);

        var rewrittenOpens = RewriteExprList(
            algorithm.Opens,
            visiblePropertySummaries,
            ownedHere,
            ancestorOwnedForChildren,
            insideConditionalAlgorithm);

        var requiredAncestorOwnedParameterNames = new HashSet<string>(StringComparer.Ordinal);
        requiredAncestorOwnedParameterNames.UnionWith(
            MergeSummaries(rewrittenOpens.Select(result => result.Summary)).RequiredAncestorOwnedParameterNames);

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

            rewrittenBranches.Add(new CondBranch(branch.Pattern, rewrittenBody.Algorithm));
            requiredAncestorOwnedParameterNames.UnionWith(rewrittenBody.Summary.RequiredAncestorOwnedParameterNames);
        }

        return new RewriteResult(
            algorithm with
            {
                Opens = rewrittenOpens.Select(result => result.Expr).ToList(),
                Branches = rewrittenBranches,
            },
            new AnalysisSummary(requiredAncestorOwnedParameterNames));
    }

    private static IReadOnlyList<ExprRewriteResult> RewriteExprList(
        IReadOnlyList<Expr> expressions,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        HashSet<string> ownedHere,
        HashSet<string> ancestorOwnedForChildren,
        bool insideConditionalAlgorithm)
    {
        var rewritten = new List<ExprRewriteResult>(expressions.Count);
        foreach (var expression in expressions)
        {
            rewritten.Add(RewriteExpr(
                expression,
                visiblePropertySummaries,
                ownedHere,
                ancestorOwnedForChildren,
                insideConditionalAlgorithm));
        }

        return rewritten;
    }

    private static ExprRewriteResult RewriteExpr(
        Expr expr,
        IReadOnlyDictionary<string, AnalysisSummary> visiblePropertySummaries,
        HashSet<string> ownedHere,
        HashSet<string> ancestorOwnedForChildren,
        bool insideConditionalAlgorithm)
    {
        switch (expr)
        {
            case Expr.Param(var name):
                return new ExprRewriteResult(
                    expr,
                    ownedHere.Contains(name)
                        ? AnalysisSummary.Empty
                        : new AnalysisSummary([name]));

            case Expr.Resolve(var name):
                return new ExprRewriteResult(
                    expr,
                    visiblePropertySummaries.TryGetValue(name, out var summary)
                        ? summary
                        : AnalysisSummary.Empty);

            case Expr.Grace(var inner, var weight):
            {
                var rewrittenInner = RewriteExpr(
                    inner,
                    visiblePropertySummaries,
                    ownedHere,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                return new ExprRewriteResult(
                    new Expr.Grace(rewrittenInner.Expr, weight) { Span = expr.Span },
                    rewrittenInner.Summary);
            }

            case Expr.Unary(var op, var operand):
            {
                var rewrittenOperand = RewriteExpr(
                    operand,
                    visiblePropertySummaries,
                    ownedHere,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                return new ExprRewriteResult(
                    new Expr.Unary(op, rewrittenOperand.Expr) { Span = expr.Span },
                    rewrittenOperand.Summary);
            }

            case Expr.Binary(var op, var left, var right):
            {
                var rewrittenLeft = RewriteExpr(
                    left,
                    visiblePropertySummaries,
                    ownedHere,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                var rewrittenRight = RewriteExpr(
                    right,
                    visiblePropertySummaries,
                    ownedHere,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                return new ExprRewriteResult(
                    new Expr.Binary(op, rewrittenLeft.Expr, rewrittenRight.Expr) { Span = expr.Span },
                    MergeSummaries([rewrittenLeft.Summary, rewrittenRight.Summary]));
            }

            case Expr.Index(var target, var selector):
            {
                var rewrittenTarget = RewriteExpr(
                    target,
                    visiblePropertySummaries,
                    ownedHere,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                var rewrittenSelector = RewriteExpr(
                    selector,
                    visiblePropertySummaries,
                    ownedHere,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                return new ExprRewriteResult(
                    new Expr.Index(rewrittenTarget.Expr, rewrittenSelector.Expr) { Span = expr.Span },
                    MergeSummaries([rewrittenTarget.Summary, rewrittenSelector.Summary]));
            }

            case Expr.Combine(var left, var right):
            {
                var rewrittenLeft = RewriteExpr(
                    left,
                    visiblePropertySummaries,
                    ownedHere,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                var rewrittenRight = RewriteExpr(
                    right,
                    visiblePropertySummaries,
                    ownedHere,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                return new ExprRewriteResult(
                    new Expr.Combine(rewrittenLeft.Expr, rewrittenRight.Expr) { Span = expr.Span },
                    MergeSummaries([rewrittenLeft.Summary, rewrittenRight.Summary]));
            }

            case Expr.Block(var algorithm):
            {
                var rewrittenAlgorithm = ProcessAlgorithm(
                    algorithm,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    CreateNameSet(),
                    insideConditionalAlgorithm);
                return new ExprRewriteResult(
                    new Expr.Block(rewrittenAlgorithm.Algorithm) { Span = expr.Span },
                    rewrittenAlgorithm.Summary);
            }

            case Expr.Call(var function, var args):
            {
                var rewrittenFunction = RewriteExpr(
                    function,
                    visiblePropertySummaries,
                    ownedHere,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                var rewrittenArgs = ProcessAlgorithm(
                    args,
                    visiblePropertySummaries,
                    ancestorOwnedForChildren,
                    CreateNameSet(),
                    insideConditionalAlgorithm);
                return new ExprRewriteResult(
                    new Expr.Call(rewrittenFunction.Expr, rewrittenArgs.Algorithm) { Span = expr.Span },
                    MergeSummaries([rewrittenFunction.Summary, rewrittenArgs.Summary]));
            }

            case Expr.DotCall(var target, var name, var argsOpt):
            {
                var rewrittenTarget = RewriteExpr(
                    target,
                    visiblePropertySummaries,
                    ownedHere,
                    ancestorOwnedForChildren,
                    insideConditionalAlgorithm);
                RewriteResult? rewrittenArgs = null;
                if (argsOpt is not null)
                {
                    rewrittenArgs = ProcessAlgorithm(
                        argsOpt,
                        visiblePropertySummaries,
                        ancestorOwnedForChildren,
                        CreateNameSet(),
                        insideConditionalAlgorithm);
                }

                return new ExprRewriteResult(
                    new Expr.DotCall(rewrittenTarget.Expr, name, rewrittenArgs?.Algorithm)
                    {
                        Span = expr.Span,
                        MemberSpan = ((Expr.DotCall)expr).MemberSpan,
                    },
                    rewrittenArgs is null
                        ? rewrittenTarget.Summary
                        : MergeSummaries([rewrittenTarget.Summary, rewrittenArgs.Summary]));
            }

            default:
                return new ExprRewriteResult(expr, AnalysisSummary.Empty);
        }
    }

    private static Dictionary<string, AnalysisSummary> MergeVisiblePropertySummaries(
        IReadOnlyDictionary<string, AnalysisSummary> ancestorSummaries,
        IReadOnlyDictionary<string, AnalysisSummary> localSummaries)
    {
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

    private static AnalysisSummary MergeSummaries(IEnumerable<AnalysisSummary> summaries)
    {
        var requiredAncestorOwnedParameterNames = new HashSet<string>(StringComparer.Ordinal);
        foreach (var summary in summaries)
            requiredAncestorOwnedParameterNames.UnionWith(summary.RequiredAncestorOwnedParameterNames);
        return new AnalysisSummary(requiredAncestorOwnedParameterNames);
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