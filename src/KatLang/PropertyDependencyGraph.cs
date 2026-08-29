namespace KatLang;

internal sealed record PropertyDependencyNode(
    int PropertyIndex,
    IReadOnlyList<int> SiblingDependencyIndices,
    IReadOnlyList<int> SummarySiblingDependencyIndices,
    IReadOnlyList<string> SummaryVisiblePropertyDependencyNames,
    IReadOnlyList<string> RequiredAncestorOwnedParameterNames);

internal sealed class PropertyDependencyGraph
{
    public static PropertyDependencyGraph Empty { get; } = new(
        Array.Empty<Property>(),
        new Dictionary<string, int>(StringComparer.Ordinal),
        Array.Empty<PropertyDependencyNode>());

    private readonly Dictionary<string, int> propertyNameToIndex;
    private readonly PropertyDependencyNode[] nodes;
    private IReadOnlyList<int>? topologicalOrder;

    public PropertyDependencyGraph(
        IReadOnlyList<Property> properties,
        Dictionary<string, int> propertyNameToIndex,
        PropertyDependencyNode[] nodes)
    {
        Properties = properties;
        this.propertyNameToIndex = propertyNameToIndex;
        this.nodes = nodes;
    }

    public IReadOnlyList<Property> Properties { get; }

    public int Count => nodes.Length;

    public PropertyDependencyNode this[int propertyIndex] => nodes[propertyIndex];

    public bool TryGetPropertyIndex(string propertyName, out int propertyIndex)
        => propertyNameToIndex.TryGetValue(propertyName, out propertyIndex);

    public IReadOnlyList<int> TopologicalOrder
        => topologicalOrder ??= BuildTopologicalOrder();

    private IReadOnlyList<int> BuildTopologicalOrder()
    {
        var inDegree = new int[nodes.Length];
        var dependents = new List<int>[nodes.Length];
        for (var i = 0; i < nodes.Length; i++)
            dependents[i] = [];

        foreach (var node in nodes)
        {
            foreach (var dependencyIndex in node.SiblingDependencyIndices)
            {
                dependents[dependencyIndex].Add(node.PropertyIndex);
                inDegree[node.PropertyIndex]++;
            }
        }

        var queue = new Queue<int>();
        for (var i = 0; i < nodes.Length; i++)
        {
            if (inDegree[i] == 0)
                queue.Enqueue(i);
        }

        var result = new List<int>(nodes.Length);
        while (queue.Count > 0)
        {
            var propertyIndex = queue.Dequeue();
            result.Add(propertyIndex);
            foreach (var dependentIndex in dependents[propertyIndex])
            {
                inDegree[dependentIndex]--;
                if (inDegree[dependentIndex] == 0)
                    queue.Enqueue(dependentIndex);
            }
        }

        if (result.Count < nodes.Length)
        {
            for (var i = 0; i < nodes.Length; i++)
            {
                if (inDegree[i] > 0)
                    result.Add(i);
            }
        }

        return result;
    }
}

internal static class PropertyDependencyGraphBuilder
{
    private sealed class SummarySeed
    {
        public SummarySeed(
            IEnumerable<string>? requiredAncestorOwnedParameterNames = null,
            IEnumerable<string>? visiblePropertyDependencyNames = null)
        {
            RequiredAncestorOwnedParameterNames = CreateNameSet(requiredAncestorOwnedParameterNames);
            VisiblePropertyDependencyNames = CreateNameSet(visiblePropertyDependencyNames);
        }

        public HashSet<string> RequiredAncestorOwnedParameterNames { get; }

        public HashSet<string> VisiblePropertyDependencyNames { get; }

        public SummarySeed Clone()
            => new(RequiredAncestorOwnedParameterNames, VisiblePropertyDependencyNames);

        public void UnionWith(SummarySeed other)
        {
            RequiredAncestorOwnedParameterNames.UnionWith(other.RequiredAncestorOwnedParameterNames);
            VisiblePropertyDependencyNames.UnionWith(other.VisiblePropertyDependencyNames);
        }

        public void RemoveRequiredAncestorOwnedParameterNames(IEnumerable<string> names)
            => RequiredAncestorOwnedParameterNames.ExceptWith(names);

        public bool SetEquals(SummarySeed other)
            => RequiredAncestorOwnedParameterNames.SetEquals(other.RequiredAncestorOwnedParameterNames)
                && VisiblePropertyDependencyNames.SetEquals(other.VisiblePropertyDependencyNames);
    }

    public static PropertyDependencyGraph Build(
        Algorithm.User algorithm,
        IEnumerable<string>? ancestorOwnedNames = null,
        IEnumerable<string>? locallyOwnedNames = null,
        Func<string, bool>? preludeNameShadowedByCaller = null)
    {
        var propertyNameToIndex = new Dictionary<string, int>(StringComparer.Ordinal);
        for (var i = 0; i < algorithm.Properties.Count; i++)
            propertyNameToIndex[algorithm.Properties[i].Name] = i;

        var siblingNames = new HashSet<string>(propertyNameToIndex.Keys, StringComparer.Ordinal);
        var ownedHere = CreateNameSet(locallyOwnedNames);
        ownedHere.UnionWith(algorithm.Params);

        var ancestorOwnedForProperties = CreateNameSet(ancestorOwnedNames);
        ancestorOwnedForProperties.UnionWith(ownedHere);

        // Whether a prelude name is shadowed at this level through ordinary
        // resolution: siblings, this algorithm's own parameters, and
        // the caller-supplied ancestor knowledge (the implicit-argument
        // resolver passes its visible property map's membership test). Math
        // alias calls and canonical `Math.X` calls both consult this so the
        // sibling-order channel has the SAME binding knowledge as rewriting. A
        // PREDICATE, not a materialized union: copying the ancestor map's keys
        // per Build call is O(ancestor properties) for every processed
        // property value and made wide flat scopes quadratic.
        bool PreludeNameShadowed(string name)
            => siblingNames.Contains(name)
                || ownedHere.Contains(name)
                || (preludeNameShadowedByCaller?.Invoke(name) ?? false);

        var nodes = new PropertyDependencyNode[algorithm.Properties.Count];
        for (var i = 0; i < algorithm.Properties.Count; i++)
        {
            var property = algorithm.Properties[i];
            var siblingDependencyIndices = CollectSiblingDependencyIndices(
                property.Value.Output,
                siblingNames,
                PreludeNameShadowed,
                propertyNameToIndex,
                i);
            var summarySeed = CollectSummarySeed(
                property.Value,
                ancestorOwnedForProperties,
                CreateNameSet());
            var summarySiblingDependencyIndices = new HashSet<int>();
            var summaryVisiblePropertyDependencyNames = CreateNameSet();
            foreach (var dependencyName in summarySeed.VisiblePropertyDependencyNames)
            {
                if (propertyNameToIndex.TryGetValue(dependencyName, out var dependencyIndex)
                    && dependencyIndex != i)
                    summarySiblingDependencyIndices.Add(dependencyIndex);
                else
                    summaryVisiblePropertyDependencyNames.Add(dependencyName);
            }

            nodes[i] = new PropertyDependencyNode(
                i,
                siblingDependencyIndices,
                summarySiblingDependencyIndices.OrderBy(static idx => idx).ToArray(),
                summaryVisiblePropertyDependencyNames.OrderBy(static name => name, StringComparer.Ordinal).ToArray(),
                summarySeed.RequiredAncestorOwnedParameterNames.OrderBy(static name => name, StringComparer.Ordinal).ToArray());
        }

        return new PropertyDependencyGraph(algorithm.Properties, propertyNameToIndex, nodes);
    }

    private static SummarySeed CollectSummarySeed(
        Algorithm algorithm,
        HashSet<string> ancestorOwnedNames,
        HashSet<string> locallyOwnedNames)
    {
        switch (algorithm)
        {
            case Algorithm.User user:
                return CollectSummarySeed(user, ancestorOwnedNames, locallyOwnedNames);

            case Algorithm.Conditional conditional:
                return CollectSummarySeed(conditional, ancestorOwnedNames, locallyOwnedNames);

            default:
                return new SummarySeed();
        }
    }

    private static SummarySeed CollectSummarySeed(
        Algorithm.User algorithm,
        HashSet<string> ancestorOwnedNames,
        HashSet<string> locallyOwnedNames)
    {
        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is self-contained: it
        // binds its own N-capture pattern and outputs one of those bound params, capturing no
        // ancestor-owned parameter and referencing no visible or sibling property (the shared
        // `$deconstruct$` source is referenced by the helper's ARGS, not the helper itself). Its
        // summary is therefore empty. Walking it costs O(N) per helper in its capture count
        // (the ownedHere union below and the fixed-point setup), so a wide deconstruction is
        // O(N^2) across its N sibling helpers without this leaf guard.
        if (algorithm.IsAssignmentDeconstructionHelper)
            return new SummarySeed();

        var ownedHere = CreateNameSet(locallyOwnedNames);
        ownedHere.UnionWith(algorithm.Params);

        var ancestorOwnedForChildren = CreateNameSet(ancestorOwnedNames);
        ancestorOwnedForChildren.UnionWith(ownedHere);

        // Ownership attribution follows the same transparency model as
        // ParameterDetector: transparent OutputBundle content (call/dot-call
        // argument bundles, surviving parenthesized groups) owns no names, so
        // its walk uses the enclosing algorithm's owned-name set. A parameter
        // reference inside such a layer therefore seeds the same
        // ancestor-capture requirement as the identical reference written
        // directly in the enclosing owner; the final
        // RemoveRequiredAncestorOwnedParameterNames strip below keeps each
        // algorithm's self-owned parameters out of the summary it returns.

        var currentPropertySummaries = new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
        var propertyBaseSeeds = new SummarySeed[algorithm.Properties.Count];
        for (var i = 0; i < algorithm.Properties.Count; i++)
        {
            var property = algorithm.Properties[i];
            currentPropertySummaries[property.Name] = new SummarySeed();
            propertyBaseSeeds[i] = CollectSummarySeed(
                property.Value,
                ancestorOwnedForChildren,
                CreateNameSet());
        }

        while (true)
        {
            var nextPropertySummaries = new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
            for (var i = 0; i < algorithm.Properties.Count; i++)
            {
                var property = algorithm.Properties[i];
                nextPropertySummaries[property.Name] = ExpandLocalPropertyDependencies(
                    propertyBaseSeeds[i],
                    currentPropertySummaries);
            }

            if (SummarySeedsEqual(currentPropertySummaries, nextPropertySummaries))
            {
                currentPropertySummaries = nextPropertySummaries;
                break;
            }

            currentPropertySummaries = nextPropertySummaries;
        }

        var seed = CollectSummarySeed(
            algorithm.Opens,
            currentPropertySummaries,
            ownedHere,
            ancestorOwnedForChildren);
        seed.UnionWith(CollectSummarySeed(
            algorithm.Output,
            currentPropertySummaries,
            ownedHere,
            ancestorOwnedForChildren));
        seed.RemoveRequiredAncestorOwnedParameterNames(ownedHere);
        return seed;
    }

    private static SummarySeed ExpandLocalPropertyDependencies(
        SummarySeed baseSeed,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries)
    {
        var expanded = new SummarySeed(
            requiredAncestorOwnedParameterNames: baseSeed.RequiredAncestorOwnedParameterNames);

        foreach (var dependencyName in baseSeed.VisiblePropertyDependencyNames)
        {
            if (localPropertySummaries.TryGetValue(dependencyName, out var localSummary))
            {
                expanded.UnionWith(localSummary);
                continue;
            }

            expanded.VisiblePropertyDependencyNames.Add(dependencyName);
        }

        return expanded;
    }

    private static SummarySeed CollectSummarySeed(
        Algorithm.Conditional algorithm,
        HashSet<string> ancestorOwnedNames,
        HashSet<string> locallyOwnedNames)
    {
        var ownedHere = CreateNameSet(locallyOwnedNames);
        var ancestorOwnedForChildren = CreateNameSet(ancestorOwnedNames);
        ancestorOwnedForChildren.UnionWith(ownedHere);

        var seed = CollectSummarySeed(
            algorithm.Opens,
            new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
            ownedHere,
            ancestorOwnedForChildren);

        foreach (var branch in algorithm.Branches)
        {
            seed.UnionWith(CollectSummarySeed(
                branch.Body,
                ancestorOwnedForChildren,
                CreateNameSet(branch.Pattern.BoundNames())));
        }

        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        IReadOnlyList<Expr> expressions,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        HashSet<string> ownedHere,
        HashSet<string> ancestorOwnedForChildren)
    {
        var seed = new SummarySeed();
        foreach (var expression in expressions)
            seed.UnionWith(CollectSummarySeed(expression, localPropertySummaries, ownedHere, ancestorOwnedForChildren));

        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        Expr expr,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        HashSet<string> ownedHere,
        HashSet<string> ancestorOwnedForChildren)
    {
        switch (expr)
        {
            case Expr.Param(var name):
                return ownedHere.Contains(name)
                    ? new SummarySeed()
                    : new SummarySeed(requiredAncestorOwnedParameterNames: [name]);

            case Expr.Resolve(var name):
                return localPropertySummaries.TryGetValue(name, out var localPropertySummary)
                    ? localPropertySummary.Clone()
                    : new SummarySeed(visiblePropertyDependencyNames: [name]);

            case Expr.Grace(var inner, _):
                return CollectSummarySeed(inner, localPropertySummaries, ownedHere, ancestorOwnedForChildren);

            case Expr.Binary(_, var left, var right):
            {
                var seed = CollectSummarySeed(left, localPropertySummaries, ownedHere, ancestorOwnedForChildren);
                seed.UnionWith(CollectSummarySeed(right, localPropertySummaries, ownedHere, ancestorOwnedForChildren));
                return seed;
            }

            case Expr.Unary(_, var operand):
                return CollectSummarySeed(operand, localPropertySummaries, ownedHere, ancestorOwnedForChildren);

            case Expr.Index(var target, var selector):
            {
                var seed = CollectSummarySeed(target, localPropertySummaries, ownedHere, ancestorOwnedForChildren);
                seed.UnionWith(CollectSummarySeed(selector, localPropertySummaries, ownedHere, ancestorOwnedForChildren));
                return seed;
            }

            case Expr.SequenceSpread(var operand):
            {
                var seed = CollectSummarySeed(operand, localPropertySummaries, ownedHere, ancestorOwnedForChildren);
                return seed;
            }

            case Expr.SequenceConstruct(var left, var right):
            {
                var seed = CollectSummarySeed(left, localPropertySummaries, ownedHere, ancestorOwnedForChildren);
                seed.UnionWith(CollectSummarySeed(right, localPropertySummaries, ownedHere, ancestorOwnedForChildren));
                return seed;
            }

            case Expr.ListLiteral(var listItems):
            {
                var seed = new SummarySeed();
                foreach (var item in listItems)
                    seed.UnionWith(CollectSummarySeed(item, localPropertySummaries, ownedHere, ancestorOwnedForChildren));
                return seed;
            }

            case Expr.AlgorithmExpr(var algorithm):
                return CollectSummarySeed(
                    algorithm,
                    ancestorOwnedForChildren,
                    CreateNameSet());

            case Expr.Capture(var captureBody):
                // A capture owns no names: its rows walk with an empty
                // owned-here set and an empty local-summary map — exactly what
                // the pre-split transparent wrapper algorithm's output walk did
                // (the same attribution as call-argument bundles).
                return CollectSummarySeed(
                    captureBody,
                    new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
                    CreateNameSet(),
                    ancestorOwnedForChildren);

            case Expr.Call(var function, var args):
            {
                // An argument bundle owns no names: slots walk with an empty
                // owned-here set and an empty local-summary map — the same
                // attribution as capture rows (and as the pre-Track-B empty
                // transparent args wrapper).
                var seed = CollectSummarySeed(function, localPropertySummaries, ownedHere, ancestorOwnedForChildren);
                seed.UnionWith(CollectSummarySeed(
                    args,
                    new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
                    CreateNameSet(),
                    ancestorOwnedForChildren));
                return seed;
            }

            case Expr.DotCall dotCall:
            {
                var seed = CollectSummarySeed(dotCall.Target, localPropertySummaries, ownedHere, ancestorOwnedForChildren);

                // The stored lexical-fallback identity is an ordinary
                // elaborated name expression (Resolve/Param) and participates
                // in dependency analysis EXACTLY like a written callee name —
                // through this same walk with the enclosing attribution — but
                // only when the receiver's static algorithm-position
                // capability makes the fallback the unconditional selection
                // (structural resolution is statically impossible). A
                // CONDITIONAL fallback — a receiver that may resolve
                // structurally at runtime — is deliberately excluded: marking
                // a structurally-resolving property LocalOnly because its
                // unreached fallback names a parameter would revoke working
                // structural/open access
                // (see AstHelpers.LexicalFallbackIsUnconditional).
                // The sibling evaluation-order channel
                // (CollectSiblingDependencyIndices) deliberately takes no
                // fallback contribution: the fallback is a CALLED name, and
                // called siblings are not order dependencies there (the same
                // rule as Call function position).
                if (dotCall.LexicalFallbackIsUnconditional())
                {
                    seed.UnionWith(CollectSummarySeed(
                        dotCall.EffectiveLexicalFallback,
                        localPropertySummaries,
                        ownedHere,
                        ancestorOwnedForChildren));
                }

                if (dotCall.Args is { } argsOpt)
                {
                    seed.UnionWith(CollectSummarySeed(
                        argsOpt,
                        new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
                        CreateNameSet(),
                        ancestorOwnedForChildren));
                }

                return seed;
            }

            // Intentional leaves with no name occurrences: literals, the empty
            // sequence, and native-call bodies (whose argument names are
            // parameter references by construction).
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                return new SummarySeed();

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently seeding no
            // dependencies (which would silently change exposure
            // classification for properties referencing it).
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(PropertyDependencyGraphBuilder)}.{nameof(CollectSummarySeed)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a collected case or an intentional leaf.");
        }
    }

    private static bool SummarySeedsEqual(
        IReadOnlyDictionary<string, SummarySeed> left,
        IReadOnlyDictionary<string, SummarySeed> right)
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

    private static IReadOnlyList<int> CollectSiblingDependencyIndices(
        IReadOnlyList<Expr> expressions,
        HashSet<string> siblingNames,
        Func<string, bool> preludeNameShadowed,
        IReadOnlyDictionary<string, int> propertyNameToIndex,
        int propertyIndex)
    {
        var dependencyIndices = new HashSet<int>();
        foreach (var expression in expressions)
            CollectSiblingDependencyIndices(expression, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition: false);

        return dependencyIndices.OrderBy(static idx => idx).ToArray();
    }

    private static void CollectSiblingDependencyIndices(
        Expr expr,
        HashSet<string> siblingNames,
        Func<string, bool> preludeNameShadowed,
        IReadOnlyDictionary<string, int> propertyNameToIndex,
        HashSet<int> dependencyIndices,
        int propertyIndex,
        bool inCallPosition)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (!inCallPosition
                    && siblingNames.Contains(name)
                    && propertyNameToIndex.TryGetValue(name, out var dependencyIndex)
                    && dependencyIndex != propertyIndex)
                {
                    dependencyIndices.Add(dependencyIndex);
                }
                break;

            case Expr.Call(var function, var callArgs):
                CollectSiblingDependencyIndices(function, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition: true);

                // An unshadowed Math-ALIAS call has the same registry-proven
                // strict-value argument contract as the written `Math.X(...)`
                // dot shape (the DotCall arm below): the resolver lifts its
                // argument slots as value positions, so those slots contribute
                // the same sibling processing-order dependencies here. Ordinary
                // neutral call arguments contribute none.
                if (function is Expr.Resolve(var calleeName)
                    && BuiltinRegistry.TryGetMathAliasFacts(calleeName, out var aliasFacts)
                    && aliasFacts.HasStrictValueArguments
                    && !preludeNameShadowed(calleeName))
                {
                    CollectArgumentSiblingDependencyIndices(callArgs, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex);
                }
                break;

            case Expr.Binary(_, var left, var right):
                CollectSiblingDependencyIndices(left, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                CollectSiblingDependencyIndices(right, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.Unary(_, var operand):
                CollectSiblingDependencyIndices(operand, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.Index(var target, var selector):
                CollectSiblingDependencyIndices(target, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                CollectSiblingDependencyIndices(selector, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.SequenceSpread(var operand):
                CollectSiblingDependencyIndices(operand, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectSiblingDependencyIndices(left, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                CollectSiblingDependencyIndices(right, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.ListLiteral(var listItems):
                foreach (var item in listItems)
                    CollectSiblingDependencyIndices(item, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.DotCall(var target, _, null):
                CollectSiblingDependencyIndices(target, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.DotCall dotCall:
                CollectSiblingDependencyIndices(dotCall.Target, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition: true);
                if (dotCall.Args is { } args
                    && dotCall.HasRegistryProvenStrictValueArguments(preludeNameShadowed))
                {
                    CollectArgumentSiblingDependencyIndices(args, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex);
                }
                break;

            case Expr.Grace(var inner, _):
                CollectSiblingDependencyIndices(inner, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition);
                break;

            case Expr.AlgorithmExpr or Expr.Capture:
                break;

            // Intentional leaves: no sibling references.
            case Expr.Num:
            case Expr.Param:
            case Expr.StringLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                break;

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above rather than silently
            // contributing no processing-order dependencies.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(PropertyDependencyGraphBuilder)}.{nameof(CollectSiblingDependencyIndices)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a collected case or an intentional leaf.");
        }
    }

    private static void CollectArgumentSiblingDependencyIndices(
        OutputBundle args,
        HashSet<string> siblingNames,
        Func<string, bool> preludeNameShadowed,
        IReadOnlyDictionary<string, int> propertyNameToIndex,
        HashSet<int> dependencyIndices,
        int propertyIndex)
    {
        foreach (var expression in args)
        {
            CollectSiblingDependencyIndices(
                expression,
                siblingNames,
                preludeNameShadowed,
                propertyNameToIndex,
                dependencyIndices,
                propertyIndex,
                inCallPosition: false);
        }
    }

    private static HashSet<string> CreateNameSet(IEnumerable<string>? names = null)
        => names is null
            ? new HashSet<string>(StringComparer.Ordinal)
            : new HashSet<string>(names, StringComparer.Ordinal);
}
