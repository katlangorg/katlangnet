namespace KatLang;

internal sealed record PropertyDependencyNode(
    int PropertyIndex,
    IReadOnlyList<int> SiblingDependencyIndices,
    IReadOnlyList<string> DirectAncestorOwnedParameterNames,
    IReadOnlyList<int> SummarySiblingDependencyIndices,
    IReadOnlyList<string> SummaryVisiblePropertyDependencyNames,
    IReadOnlyList<string> RequiredAncestorOwnedParameterNames)
{
    public bool DirectlyCapturesAncestorOwnedParameters
        => DirectAncestorOwnedParameterNames.Count > 0;

    public bool RequiresAncestorOwnedParameters
        => RequiredAncestorOwnedParameterNames.Count > 0;
}

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

        public bool SetEquals(SummarySeed other)
            => RequiredAncestorOwnedParameterNames.SetEquals(other.RequiredAncestorOwnedParameterNames)
                && VisiblePropertyDependencyNames.SetEquals(other.VisiblePropertyDependencyNames);
    }

    public static PropertyDependencyGraph Build(
        Algorithm.User algorithm,
        IEnumerable<string>? ancestorOwnedNames = null,
        IEnumerable<string>? locallyOwnedNames = null)
    {
        var propertyNameToIndex = new Dictionary<string, int>(StringComparer.Ordinal);
        for (var i = 0; i < algorithm.Properties.Count; i++)
            propertyNameToIndex[algorithm.Properties[i].Name] = i;

        var siblingNames = new HashSet<string>(propertyNameToIndex.Keys, StringComparer.Ordinal);
        var ownedHere = CreateNameSet(locallyOwnedNames);
        ownedHere.UnionWith(algorithm.Params);

        var ancestorOwnedForProperties = CreateNameSet(ancestorOwnedNames);
        ancestorOwnedForProperties.UnionWith(ownedHere);

        var nodes = new PropertyDependencyNode[algorithm.Properties.Count];
        for (var i = 0; i < algorithm.Properties.Count; i++)
        {
            var property = algorithm.Properties[i];
            var siblingDependencyIndices = CollectSiblingDependencyIndices(
                property.Value.Output,
                siblingNames,
                propertyNameToIndex,
                i);
            var directAncestorOwnedParameterNames = CollectDirectAncestorOwnedParameterNames(
                property.Value,
                ancestorOwnedForProperties,
                CreateNameSet());
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
                directAncestorOwnedParameterNames,
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
        var ownedHere = CreateNameSet(locallyOwnedNames);
        ownedHere.UnionWith(algorithm.Params);

        var ancestorOwnedForChildren = CreateNameSet(ancestorOwnedNames);
        ancestorOwnedForChildren.UnionWith(ownedHere);

        var summaryOwnedHere = algorithm.IsParametrized
            ? ownedHere
            : CreateNameSet(ancestorOwnedForChildren);

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
            summaryOwnedHere,
            ancestorOwnedForChildren);
        seed.UnionWith(CollectSummarySeed(
            algorithm.Output,
            currentPropertySummaries,
            summaryOwnedHere,
            ancestorOwnedForChildren));
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

            case Expr.ResultJoin(var left, var right):
            {
                var seed = CollectSummarySeed(left, localPropertySummaries, ownedHere, ancestorOwnedForChildren);
                seed.UnionWith(CollectSummarySeed(right, localPropertySummaries, ownedHere, ancestorOwnedForChildren));
                return seed;
            }

            case Expr.Block(var algorithm):
                return CollectSummarySeed(
                    algorithm,
                    ancestorOwnedForChildren,
                    CreateNameSet());

            case Expr.Call(var function, var args):
            {
                var seed = CollectSummarySeed(function, localPropertySummaries, ownedHere, ancestorOwnedForChildren);
                seed.UnionWith(CollectSummarySeed(
                    args,
                    ancestorOwnedForChildren,
                    CreateNameSet()));
                return seed;
            }

            case Expr.DotCall(var target, _, var argsOpt):
            {
                var seed = CollectSummarySeed(target, localPropertySummaries, ownedHere, ancestorOwnedForChildren);
                if (argsOpt is not null)
                {
                    seed.UnionWith(CollectSummarySeed(
                        argsOpt,
                        ancestorOwnedForChildren,
                        CreateNameSet()));
                }

                return seed;
            }

            default:
                return new SummarySeed();
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
        IReadOnlyDictionary<string, int> propertyNameToIndex,
        int propertyIndex)
    {
        var dependencyIndices = new HashSet<int>();
        foreach (var expression in expressions)
            CollectSiblingDependencyIndices(expression, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition: false);

        return dependencyIndices.OrderBy(static idx => idx).ToArray();
    }

    private static void CollectSiblingDependencyIndices(
        Expr expr,
        HashSet<string> siblingNames,
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

            case Expr.Call(var function, _):
                CollectSiblingDependencyIndices(function, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition: true);
                break;

            case Expr.Binary(_, var left, var right):
                CollectSiblingDependencyIndices(left, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                CollectSiblingDependencyIndices(right, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.Unary(_, var operand):
                CollectSiblingDependencyIndices(operand, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.Index(var target, var selector):
                CollectSiblingDependencyIndices(target, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                CollectSiblingDependencyIndices(selector, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.ResultJoin(var left, var right):
                CollectSiblingDependencyIndices(left, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                CollectSiblingDependencyIndices(right, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.DotCall(var target, _, null):
                CollectSiblingDependencyIndices(target, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.DotCall(var target, var name, var args):
                CollectSiblingDependencyIndices(target, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition: true);
                if (args is not null && IsMathValueDotCall(target, name))
                    CollectArgumentSiblingDependencyIndices(args, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex);
                break;

            case Expr.Grace(var inner, _):
                CollectSiblingDependencyIndices(inner, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition);
                break;

            case Expr.Block:
                break;

            default:
                break;
        }
    }

    private static void CollectArgumentSiblingDependencyIndices(
        Algorithm args,
        HashSet<string> siblingNames,
        IReadOnlyDictionary<string, int> propertyNameToIndex,
        HashSet<int> dependencyIndices,
        int propertyIndex)
    {
        if (args.IsParametrized)
            return;

        foreach (var expression in args.Output)
        {
            CollectSiblingDependencyIndices(
                expression,
                siblingNames,
                propertyNameToIndex,
                dependencyIndices,
                propertyIndex,
                inCallPosition: false);
        }
    }

    private static bool IsMathValueDotCall(Expr target, string name)
        => target is Expr.Resolve { Name: "Math" }
            && BuiltinRegistry.IsMathFunctionMember(name);

    private static IReadOnlyList<string> CollectDirectAncestorOwnedParameterNames(
        Algorithm algorithm,
        HashSet<string> ancestorOwnedNames,
        HashSet<string> locallyOwnedNames)
    {
        var captures = CreateNameSet();
        CollectDirectAncestorOwnedParameterNames(algorithm, ancestorOwnedNames, locallyOwnedNames, captures);
        return captures.OrderBy(static name => name, StringComparer.Ordinal).ToArray();
    }

    private static void CollectDirectAncestorOwnedParameterNames(
        Algorithm algorithm,
        HashSet<string> ancestorOwnedNames,
        HashSet<string> locallyOwnedNames,
        HashSet<string> captures)
    {
        switch (algorithm)
        {
            case Algorithm.User user:
            {
                var ownedHere = CreateNameSet(locallyOwnedNames);
                ownedHere.UnionWith(user.Params);

                var ancestorOwnedForChildren = CreateNameSet(ancestorOwnedNames);
                ancestorOwnedForChildren.UnionWith(ownedHere);

                CollectDirectAncestorOwnedParameterNames(
                    user.Opens,
                    ancestorOwnedNames,
                    ownedHere,
                    ancestorOwnedForChildren,
                    captures);
                CollectDirectAncestorOwnedParameterNames(
                    user.Output,
                    ancestorOwnedNames,
                    ownedHere,
                    ancestorOwnedForChildren,
                    captures);
                break;
            }

            case Algorithm.Conditional conditional:
            {
                var ownedHere = CreateNameSet(locallyOwnedNames);
                var ancestorOwnedForChildren = CreateNameSet(ancestorOwnedNames);
                ancestorOwnedForChildren.UnionWith(ownedHere);

                CollectDirectAncestorOwnedParameterNames(
                    conditional.Opens,
                    ancestorOwnedNames,
                    ownedHere,
                    ancestorOwnedForChildren,
                    captures);

                foreach (var branch in conditional.Branches)
                {
                    var binderNames = CreateNameSet(branch.Pattern.BoundNames());
                    CollectDirectAncestorOwnedParameterNames(
                        branch.Body,
                        ancestorOwnedForChildren,
                        binderNames,
                        captures);
                }
                break;
            }
        }
    }

    private static void CollectDirectAncestorOwnedParameterNames(
        IReadOnlyList<Expr> expressions,
        HashSet<string> ancestorOwnedNames,
        HashSet<string> ownedHere,
        HashSet<string> ancestorOwnedForChildren,
        HashSet<string> captures)
    {
        foreach (var expression in expressions)
        {
            CollectDirectAncestorOwnedParameterNames(
                expression,
                ancestorOwnedNames,
                ownedHere,
                ancestorOwnedForChildren,
                captures);
        }
    }

    private static void CollectDirectAncestorOwnedParameterNames(
        Expr expr,
        HashSet<string> ancestorOwnedNames,
        HashSet<string> ownedHere,
        HashSet<string> ancestorOwnedForChildren,
        HashSet<string> captures)
    {
        switch (expr)
        {
            case Expr.Param(var name):
                if (!ownedHere.Contains(name) && ancestorOwnedNames.Contains(name))
                    captures.Add(name);
                break;

            case Expr.Grace(var inner, _):
                CollectDirectAncestorOwnedParameterNames(inner, ancestorOwnedNames, ownedHere, ancestorOwnedForChildren, captures);
                break;

            case Expr.Binary(_, var left, var right):
                CollectDirectAncestorOwnedParameterNames(left, ancestorOwnedNames, ownedHere, ancestorOwnedForChildren, captures);
                CollectDirectAncestorOwnedParameterNames(right, ancestorOwnedNames, ownedHere, ancestorOwnedForChildren, captures);
                break;

            case Expr.Unary(_, var operand):
                CollectDirectAncestorOwnedParameterNames(operand, ancestorOwnedNames, ownedHere, ancestorOwnedForChildren, captures);
                break;

            case Expr.Index(var target, var selector):
                CollectDirectAncestorOwnedParameterNames(target, ancestorOwnedNames, ownedHere, ancestorOwnedForChildren, captures);
                CollectDirectAncestorOwnedParameterNames(selector, ancestorOwnedNames, ownedHere, ancestorOwnedForChildren, captures);
                break;

            case Expr.ResultJoin(var left, var right):
                CollectDirectAncestorOwnedParameterNames(left, ancestorOwnedNames, ownedHere, ancestorOwnedForChildren, captures);
                CollectDirectAncestorOwnedParameterNames(right, ancestorOwnedNames, ownedHere, ancestorOwnedForChildren, captures);
                break;

            case Expr.Block(var algorithm):
                CollectDirectAncestorOwnedParameterNames(
                    algorithm,
                    ancestorOwnedForChildren,
                    CreateNameSet(),
                    captures);
                break;

            case Expr.Call(var function, var args):
                CollectDirectAncestorOwnedParameterNames(function, ancestorOwnedNames, ownedHere, ancestorOwnedForChildren, captures);
                CollectDirectAncestorOwnedParameterNames(
                    args,
                    ancestorOwnedForChildren,
                    CreateNameSet(),
                    captures);
                break;

            case Expr.DotCall(var target, _, var argsOpt):
                CollectDirectAncestorOwnedParameterNames(target, ancestorOwnedNames, ownedHere, ancestorOwnedForChildren, captures);
                if (argsOpt is not null)
                {
                    CollectDirectAncestorOwnedParameterNames(
                        argsOpt,
                        ancestorOwnedForChildren,
                        CreateNameSet(),
                        captures);
                }
                break;
        }
    }

    private static HashSet<string> CreateNameSet(IEnumerable<string>? names = null)
        => names is null
            ? new HashSet<string>(StringComparer.Ordinal)
            : new HashSet<string>(names, StringComparer.Ordinal);
}