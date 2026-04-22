namespace KatLang;

internal sealed record PropertyDependencyNode(
    int PropertyIndex,
    IReadOnlyList<int> SiblingDependencyIndices,
    IReadOnlyList<string> DirectAncestorOwnedParameterNames)
{
    public bool DirectlyCapturesAncestorOwnedParameters
        => DirectAncestorOwnedParameterNames.Count > 0;
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
            nodes[i] = new PropertyDependencyNode(
                i,
                siblingDependencyIndices,
                directAncestorOwnedParameterNames);
        }

        return new PropertyDependencyGraph(algorithm.Properties, propertyNameToIndex, nodes);
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

            case Expr.Combine(var left, var right):
                CollectSiblingDependencyIndices(left, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                CollectSiblingDependencyIndices(right, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.DotCall(var target, _, null):
                CollectSiblingDependencyIndices(target, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, false);
                break;

            case Expr.DotCall(var target, _, _):
                CollectSiblingDependencyIndices(target, siblingNames, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition: true);
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

            case Expr.Combine(var left, var right):
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