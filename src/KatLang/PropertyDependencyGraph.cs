namespace KatLang;

internal sealed record PropertyDependencyNode(
    int PropertyIndex,
    IReadOnlyList<int> SiblingDependencyIndices);

internal sealed record PropertyDependencySummaryNode(
    int PropertyIndex,
    IReadOnlyList<int> SummarySiblingDependencyIndices,
    IReadOnlyList<string> SummaryVisiblePropertyDependencyNames,
    IReadOnlyList<string> RequiredAncestorOwnedParameterNames);

/// <summary>
/// Sibling/processing-order channel result: per-property direct sibling dependency edges and
/// the topological property-processing order derived from them. This is the ONLY channel the
/// implicit-argument resolver consumes; the recursive summary channel lives on
/// <see cref="PropertyDependencySummaryGraph"/> and is never computed here (M17).
/// </summary>
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

/// <summary>
/// Recursive summary channel result: per-property recursive ancestor-capture facts — direct
/// required ancestor-owned parameter names plus summary edges to visible names and sibling
/// properties. This is the ONLY channel the exposure resolver consumes; the sibling/order
/// channel lives on <see cref="PropertyDependencyGraph"/> and is never computed here (M17).
/// </summary>
internal sealed class PropertyDependencySummaryGraph
{
    private readonly Dictionary<string, int> propertyNameToIndex;
    private readonly PropertyDependencySummaryNode[] nodes;

    public PropertyDependencySummaryGraph(
        IReadOnlyList<Property> properties,
        Dictionary<string, int> propertyNameToIndex,
        PropertyDependencySummaryNode[] nodes)
    {
        Properties = properties;
        this.propertyNameToIndex = propertyNameToIndex;
        this.nodes = nodes;
    }

    public IReadOnlyList<Property> Properties { get; }

    public int Count => nodes.Length;

    public PropertyDependencySummaryNode this[int propertyIndex] => nodes[propertyIndex];

    public bool TryGetPropertyIndex(string propertyName, out int propertyIndex)
        => propertyNameToIndex.TryGetValue(propertyName, out propertyIndex);
}

internal static class PropertyDependencyGraphBuilder
{
    /// <summary>
    /// Mutable name-set accumulator AND value of the summary channel. Callers mutate returned
    /// seeds in place (<see cref="UnionWith"/>) while accumulating an enclosing expression's
    /// contribution, so a completed summary admitted to a memo is stored as a PRISTINE CLONE
    /// and every reach — first or later — receives its own mutable copy; returning a stored
    /// instance directly would let one reader's accumulation corrupt every later reader. For
    /// the same reason there is deliberately NO shared <c>Empty</c> singleton: every empty
    /// seed is a fresh mutable instance.
    /// </summary>
    internal sealed class SummarySeed
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

    /// <summary>
    /// Completed-summary memo for the summary channel, keyed by ALGORITHM node REFERENCE
    /// (reference identity, like every other front-end memo: two structurally equal but
    /// distinct nodes summarize independently, while host-DAG sharing is by reference). An
    /// entry is the finished summary of <c>CollectSummarySeed(algorithm, empty locally-owned
    /// names)</c>, which is a pure function of the node: the summary walk never queries what
    /// ancestors own — a free parameter reference is reported as a required ancestor-owned
    /// name regardless of the ancestor context — so the empty-locals summary carries no
    /// caller state. Conditional BRANCH bodies summarize under their per-branch binder names
    /// (a genuinely context-sensitive input) and therefore never pass through this memo.
    /// Entries are admitted only AFTER a summary is fully computed (local fixed point
    /// converged, self-owned parameters stripped); the structural preflight guarantees
    /// acyclic inputs, so a node can never be reached again while its own summary is still
    /// in flight. Lifetime is the caller's: <see cref="PropertyExposureResolver"/> creates
    /// ONE memo per resolution (never static, never cross-run) so each context-independent
    /// summary is computed once per resolution instead of once per ancestor level, and a
    /// standalone <see cref="BuildSummaries"/> call creates its own. Stored seeds follow the
    /// clone discipline documented on <see cref="SummarySeed"/>.
    /// </summary>
    internal sealed class SummaryMemo
    {
        internal Dictionary<Algorithm, SummarySeed>? CompletedAlgorithmSummaries;

        /// <summary>
        /// Completed conditional BRANCH-BODY summaries, keyed by body node REFERENCE plus the
        /// branch's binder-name SET (M4). A branch body summarizes under its binder names, so
        /// its summary is not a function of the node alone — but it IS a pure function of
        /// (node, binder names): the walk never queries anything else about its context. Two
        /// families sharing one body under the same binders therefore share one summary,
        /// while the same body under different binders (or as a plain property value, which
        /// goes through <see cref="CompletedAlgorithmSummaries"/>) summarizes independently.
        /// Same admission and clone discipline as the node-keyed memo.
        /// </summary>
        internal Dictionary<BranchBodySummaryKey, SummarySeed>? CompletedBranchBodySummaries;
    }

    /// <summary>Key of <see cref="SummaryMemo.CompletedBranchBodySummaries"/>: body by reference, binders by content.</summary>
    internal sealed record BranchBodySummaryKey(Algorithm Body, string BinderNames)
    {
        public bool Equals(BranchBodySummaryKey? other)
            => other is not null && ReferenceEquals(Body, other.Body) && BinderNames == other.BinderNames;

        public override int GetHashCode()
            => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Body), BinderNames);
    }

    /// <summary>
    /// Reference-identity memo state for ONE summary-collection region (one algorithm-level
    /// analysis, or one <see cref="BuildSummaries"/> call's top property loop): the walk's
    /// two context flavors get separate expression maps — the region's PRIMARY (its local
    /// summaries and owned-here names) and the TRANSPARENT bundle context (empty summaries,
    /// empty owned-here — call/dot-call argument bundles and capture rows, identical however
    /// deeply they nest). Stored seeds follow a CLONE discipline: callers mutate returned
    /// seeds as accumulators, so a memo keeps a pristine clone and every reach (first or
    /// later) receives its own mutable copy — semantically identical to re-walking the
    /// equivalent duplicated tree, because seed contributions are name SETS. Whole
    /// nested-algorithm summaries (property values and <see cref="Expr.AlgorithmExpr"/>
    /// contents alike, all summarized under the empty locally-owned context) live on the
    /// region-spanning <see cref="SharedMemo"/> instead, so they are computed once per memo
    /// lifetime rather than once per region; conditional BRANCH bodies stay exempt (their
    /// binder-name context varies per branch).
    /// </summary>
    private sealed class SummaryWalkMemos(SummaryMemo sharedMemo, FrontEndTraversalObservations? observations)
    {
        public Dictionary<Expr, SummarySeed>? PrimarySeeds;

        public Dictionary<Expr, SummarySeed>? TransparentSeeds;

        public readonly SummaryMemo SharedMemo = sharedMemo;

        public readonly FrontEndTraversalObservations? Observations = observations;
    }

    /// <summary>
    /// Reference-identity memo for ONE sibling-dependency collection (one property's value
    /// subtree): contributions are an index SET, so a completed node reference — split by the
    /// two context dimensions that change a node's contribution, the shadow context of the
    /// nested bodies around it and its position (value, callee, transparent) — is skipped,
    /// and a nested body reached again under the same shadow context is not re-walked.
    /// </summary>
    private sealed class SiblingWalkMemo(FrontEndTraversalObservations? observations)
    {
        private readonly Dictionary<(string Shadow, SiblingWalkPosition Position), HashSet<Expr>> _visited = new();

        private readonly Dictionary<string, HashSet<Algorithm>> _algorithms = new(StringComparer.Ordinal);

        public readonly FrontEndTraversalObservations? Observations = observations;

        public HashSet<Expr> Visited(string shadowKey, SiblingWalkPosition position)
        {
            if (!_visited.TryGetValue((shadowKey, position), out var visited))
                _visited[(shadowKey, position)] = visited = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
            return visited;
        }

        public HashSet<Algorithm> Algorithms(string shadowKey)
        {
            if (!_algorithms.TryGetValue(shadowKey, out var visited))
                _algorithms[shadowKey] = visited = new HashSet<Algorithm>(ReferenceEqualityComparer.Instance);
            return visited;
        }
    }

    /// <summary>
    /// Sibling/processing-order channel: per-property direct sibling dependency edges (and,
    /// lazily, the topological order derived from them). Deliberately computes NO summary
    /// data — the implicit-argument resolver consumes only this channel, and the recursive
    /// summary fixed-point was pure dead work on its path (M17).
    /// </summary>
    public static PropertyDependencyGraph BuildDependencyOrder(
        Algorithm.User algorithm,
        Func<string, bool>? preludeNameShadowedByCaller = null,
        FrontEndTraversalObservations? observations = null)
    {
        var propertyNameToIndex = new Dictionary<string, int>(StringComparer.Ordinal);
        for (var i = 0; i < algorithm.Properties.Count; i++)
            propertyNameToIndex[algorithm.Properties[i].Name] = i;

        var siblingNames = new HashSet<string>(propertyNameToIndex.Keys, StringComparer.Ordinal);
        var ownedHere = CreateNameSet(algorithm.Params);

        // Whether a prelude name is shadowed at this level through ordinary
        // resolution: siblings, this algorithm's own parameters, and
        // the caller-supplied ancestor knowledge (the implicit-argument
        // resolver passes its visible property map's membership test). Math
        // alias calls and canonical `Math.X` calls both consult this so the
        // sibling-order channel has the SAME binding knowledge as rewriting. A
        // PREDICATE, not a materialized union: copying the ancestor map's keys
        // per build call is O(ancestor properties) for every processed
        // property value and made wide flat scopes quadratic.
        bool PreludeNameShadowed(string name)
            => siblingNames.Contains(name)
                || ownedHere.Contains(name)
                || (preludeNameShadowedByCaller?.Invoke(name) ?? false);

        var nodes = new PropertyDependencyNode[algorithm.Properties.Count];
        for (var i = 0; i < algorithm.Properties.Count; i++)
        {
            // Every value-position sibling reference in the property's whole value subtree
            // — output rows, nested property values, block literals, capture rows, and
            // conditional branch bodies alike — is a processing-order dependency, because the
            // resolver rewrites all of it while processing this property.
            var dependencyIndices = new HashSet<int>();
            CollectAlgorithmSiblingDependencyIndices(
                algorithm.Properties[i].Value,
                new SiblingWalkContext(siblingNames, propertyNameToIndex, dependencyIndices, i, new SiblingWalkMemo(observations)),
                ShadowScope.Level(PreludeNameShadowed));
            nodes[i] = new PropertyDependencyNode(i, dependencyIndices.OrderBy(static idx => idx).ToArray());
        }

        return new PropertyDependencyGraph(algorithm.Properties, propertyNameToIndex, nodes);
    }

    /// <summary>
    /// Recursive summary channel: per-property recursive ancestor-capture facts for the
    /// exposure resolver. Deliberately computes NO sibling/order data (M17). A
    /// caller-supplied <paramref name="memo"/> extends completed-summary reuse across every
    /// <see cref="BuildSummaries"/> call of one logical analysis (the exposure resolver
    /// passes one memo per resolution, so a nested algorithm's summary is computed once
    /// rather than once per ancestor level); with no memo the call is standalone and
    /// creates its own.
    /// </summary>
    public static PropertyDependencySummaryGraph BuildSummaries(
        Algorithm.User algorithm,
        SummaryMemo? memo = null,
        FrontEndTraversalObservations? observations = null)
    {
        var propertyNameToIndex = new Dictionary<string, int>(StringComparer.Ordinal);
        for (var i = 0; i < algorithm.Properties.Count; i++)
            propertyNameToIndex[algorithm.Properties[i].Name] = i;

        // One memo bundle spans the whole BuildSummaries call: every property value below is
        // summarized under the same empty locally-owned context, so two properties sharing
        // ONE value algorithm summarize it once — and the caller's shared memo carries the
        // same completed summaries across nesting levels.
        var buildMemos = new SummaryWalkMemos(memo ?? new SummaryMemo(), observations);
        var nodes = new PropertyDependencySummaryNode[algorithm.Properties.Count];
        for (var i = 0; i < algorithm.Properties.Count; i++)
        {
            var summarySeed = CollectSharedAlgorithmSummarySeed(algorithm.Properties[i].Value, buildMemos);
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

            nodes[i] = new PropertyDependencySummaryNode(
                i,
                summarySiblingDependencyIndices.OrderBy(static idx => idx).ToArray(),
                summaryVisiblePropertyDependencyNames.OrderBy(static name => name, StringComparer.Ordinal).ToArray(),
                summarySeed.RequiredAncestorOwnedParameterNames.OrderBy(static name => name, StringComparer.Ordinal).ToArray());
        }

        return new PropertyDependencySummaryGraph(algorithm.Properties, propertyNameToIndex, nodes);
    }

    /// <summary>
    /// Memo-shared nested-algorithm summary for the constant empty locally-owned context —
    /// see <see cref="SummaryMemo"/> for why that summary is a pure function of the node
    /// reference and <see cref="SummarySeed"/> for the clone discipline. The observation
    /// counter records completed COMPUTATIONS (memo misses) only, so an observed analysis
    /// is pinned to at most one computation per distinct algorithm node per memo lifetime.
    /// </summary>
    private static SummarySeed CollectSharedAlgorithmSummarySeed(
        Algorithm algorithm,
        SummaryWalkMemos memos)
    {
        var completedSummaries = memos.SharedMemo.CompletedAlgorithmSummaries ??= new(ReferenceEqualityComparer.Instance);
        if (completedSummaries.TryGetValue(algorithm, out var stored))
            return stored.Clone();

        memos.Observations?.RecordDependencyAlgorithmSummaryComputation();
        var seed = CollectSummarySeed(algorithm, CreateNameSet(), memos.SharedMemo, memos.Observations);
        completedSummaries[algorithm] = seed.Clone();
        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        Algorithm algorithm,
        HashSet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations)
    {
        switch (algorithm)
        {
            case Algorithm.User user:
                return CollectSummarySeed(user, locallyOwnedNames, sharedMemo, observations);

            case Algorithm.Conditional conditional:
                return CollectSummarySeed(conditional, locallyOwnedNames, sharedMemo, observations);

            default:
                return new SummarySeed();
        }
    }

    private static SummarySeed CollectSummarySeed(
        Algorithm.User algorithm,
        HashSet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations)
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

        // Ownership attribution follows the same transparency model as
        // ParameterDetector: transparent OutputBundle content (call/dot-call
        // argument bundles, surviving parenthesized groups) owns no names, so
        // its walk uses the enclosing algorithm's owned-name set. A parameter
        // reference inside such a layer therefore seeds the same
        // ancestor-capture requirement as the identical reference written
        // directly in the enclosing owner; the final
        // RemoveRequiredAncestorOwnedParameterNames strip below keeps each
        // algorithm's self-owned parameters out of the summary it returns. What
        // ancestors own is deliberately NOT an input: a parameter reference not
        // owned within this walk is reported as a required ancestor-owned name
        // regardless, which is what makes the empty-locals summary a pure
        // function of the node (see SummaryMemo).

        // One expression-memo bundle per algorithm-level analysis region: the property base
        // seeds and the opens/output walks below all run against this region's local-summary
        // and owned-here context (property values and nested AlgorithmExpr contents go
        // through the shared completed-summary memo instead).
        var memos = new SummaryWalkMemos(sharedMemo, observations);
        var currentPropertySummaries = new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
        var propertyBaseSeeds = new SummarySeed[algorithm.Properties.Count];
        for (var i = 0; i < algorithm.Properties.Count; i++)
        {
            var property = algorithm.Properties[i];
            currentPropertySummaries[property.Name] = new SummarySeed();
            propertyBaseSeeds[i] = CollectSharedAlgorithmSummarySeed(property.Value, memos);
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
            memos,
            inTransparentContext: false);
        seed.UnionWith(CollectSummarySeed(
            algorithm.Output,
            currentPropertySummaries,
            ownedHere,
            memos,
            inTransparentContext: false));
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
        HashSet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations)
    {
        var ownedHere = CreateNameSet(locallyOwnedNames);

        var seed = CollectSummarySeed(
            algorithm.Opens,
            new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
            ownedHere,
            new SummaryWalkMemos(sharedMemo, observations),
            inTransparentContext: false);

        foreach (var branch in algorithm.Branches)
        {
            // Branch bodies deliberately bypass the node-keyed completed-summary memo: their
            // binder-name context varies per branch, so their summaries are NOT pure
            // functions of the body node (see SummaryMemo). They are pure functions of
            // (body, binder names), which the branch-body memo keys on — so a body shared by
            // several families under the same binders is summarized once (M4).
            seed.UnionWith(CollectBranchBodySummarySeed(branch, sharedMemo, observations));
        }

        return seed;
    }

    /// <summary>
    /// Memo-shared branch-body summary for one (body, binder-name set) — see
    /// <see cref="SummaryMemo.CompletedBranchBodySummaries"/>. Records completed computations
    /// (memo misses) only, like <see cref="CollectSharedAlgorithmSummarySeed"/>.
    /// </summary>
    private static SummarySeed CollectBranchBodySummarySeed(
        CondBranch branch,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations)
    {
        var binderNames = branch.Pattern.BoundNames();
        var key = new BranchBodySummaryKey(branch.Body, FrontEndRegionKeys.NameSet(binderNames));
        var completedSummaries = sharedMemo.CompletedBranchBodySummaries ??= new();
        if (completedSummaries.TryGetValue(key, out var stored))
            return stored.Clone();

        observations?.RecordDependencyBranchBodySummaryComputation();
        var seed = CollectSummarySeed(branch.Body, CreateNameSet(binderNames), sharedMemo, observations);
        completedSummaries[key] = seed.Clone();
        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        IReadOnlyList<Expr> expressions,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        HashSet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
    {
        var seed = new SummarySeed();
        foreach (var expression in expressions)
            seed.UnionWith(CollectSummarySeed(expression, localPropertySummaries, ownedHere, memos, inTransparentContext));

        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        Expr expr,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        HashSet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
    {
        // DAG-safety: a shared node reference is summarized once per (region, context
        // flavor); every reach receives its own mutable CLONE of the pristine stored seed
        // (see SummaryWalkMemos), which is exactly what re-walking the duplicated tree
        // would contribute. The inTransparentContext flag travels in lock-step with the
        // empty summaries/owned-here maps the transparent arms pass. Childless leaves
        // build their seed in place.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return CollectSummarySeedCore(expr, localPropertySummaries, ownedHere, memos, inTransparentContext);

        var seedMap = inTransparentContext
            ? memos.TransparentSeeds ??= new(ReferenceEqualityComparer.Instance)
            : memos.PrimarySeeds ??= new(ReferenceEqualityComparer.Instance);
        if (seedMap.TryGetValue(expr, out var stored))
            return stored.Clone();

        memos.Observations?.RecordDependencySeedExpansion();
        var seed = CollectSummarySeedCore(expr, localPropertySummaries, ownedHere, memos, inTransparentContext);
        seedMap[expr] = seed.Clone();
        return seed;
    }

    private static SummarySeed CollectSummarySeedCore(
        Expr expr,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        HashSet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
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
                return CollectSummarySeed(inner, localPropertySummaries, ownedHere, memos, inTransparentContext);

            case Expr.Binary(_, var left, var right):
            {
                var seed = CollectSummarySeed(left, localPropertySummaries, ownedHere, memos, inTransparentContext);
                seed.UnionWith(CollectSummarySeed(right, localPropertySummaries, ownedHere, memos, inTransparentContext));
                return seed;
            }

            case Expr.Unary(_, var operand):
                return CollectSummarySeed(operand, localPropertySummaries, ownedHere, memos, inTransparentContext);

            case Expr.Index(var target, var selector):
            {
                var seed = CollectSummarySeed(target, localPropertySummaries, ownedHere, memos, inTransparentContext);
                seed.UnionWith(CollectSummarySeed(selector, localPropertySummaries, ownedHere, memos, inTransparentContext));
                return seed;
            }

            case Expr.SequenceSpread(var operand):
            {
                var seed = CollectSummarySeed(operand, localPropertySummaries, ownedHere, memos, inTransparentContext);
                return seed;
            }

            case Expr.SequenceConstruct(var left, var right):
            {
                var seed = CollectSummarySeed(left, localPropertySummaries, ownedHere, memos, inTransparentContext);
                seed.UnionWith(CollectSummarySeed(right, localPropertySummaries, ownedHere, memos, inTransparentContext));
                return seed;
            }

            case Expr.ListLiteral(var listItems):
            {
                var seed = new SummarySeed();
                foreach (var item in listItems)
                    seed.UnionWith(CollectSummarySeed(item, localPropertySummaries, ownedHere, memos, inTransparentContext));
                return seed;
            }

            case Expr.AlgorithmExpr(var algorithm):
                return CollectSharedAlgorithmSummarySeed(algorithm, memos);

            case Expr.Capture(var captureBody):
                // A capture owns no names: its rows walk with an empty
                // owned-here set and an empty local-summary map — exactly what
                // the pre-split transparent wrapper algorithm's output walk did
                // (the same attribution as call-argument bundles).
                return CollectSummarySeed(
                    captureBody,
                    new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
                    CreateNameSet(),
                    memos,
                    inTransparentContext: true);

            case Expr.Call(var function, var args):
            {
                // An argument bundle owns no names: slots walk with an empty
                // owned-here set and an empty local-summary map — the same
                // attribution as capture rows (and as the pre-Track-B empty
                // transparent args wrapper).
                var seed = CollectSummarySeed(function, localPropertySummaries, ownedHere, memos, inTransparentContext);
                seed.UnionWith(CollectSummarySeed(
                    args,
                    new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
                    CreateNameSet(),
                    memos,
                    inTransparentContext: true));
                return seed;
            }

            case Expr.DotCall dotCall:
            {
                var seed = CollectSummarySeed(dotCall.Target, localPropertySummaries, ownedHere, memos, inTransparentContext);

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
                        memos,
                        inTransparentContext));
                }

                if (dotCall.Args is { } argsOpt)
                {
                    seed.UnionWith(CollectSummarySeed(
                        argsOpt,
                        new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
                        CreateNameSet(),
                        memos,
                        inTransparentContext: true));
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

    /// <summary>
    /// The constant inputs of ONE property's sibling-dependency collection: the sibling name
    /// set, the level's prelude-shadow predicate, the name→index map, the accumulating index
    /// set, the property's own index, and the walk memo.
    /// </summary>
    private sealed record SiblingWalkContext(
        HashSet<string> SiblingNames,
        IReadOnlyDictionary<string, int> PropertyNameToIndex,
        HashSet<int> DependencyIndices,
        int PropertyIndex,
        SiblingWalkMemo Memo);

    /// <summary>
    /// The names bound by the bodies between a property's value and the node being walked
    /// (the value's own properties included: its output rows resolve inside its own scope). A
    /// body's own property names shadow same-named siblings for everything inside it —
    /// ownership-first lookup reaches the enclosing level's siblings before any open — so a
    /// shadowed reference is no processing-order dependency; binders and parameters are
    /// already <see cref="Expr.Param"/>s and never match a sibling name. The scope composes
    /// the level's prelude-shadow predicate with those names, so a nested <c>abs</c> property
    /// shadows the alias inside that body exactly as a sibling <c>abs</c> does at the level.
    /// <see cref="Key"/> is the content identity the walk memo splits on.
    /// </summary>
    private sealed class ShadowScope
    {
        private readonly HashSet<string> _names;

        private ShadowScope(HashSet<string> names, string key, Func<string, bool> preludeNameShadowed)
        {
            _names = names;
            Key = key;
            PreludeNameShadowed = preludeNameShadowed;
        }

        public static ShadowScope Level(Func<string, bool> preludeNameShadowed)
            => new(CreateNameSet(), "", preludeNameShadowed);

        public string Key { get; }

        public Func<string, bool> PreludeNameShadowed { get; }

        public bool Shadows(string name) => _names.Contains(name);

        public ShadowScope Enter(Algorithm body)
        {
            if (body.Properties.Count == 0)
                return this;

            var names = new HashSet<string>(_names, StringComparer.Ordinal);
            foreach (var property in body.Properties)
                names.Add(property.Name);
            var outer = PreludeNameShadowed;
            return new ShadowScope(names, FrontEndRegionKeys.NameSet(names), name => names.Contains(name) || outer(name));
        }
    }

    /// <summary>
    /// The position a walked expression stands in, which decides what a name contributes —
    /// mirroring what the resolver reads there: a VALUE-position sibling reference is lifted
    /// (its signature is read); a CALLEE is not (called siblings are not order
    /// dependencies, the same rule as Call function position); a TRANSPARENT context (neutral
    /// call arguments, capture rows — <c>ImplicitArgumentResolver.ProcessExprNested</c>)
    /// lifts nothing, so only the nested algorithms inside it contribute.
    /// </summary>
    private enum SiblingWalkPosition
    {
        Value,
        Callee,
        Transparent,
    }

    /// <summary>
    /// Collects the sibling dependencies of ONE property value: every value-position sibling
    /// reference anywhere in the value's subtree that no nested body shadows — its output
    /// rows, its nested property values, block literals and capture rows in expression
    /// position, and every branch body of a conditional family — because the resolver
    /// rewrites all of those while processing the property and reads each referenced
    /// sibling's CURRENT signature there. Complete edges are what make the topological order
    /// process a sibling before every consumer, whatever the declaration order, so no
    /// consumer's rewrite depends on where it was written. Memoized per (node, shadow
    /// context, position): a shared subtree is walked once per context, never once per path.
    /// </summary>
    private static void CollectAlgorithmSiblingDependencyIndices(
        Algorithm value,
        SiblingWalkContext context,
        ShadowScope shadow)
    {
        switch (value)
        {
            case Algorithm.User user:
            {
                var inner = shadow.Enter(user);
                if (!context.Memo.Algorithms(inner.Key).Add(user))
                    return;

                foreach (var row in user.Output)
                    CollectSiblingDependencyIndices(row, context, inner, SiblingWalkPosition.Value);

                foreach (var property in user.Properties)
                    CollectAlgorithmSiblingDependencyIndices(property.Value, context, inner);
                break;
            }

            case Algorithm.Conditional conditional:
            {
                if (!context.Memo.Algorithms(shadow.Key).Add(conditional))
                    return;

                // Family-owned opens are open targets, which the resolver never reads through
                // the signature map; binders are Params. Each branch body is a body of its own,
                // resolved inside the family's scope.
                foreach (var branch in conditional.Branches)
                    CollectAlgorithmSiblingDependencyIndices(branch.Body, context, shadow);
                break;
            }

            case Algorithm.Builtin:
                break;

            default:
                throw new InvalidOperationException(
                    $"Unhandled Algorithm variant in {nameof(PropertyDependencyGraphBuilder)}.{nameof(CollectAlgorithmSiblingDependencyIndices)}: {value.GetType().Name}.");
        }
    }

    private static void CollectSiblingDependencyIndices(
        Expr expr,
        SiblingWalkContext context,
        ShadowScope shadow,
        SiblingWalkPosition position)
    {
        // DAG-safety: contributions are index-set idempotent, so a completed node reference
        // reached again under the same shadow context and position is skipped (see
        // SiblingWalkMemo).
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
        {
            CollectSiblingDependencyIndicesCore(expr, context, shadow, position);
            return;
        }

        var visited = context.Memo.Visited(shadow.Key, position);
        if (visited.Contains(expr))
            return;

        context.Memo.Observations?.RecordDependencySiblingExpansion();
        CollectSiblingDependencyIndicesCore(expr, context, shadow, position);
        visited.Add(expr);
    }

    /// <summary>A child of a value or callee expression stands in value position; a child of a transparent one stays transparent.</summary>
    private static SiblingWalkPosition ChildPosition(SiblingWalkPosition position)
        => position == SiblingWalkPosition.Transparent ? SiblingWalkPosition.Transparent : SiblingWalkPosition.Value;

    private static void CollectSiblingDependencyIndicesCore(
        Expr expr,
        SiblingWalkContext context,
        ShadowScope shadow,
        SiblingWalkPosition position)
    {
        var child = ChildPosition(position);
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (position == SiblingWalkPosition.Value
                    && !shadow.Shadows(name)
                    && context.SiblingNames.Contains(name)
                    && context.PropertyNameToIndex.TryGetValue(name, out var dependencyIndex)
                    && dependencyIndex != context.PropertyIndex)
                {
                    context.DependencyIndices.Add(dependencyIndex);
                }
                break;

            case Expr.Call(var function, var callArgs) call:
                CollectSiblingDependencyIndices(
                    function, context, shadow, position == SiblingWalkPosition.Transparent ? SiblingWalkPosition.Transparent : SiblingWalkPosition.Callee);

                // An unshadowed Math-ALIAS call has the same registry-proven
                // strict-value argument contract as the written `Math.X(...)`
                // dot shape (the DotCall arm below), classified by the shared
                // alias-call twin: the resolver lifts its argument slots as value
                // positions, so those slots contribute the same sibling
                // processing-order dependencies here. Ordinary neutral call
                // arguments lift nothing (transparent), so only the nested
                // algorithms inside them contribute.
                CollectArgumentSiblingDependencyIndices(
                    callArgs,
                    context,
                    shadow,
                    position != SiblingWalkPosition.Transparent && call.HasRegistryProvenStrictValueArguments(shadow.PreludeNameShadowed)
                        ? SiblingWalkPosition.Value
                        : SiblingWalkPosition.Transparent);
                break;

            case Expr.Binary(_, var left, var right):
                CollectSiblingDependencyIndices(left, context, shadow, child);
                CollectSiblingDependencyIndices(right, context, shadow, child);
                break;

            case Expr.Unary(_, var operand):
                CollectSiblingDependencyIndices(operand, context, shadow, child);
                break;

            case Expr.Index(var target, var selector):
                CollectSiblingDependencyIndices(target, context, shadow, child);
                CollectSiblingDependencyIndices(selector, context, shadow, child);
                break;

            case Expr.SequenceSpread(var operand):
                CollectSiblingDependencyIndices(operand, context, shadow, child);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectSiblingDependencyIndices(left, context, shadow, child);
                CollectSiblingDependencyIndices(right, context, shadow, child);
                break;

            case Expr.ListLiteral(var listItems):
                foreach (var item in listItems)
                    CollectSiblingDependencyIndices(item, context, shadow, child);
                break;

            case Expr.DotCall(var target, _, null):
                CollectSiblingDependencyIndices(target, context, shadow, child);
                break;

            case Expr.DotCall dotCall:
                CollectSiblingDependencyIndices(
                    dotCall.Target, context, shadow, position == SiblingWalkPosition.Transparent ? SiblingWalkPosition.Transparent : SiblingWalkPosition.Callee);
                if (dotCall.Args is { } args)
                {
                    CollectArgumentSiblingDependencyIndices(
                        args,
                        context,
                        shadow,
                        position != SiblingWalkPosition.Transparent && dotCall.HasRegistryProvenStrictValueArguments(shadow.PreludeNameShadowed)
                            ? SiblingWalkPosition.Value
                            : SiblingWalkPosition.Transparent);
                }
                break;

            case Expr.Grace(var inner, _):
                CollectSiblingDependencyIndices(inner, context, shadow, position);
                break;

            case Expr.AlgorithmExpr(var nested):
                // A block literal is a body of its own in every position: the resolver
                // rewrites it (and reads sibling signatures inside it) wherever it stands.
                CollectAlgorithmSiblingDependencyIndices(nested, context, shadow);
                break;

            case Expr.Capture(var captureBody):
                // Capture rows are transparent (no lifting at this level); their nested
                // algorithms still contribute.
                foreach (var row in captureBody)
                    CollectSiblingDependencyIndices(row, context, shadow, SiblingWalkPosition.Transparent);
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
        SiblingWalkContext context,
        ShadowScope shadow,
        SiblingWalkPosition position)
    {
        foreach (var expression in args)
            CollectSiblingDependencyIndices(expression, context, shadow, position);
    }

    private static HashSet<string> CreateNameSet(IEnumerable<string>? names = null)
        => names is null
            ? new HashSet<string>(StringComparer.Ordinal)
            : new HashSet<string>(names, StringComparer.Ordinal);
}
