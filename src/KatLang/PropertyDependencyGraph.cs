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
    /// Reference-identity memo for ONE sibling-dependency collection (one property's rows):
    /// contributions are an index SET, so a completed node reference — split by call
    /// position, the one context dimension that changes a node's contribution — is skipped.
    /// </summary>
    private sealed class SiblingWalkMemo(FrontEndTraversalObservations? observations)
    {
        public readonly HashSet<Expr> ValueVisited = new(ReferenceEqualityComparer.Instance);

        public HashSet<Expr>? CalleeVisited;

        public readonly FrontEndTraversalObservations? Observations = observations;
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
            nodes[i] = new PropertyDependencyNode(
                i,
                CollectSiblingDependencyIndices(
                    algorithm.Properties[i].Value.Output,
                    siblingNames,
                    PreludeNameShadowed,
                    propertyNameToIndex,
                    i,
                    new SiblingWalkMemo(observations)));
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
            // Branch bodies deliberately bypass the shared completed-summary memo: their
            // binder-name context varies per branch, so their summaries are NOT pure
            // functions of the body node (see SummaryMemo).
            seed.UnionWith(CollectSummarySeed(
                branch.Body,
                CreateNameSet(branch.Pattern.BoundNames()),
                sharedMemo,
                observations));
        }

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

    private static IReadOnlyList<int> CollectSiblingDependencyIndices(
        IReadOnlyList<Expr> expressions,
        HashSet<string> siblingNames,
        Func<string, bool> preludeNameShadowed,
        IReadOnlyDictionary<string, int> propertyNameToIndex,
        int propertyIndex,
        SiblingWalkMemo memo)
    {
        var dependencyIndices = new HashSet<int>();
        foreach (var expression in expressions)
            CollectSiblingDependencyIndices(expression, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition: false, memo);

        return dependencyIndices.OrderBy(static idx => idx).ToArray();
    }

    private static void CollectSiblingDependencyIndices(
        Expr expr,
        HashSet<string> siblingNames,
        Func<string, bool> preludeNameShadowed,
        IReadOnlyDictionary<string, int> propertyNameToIndex,
        HashSet<int> dependencyIndices,
        int propertyIndex,
        bool inCallPosition,
        SiblingWalkMemo memo)
    {
        // DAG-safety: contributions are index-set idempotent, so a completed node reference
        // reached again under the same call-position flavor is skipped (see SiblingWalkMemo).
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
        {
            CollectSiblingDependencyIndicesCore(expr, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition, memo);
            return;
        }

        var visited = inCallPosition
            ? memo.CalleeVisited ??= new(ReferenceEqualityComparer.Instance)
            : memo.ValueVisited;
        if (visited.Contains(expr))
            return;

        memo.Observations?.RecordDependencySiblingExpansion();
        CollectSiblingDependencyIndicesCore(expr, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition, memo);
        visited.Add(expr);
    }

    private static void CollectSiblingDependencyIndicesCore(
        Expr expr,
        HashSet<string> siblingNames,
        Func<string, bool> preludeNameShadowed,
        IReadOnlyDictionary<string, int> propertyNameToIndex,
        HashSet<int> dependencyIndices,
        int propertyIndex,
        bool inCallPosition,
        SiblingWalkMemo memo)
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
                CollectSiblingDependencyIndices(function, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition: true, memo);

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
                    CollectArgumentSiblingDependencyIndices(callArgs, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, memo);
                }
                break;

            case Expr.Binary(_, var left, var right):
                CollectSiblingDependencyIndices(left, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false, memo);
                CollectSiblingDependencyIndices(right, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false, memo);
                break;

            case Expr.Unary(_, var operand):
                CollectSiblingDependencyIndices(operand, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false, memo);
                break;

            case Expr.Index(var target, var selector):
                CollectSiblingDependencyIndices(target, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false, memo);
                CollectSiblingDependencyIndices(selector, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false, memo);
                break;

            case Expr.SequenceSpread(var operand):
                CollectSiblingDependencyIndices(operand, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false, memo);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectSiblingDependencyIndices(left, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false, memo);
                CollectSiblingDependencyIndices(right, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false, memo);
                break;

            case Expr.ListLiteral(var listItems):
                foreach (var item in listItems)
                    CollectSiblingDependencyIndices(item, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false, memo);
                break;

            case Expr.DotCall(var target, _, null):
                CollectSiblingDependencyIndices(target, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, false, memo);
                break;

            case Expr.DotCall dotCall:
                CollectSiblingDependencyIndices(dotCall.Target, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition: true, memo);
                if (dotCall.Args is { } args
                    && dotCall.HasRegistryProvenStrictValueArguments(preludeNameShadowed))
                {
                    CollectArgumentSiblingDependencyIndices(args, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, memo);
                }
                break;

            case Expr.Grace(var inner, _):
                CollectSiblingDependencyIndices(inner, siblingNames, preludeNameShadowed, propertyNameToIndex, dependencyIndices, propertyIndex, inCallPosition, memo);
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
        int propertyIndex,
        SiblingWalkMemo memo)
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
                inCallPosition: false,
                memo);
        }
    }

    private static HashSet<string> CreateNameSet(IEnumerable<string>? names = null)
        => names is null
            ? new HashSet<string>(StringComparer.Ordinal)
            : new HashSet<string>(names, StringComparer.Ordinal);
}
