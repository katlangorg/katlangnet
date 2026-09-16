using System.Runtime.CompilerServices;

namespace KatLang;

internal readonly record struct OwnerQualifiedParameter(string Name, Algorithm? Owner)
{
    private sealed record Identity(long Value);
    private static long _nextIdentity;
    private static readonly ConditionalWeakTable<Algorithm, Identity> Identities = new();
    internal static long OwnerKey(Algorithm owner) => Identities.GetValue(owner, static _ => new(Interlocked.Increment(ref _nextIdentity))).Value;
    internal string ContentKey => $"{(Owner is null ? 0 : OwnerKey(Owner))}:{Name.Length}:{Name}";
    public bool Equals(OwnerQualifiedParameter other) => Name == other.Name && ReferenceEquals(Owner, other.Owner);
    public override int GetHashCode() => HashCode.Combine(Name, Owner is null ? 0 : RuntimeHelpers.GetHashCode(Owner));
}

internal sealed record PropertyDependencyNode(
    int PropertyIndex,
    IReadOnlyList<int> SiblingDependencyIndices);

internal sealed record PropertyDependencySummaryNode(
    int PropertyIndex,
    IReadOnlyList<int> SummarySiblingDependencyIndices,
    IReadOnlyList<string> SummaryVisiblePropertyDependencyNames,
    IReadOnlyList<string> RequiredAncestorOwnedParameterNames,
    IReadOnlyList<PendingReference> PendingReferences,
    IReadOnlyList<OwnerQualifiedParameter> OwnerQualifiedParameters);

/// <summary>
/// A reference the scope-free summary walk could not reduce to a bare visible name: a
/// static member PATH (<c>Inner.X</c> — <see cref="Head"/> <c>Inner</c>, <see cref="Members"/>
/// <c>[X]</c>), and/or a name that escaped a level owning <c>open</c> declarations, whose
/// providers are carried as <see cref="Candidates"/> (innermost level first — the order
/// <c>open</c> lookup consults them). The owning level's resolver settles it with the
/// ownership-first rule: the head as a PROPERTY of the chain first, then the candidates in
/// order, then the owning level's and its ancestors' own opens (Lean/evaluator:
/// <c>lookupLexicalProperty</c> then <c>lookupOpenPropertiesInChain</c>). Navigated members
/// charge THEIR requirement summaries — that is what makes a container that reads a captured
/// member through <c>Inner.X</c> or <c>open Inner</c> itself local-only. Immutable; equality
/// is by content so a summary fixed point can compare seeds.
/// </summary>
internal sealed class PendingReference : IEquatable<PendingReference>
{
    public PendingReference(string head, IReadOnlyList<string> members, IReadOnlyList<OpenCandidate> candidates,
        IReadOnlyList<Algorithm>? boundOwners = null)
    {
        Head = head;
        Members = members;
        Candidates = candidates;
        BoundOwners = boundOwners ?? [];
        ResolutionKey = KeyParts([head, KeyParts(members), KeyParts(candidates.Select(static candidate => candidate.ContentKey))]);
        ContentKey = KeyParts([ResolutionKey, string.Join(",", BoundOwners.Select(OwnerQualifiedParameter.OwnerKey).Order())]);
    }

    public string Head { get; }

    /// <summary>Member steps navigated structurally after the head (any visibility).</summary>
    public IReadOnlyList<string> Members { get; }

    /// <summary>Open providers of the levels the reference escaped, innermost first.</summary>
    public IReadOnlyList<OpenCandidate> Candidates { get; }
    public IReadOnlyList<Algorithm> BoundOwners { get; }

    internal string ContentKey { get; }
    internal string ResolutionKey { get; }

    internal static string KeyParts(IEnumerable<string> parts)
        => string.Concat(parts.Select(static part => $"{part.Length}:{part}"));

    public PendingReference WithCandidates(IReadOnlyList<OpenCandidate> candidates)
        => new(Head, Members, candidates, BoundOwners);

    public PendingReference BoundBy(Algorithm owner)
        => owner.Params.Count == 0 || BoundOwners.Any(a => ReferenceEquals(a, owner))
            ? this : new(Head, Members, Candidates, [.. BoundOwners, owner]);

    public bool Equals(PendingReference? other) => other is not null && ContentKey == other.ContentKey;

    public override bool Equals(object? obj) => Equals(obj as PendingReference);

    public override int GetHashCode() => ContentKey.GetHashCode(StringComparison.Ordinal);
}

/// <summary>
/// Union of pending requirements. Repeated references with the same resolution context
/// discharge an owner only when EVERY occurrence binds it. Intersecting those bound sets
/// implements (requirements - bound1) union (requirements - bound2), without enumerating
/// the exponentially many call paths of a shared algorithm DAG.
/// </summary>
internal sealed class PendingReferenceSet : IReadOnlyCollection<PendingReference>
{
    private readonly Dictionary<string, PendingReference> _references = new(StringComparer.Ordinal);
    public PendingReferenceSet() { }
    public PendingReferenceSet(IEnumerable<PendingReference> references) => UnionWith(references);
    public int Count => _references.Count;
    public void Clear() => _references.Clear();
    public void Add(PendingReference reference)
    {
        if (!_references.TryGetValue(reference.ResolutionKey, out var existing))
        {
            _references.Add(reference.ResolutionKey, reference);
            return;
        }
        var common = existing.BoundOwners.Where(owner => reference.BoundOwners.Any(other => ReferenceEquals(owner, other))).ToArray();
        if (common.Length != existing.BoundOwners.Count)
            _references[reference.ResolutionKey] = new(existing.Head, existing.Members, existing.Candidates, common);
    }
    public void UnionWith(IEnumerable<PendingReference> references)
    {
        foreach (var reference in references) Add(reference);
    }
    public bool SetEquals(PendingReferenceSet other)
        => Count == other.Count && _references.All(pair => other._references.TryGetValue(pair.Key, out var value) && pair.Value.Equals(value));
    public IEnumerator<PendingReference> GetEnumerator() => _references.Values.GetEnumerator();
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
}

/// <summary>
/// One <c>open</c> target of a level a <see cref="PendingReference"/> escaped. RESOLVED when
/// the level could settle it in place — the target's head was that level's own property (or an
/// inline block) and it provides the referenced name — carrying the charged requirement seed,
/// relative to the level above the one that resolved it (later levels expand it like every
/// other escaping seed). UNRESOLVED when the target's head was not a property of that level:
/// the head name and the public steps of the dotted target are carried outward for a level
/// whose direct chain declares the head. A target that provides nothing is not a candidate.
/// </summary>
internal abstract class OpenCandidate
{
    internal abstract string ContentKey { get; }
}

internal sealed class ResolvedOpenCandidate(PropertyDependencyGraphBuilder.SummarySeed seed) : OpenCandidate
{
    /// <summary>Frozen: never mutated after construction; readers clone before accumulating.</summary>
    public PropertyDependencyGraphBuilder.SummarySeed Seed { get; } = seed;

    internal override string ContentKey => $"resolved({Seed.ContentKey})";
}

internal sealed class UnresolvedOpenCandidate(string head, IReadOnlyList<string> publicSteps) : OpenCandidate
{
    public string Head { get; } = head;

    public IReadOnlyList<string> PublicSteps { get; } = publicSteps;

    internal override string ContentKey => "open" + PendingReference.KeyParts([Head, PendingReference.KeyParts(PublicSteps)]);
}

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
            IEnumerable<string>? visiblePropertyDependencyNames = null,
            IEnumerable<PendingReference>? pendingReferences = null,
            IEnumerable<OwnerQualifiedParameter>? ownerQualifiedParameters = null)
        {
            RequiredAncestorOwnedParameterNames = CreateNameSet(requiredAncestorOwnedParameterNames);
            VisiblePropertyDependencyNames = CreateNameSet(visiblePropertyDependencyNames);
            PendingReferences = pendingReferences is null ? new() : new(pendingReferences);
            OwnerQualifiedParameters = ownerQualifiedParameters is null ? [] : new(ownerQualifiedParameters);
        }

        public HashSet<string> RequiredAncestorOwnedParameterNames { get; }
        public HashSet<OwnerQualifiedParameter> OwnerQualifiedParameters { get; }

        /// <summary>Bare names no level between the reference and the consumer resolved, with no open providers on the way.</summary>
        public HashSet<string> VisiblePropertyDependencyNames { get; }

        /// <summary>Member paths and open-shadowed names (see <see cref="PendingReference"/>).</summary>
        public PendingReferenceSet PendingReferences { get; }

        public SummarySeed Clone()
            => new(RequiredAncestorOwnedParameterNames, VisiblePropertyDependencyNames, PendingReferences, OwnerQualifiedParameters);

        public void UnionWith(SummarySeed other)
        {
            RequiredAncestorOwnedParameterNames.UnionWith(other.RequiredAncestorOwnedParameterNames);
            VisiblePropertyDependencyNames.UnionWith(other.VisiblePropertyDependencyNames);
            PendingReferences.UnionWith(other.PendingReferences);
            OwnerQualifiedParameters.UnionWith(other.OwnerQualifiedParameters);
        }

        /// <summary><see cref="UnionWith"/> returning this seed, for expression-shaped folds.</summary>
        public SummarySeed Absorb(SummarySeed other)
        {
            UnionWith(other);
            return this;
        }

        public void QualifyParameters(Algorithm owner)
        {
            foreach (var name in owner.Params)
                if (RequiredAncestorOwnedParameterNames.Remove(name))
                    OwnerQualifiedParameters.Add(new(name, owner));

            var pending = PendingReferences.ToArray();
            PendingReferences.Clear();
            foreach (var reference in pending)
                PendingReferences.Add(reference.WithCandidates(reference.Candidates.Select(candidate =>
                {
                    if (candidate is not ResolvedOpenCandidate resolved) return candidate;
                    var seed = resolved.Seed.Clone();
                    seed.QualifyParameters(owner);
                    return new ResolvedOpenCandidate(seed);
                }).ToArray()));
        }

        /// <summary>
        /// Strips the names a level itself binds from every requirement the seed carries —
        /// its own and those of the resolved open candidates riding along, which are seeds
        /// relative to the same level.
        /// </summary>
        public void RemoveRequiredAncestorOwnedParameterNames(IEnumerable<string> names, Algorithm owner)
        {
            RequiredAncestorOwnedParameterNames.ExceptWith(names);
            OwnerQualifiedParameters.RemoveWhere(r => ReferenceEquals(r.Owner, owner) && names.Contains(r.Name));
            if (PendingReferences.Count == 0)
                return;

            var stripped = new List<string>(names);
            var rewritten = new List<PendingReference>(PendingReferences.Count);
            var changed = owner.Params.Count > 0;
            foreach (var pending in PendingReferences)
            {
                if (pending.Candidates.Count == 0)
                {
                    rewritten.Add(pending.BoundBy(owner));
                    continue;
                }

                var candidates = new List<OpenCandidate>(pending.Candidates.Count);
                foreach (var candidate in pending.Candidates)
                {
                    if (candidate is ResolvedOpenCandidate resolved
                        && resolved.Seed.RequiresAny(stripped, owner))
                    {
                        var seed = resolved.Seed.Clone();
                        seed.RemoveRequiredAncestorOwnedParameterNames(stripped, owner);
                        candidates.Add(new ResolvedOpenCandidate(seed));
                        changed = true;
                    }
                    else
                    {
                        candidates.Add(candidate);
                    }
                }

                rewritten.Add(pending.WithCandidates(candidates).BoundBy(owner));
            }

            if (!changed)
                return;

            PendingReferences.Clear();
            PendingReferences.UnionWith(rewritten);
        }

        private bool RequiresAny(IReadOnlyList<string> names, Algorithm owner)
        {
            if (OwnerQualifiedParameters.Any(r => ReferenceEquals(r.Owner, owner) && names.Contains(r.Name)))
                return true;
            foreach (var name in names)
            {
                if (RequiredAncestorOwnedParameterNames.Contains(name))
                    return true;
            }

            foreach (var pending in PendingReferences)
            {
                foreach (var candidate in pending.Candidates)
                {
                    if (candidate is ResolvedOpenCandidate resolved && resolved.Seed.RequiresAny(names, owner))
                        return true;
                }
            }

            return false;
        }

        public bool SetEquals(SummarySeed other)
            => RequiredAncestorOwnedParameterNames.SetEquals(other.RequiredAncestorOwnedParameterNames)
                && VisiblePropertyDependencyNames.SetEquals(other.VisiblePropertyDependencyNames)
                && PendingReferences.SetEquals(other.PendingReferences)
                && OwnerQualifiedParameters.SetEquals(other.OwnerQualifiedParameters);

        public bool IsEmpty
            => RequiredAncestorOwnedParameterNames.Count == 0
                && VisiblePropertyDependencyNames.Count == 0
                && PendingReferences.Count == 0
                && OwnerQualifiedParameters.Count == 0;

        /// <summary>Content identity (sorted), for candidate equality within a fixed point.</summary>
        internal string ContentKey
            => PendingReference.KeyParts([
                FrontEndRegionKeys.NameSet(RequiredAncestorOwnedParameterNames),
                FrontEndRegionKeys.NameSet(VisiblePropertyDependencyNames),
                FrontEndRegionKeys.NameSet(PendingReferences.Select(static pending => pending.ContentKey)),
                FrontEndRegionKeys.NameSet(OwnerQualifiedParameters.Select(static r => r.ContentKey))]);
    }

    /// <summary>
    /// The completed summary of one algorithm node under the empty locally-owned context: the
    /// requirements of its OUTPUT (what evaluating the algorithm's value needs) and, per
    /// declared property, that member's requirements expanded through the algorithm's own
    /// sibling fixed point (relative to the algorithm's declaring level). The member seeds are
    /// what structural navigation (<c>Inner.X</c>) and <c>open</c>-provided names charge.
    /// Both are stored pristine; readers clone before accumulating.
    /// </summary>
    internal sealed class AlgorithmSummary(
        SummarySeed outputSeed,
        IReadOnlyDictionary<string, SummarySeed> memberSeeds)
    {
        public SummarySeed OutputSeed { get; } = outputSeed;

        public IReadOnlyDictionary<string, SummarySeed> MemberSeeds { get; } = memberSeeds;

        public static readonly IReadOnlyDictionary<string, SummarySeed> NoMembers =
            new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
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
        internal Dictionary<Algorithm, AlgorithmSummary>? CompletedAlgorithmSummaries;

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
    internal sealed class SummaryWalkMemos(SummaryMemo sharedMemo, FrontEndTraversalObservations? observations)
    {
        public Dictionary<Expr, SummarySeed>? PrimarySeeds;

        public Dictionary<Expr, SummarySeed>? TransparentSeeds;

        public readonly SummaryMemo SharedMemo = sharedMemo;

        public readonly FrontEndTraversalObservations? Observations = observations;
    }

    /// <summary>
    /// The context ONE level offers to the seeds escaping from inside it: the level's
    /// algorithm (its properties for navigation, its <c>open</c> targets as candidates) and
    /// its current local property summaries. Used by the builder for every nested level and
    /// by the exposure resolver when it expands a navigated member's seed through the
    /// algorithms of a member path.
    /// </summary>
    internal sealed class LevelContext(
        Algorithm algorithm,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        SummaryWalkMemos memos)
    {
        public Algorithm Algorithm { get; } = algorithm;

        public IReadOnlyDictionary<string, SummarySeed> LocalPropertySummaries { get; } = localPropertySummaries;

        public SummaryWalkMemos Memos { get; } = memos;

        public bool HasOpens => Algorithm.Opens.Count > 0;
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
                summarySeed.RequiredAncestorOwnedParameterNames.OrderBy(static name => name, StringComparer.Ordinal).ToArray(),
                summarySeed.PendingReferences.OrderBy(static pending => pending.ContentKey, StringComparer.Ordinal).ToArray(),
                summarySeed.OwnerQualifiedParameters.ToArray());
        }

        return new PropertyDependencySummaryGraph(algorithm.Properties, propertyNameToIndex, nodes);
    }

    /// <summary>A fresh walk-memo bundle over a shared memo, for the exposure resolver's own charging calls.</summary>
    internal static SummaryWalkMemos CreateWalkMemos(SummaryMemo memo, FrontEndTraversalObservations? observations)
        => new(memo, observations);

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
        => GetAlgorithmSummary(algorithm, memos).OutputSeed.Clone();

    /// <summary>
    /// The completed summary of a node (output seed and per-member seeds), computed at most
    /// once per memo lifetime. Conditional families and builtins have no members.
    /// </summary>
    internal static AlgorithmSummary GetAlgorithmSummary(Algorithm algorithm, SummaryWalkMemos memos)
    {
        var completedSummaries = memos.SharedMemo.CompletedAlgorithmSummaries ??= new(ReferenceEqualityComparer.Instance);
        if (completedSummaries.TryGetValue(algorithm, out var stored))
            return stored;

        memos.Observations?.RecordDependencyAlgorithmSummaryComputation();
        var summary = CollectAlgorithmSummary(algorithm, CreateNameSet(), memos.SharedMemo, memos.Observations);
        completedSummaries[algorithm] = summary;
        return summary;
    }

    private static SummarySeed CollectSummarySeed(
        Algorithm algorithm,
        HashSet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations)
        => CollectAlgorithmSummary(algorithm, locallyOwnedNames, sharedMemo, observations).OutputSeed;

    private static AlgorithmSummary CollectAlgorithmSummary(
        Algorithm algorithm,
        HashSet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations)
    {
        switch (algorithm)
        {
            case Algorithm.User user:
                return CollectAlgorithmSummary(user, locallyOwnedNames, sharedMemo, observations);

            case Algorithm.Conditional conditional:
                return new AlgorithmSummary(
                    CollectSummarySeed(conditional, locallyOwnedNames, sharedMemo, observations),
                    AlgorithmSummary.NoMembers);

            default:
                return new AlgorithmSummary(new SummarySeed(), AlgorithmSummary.NoMembers);
        }
    }

    private static AlgorithmSummary CollectAlgorithmSummary(
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
            return new AlgorithmSummary(new SummarySeed(), AlgorithmSummary.NoMembers);

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
            var level = new LevelContext(algorithm, currentPropertySummaries, memos);
            var nextPropertySummaries = new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
            for (var i = 0; i < algorithm.Properties.Count; i++)
            {
                var property = algorithm.Properties[i];
                nextPropertySummaries[property.Name] = ExpandAtLevel(propertyBaseSeeds[i], level);
            }

            if (SummarySeedsEqual(currentPropertySummaries, nextPropertySummaries))
            {
                currentPropertySummaries = nextPropertySummaries;
                break;
            }

            currentPropertySummaries = nextPropertySummaries;
        }

        var seed = CollectOpenTargetSeeds(algorithm.Opens, currentPropertySummaries, ownedHere, memos);
        seed.UnionWith(CollectSummarySeed(
            algorithm.Output,
            currentPropertySummaries,
            ownedHere,
            memos,
            inTransparentContext: false));

        // A name the opens/output walk reported unresolved from a transparent layer (a capture
        // row, a call or dot-call argument bundle — walked with empty local maps, see the arms
        // below) or from a nested block (whose completed summary knows nothing of this level)
        // is a reference written in THIS algorithm's lexical context, so ownership-first
        // resolution consults this algorithm's own properties before the name may escape to
        // the enclosing level — exactly as each property base seed is expanded against the
        // same local fixed point. Without this step `G = { Q = p + 1  (Q) }` reported the bare
        // name `Q` upward: an enclosing level with no `Q` dropped it (a local-only `G` leaked
        // through `open`), and an enclosing sibling `Q` was wrongly consulted (a self-contained
        // `G` was hidden). The same expansion turns each name this level's own `open`
        // declarations may provide into a pending reference carrying those providers.
        var finalLevel = new LevelContext(algorithm, currentPropertySummaries, memos);
        seed = ExpandAtLevel(seed, finalLevel);
        seed.RemoveRequiredAncestorOwnedParameterNames(ownedHere, algorithm);

        // Navigating a member does not call its owner. Retain the exact declaration
        // that binds each parameter instead of reinterpreting its name at the consumer.
        foreach (var member in currentPropertySummaries.Values)
            member.QualifyParameters(algorithm);

        // The member seeds a consumer navigates into (`Inner.X`, an opened `X`) are the
        // level's final local summaries, which are relative to this level's PARENT: they keep
        // this level's own parameters as requirements (an `X = p` inside `Lib(p)` requires
        // `p` — that is exactly what makes it local-only), so only the output seed strips them.
        return new AlgorithmSummary(seed, currentPropertySummaries);
    }

    /// <summary>
    /// The level expansion — THE ownership-first step of the summary channel at one level:
    /// a bare name or a pending reference's head that is one of the level's own properties
    /// resolves here (a bare name to that property's summary, a member path by structural
    /// navigation from that property's value); anything else escapes to the enclosing level,
    /// and when this level declares <c>open</c> targets those become the escaping reference's
    /// next candidates (after the candidates of the levels inside it — the inner-first order
    /// <c>open</c> lookup consults them in). Resolved candidate seeds riding along are seeds
    /// relative to this level and are expanded like everything else.
    /// </summary>
    internal static SummarySeed ExpandAtLevel(SummarySeed baseSeed, LevelContext level)
    {
        var expanded = new SummarySeed(
            requiredAncestorOwnedParameterNames: baseSeed.RequiredAncestorOwnedParameterNames,
            ownerQualifiedParameters: baseSeed.OwnerQualifiedParameters);

        foreach (var dependencyName in baseSeed.VisiblePropertyDependencyNames)
        {
            if (level.LocalPropertySummaries.TryGetValue(dependencyName, out var localSummary))
            {
                expanded.UnionWith(localSummary);
                continue;
            }

            AddEscaping(expanded, new PendingReference(dependencyName, [], []), level);
        }

        foreach (var pending in baseSeed.PendingReferences)
        {
            if (level.LocalPropertySummaries.TryGetValue(pending.Head, out var localSummary))
            {
                if (pending.Members.Count == 0)
                {
                    expanded.UnionWith(localSummary);
                    continue;
                }

                var headNode = LocalPropertyValue(level.Algorithm, pending.Head);
                var (charged, navigated) = ChargePath(headNode, StructuralSteps(pending.Members), level.Memos);
                // This locally declared provider is outside the escaped reference's
                // lexical chain unless its own call boundary accompanied that reference.
                charged.OwnerQualifiedParameters.RemoveWhere(r => r.Owner is not null
                    && pending.BoundOwners.Any(a => ReferenceEquals(a, r.Owner)));
                var unavailable = charged.OwnerQualifiedParameters.Select(r => new OwnerQualifiedParameter(r.Name, null)).ToArray();
                charged.OwnerQualifiedParameters.Clear();
                charged.OwnerQualifiedParameters.UnionWith(unavailable);
                if (navigated == 0)
                    expanded.UnionWith(localSummary);
                expanded.UnionWith(ExpandAtLevel(charged, level));
                continue;
            }

            AddEscaping(expanded, pending, level);
        }

        expanded.QualifyParameters(level.Algorithm);
        return expanded;
    }

    private static void AddEscaping(SummarySeed expanded, PendingReference pending, LevelContext level)
    {
        List<OpenCandidate>? candidates = null;
        foreach (var candidate in pending.Candidates)
        {
            candidates ??= new List<OpenCandidate>(pending.Candidates.Count);
            switch (candidate)
            {
                case ResolvedOpenCandidate resolved:
                    candidates.Add(new ResolvedOpenCandidate(ExpandAtLevel(resolved.Seed, level)));
                    break;

                case UnresolvedOpenCandidate unresolved when level.LocalPropertySummaries.ContainsKey(unresolved.Head):
                    // THIS level declares the carried target's head (the opener's direct
                    // chain reaches it here, before any farther level): settle the candidate
                    // in place exactly as the opener would have settled its own head — the
                    // charged provider seed, relative to this level. A head that does not
                    // publicly provide the referenced name is not a candidate (final audit,
                    // September 2026: an unsettled head declared BETWEEN the opener and the
                    // settling level used to be carried past its declaration, so a property
                    // reading `p` through it was classified exported and the run cache
                    // served the first activation's value to every later call).
                    if (TryResolveLocalHeadCandidate(unresolved.Head, unresolved.PublicSteps, pending, level) is { } settled)
                        candidates.Add(settled);
                    break;

                default:
                    candidates.Add(candidate);
                    break;
            }
        }

        if (level.HasOpens)
        {
            foreach (var candidate in MakeOpenCandidates(pending, level))
                (candidates ??= []).Add(candidate);
        }

        if (candidates is null || candidates.Count == 0)
        {
            if (pending.Members.Count == 0)
                expanded.VisiblePropertyDependencyNames.Add(pending.Head);
            else
                expanded.PendingReferences.Add(pending.WithCandidates([]));
            return;
        }

        expanded.PendingReferences.Add(pending.WithCandidates(candidates));
    }

    /// <summary>
    /// The candidates this level's <c>open</c> targets contribute to an escaping reference, in
    /// declaration order with the evaluator's dedup rule (<see cref="Evaluator.OpenTargetDedupKey"/>).
    /// A target whose head is this level's own property (or an inline block) is settled in
    /// place: it is a candidate exactly when it publicly provides the reference's head, and
    /// then carries the charged member seed, relative to this level's parent. A target whose
    /// head is declared farther out is carried unresolved.
    /// </summary>
    private static IEnumerable<OpenCandidate> MakeOpenCandidates(PendingReference pending, LevelContext level)
    {
        var opens = level.Algorithm.Opens;
        HashSet<string>? seen = null;
        for (var i = 0; i < opens.Count; i++)
        {
            var target = opens[i];
            seen ??= new HashSet<string>(StringComparer.Ordinal);
            if (!seen.Add(Evaluator.OpenTargetDedupKey(target, i)))
                continue;

            if (target is Expr.AlgorithmExpr(var block))
            {
                // An inline target is wired to the prelude: nothing outside it can be
                // referenced, so only its own requirement names survive.
                if (TryChargeProvidedMember(block, pending, level.Memos) is { } inlineSeed)
                    yield return new ResolvedOpenCandidate(new SummarySeed(inlineSeed.RequiredAncestorOwnedParameterNames,
                        ownerQualifiedParameters: inlineSeed.OwnerQualifiedParameters));
                continue;
            }

            if (!TryGetOpenTargetPath(target, out var head, out var steps))
                continue;

            if (!level.LocalPropertySummaries.ContainsKey(head))
            {
                yield return new UnresolvedOpenCandidate(head, steps);
                continue;
            }

            if (TryResolveLocalHeadCandidate(head, steps, pending, level) is { } candidate)
                yield return candidate;
        }
    }

    /// <summary>
    /// The ONE settlement of an <c>open</c> target whose head is a property of
    /// <paramref name="level"/> — reached either by the opener itself
    /// (<see cref="MakeOpenCandidates"/>) or by an escaping reference carrying the head
    /// outward (<see cref="AddEscaping"/>): the dotted steps must be public members, the
    /// provider must publicly declare the referenced head, and the charged seed (the
    /// navigated steps' and the provided member's requirements) is relative to this level's
    /// parent. Null when the target provides nothing.
    /// </summary>
    private static ResolvedOpenCandidate? TryResolveLocalHeadCandidate(
        string head,
        IReadOnlyList<string> steps,
        PendingReference pending,
        LevelContext level)
    {
        var (providerSeed, providerNavigated) = ChargePath(LocalPropertyValue(level.Algorithm, head), PublicSteps(steps), level.Memos);
        if (providerNavigated < steps.Count)
            return null;

        var provider = NavigateNode(LocalPropertyValue(level.Algorithm, head), steps);
        if (provider is null || TryChargeProvidedMember(provider, pending, level.Memos) is not { } memberSeed)
            return null;

        // The provided member's seed is relative to the provider, which is relative to
        // the head's declaring level — this level; the dotted steps were navigated by
        // ChargePath from the head, so expand the member seed through the same nodes.
        var seed = ExpandThroughNodes(memberSeed, NodePath(LocalPropertyValue(level.Algorithm, head), steps), level.Memos);
        seed.UnionWith(providerSeed);
        return new ResolvedOpenCandidate(ExpandAtLevel(seed, level));
    }

    /// <summary>
    /// The seed a provider contributes for an opened reference — its PUBLIC member named by
    /// the reference's head plus the structural members navigated after it — relative to the
    /// provider's own declaring level; null when the provider does not publicly declare the
    /// head.
    /// </summary>
    internal static SummarySeed? TryChargeProvidedMember(Algorithm provider, PendingReference pending, SummaryWalkMemos memos)
    {
        if (ElaboratedScopeLookup.TryLookupPublicProperty(provider, pending.Head) is null)
            return null;

        var steps = new List<(string Name, bool Public)>(pending.Members.Count + 1) { (pending.Head, true) };
        foreach (var member in pending.Members)
            steps.Add((member, false));
        return ChargePath(provider, steps, memos).Seed;
    }

    internal static IReadOnlyList<(string Name, bool Public)> StructuralSteps(IReadOnlyList<string> members)
        => members.Select(static member => (member, false)).ToArray();

    internal static IReadOnlyList<(string Name, bool Public)> PublicSteps(IReadOnlyList<string> members)
        => members.Select(static member => (member, true)).ToArray();

    /// <summary>
    /// Structural navigation for the summary channel — the static twin of the evaluator's
    /// member navigation: from <paramref name="headNode"/>, each step selects the declared
    /// member (public-only when the step is an <c>open</c> path step) and CHARGES that member's
    /// requirement seed, expanded back through the nodes navigated before it so the result is
    /// relative to the head's declaring level. A step whose member is absent stops the walk:
    /// the last reached node is then evaluated as a value (the dot edge falls back to its
    /// lexical callable with the receiver injected), so its OUTPUT seed is charged instead.
    /// Returns the charged seed and the number of steps navigated.
    /// </summary>
    internal static (SummarySeed Seed, int Navigated) ChargePath(
        Algorithm headNode,
        IReadOnlyList<(string Name, bool Public)> steps,
        SummaryWalkMemos memos)
    {
        var result = new SummarySeed();
        var nodes = new List<Algorithm> { headNode };
        var current = headNode;
        for (var i = 0; i < steps.Count; i++)
        {
            var (name, isPublic) = steps[i];
            var member = isPublic
                ? ElaboratedScopeLookup.TryLookupPublicProperty(current, name)
                : ElaboratedScopeLookup.TryLookupProperty(current, name);
            if (member is null)
            {
                if (!isPublic && i > 0)
                {
                    // The receiver value of a lexical fallback is evaluated: charge it.
                    var outputSeed = GetAlgorithmSummary(current, memos).OutputSeed.Clone();
                    result.UnionWith(ExpandThroughNodes(outputSeed, nodes.GetRange(0, nodes.Count - 1), memos));
                }

                return (result, i);
            }

            var summary = GetAlgorithmSummary(current, memos);
            if (summary.MemberSeeds.TryGetValue(name, out var memberSeed))
                result.UnionWith(ExpandThroughNodes(memberSeed.Clone(), nodes, memos));

            current = member.Value.Property.Value;
            nodes.Add(current);
        }

        return (result, steps.Count);
    }

    /// <summary>
    /// Brings a seed relative to the last node's parent level back to the first node's
    /// declaring level: expand against each node's own local summaries, innermost first.
    /// </summary>
    internal static SummarySeed ExpandThroughNodes(SummarySeed seed, IReadOnlyList<Algorithm> nodes, SummaryWalkMemos memos)
    {
        for (var k = nodes.Count - 1; k >= 0; k--)
            seed = ExpandAtLevel(seed, new LevelContext(nodes[k], GetAlgorithmSummary(nodes[k], memos).MemberSeeds, memos));
        return seed;
    }

    private static Algorithm LocalPropertyValue(Algorithm level, string name)
        => ElaboratedScopeLookup.TryLookupProperty(level, name)!.Value.Property.Value;

    internal static Algorithm? NavigateNode(Algorithm head, IReadOnlyList<string> publicSteps)
    {
        var current = head;
        foreach (var step in publicSteps)
        {
            if (ElaboratedScopeLookup.TryLookupPublicProperty(current, step) is not { } hit)
                return null;
            current = hit.Property.Value;
        }

        return current;
    }

    internal static IReadOnlyList<Algorithm> NodePath(Algorithm head, IReadOnlyList<string> publicSteps)
    {
        var nodes = new List<Algorithm> { head };
        var current = head;
        foreach (var step in publicSteps)
        {
            current = ElaboratedScopeLookup.TryLookupPublicProperty(current, step)!.Value.Property.Value;
            nodes.Add(current);
        }

        return nodes;
    }

    /// <summary>
    /// The lexical head and dotted public steps of a named <c>open</c> target (<c>open A</c>,
    /// <c>open A.B.C</c>); false for inline, parameter-owned (an <see cref="Expr.Param"/> head
    /// provides nothing, F2), and illegal target shapes.
    /// </summary>
    internal static bool TryGetOpenTargetPath(Expr target, out string head, out IReadOnlyList<string> steps)
    {
        var reversed = new List<string>();
        var current = target;
        while (current is Expr.DotCall { Args: null } edge && edge.IsCoreOpenForm())
        {
            reversed.Add(edge.Name);
            current = edge.Target;
        }

        if (current is Expr.Resolve(var name))
        {
            reversed.Reverse();
            head = name;
            steps = reversed;
            return true;
        }

        head = string.Empty;
        steps = [];
        return false;
    }

    /// <summary>
    /// The static member path of a dot chain — a lexical head followed by argumentless,
    /// non-<c>string</c> dot steps, the shape the evaluator navigates structurally
    /// (<c>ResolveDotReceiver</c>) — with the final edge's member included whether or not it
    /// carries arguments. False for every other receiver shape (a parameter, a block, a
    /// capture, a call, the <c>string</c> intrinsic).
    /// </summary>
    private static bool TryGetStaticMemberPath(Expr.DotCall dotCall, out string head, out IReadOnlyList<string> members)
    {
        if (dotCall.UsesOrdinaryDotStringIntrinsic())
        {
            head = string.Empty;
            members = [];
            return false;
        }

        var reversed = new List<string> { dotCall.Name };
        var current = dotCall.Target.UnwrapGraceOperand();
        while (current is Expr.DotCall { Args: null } edge && !edge.UsesOrdinaryDotStringIntrinsic())
        {
            reversed.Add(edge.Name);
            current = edge.Target.UnwrapGraceOperand();
        }

        if (current is Expr.Resolve(var name))
        {
            reversed.Reverse();
            head = name;
            members = reversed;
            return true;
        }

        head = string.Empty;
        members = [];
        return false;
    }

    /// <summary>
    /// The opens walk of a level: a named target charges the navigated provider path
    /// (<c>open A</c> needs only A's identity; <c>open A.B</c> charges the
    /// requirements of the navigated member <c>B</c>), and
    /// any other (illegal, recovery) shape walks as an ordinary expression. An open target is
    /// not a call, so no lexical fallback is ever charged for it.
    /// </summary>
    private static SummarySeed CollectOpenTargetSeeds(
        IReadOnlyList<Expr> opens,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        HashSet<string> ownedHere,
        SummaryWalkMemos memos)
    {
        var seed = new SummarySeed();
        foreach (var target in opens)
        {
            if (TryGetOpenTargetPath(target, out var head, out var steps))
            {
                if (steps.Count > 0)
                    seed.UnionWith(new SummarySeed(pendingReferences: [new PendingReference(head, steps, [])]));
                continue;
            }

            // An inline provider is also an identity, never an evaluated output.
            // Provider signature/form validity is checked independently.
            if (target is Expr.AlgorithmExpr)
                continue;

            seed.UnionWith(CollectSummarySeed(target, localPropertySummaries, ownedHere, memos, inTransparentContext: false));
        }

        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        Algorithm.Conditional algorithm,
        HashSet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations)
    {
        var ownedHere = CreateNameSet(locallyOwnedNames);
        var localSummaries = new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
        var memos = new SummaryWalkMemos(sharedMemo, observations);
        var seed = CollectOpenTargetSeeds(
            algorithm.Opens,
            localSummaries,
            ownedHere,
            memos);

        foreach (var branch in algorithm.Branches)
        {
            // Branch bodies deliberately bypass the node-keyed completed-summary memo: their
            // binder-name context varies per branch, so their summaries are NOT pure
            // functions of the body node (see SummaryMemo). They are pure functions of
            // (body, binder names), which the branch-body memo keys on — so a body shared by
            // several families under the same binders is summarized once (M4).
            seed.UnionWith(CollectBranchBodySummarySeed(branch, sharedMemo, observations));
        }

        // Host-built families can own opens. They are a static lookup level above
        // the branch bodies, just as at runtime: never charge a provider's output,
        // and carry its candidate members when branch references escape this level.
        return algorithm.Opens.Count == 0 ? seed
            : ExpandAtLevel(seed, new LevelContext(algorithm, localSummaries, memos));
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
        SummarySeed Seed(Expr child)
            => CollectSummarySeed(child, localPropertySummaries, ownedHere, memos, inTransparentContext);

        return expr switch
        {
            Expr.Param(var name) => ownedHere.Contains(name)
                ? new SummarySeed()
                : new SummarySeed(requiredAncestorOwnedParameterNames: [name]),

            Expr.Resolve(var name) => localPropertySummaries.TryGetValue(name, out var localPropertySummary)
                ? localPropertySummary.Clone()
                : new SummarySeed(visiblePropertyDependencyNames: [name]),

            Expr.Grace(var inner, _) => Seed(inner),
            Expr.Binary(_, var left, var right) => Seed(left).Absorb(Seed(right)),
            Expr.Unary(_, var operand) => Seed(operand),
            Expr.Index(var target, var selector) => Seed(target).Absorb(Seed(selector)),
            Expr.SequenceSpread(var operand) => Seed(operand),
            Expr.SequenceConstruct(var left, var right) => Seed(left).Absorb(Seed(right)),
            Expr.ListLiteral(var listItems) => CollectSummarySeed(
                listItems, localPropertySummaries, ownedHere, memos, inTransparentContext),

            Expr.AlgorithmExpr(var algorithm) => CollectSharedAlgorithmSummarySeed(algorithm, memos),

            // A capture owns no names: its rows walk with an empty
            // owned-here set and an empty local-summary map — exactly what
            // the pre-split transparent wrapper algorithm's output walk did
            // (the same attribution as call-argument bundles). The names it
            // reports unresolved are resolved against the enclosing
            // algorithm's own property summaries at the algorithm level
            // (CollectSummarySeed(Algorithm.User)), never left to escape.
            Expr.Capture(var captureBody) => CollectTransparentBundleSummarySeed(captureBody, memos),

            // An argument bundle owns no names: slots walk with an empty
            // owned-here set and an empty local-summary map — the same
            // attribution as capture rows (and as the pre-Track-B empty
            // transparent args wrapper).
            Expr.Call(var function, var args) => Seed(function).Absorb(CollectTransparentBundleSummarySeed(args, memos)),

            Expr.DotCall dotCall => CollectDotCallSummarySeed(
                dotCall, localPropertySummaries, ownedHere, memos, inTransparentContext),

            // Intentional leaves with no name occurrences: literals, the empty
            // sequence, and native-call bodies (whose argument names are
            // parameter references by construction).
            Expr.Num or Expr.StringLiteral or Expr.EmptySequence or Expr.NativeCall => new SummarySeed(),
        };
    }

    /// <summary>
    /// Seed of a scope-less bundle (capture rows, argument slots): the rows walk with an
    /// empty owned-here set and an empty local-summary map in the transparent context.
    /// </summary>
    private static SummarySeed CollectTransparentBundleSummarySeed(OutputBundle bundle, SummaryWalkMemos memos)
        => CollectSummarySeed(
            bundle,
            new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
            CreateNameSet(),
            memos,
            inTransparentContext: true);

    /// <summary>
    /// The DotCall arm of <see cref="CollectSummarySeedCore"/>. A static member path
    /// (<c>Inner.X</c>, <c>Lib.Sub.Q</c>, <c>Lib.F(1)</c>) is charged by NAVIGATION at the
    /// level that resolves its head: every member the evaluator would navigate to charges
    /// its own requirements — so a container reading a captured member through
    /// <c>Inner.X</c> is itself local-only — and a receiver the walk stops at (the member
    /// is absent: the edge falls back) charges its output exactly as the bare target seed
    /// did. A receiver of any other shape (a parameter, a block, a capture, a call, the
    /// <c>string</c> intrinsic) is a value and keeps charging its own seed.
    /// <para>The stored lexical-fallback identity is an ordinary elaborated name expression
    /// (Resolve/Param) and participates in dependency analysis EXACTLY like a written
    /// callee name — through this same walk with the enclosing attribution — whenever the
    /// fallback MAY be selected at runtime (<see cref="AstHelpers.LexicalFallbackMayBeSelected"/>:
    /// the detector's stamped scope-aware verdict, or the raw shape classification on an
    /// unstamped edge). A receiver that declares the member never selects the fallback, so
    /// a Param fallback hidden behind a structural winner charges nothing and the property
    /// keeps its exported structural/open access; a receiver known to lack it — a sibling
    /// property whose value is a list, a call result, a literal — always does, so
    /// <c>Big = Data.f</c> with <c>f</c> an enclosing parameter is local-only exactly like
    /// the direct call <c>f(Data)</c>. Charging only CERTAIN selections left such a
    /// property exported although its value depends on the parameter: structural
    /// navigation could then read a dynamic binding through it, and the run-wide
    /// zero-argument property cache of an exported binding would have served one
    /// activation's value to another (SEMANTIC-ALIGNMENT, F3). The sibling
    /// evaluation-order channel (<see cref="CollectSiblingDependencyIndices"/>) deliberately
    /// takes no fallback contribution: the fallback is a CALLED name, and called siblings
    /// are not order dependencies there (the same rule as Call function position).</para>
    /// </summary>
    private static SummarySeed CollectDotCallSummarySeed(
        Expr.DotCall dotCall,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        HashSet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
    {
        var seed = TryGetStaticMemberPath(dotCall, out var pathHead, out var pathMembers)
            ? new SummarySeed(pendingReferences: [new PendingReference(pathHead, pathMembers, [])])
            : CollectSummarySeed(dotCall.Target, localPropertySummaries, ownedHere, memos, inTransparentContext);

        if (dotCall.LexicalFallbackMayBeSelected())
        {
            seed.UnionWith(CollectSummarySeed(
                dotCall.EffectiveLexicalFallback,
                localPropertySummaries,
                ownedHere,
                memos,
                inTransparentContext));
        }

        if (dotCall.Args is { } argsOpt)
            seed.UnionWith(CollectTransparentBundleSummarySeed(argsOpt, memos));

        return seed;
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

            // Runtime exhaustiveness guard (statement-form collector, which the
            // closed Expr hierarchy cannot make compiler-exhaustive — see
            // AstWalker.VisitExpr): a new Expr variant must be classified above
            // rather than silently contributing no processing-order dependencies.
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
