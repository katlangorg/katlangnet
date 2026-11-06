namespace KatLang;

/// <summary>
/// The algorithms of one input graph that more than one path reaches: an algorithm held by several edges, or an algorithm
/// below a shared expression. Only these can be reached in a second context, so only these pay for a cross-parent region
/// key; a tree (every parsed program without a module splice) has none and does no region work at all. Pure
/// reference-identity accounting over the immutable input, never a semantic statement about the bodies.
/// </summary>
internal sealed class SharedBodyCensus
{
    private readonly HashSet<Algorithm> _bodies = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<object, bool> _reachesDeferred = new(ReferenceEqualityComparer.Instance);

    private SharedBodyCensus() { }

    /// <summary>The census of the nodes a walk saw through more than one edge; null when no algorithm is reached twice.</summary>
    internal static SharedBodyCensus? FromSharedNodes(HashSet<object>? sharedNodes)
    {
        if (sharedNodes is null) return null;
        var census = new SharedBodyCensus();
        var pending = new Stack<object>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        void Mark(object node)
        {
            // A family is no region of its own: it is processed once per holder, and its branch bodies are what is reached twice.
            if (node is Algorithm body && census._bodies.Add(body) && body is not Algorithm.Conditional) return;
            if (node is not Algorithm.User && seen.Add(node)) pending.Push(node);
        }

        foreach (var node in sharedNodes) Mark(node);

        // Below a shared expression every algorithm is reached through each of its edges. A user body ends the descent: what
        // lies below it is reached once per region of that body.
        while (pending.TryPop(out var node))
        {
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                Mark(child);
        }

        return census._bodies.Count == 0 ? null : census;
    }

    /// <summary>The census of <paramref name="root"/>, walked here; null when nothing is shared.</summary>
    internal static SharedBodyCensus? Of(object root, CancellationToken cancellationToken = default)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance) { root };
        var pending = new Stack<object>();
        pending.Push(root);
        HashSet<object>? shared = null;
        while (pending.TryPop(out var node))
        {
            cancellationToken.ThrowIfCancellationRequested();
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
            {
                if (seen.Add(child)) pending.Push(child);
                else (shared ??= new(ReferenceEqualityComparer.Instance)).Add(child);
            }
        }

        return FromSharedNodes(shared);
    }

    /// <summary>
    /// Whether <paramref name="body"/> may be served across contexts: it is shared, and nothing below it is a deferred module
    /// region, whose forked continuation is an occurrence's own (its detection, resolution and exposure contexts).
    /// </summary>
    internal bool Holds(Algorithm body) => _bodies.Contains(body) && !ReachesDeferred(body);

    private bool ReachesDeferred(object root)
    {
        if (_reachesDeferred.TryGetValue(root, out var known)) return known;
        var stack = new Stack<(object Node, int NextChild)>();
        stack.Push((root, 0));
        while (stack.TryPop(out var frame))
        {
            if (_reachesDeferred.ContainsKey(frame.Node)) continue;
            if (frame.Node is Algorithm { DeferredRegion: not null })
            {
                _reachesDeferred[frame.Node] = true;
                continue;
            }
            if (!AstStructuralPreflight.TryGetChild(frame.Node, frame.NextChild, out var child))
            {
                _reachesDeferred[frame.Node] = false;
                continue;
            }
            if (!_reachesDeferred.TryGetValue(child, out var reaches))
            {
                stack.Push(frame);
                stack.Push((child, 0));
            }
            else if (reaches) _reachesDeferred[frame.Node] = true;
            else stack.Push((frame.Node, frame.NextChild + 1));
        }

        return _reachesDeferred[root];
    }
}

/// <summary>
/// The names a body can read from OUTSIDE itself, by node: every name it writes (a reference, a parameter read, a dot edge's
/// lexical fallback, an open head) minus what the body's own declarations bind. A pure function of the node, memoized by
/// reference, and an over-approximation on purpose: a parameter the body infers or a member it opens stays in the set, so a
/// region key can only be finer than necessary, never coarser. An open list is read outside the level that writes it, so a
/// level's declarations never remove its own open heads.
/// </summary>
internal sealed class RegionFreeNames(NameSetInterner names)
{
    private readonly Dictionary<object, CanonicalNameSet> _memo = new(ReferenceEqualityComparer.Instance);

    internal NameSetInterner Names { get; } = names;

    internal CanonicalNameSet Of(object node)
    {
        if (_memo.TryGetValue(node, out var known)) return known;
        var set = node switch
        {
            Algorithm body => Body(body),
            Expr.Resolve(var name) => Names.With(NameSetInterner.Empty, [name]),
            Expr.Param(var name) => Names.With(NameSetInterner.Empty, [name]),
            _ => Children(node),
        };
        if (node is Expr.DotCall { EffectiveLexicalFallback: Expr.Resolve(var fallback) })
            set = Names.With(set, [fallback]);
        _memo[node] = set;
        return set;
    }

    private CanonicalNameSet Children(object node)
    {
        var set = NameSetInterner.Empty;
        for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
            if (child is Expr or Algorithm or OutputBundle)
                set = Names.Union(set, Of(child));
        return set;
    }

    private CanonicalNameSet Body(Algorithm body)
    {
        var opens = NameSetInterner.Empty;
        foreach (var open in body.Opens) opens = Names.Union(opens, Of(open));
        var own = NameSetInterner.Empty;
        foreach (var row in body.Output) own = Names.Union(own, Of(row));
        foreach (var property in body.Properties) own = Names.Union(own, Of(property.Value));
        foreach (var branch in body.Branches) own = Names.Union(own, Of(branch.Body));
        if (body.Properties.Count > 0)
            own = Names.Except(own, Names.With(NameSetInterner.Empty, body.Properties.Select(property => property.Name)));
        return Names.Union(opens, own);
    }
}

/// <summary>
/// The completed-facts counterpart of <see cref="BindingFootprint"/>, for the passes that run after completion: one shared
/// body in one context, with what each of its free names selects from outside it (the nearest enclosing key that binds it as a
/// parameter or declares it as a member) and, when a name reaches past every direct level, the nearest context with open
/// providers. Equal regions read equal declarations through equal chains, so a summary or a clean validation of one
/// context holds for the other. Names the body binds itself (its parameters, a branch's binders) select nothing outside.
/// Null when an enclosing context has no facts: an unavailable chain is never equivalent to anything.
/// </summary>
internal sealed class CompletedBodyRegion : IEquatable<CompletedBodyRegion>
{
    private readonly StaticLookupFacts _facts;
    private readonly Algorithm _body;
    private readonly object? _bindingRegion;
    private readonly StaticScopeKey? _opens;
    private readonly (StaticScopeKey? Selected, bool IsParameter)[] _names;
    private readonly int _hash;

    private CompletedBodyRegion(StaticLookupFacts facts, Algorithm body, object? bindingRegion, StaticScopeKey? opens, (StaticScopeKey?, bool)[] names)
    {
        (_facts, _body, _bindingRegion, _opens, _names) = (facts, body, bindingRegion, opens, names);
        var hash = new HashCode();
        hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(body));
        hash.Add(opens is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(opens));
        foreach (var (selected, isParameter) in names)
        {
            hash.Add(selected is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(selected));
            hash.Add(isParameter);
        }
        _hash = hash.ToHashCode();
    }

    internal static CompletedBodyRegion? Of(StaticLookupFacts facts, StaticScopeKey key, Algorithm body, RegionFreeNames freeNames)
    {
        if (key.Parent is not { } parent || facts.Facts(key) is not { } own) return null;
        var free = freeNames.Of(body);
        var names = new (StaticScopeKey?, bool)[free.Count];
        var next = 0;
        var reachesOpens = false;
        foreach (var name in free.Names)
        {
            if (own.Parameters.Contains(name)) { names[next++] = (null, true); continue; }
            (StaticScopeKey?, bool) selected = (null, false);
            for (StaticScopeKey? at = parent; at is not null; at = at.Parent)
            {
                if (facts.Facts(at) is not { } level) return null;
                if (level.Parameters.Contains(name)) { selected = (at, true); break; }
                if (level.Members.TryGetValue(name, out var member)) { selected = (member, false); break; }
            }
            reachesOpens |= selected.Item1 is null;
            names[next++] = selected;
        }

        StaticScopeKey? opens = null;
        if (reachesOpens)
            for (StaticScopeKey? at = parent; at is not null && opens is null; at = at.Parent)
                if (facts.Facts(at) is { } level && (level.Providers.Length > 0 || level.Body?.Opens.Count > 0)) opens = at;
        return new(facts, body, key.BindingRegion, opens, names);
    }

    public bool Equals(CompletedBodyRegion? other)
    {
        if (other is null || !ReferenceEquals(_facts, other._facts) || !ReferenceEquals(_body, other._body)
            || !ReferenceEquals(_bindingRegion, other._bindingRegion) || !ReferenceEquals(_opens, other._opens)
            || _names.Length != other._names.Length) return false;
        for (var index = 0; index < _names.Length; index++)
            if (!ReferenceEquals(_names[index].Selected, other._names[index].Selected) || _names[index].IsParameter != other._names[index].IsParameter)
                return false;
        return true;
    }

    public override bool Equals(object? obj) => Equals(obj as CompletedBodyRegion);
    public override int GetHashCode() => _hash;
}

/// <summary>
/// What a body's free names mean from one declaring context: for every name, its owned, opened and open-head bindings in the
/// Q1 facts of the declaring scope. An inner lookup consults these three projections of the enclosing chain and nothing else
/// of it, so two contexts with equal footprints give one body one elaboration. Compared by binding identity (declaring scope
/// key and property object), never by displayed value or signature; null when a binding is not conclusive.
/// </summary>
internal sealed class BindingFootprint : IEquatable<BindingFootprint>
{
    private static readonly StaticQueryProjection[] Projections =
        [StaticQueryProjection.OwnedBinding, StaticQueryProjection.OpenedBinding, StaticQueryProjection.OpenHeadBinding];

    private readonly (StaticFactKind Kind, StaticScopeKey? Scope, Property? Property)[] _facts;
    private readonly int _hash;
    private readonly StaticQueryResourceBudget _resources;
    private readonly CancellationToken _cancellationToken;

    private BindingFootprint((StaticFactKind, StaticScopeKey?, Property?)[] facts, StaticQueryResourceBudget resources,
        CancellationToken cancellationToken)
    {
        _facts = facts;
        _resources = resources;
        _cancellationToken = cancellationToken;
        var hash = new HashCode();
        foreach (var (kind, scope, property) in facts)
        {
            resources.Metadata(0, cancellationToken: cancellationToken);
            hash.Add(kind);
            hash.Add(scope is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(scope));
            hash.Add(property is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(property));
        }
        _hash = hash.ToHashCode();
    }

    /// <summary>The footprint of <paramref name="names"/> at <paramref name="declaring"/>; null when any fact is unsettled.</summary>
    internal static BindingFootprint? At(StaticStructureOperation operation, StaticScopeKey declaring, CanonicalNameSet names)
    {
        var count = (long)names.Count * Projections.Length;
        // A tuple occupies three machine words, not one. Refuse before allocating, including when binding queries would
        // later prove inconclusive. Construction and comparisons belong to the same terminal operation ledger.
        operation.Queries.Resources.Metadata(1L + (3 * count + 7) / 8, 1L + count,
            operation.Queries.OperationToken);
        var facts = new (StaticFactKind, StaticScopeKey?, Property?)[checked((int)count)];
        var next = 0;
        foreach (var name in names.Names)
        {
            foreach (var projection in Projections)
            {
                var fact = operation.Binding(declaring, name, projection);
                if (fact.Kind is not (StaticFactKind.Parameter or StaticFactKind.Declaration or StaticFactKind.Missing)) return null;
                facts[next++] = (fact.Kind, fact.Scope, fact.Property);
            }
        }

        return new(facts, operation.Queries.Resources, operation.Queries.OperationToken);
    }

    public bool Equals(BindingFootprint? other)
    {
        if (other is null || _facts.Length != other._facts.Length) return false;
        for (var index = 0; index < _facts.Length; index++)
        {
            _resources.Metadata(0, cancellationToken: _cancellationToken);
            var (kind, scope, property) = _facts[index];
            var (otherKind, otherScope, otherProperty) = other._facts[index];
            if (kind != otherKind || !ReferenceEquals(scope, otherScope) || !ReferenceEquals(property, otherProperty)) return false;
        }
        return true;
    }

    public override bool Equals(object? obj) => Equals(obj as BindingFootprint);
    public override int GetHashCode() => _hash;
}
