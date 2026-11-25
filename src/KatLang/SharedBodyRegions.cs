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

    /// <summary>
    /// The census of the nodes a walk saw through more than one edge; null when no algorithm is reached twice.
    /// </summary>
    internal static SharedBodyCensus? FromSharedNodes(HashSet<object>? sharedNodes)
        => MergeSharedNodes(sharedNodes, null, default);

    private static SharedBodyCensus? MergeSharedNodes(HashSet<object>? sharedNodes, SharedBodyCensus? census, CancellationToken cancellationToken)
    {
        if (sharedNodes is null) return census;
        census ??= new();
        var pending = new Stack<object>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        void Mark(object node)
        {
            // A family is no region of its own: it is processed once per holder, and its branch bodies are what is reached twice.
            if (node is Algorithm body && census._bodies.Add(body) && body is not Algorithm.Conditional) return;
            if (node is not Algorithm.User && seen.Add(node)) pending.Push(node);
        }

        foreach (var node in sharedNodes)
        {
            cancellationToken.ThrowIfCancellationRequested();
            Mark(node);
        }

        // Below a shared expression every algorithm is reached through each of its edges. A user body ends the descent: what
        // lies below it is reached once per region of that body.
        while (pending.TryPop(out var node))
        {
            cancellationToken.ThrowIfCancellationRequested();
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                Mark(child);
        }

        return census._bodies.Count == 0 ? null : census;
    }

    /// <summary>The census of <paramref name="root"/>, walked here; null when nothing is shared.</summary>
    internal static SharedBodyCensus? Of(object root, CancellationToken cancellationToken = default)
        => Of(root, observations: null, cancellationToken);

    private static SharedBodyCensus? Of(object root, FrontEndTraversalObservations? observations, CancellationToken cancellationToken)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance) { root };
        var pending = new Stack<object>();
        pending.Push(root);
        HashSet<object>? shared = null;
        while (pending.TryPop(out var node))
        {
            cancellationToken.ThrowIfCancellationRequested();
            observations?.RecordDeferredCensusExpansion();
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
            {
                if (seen.Add(child)) pending.Push(child);
                else (shared ??= new(ReferenceEqualityComparer.Instance)).Add(child);
            }
        }

        return MergeSharedNodes(shared, null, cancellationToken);
    }

    /// <summary>
    /// THE CENSUS OF A DEFERRED MATERIALIZATION'S EXPOSURE INPUT (C#-only work sharing; the census is exactly
    /// <see cref="Of(object, CancellationToken)"/>'s): the resolved branch body <paramref name="root"/>, with every module
    /// declaration it splices counted as one CENSUS UNIT (<see cref="CompletedModuleViews.CensusUnit"/>) instead of walked.
    /// The census marks the algorithms reached through more than one edge and those below a shared expression down to a
    /// user body (<see cref="FromSharedNodes"/>). A module declaration's own nodes are reached only through its root: each
    /// is the elaboration of its own parse's import view, spliced by reference, so no other part of the graph holds one of
    /// them (the admission measure's partition, <see cref="StaticStructureAdmission.MeasureLoadedBody"/>). Hence a node
    /// inside a declaration is shared exactly when the declaration's own walk, stopped at the module declarations it
    /// splices in turn, reaches it twice, and the descent below such a node stays inside the declaration (it ends at a user
    /// body, and every module root a unit stands for is one; a module root elaborated to a callable alias, which the
    /// descent may enter, is walked by the part that reaches it, and a unit that reaches one makes the census walk the
    /// ordinary way): both are the unit's, a pure function of the immutable declaration. What is
    /// SHARED ACROSS PARTS is a module root alone: the body and the units each count the edges they hold to every module
    /// root, and a root those counts reach twice (two loads of one module in the branch, a module the branch and another
    /// module both splice) is a shared node of the composition like any other. So the body's own shared nodes, the roots
    /// counted twice and the units' bodies give the ordinary census. A unit an earlier materialization published is taken
    /// as published; any other is computed here and staged in <paramref name="moduleViews"/>. The deferred-region and
    /// sharing decisions read from the census (<see cref="Holds"/>) are therefore those of the ordinary walk. The reference
    /// mode walks the ordinary way; the verifying mode also walks it and compares the bodies.
    /// </summary>
    internal static SharedBodyCensus? OfLoadedBody(Algorithm root, CompletedModuleViews.Attempt? moduleViews,
        CancellationToken cancellationToken = default)
    {
        if (moduleViews is not { Shares: true })
            return Of(root, moduleViews?.Observations, cancellationToken);
        // A module root elaborated to a callable alias is no unit: the part that reaches it walks it as its own nodes,
        // which is exact while no other part reaches it. A unit that reaches one leaves that open (another part may reach
        // it too, and the census's descent below an algorithm that is no user body depends on how often the whole graph
        // marks it), so such a composition is walked the ordinary way.
        if (!TryOfComposition(root, moduleViews, out var census, cancellationToken))
            return Of(root, moduleViews.Observations, cancellationToken);
        if (moduleViews.Verifies && !SameBodies(census, Of(root, cancellationToken)))
            throw new InvalidOperationException("The shared-body census by module-declaration units differs from the ordinary walk's.");
        return census;
    }

    private static bool TryOfComposition(Algorithm root, CompletedModuleViews.Attempt moduleViews, out SharedBodyCensus? census,
        CancellationToken cancellationToken)
    {
        census = null;
        var observations = moduleViews.Observations;
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance) { root };
        var pending = new Stack<object>();
        pending.Push(root);
        HashSet<object>? shared = null;
        // The edges every part holds to each module root, and the roots in discovery order (units add theirs as they are read).
        Dictionary<Algorithm.User, long>? rootEdges = null;
        List<Algorithm.User>? roots = null;
        void CountRootEdges(Algorithm.User view, long edges)
        {
            rootEdges ??= new(ReferenceEqualityComparer.Instance);
            if (rootEdges.TryGetValue(view, out var known))
                rootEdges[view] = known + edges;
            else
            {
                rootEdges[view] = edges;
                (roots ??= []).Add(view);
            }
        }

        while (pending.TryPop(out var node))
        {
            cancellationToken.ThrowIfCancellationRequested();
            observations?.RecordDeferredCensusExpansion();
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
            {
                if (CompletedModuleViews.IsModuleView(child, out var view)) CountRootEdges(view, 1);
                else if (seen.Add(child)) pending.Push(child);
                else (shared ??= new(ReferenceEqualityComparer.Instance)).Add(child);
            }
        }

        if (roots is not null)
        {
            // Each distinct root once: its unit's bodies, and the edges its own nodes hold to the roots it splices.
            for (var next = 0; next < roots.Count; next++)
            {
                cancellationToken.ThrowIfCancellationRequested();
                var unit = moduleViews.CensusUnitOf(roots[next], cancellationToken);
                if (unit.ReachesAliasModuleRoot) return false;
                foreach (var body in unit.Bodies)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    (census ??= new())._bodies.Add(body);
                }
                foreach (var (nested, edges) in unit.Nested)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    CountRootEdges(nested, edges);
                }
            }

            foreach (var view in roots)
            {
                cancellationToken.ThrowIfCancellationRequested();
                if (rootEdges![view] > 1) (shared ??= new(ReferenceEqualityComparer.Instance)).Add(view);
            }
        }

        census = MergeSharedNodes(shared, census, cancellationToken);
        return true;
    }

    /// <summary>
    /// The census unit of the module declaration <paramref name="view"/> (<see cref="CompletedModuleViews.CensusUnit"/>):
    /// the census walk from the declaration, stopping at every other module root (whose edges it counts, never entering
    /// it), with the walk's own cancellation checks.
    /// </summary>
    internal static CompletedModuleViews.CensusUnit ComputeUnit(Algorithm.User view, FrontEndTraversalObservations? observations,
        CancellationToken cancellationToken)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance) { view };
        var pending = new Stack<object>();
        pending.Push(view);
        HashSet<object>? shared = null;
        Dictionary<Algorithm.User, int>? nested = null;
        List<Algorithm.User>? order = null;
        var reachesAliasModuleRoot = false;
        while (pending.TryPop(out var node))
        {
            cancellationToken.ThrowIfCancellationRequested();
            observations?.RecordDeferredCensusExpansion();
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
            {
                if (CompletedModuleViews.IsModuleView(child, out var inner))
                {
                    nested ??= new(ReferenceEqualityComparer.Instance);
                    if (nested.TryGetValue(inner, out var edges))
                        nested[inner] = edges + 1;
                    else
                    {
                        nested[inner] = 1;
                        (order ??= []).Add(inner);
                    }

                    continue;
                }

                reachesAliasModuleRoot |= child is Algorithm.Alias { IsModuleElaborated: true };
                if (seen.Add(child)) pending.Push(child);
                else (shared ??= new(ReferenceEqualityComparer.Instance)).Add(child);
            }
        }

        var bodies = MergeSharedNodes(shared, null, cancellationToken) is { } census ? census._bodies.ToArray() : [];
        return new(bodies, order is null ? [] : [.. order.Select(inner => (inner, nested![inner]))], reachesAliasModuleRoot);
    }

    /// <summary>Whether two censuses mark the same bodies (both null when nothing is shared).</summary>
    internal static bool SameBodies(SharedBodyCensus? left, SharedBodyCensus? right)
        => left is null ? right is null : right is not null && left._bodies.SetEquals(right._bodies);

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
/// <para>For host alias preflight the free-name set also tracks the null name. It has its own bit alongside the
/// interned strings and follows the same union and shadowing rules as every written name.</para>
/// </summary>
internal sealed class RegionFreeNames(NameSetInterner names)
{
    internal readonly record struct FreeNames(CanonicalNameSet Named, bool HasNull);

    private readonly Dictionary<object, FreeNames> _memo = new(ReferenceEqualityComparer.Instance);

    internal NameSetInterner Names { get; } = names;

    internal CanonicalNameSet Of(object node) => IncludingNull(node).Named;

    internal FreeNames IncludingNull(object node)
    {
        if (_memo.TryGetValue(node, out var known)) return known;
        var set = node switch
        {
            Algorithm body => Body(body),
            Expr.Resolve(var name) => Add(default, name),
            Expr.Param(var name) => Add(default, name),
            _ => Children(node),
        };
        if (node is Expr.DotCall { EffectiveLexicalFallback: Expr.Resolve(var fallback) })
            set = Add(set, fallback);
        _memo[node] = set;
        return set;
    }

    private FreeNames Add(FreeNames set, string name)
        => name is null ? set with { HasNull = true } : set with { Named = Names.With(set.Named, [name]) };

    private FreeNames Union(FreeNames left, FreeNames right)
        => new(Names.Union(left.Named, right.Named), left.HasNull || right.HasNull);

    private FreeNames Children(object node)
    {
        FreeNames set = default;
        for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
            if (child is Expr or Algorithm or OutputBundle)
                set = Union(set, IncludingNull(child));
        return set;
    }

    private FreeNames Body(Algorithm body)
    {
        FreeNames opens = default;
        foreach (var open in body.Opens) opens = Union(opens, IncludingNull(open));
        FreeNames own = default;
        foreach (var row in body.Output) own = Union(own, IncludingNull(row));
        foreach (var property in body.Properties) own = Union(own, IncludingNull(property.Value));
        foreach (var branch in body.Branches) own = Union(own, IncludingNull(branch.Body));
        if (body.Properties.Count > 0)
        {
            own = new(Names.Except(own.Named, Names.With(NameSetInterner.Empty, DeclaredNames(body.Properties))),
                own.HasNull && !body.Properties.Any(static property => property.Name is null));
        }
        return Union(opens, own);
    }

    // The string-valued names to intern. The null declaration shadows the separate bit in Body.
    private static IEnumerable<string> DeclaredNames(IReadOnlyList<Property> properties)
    {
        foreach (var property in properties)
            if (property.Name is { } name)
                yield return name;
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
