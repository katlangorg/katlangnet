namespace KatLang;

internal sealed partial class StaticStructureOperation
{
    private readonly Dictionary<StaticScopeKey, ImplicitArgumentResolver.ResolverLevel> _resolverLevels = new(ReferenceEqualityComparer.Instance);
    private readonly HashSet<ImplicitArgumentResolver.ResolverLevel> _resolverLevelViews = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<StaticScopeKey, DeclaringOwners> _declaringOwners = new(ReferenceEqualityComparer.Instance);

    internal void ReleaseResolverLevels()
    {
        foreach (var level in _resolverLevelViews) level.Release();
        _resolverLevels.Clear();
        _resolverLevelViews.Clear();
    }

    internal void RegisterResolverLevel(ImplicitArgumentResolver.ResolverLevel level)
    {
        if (!_resolverLevelViews.Contains(level)) Queries.Resources.Metadata(8);
        _resolverLevels[level.StaticContext!.Key] = level;
        _resolverLevelViews.Add(level);
    }

    internal DeclaringOwners OwnersOf(StaticScopeKey key)
    {
        var pending = new Stack<StaticScopeKey>();
        for (var at = key; !_declaringOwners.ContainsKey(at); at = at.Parent!)
        {
            pending.Push(at);
            if (at.Parent is null) break;
        }
        while (pending.TryPop(out var next))
        {
            Queries.Resources.Metadata(3);
            _declaringOwners[next] = next.Parent is { } parent ? _declaringOwners[parent].InsideIdentity(next.Declaration) : DeclaringOwners.Root;
        }
        return _declaringOwners[key];
    }

    internal ImplicitArgumentResolver.ResolverLevel? ResolverLevel(StaticScopeKey key)
    {
        if (ReferenceEquals(key, Queries.Keys.Root)) return null;
        if (_resolverLevels.TryGetValue(key, out var level)) return level;
        var parent = ResolverLevel(key.Parent!);
        var body = DetectedView(key) ?? SourceOf(key);
        Queries.Resources.Metadata(8);
        level = new(body, OwnersOf(key), parent, staticContext: Context(key)) { Raw = true };
        _resolverLevels.Add(key, level);
        _resolverLevelViews.Add(level);
        return level;
    }

    /// <summary>
    /// The declaration <paramref name="key"/> denotes as a static chase reads it: its DETECTED input, never a processed
    /// form (B3-5★: every signature a chase could need is selected before any rewrite, so no reading depends on which
    /// body a region processed first).
    /// </summary>
    internal ImplicitArgumentResolver.StaticDeclaration Declaration(StaticScopeKey key)
    {
        var parent = key.Parent ?? Queries.Keys.Root;
        var level = ResolverLevel(parent);
        var value = DetectedView(key) ?? SourceOf(key);
        return new(value, OpenProviderIdentity.DeclaredIn(value, OwnersOf(parent)), OwnersOf(parent), level) { Raw = true };
    }

    internal ImplicitArgumentResolver.StaticDeclaration? SelectedDeclaration(StaticScopeKey from, string name,
        StaticQueryProjection projection, StaticCycleCheck stratum)
    {
        var fact = Binding(from, name, projection, stratum);
        return fact.Kind == StaticFactKind.Declaration
            ? Declaration(ContextOf(fact.Scope!, fact.Property!.Value)) : null;
    }

    internal ImplicitArgumentResolver.StaticDeclaration? SelectedStructure(StaticScopeKey key, bool viaOpens, StaticCycleCheck stratum)
    {
        var fact = Read(viaOpens ? StaticQueryKey.TargetWalk(key, stratum)
            : StaticQueryKey.Project(StaticQueryKind.TargetWalk, key, StaticQueryProjection.OpenStructure, stratum: stratum));
        return fact.Kind == StaticFactKind.Structure && fact.Scope is { } target ? Declaration(target) : null;
    }

    internal bool IsCyclic(StaticScopeKey scope, StaticCycleCheck check)
        => Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.TargetCycle,
                stratum: StaticCycleCheck.None)).Kind == StaticFactKind.Refused
            || check == StaticCycleCheck.Formation && Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, scope,
                StaticQueryProjection.TargetCycle, stratum: StaticCycleCheck.Lower)).Kind == StaticFactKind.Refused;

    internal (ImplicitArgumentResolver.StaticDeclaration End, Expr? Through) InvocationTarget(
        ImplicitArgumentResolver.StaticDeclaration start)
    {
        var key = ContextOf(start.Level?.StaticContext?.Key ?? Queries.Keys.Root, start.Target);
        var end = Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, key, StaticQueryProjection.InvocationTarget));
        if (end.Kind != StaticFactKind.Structure || end.Scope is null)
            throw new InvalidOperationException("An invocation target must be conclusive after A1 admission.");
        return (Declaration(end.Scope), end.Data as Expr);
    }
}
