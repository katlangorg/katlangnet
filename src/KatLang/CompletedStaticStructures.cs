using System.Collections.Immutable;

namespace KatLang;

/// <summary>
/// Completed Q1–Q7 projections. Scope keys contain declaration/pattern identity only: no query definition, engine,
/// token, physical scope or raw-to-processed map is retained. Local erroneous trees may carry these facts; only the
/// pipeline's successful freeze can share them with another unit. Exposure retargets views before sealing the table.
/// </summary>
internal sealed class CompletedStaticStructures : StaticLookupFacts
{
    internal readonly record struct Selection(StaticFactKind Kind, StaticScopeKey? Target = null, OpenProviderIdentity? Identity = null)
    {
        internal static Selection Unavailable => new(StaticFactKind.Unknown);
    }

    internal sealed record BodyFacts(Algorithm? Body, Selection Receiver, Selection Open,
        IReadOnlyDictionary<string, StaticScopeKey> Members, IReadOnlySet<string> Parameters, ImmutableArray<Selection> Providers,
        ImmutableHashSet<string>? UnavailableOpenNames = null, ImmutableHashSet<string>? AmbiguousOpenNames = null,
        bool IsProvisional = false, Selection? RequirementReceiver = null, Selection? RequirementOpen = null);

    private ImmutableDictionary<StaticScopeKey, BodyFacts> _bodies;
    private ImmutableDictionary<(StaticScopeKey Parent, object Declaration, object? Region), StaticScopeKey?> _children;
    // Most keys use the body's declaration. An explicitly supplied owner identity may differ;
    // retain that exception so a missing ordinary child key is conclusive without rebuilding
    // the versioned, body-specific catalog. Only genuine exceptions need this additional metadata.
    private ImmutableHashSet<(StaticScopeKey Parent, object Declaration, object? Region)> _alternateChildDeclarations;
    private Dictionary<StaticScopeKey, BodyFacts>? _local = new(ReferenceEqualityComparer.Instance);
    private bool _failed;
    private StaticQueryResourceBudget? _resources;

    internal CompletedStaticStructures(StaticScopeKey prelude, CompletedStaticStructures? previous = null, StaticQueryResourceBudget? resources = null)
    {
        previous?.EnsureUsable();
        _resources = resources;
        if (previous is { IsSealed: false }) throw new InvalidOperationException("Only sealed completed facts may cross a unit boundary.");
        RetainedStorageUnits = previous?.RetainedStorageUnits ?? 0;
        HasProvisional = previous?.HasProvisional ?? false;
        PreludeKey = prelude;
        _bodies = previous?._bodies ?? ImmutableDictionary.Create<StaticScopeKey, BodyFacts>(ReferenceEqualityComparer.Instance);
        _children = previous?._children ?? ImmutableDictionary.Create<(StaticScopeKey, object, object?), StaticScopeKey?>(ChildComparer.Instance);
        _alternateChildDeclarations = previous?._alternateChildDeclarations
            ?? ImmutableHashSet.Create<(StaticScopeKey, object, object?)>(ChildComparer.Instance);
    }

    internal static void Attach(Algorithm body, CompletedStructurePublication publication)
    {
        if (publication.Entry is { } entry && publication.Facts.Facts(entry)?.Body is null)
            publication = publication with { EntryView = body };
        switch (body)
        {
            case Algorithm.User user: user.CompletedStructure = publication; break;
            case Algorithm.Conditional family: family.CompletedStructure = publication; break;
            case Algorithm.Alias alias: alias.CompletedStructure = publication; break;
            case Algorithm.Builtin: throw new InvalidOperationException("A builtin cannot retain a program publication.");
        }
    }

    internal override StaticScopeKey PreludeKey { get; }
    internal bool IsSealed => _local is null;
    internal bool HasProvisional { get; private set; }
    private int _viewVersion;
    internal override int ViewVersion => _viewVersion;
    internal long RetargetNodeVisits { get; private set; }
    internal long RetainedStorageUnits { get; private set; }
    internal bool IsFailed => _failed || _resources?.IsFailed == true;
    internal void RejectUnsealed()
    {
        if (!IsSealed) _failed = true;
    }
    internal int Count => _bodies.Count + (_local?.Keys.Count(k => !_bodies.ContainsKey(k)) ?? 0);
    internal override BodyFacts? Facts(StaticScopeKey key)
    {
        EnsureUsable();
        return _local?.GetValueOrDefault(key) ?? _bodies.GetValueOrDefault(key);
    }

    internal override void EnsureUsable()
    {
        if (IsFailed) throw new InvalidOperationException("A failed structural publication cannot be read or changed.");
    }

    internal void Add(StaticScopeKey key, BodyFacts facts)
    {
        EnsureUsable();
        if (_local is null) throw new InvalidOperationException("A sealed structural publication is immutable.");
        HasProvisional |= facts.IsProvisional;
        if (!_local.ContainsKey(key) && !_bodies.ContainsKey(key))
            RetainedStorageUnits += 12 + 2L * facts.Members.Count + 4L * facts.Parameters.Count + 2L * facts.Providers.Length
                + 2L * ((facts.UnavailableOpenNames?.Count ?? 0) + (facts.AmbiguousOpenNames?.Count ?? 0))
                + (facts.IsProvisional ? 2 : 0);
        else RetainedStorageUnits += 2L * ((facts.UnavailableOpenNames?.Count ?? 0)
            + (facts.AmbiguousOpenNames?.Count ?? 0) - (Facts(key)?.UnavailableOpenNames?.Count ?? 0)
            - (Facts(key)?.AmbiguousOpenNames?.Count ?? 0));
        _local[key] = facts;
        if (key.Parent is { } parent)
        {
            if (facts.Body is { } body && !ReferenceEquals(key.Declaration, OpenProviderIdentity.DeclarationOf(body)))
            {
                var alternate = (parent, OpenProviderIdentity.DeclarationOf(body), key.BindingRegion);
                if (!_alternateChildDeclarations.Contains(alternate))
                {
                    _resources?.Metadata(2);
                    RetainedStorageUnits += 2;
                    _alternateChildDeclarations = _alternateChildDeclarations.Add(alternate);
                }
            }
            var child = (parent, key.Declaration, key.BindingRegion);
            if (!_children.TryGetValue(child, out var existing)) _children = _children.Add(child, key);
            else if (!ReferenceEquals(existing, key)) _children = _children.SetItem(child, null);
        }
    }

    internal void Retarget(StaticScopeKey key, Algorithm body)
    {
        if (Facts(key) is not { Body: { } previous } facts) return;
        if (!ReferenceEquals(OpenProviderIdentity.DeclarationOf(previous), OpenProviderIdentity.DeclarationOf(body)))
            throw new InvalidOperationException("Exposure must preserve a published declaration identity.");
        if (_local is null || !_local.ContainsKey(key))
        {
            // A module already classified by an earlier successful unit is immutable and reused by identity.
            if (!ReferenceEquals(previous, body)) throw new InvalidOperationException("A completed external view cannot be replaced.");
            return;
        }
        if (!ReferenceEquals(previous, body))
        {
            _resources?.Metadata(2);
            _local[key] = facts with { Body = body };
            _viewVersion++;
        }
    }

    internal void Seal(CancellationToken cancellationToken = default)
    {
        EnsureUsable();
        if (_local is null) return;
        try
        {
            var builder = _bodies.ToBuilder();
            foreach (var (key, facts) in _local)
            {
                cancellationToken.ThrowIfCancellationRequested();
                _resources?.Metadata(2, cancellationToken: cancellationToken);
                builder[key] = facts;
            }
            _bodies = builder.ToImmutable();
            _local = null;
            // Completed immutable facts outlive their producer. A later cancellation/fault of that
            // producer cannot invalidate this successful publication or any continuation sharing it.
            _resources = null;
        }
        catch { _failed = true; throw; }
    }

    /// <summary>Retargets the final exposed tree by published context, including memo hits and branch occurrences.</summary>
    internal void RetargetTree(StaticScopeKey entry, Algorithm tree, CancellationToken cancellationToken = default)
    {
        EnsureUsable();
        if (_local is null) return;
        using var storage = _resources?.Temporary();
        var seen = new Dictionary<StaticScopeKey, HashSet<object>>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<(object Node, StaticScopeKey Context)>();
        pending.Push((tree, entry));
        try
        {
            while (pending.TryPop(out var item))
            {
                cancellationToken.ThrowIfCancellationRequested();
                _resources?.Metadata(0, cancellationToken: cancellationToken);
                if (!seen.TryGetValue(item.Context, out var nodes))
                {
                    storage?.Add(3, cancellationToken);
                    seen[item.Context] = nodes = new(ReferenceEqualityComparer.Instance);
                }
                if (nodes.Contains(item.Node)) continue;
                storage?.Add(1, cancellationToken);
                nodes.Add(item.Node);
                RetargetNodeVisits++;
                if (item.Node is Algorithm body)
                {
                    if (!_local.TryGetValue(item.Context, out var facts) || facts.Body is null) continue;
                    Retarget(item.Context, body);
                    foreach (var property in body.Properties)
                        if (property.Value is Algorithm.User { IsAssignmentDeconstructionSource: true } source)
                        {
                            // Detection and resolution admitted these rows in the written owner.
                            foreach (var row in source.Output) pending.Push((row, item.Context));
                        }
                        else if (Child(item.Context, property.Value) is { } child) pending.Push((property.Value, child));
                    foreach (var open in body.Opens) pending.Push((open, PreludeKey));
                    if (body is Algorithm.Conditional family)
                    {
                        var declaring = family.Opens.Count == 0 ? item.Context.Parent ?? PreludeKey : item.Context;
                        foreach (var branch in family.Branches)
                            if (Child(declaring, branch.Body, branch.Pattern) is { } child) pending.Push((branch.Body, child));
                    }
                    else foreach (var row in body.Output) pending.Push((row, item.Context));
                }
                else if (item.Node is Expr.AlgorithmExpr block)
                {
                    if (Child(item.Context, block.Algorithm) is { } child) pending.Push((block.Algorithm, child));
                }
                else for (var i = 0; AstStructuralPreflight.TryGetChild(item.Node, i, out var child); i++)
                    pending.Push((child, item.Context));
            }
        }
        catch
        {
            _failed = true;
            throw;
        }
    }

    internal override IEnumerable<StaticScopeKey> Scopes => _bodies.Keys.Concat(_local?.Keys ?? Enumerable.Empty<StaticScopeKey>()).Distinct();

    internal override StaticScopeKey? Child(StaticScopeKey parent, Algorithm body, Pattern? pattern = null)
    {
        EnsureUsable();
        var declaring = body.IsModuleRoot ? PreludeKey : parent;
        var region = body.IsModuleRoot ? null : pattern;
        var child = (declaring, OpenProviderIdentity.DeclarationOf(body), region);
        if (_children.TryGetValue(child, out var selected))
            return selected ?? ContextualBody(declaring, body, region);
        // The catalog has no declaration in this exact owner/pattern region. Retargeting
        // preserves declarations, so a missing inert helper cannot become a child after a
        // view change. Ambiguous definitions and alternate owner identities still use the
        // body-specific projection; neither their contexts nor their language identities merge.
        return _alternateChildDeclarations.Contains(child) ? ContextualBody(declaring, body, region) : null;
    }

    private sealed class ChildComparer : IEqualityComparer<(StaticScopeKey Parent, object Declaration, object? Region)>
    {
        internal static readonly ChildComparer Instance = new();
        public bool Equals((StaticScopeKey Parent, object Declaration, object? Region) x, (StaticScopeKey Parent, object Declaration, object? Region) y)
            => ReferenceEquals(x.Parent, y.Parent) && ReferenceEquals(x.Declaration, y.Declaration) && ReferenceEquals(x.Region, y.Region);
        public int GetHashCode((StaticScopeKey Parent, object Declaration, object? Region) value)
            => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Parent),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Declaration),
                value.Region is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Region));
    }
}

/// <summary>Carried metadata; the entry key is present only on a compilation unit's root.</summary>
internal sealed record CompletedStructurePublication(CompletedStaticStructures Facts, StaticScopeKey? Entry = null, Algorithm? EntryView = null)
{
    internal bool MatchesEntry(Algorithm body)
        => Entry is { } entry && (Facts.Facts(entry)?.Body is { } published
            ? ReferenceEquals(published, body) : ReferenceEquals(EntryView, body));
}

/// <summary>A physical completed lookup context. It has no inference or reference-chasing capability.</summary>
internal sealed class CompletedStructureContext(StaticLookupFacts facts, StaticScopeKey key)
{
    internal long Identity => Key.RequirementIdentity;
    internal StaticLookupFacts Facts { get; } = facts;
    internal StaticScopeKey Key { get; } = key;

    internal static CompletedStructureContext? For(Algorithm? body, ElaboratedPropertyScope? parent, Pattern? pattern = null)
    {
        if (body is null) return null;
        if (parent?.CompletedContext is { Facts: AnalyzedStaticStructures } analyzed)
        {
            var declaringKey = pattern is not null && parent.OwnerAlgorithm is Algorithm.Conditional { Opens.Count: 0 }
                ? analyzed.Key.Parent ?? analyzed.Facts.PreludeKey : analyzed.Key;
            return analyzed.Facts.Child(declaringKey, body, pattern) is { } analyzedKey
                ? analyzed.Facts.Context(analyzedKey) : analyzed.Facts.ExactContext(body);
        }
        if (body.CompletedStructure is { Entry: { } entry } root)
            return root.MatchesEntry(body) ? root.Facts.Context(entry) : null;
        var inherited = parent?.CompletedContext;
        var graph = inherited?.Facts ?? body.CompletedStructure?.Facts;
        if (graph is null) return null;
        var declaring = inherited?.Key ?? graph.PreludeKey;
        if (pattern is not null && parent?.OwnerAlgorithm is Algorithm.Conditional { Opens.Count: 0 })
            declaring = declaring.Parent ?? graph.PreludeKey;
        var child = graph.Child(declaring, body, pattern);
        if (child is null && body.CompletedStructure is { } own && !ReferenceEquals(own.Facts, graph))
        {
            graph = own.Facts;
            child = graph.Child(declaring, body, pattern);
        }
        // A declaration-preserving host copy is a supplied view, not the published definition.
        // A real unavailable publication still has its admitted key; an invented key is not provenance.
        if (child is null || graph.Facts(child)?.Body is { } published && !ReferenceEquals(published, body)) return null;
        return new(graph, child);
    }

    internal ElaboratedPropertyScope Level(StaticScopeKey wanted, ElaboratedPropertyScope caller)
    {
        var cache = caller.MemberIndexes?.CompletedLevels;
        for (var physical = caller; physical is not null; physical = physical.Parent)
            if (ReferenceEquals(physical.CompletedContext?.Key, wanted))
            {
                cache?.TryAdd((Facts, wanted), physical);
                return physical;
            }
        if (cache is not null && cache.TryGetValue((Facts, wanted), out var known)) return known;
        var pending = new Stack<StaticScopeKey>();
        var at = wanted;
        while (cache is null || !cache.ContainsKey((Facts, at)))
        {
            pending.Push(at);
            if (at.Parent is not { } parent) break;
            at = parent;
        }
        ElaboratedPropertyScope? level = cache is not null && cache.TryGetValue((Facts, at), out known) ? known : null;
        while (pending.TryPop(out var next))
        {
            var body = Facts.Facts(next)?.Body;
            if (body is null) throw new InvalidOperationException("An unavailable completed owner cannot be materialized.");
            level = ElaboratedScopeLookup.CreateScope(body, level, observations: caller.Observations,
                memberIndexes: caller.MemberIndexes, completedContext: Facts.Context(next));
            cache?.TryAdd((Facts, next), level);
        }
        return level!;
    }

    internal StaticScopeKey? BodyKey(Algorithm body) => Facts.Child(Key, body);

    internal (Algorithm Structure, ElaboratedScopeLookup.StaticStructureScope Scope)? Receiver(Algorithm body, ElaboratedPropertyScope caller)
    {
        var selected = Facts.Child(Key, body);
        if (selected is not null)
        {
            if (Facts.Facts(selected)?.Body is { } published && !ReferenceEquals(published, body))
                throw new ArgumentException("The supplied view requires its own explicit structural admission.", nameof(body));
            return ReceiverAt(selected, caller);
        }
        var context = For(body, caller);
        return context?.ReceiverAt(context.Key, caller);
    }

    internal (Algorithm Structure, ElaboratedScopeLookup.StaticStructureScope Scope)? ReceiverAt(StaticScopeKey scope, ElaboratedPropertyScope caller)
    {
        RecordRead(caller);
        var selection = Facts.Facts(scope)?.Receiver;
        return selection is { Kind: StaticFactKind.Structure, Target: { } target }
            && Facts.Facts(target)?.Body is { } body && target.Parent is { } parent
                ? (body, new(Level(parent, caller), target, Facts)) : null;
    }

    internal ResolvedOpenTarget? Open(Algorithm body, ElaboratedPropertyScope declaring)
    {
        RecordRead(declaring);
        var selectedKey = Facts.Child(Key, body);
        if (selectedKey is not null && Facts.Facts(selectedKey)?.Body is { } published && !ReferenceEquals(published, body))
            throw new ArgumentException("The supplied view requires its own explicit structural admission.", nameof(body));
        var context = selectedKey is not null ? Facts.Context(selectedKey) : For(body, declaring);
        if (context?.Facts.Facts(context.Key)?.Open is not { Kind: StaticFactKind.Structure, Target: { } target, Identity: { } identity }
            || context.Facts.Facts(target)?.Body is not { } selected || target.Parent is not { } parent) return null;
        return new(selected, identity, context.Level(parent, declaring));
    }

    internal ResolvedOpenTarget? ProviderAt(int index, ElaboratedPropertyScope caller)
    {
        RecordRead(caller);
        return Facts.Facts(Key)?.Providers is { } providers && index < providers.Length ? Provider(providers[index], caller) : null;
    }

    private ResolvedOpenTarget? Provider(CompletedStaticStructures.Selection selection, ElaboratedPropertyScope caller)
        => selection is { Kind: StaticFactKind.Structure, Target: { Parent: { } parent } target, Identity: { } identity }
            && Facts.Facts(target)?.Body is { } body ? new(body, identity, Level(parent, caller)) : null;

    internal IReadOnlyList<ResolvedOpenProvider> Providers(ElaboratedPropertyScope caller)
    {
        RecordRead(caller);
        var result = new List<ResolvedOpenProvider>();
        var seen = new HashSet<OpenProviderIdentity>();
        if (Facts.Facts(Key)?.Providers is not { } providers) return result;
        for (var index = 0; index < providers.Length; index++)
            if (Provider(providers[index], caller) is { } selected && seen.Add(selected.Identity))
                result.Add(new(selected.Target, caller.Observations, caller.MemberIndexes, selected.Identity)
                { Level = selected.Level, Written = index < caller.Opens.Count ? caller.Opens[index] : null });
        return result;
    }

    internal bool OpenIsUnavailable(Algorithm body, ElaboratedPropertyScope declaring)
    {
        var context = For(body, declaring);
        return context?.Facts.Facts(context.Key)?.Open.Kind is null or StaticFactKind.Unknown;
    }

    private static void RecordRead(ElaboratedPropertyScope caller)
    {
        if (caller.MemberIndexes is { } cache) cache.RecordCompletedRead();
        else caller.Observations?.RecordCompletedStaticStructureRead();
    }
}
