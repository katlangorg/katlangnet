namespace KatLang.Evaluation;

/// <summary>
/// Run-local indexes of ordered property lists. Only selection is cached: the first
/// matching Property instance — of a name, or of a name among the public members
/// (<see cref="LookupPublic"/>) — without exposure, parent wiring or values.
/// Host-owned executable metadata is stable during a run; a new run builds new indexes
/// so replacement, reordering and same-count edits between runs remain visible.
/// </summary>
internal sealed class PropertyBindingIndexCache
{
    internal const int MinimumIndexedPropertyCount = 32;

    // Key the actual list, not an algorithm's record equality or declaration token:
    // wired views share their list, while a with-copy can replace it independently.
    private Dictionary<IReadOnlyList<Property>, Dictionary<string, Property>>? _indexes;

    internal Property? Lookup(IReadOnlyList<Property> properties, string name)
    {
        if (properties.Count < MinimumIndexedPropertyCount)
        {
            // Indexed, not `foreach`: no boxed enumerator per lookup (PERF-ORD-1).
            for (var i = 0; i < properties.Count; i++)
            {
                var property = properties[i];
                if (property.Name == name)
                    return property;
            }
            return null;
        }

        _indexes ??= new(ReferenceEqualityComparer.Instance);
        if (!_indexes.TryGetValue(properties, out var index))
        {
            index = new(properties.Count, StringComparer.Ordinal);
            foreach (var property in properties)
                index.TryAdd(property.Name, property);
            _indexes.Add(properties, index);
        }

        return index.GetValueOrDefault(name);
    }

    /// <summary>
    /// The smallest provider member list whose PUBLIC members are indexed for open selection
    /// (<see cref="LookupPublic"/>). Measured in November 2026 (Release, FullOpts, a query string distinct
    /// from the member name): an unambiguous read checks the other providers for a second offer.
    /// Missing in 16 members costs the scan about 33 ns against
    /// about 20 ns for the index's two probes (the list by reference, then the name); in 8 members about
    /// 11 ns against 16 ns, so smaller providers keep the scan. Building an index of 16 members costs about
    /// 0.3 µs, once per run per list.
    /// </summary>
    internal const int MinimumIndexedPublicPropertyCount = 16;

    // Key the actual list, as for _indexes: name -> the FIRST PUBLIC property of that name, per list.
    private Dictionary<IReadOnlyList<Property>, (Dictionary<string, Property> Named, Property? Unnamed)>? _publicIndexes;

    /// <summary>
    /// The first PUBLIC property of <paramref name="properties"/> named <paramref name="name"/>, or null —
    /// exactly what the ordered scan for <c>Name == name &amp;&amp; IsPublic</c> returns (Lean
    /// <c>Algorithm.lookupPropDefPublic?</c>): a private member of the name is skipped, never selected and
    /// never hiding a later public one. Open selection asks it of every provider of a consulted level
    /// (<c>Evaluator.ResolvedOpenLevel</c>). A list of at least
    /// <see cref="MinimumIndexedPublicPropertyCount"/> members is indexed once per run, in list order, each
    /// name keeping its first public member; a smaller list is scanned. Selection only, like
    /// <see cref="Lookup"/>: exposure, the access check, wiring and values stay with the caller. Sequential,
    /// like <see cref="Lookup"/>: open selection runs in the same lexical lookups.
    /// </summary>
    internal Property? LookupPublic(IReadOnlyList<Property> properties, string name)
    {
        // The count is read once: the list is stable during a run, and the provider walk asks every provider.
        var count = properties.Count;
        if (count >= MinimumIndexedPublicPropertyCount)
            return LookupIndexedPublic(properties, name);

        // Indexed, not `foreach`: no boxed enumerator per provider of every open read (PERF-ORD-1). Not forced
        // inline: one call per provider, as the scan was before the index existed.
        for (var i = 0; i < count; i++)
        {
            var property = properties[i];
            if (property.Name == name && property.IsPublic)
                return property;
        }
        return null;
    }

    // The index path of LookupPublic, out of line: built on the list's first indexed read of the run.
    private Property? LookupIndexedPublic(IReadOnlyList<Property> properties, string name)
    {
        _publicIndexes ??= new(ReferenceEqualityComparer.Instance);
        if (!_publicIndexes.TryGetValue(properties, out var index))
        {
            index = (new(StringComparer.Ordinal), null);
            for (var i = 0; i < properties.Count; i++)
            {
                var property = properties[i];
                if (!property.IsPublic)
                    continue;
                // Host-built lists can contain a null name. The ordered scan compares it like any other name.
                if (property.Name is null)
                    index.Unnamed ??= property;
                else
                    index.Named.TryAdd(property.Name, property);
            }
            _publicIndexes.Add(properties, index);
        }

        return name is null ? index.Unnamed : index.Named.GetValueOrDefault(name);
    }

    /// <summary>The number of member lists whose public members this run has indexed (<see cref="LookupPublic"/>); a test observation.</summary>
    internal int PublicIndexCount => _publicIndexes?.Count ?? 0;

    // Declaration token -> the first property carrying it, per list (again keyed by the list itself).
    // Guarded: a binding-cell establishment may be raced, unlike the sequential name lookups above.
    private Dictionary<IReadOnlyList<Property>, Dictionary<DeclarationIdentity, Property>>? _declarationIndexes;
    private readonly Lock _declarationIndexGate = new();

    /// <summary>
    /// The first property of <paramref name="properties"/> whose value carries the declaration
    /// <paramref name="declaration"/> — compared by reference, never by spelling — or null when the
    /// list declares none. This is how a wired runtime-target alias finds its OWN property, hence
    /// its exposure (ALIAS-CELL-LIFETIME; Lean <c>aliasOwnProperty?</c>): the wired
    /// <see cref="Algorithm.Alias"/> does not carry it, and no copy of it is kept anywhere else.
    /// Selection only, like <see cref="Lookup"/>: nothing of the property is cached but its identity.
    /// </summary>
    internal Property? LookupDeclaration(IReadOnlyList<Property> properties, DeclarationIdentity declaration)
    {
        if (properties.Count < MinimumIndexedPropertyCount)
        {
            for (var i = 0; i < properties.Count; i++)
            {
                var property = properties[i];
                if (ReferenceEquals(property.Value.Declaration, declaration))
                    return property;
            }
            return null;
        }

        lock (_declarationIndexGate)
        {
            _declarationIndexes ??= new(ReferenceEqualityComparer.Instance);
            if (!_declarationIndexes.TryGetValue(properties, out var index))
            {
                index = new(properties.Count);
                foreach (var property in properties)
                {
                    if (property.Value.Declaration is { } token)
                        index.TryAdd(token, property);
                }
                _declarationIndexes.Add(properties, index);
            }

            return index.GetValueOrDefault(declaration);
        }
    }
}
