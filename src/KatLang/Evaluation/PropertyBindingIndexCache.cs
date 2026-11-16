namespace KatLang.Evaluation;

/// <summary>
/// Run-local indexes of ordered property lists. Only selection is cached: the first
/// matching Property instance, without visibility, exposure, parent wiring or values.
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
