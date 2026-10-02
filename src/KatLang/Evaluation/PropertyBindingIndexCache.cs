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
            foreach (var property in properties)
                if (property.Name == name)
                    return property;
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
}
