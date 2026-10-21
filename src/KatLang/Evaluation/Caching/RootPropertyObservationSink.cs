namespace KatLang.Evaluation.Caching;

/// <summary>
/// The run-owned recorder behind <see cref="RunOptions.ObservePropertyValues"/> (IV-1/IV-2): it
/// receives every entry the run's <see cref="ZeroArgPropertyPublications"/> law PUBLISHES and keeps,
/// in publication order, those that belong to a source-declared root property of the run's final
/// elaborated root. It never evaluates, charges, renders, or observes cancellation, and it cannot
/// change a publication decision — it is told about one only after the law made it.
/// <para><b>Root membership.</b> A publication is kept when its binding is one of the root's own
/// <see cref="Property"/> instances (reference identity — never the name, a span, or record
/// equality), that property is <see cref="PropertyExposure.Exported"/> and has a real declaration
/// anchor, and the key's owner is the root itself: the root's declaration token and its own
/// property list (<see cref="StructuralOwnerIdentity.IsPropertyOwner"/>), so a binding object
/// reused under another owner is not mistaken for the root's. Spanless properties — the hoisted
/// <c>$deconstruct$N</c> source of an assignment deconstruction, host-built nodes — are never
/// kept, and neither is anything nested, imported, or local-only.</para>
/// <para><b>Lifetime.</b> One sink per engine run, created only when observation is requested, and
/// sequential like the cache that calls it. While the run executes it retains only the binding and
/// the published <see cref="ZeroArgPropertyResult"/> — no key, context, budget, or environment.
/// <see cref="Complete"/> turns the records into the public snapshot and releases them.</para>
/// </summary>
internal sealed class RootPropertyObservationSink
{
    // Value: whether the binding already has a kept publication (duplicate detection).
    private readonly Dictionary<Property, bool> _eligible = new(ReferenceEqualityComparer.Instance);
    private readonly object? _rootDeclaration;
    private readonly IReadOnlyList<Property> _rootProperties;
    private readonly List<(Property Binding, ZeroArgPropertyResult Published)> _records = [];

    internal RootPropertyObservationSink(Algorithm root)
    {
        _rootDeclaration = root.Declaration;
        _rootProperties = root.Properties;
        foreach (var property in root.Properties)
        {
            if (property.Exposure == PropertyExposure.Exported
                && property.FirstDeclarationSpan is { Start.Line: >= 1 })
            {
                _eligible.TryAdd(property, false);
            }
        }
    }

    /// <summary>
    /// Kept publications of a binding that had already been kept once. The root-publication
    /// contract expects zero (an exported root binding has one root-owner key per run); a
    /// nonzero count is an invariant violation that tests surface — the extra record is kept
    /// rather than merged or dropped, so nothing is concealed from the snapshot either.
    /// </summary>
    internal int DuplicateBindingPublications { get; private set; }

    /// <summary>Called by <see cref="ZeroArgPropertyPublications"/> right after it published <paramref name="key"/>.</summary>
    internal void Published(in ZeroArgPropertyCacheKey key, ZeroArgPropertyResult published)
    {
        if (key.BindingIdentity is not Property binding
            || !_eligible.TryGetValue(binding, out var seen)
            || key.OwnerIdentity is not StructuralOwnerIdentity owner
            || !owner.IsPropertyOwner(_rootDeclaration, _rootProperties))
        {
            return;
        }

        if (seen)
            DuplicateBindingPublications++;
        else
            _eligible[binding] = true;

        _records.Add((binding, published));
    }

    /// <summary>
    /// Builds the immutable public snapshot of the completed run and releases the raw records.
    /// Called once, after the engine's ordinary outcome projection and its cancellation checks.
    /// Each value is classified by the context-free predicate of the run-result boundary
    /// (<see cref="Evaluator.ContainsCallReference(Result, Dictionary{Result, bool})"/>, the scan behind
    /// <see cref="Evaluator.CallReferenceBoundaryError"/>, with one completed-verdict memo across the snapshot
    /// so shared structure is scanned once): a value containing a call reference
    /// anywhere becomes <see cref="PropertyValueStatus.Withheld"/> and is not retained; every other
    /// value is shared as is. Classification charges nothing and observes no token.
    /// </summary>
    internal PropertyObservations Complete()
    {
        if (_records.Count == 0)
            return PropertyObservations.Empty;

        // One memo for the whole snapshot: roots sharing a large graph scan it once, not once each.
        var completed = new Dictionary<Result, bool>(ReferenceEqualityComparer.Instance);
        var observations = new PropertyValueObservation[_records.Count];
        for (var i = 0; i < observations.Length; i++)
        {
            var (binding, published) = _records[i];
            var available = !Evaluator.ContainsCallReference(published.Value, completed);
            observations[i] = new PropertyValueObservation(
                binding.Name,
                binding.FirstDeclarationSpan!.Value,
                available ? PropertyValueStatus.Available : PropertyValueStatus.Withheld,
                available ? published.Value : null,
                published.EmittedCount);
        }

        _records.Clear();
        _records.TrimExcess();
        return new PropertyObservations(observations);
    }
}
