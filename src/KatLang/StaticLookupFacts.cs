namespace KatLang;

internal enum StaticAstPhase { RawSource, NameResolved, Resolved }

/// <summary>
/// Read-only Q1–Q7 selections. Analysis snapshots and resolved publications share projections, not completion status.
/// Neither implementation retains a producer engine or recomputes reference structure at a consumer.
/// </summary>
internal abstract class StaticLookupFacts
{
    private Dictionary<Algorithm, StaticScopeKey?>? _exactBodies;
    private Dictionary<Algorithm, Algorithm?>? _receiverBodies;
    private HashSet<Algorithm>? _differentReceivers;
    private Dictionary<(StaticScopeKey Parent, object Body, object? Region), StaticScopeKey>? _contextualBodies;
    private sealed class BodyContextComparer : IEqualityComparer<(StaticScopeKey Parent, object Body, object? Region)>
    {
        internal static readonly BodyContextComparer Instance = new();
        public bool Equals((StaticScopeKey Parent, object Body, object? Region) x, (StaticScopeKey Parent, object Body, object? Region) y)
            => ReferenceEquals(x.Parent, y.Parent) && ReferenceEquals(x.Body, y.Body) && ReferenceEquals(x.Region, y.Region);
        public int GetHashCode((StaticScopeKey Parent, object Body, object? Region) value)
            => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Parent),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Body),
                value.Region is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Region));
    }
    private int _indexedVersion = -1;
    internal long BodyIndexBuilds { get; private set; }
    internal long BodyIndexScopeVisits { get; private set; }
    internal abstract StaticScopeKey PreludeKey { get; }
    internal Algorithm Prelude => Facts(PreludeKey)!.Body!;
    internal abstract CompletedStaticStructures.BodyFacts? Facts(StaticScopeKey key);
    internal abstract StaticScopeKey? Child(StaticScopeKey parent, Algorithm body, Pattern? pattern = null);
    internal abstract IEnumerable<StaticScopeKey> Scopes { get; }
    internal virtual int ViewVersion => 0;
    internal abstract void EnsureUsable();
    internal CompletedStructureContext Context(StaticScopeKey key) => new(this, key);
    internal StaticScopeKey? Member(StaticScopeKey owner, string name) => Facts(owner)?.Members.GetValueOrDefault(name);

    internal CompletedStructureContext? ExactContext(Algorithm body)
    {
        IndexBodies();
        if (!_exactBodies!.TryGetValue(body, out var selected)) return null;
        if (selected is null)
            throw new ArgumentException("A shared body has several structural contexts; supply its occurrence context explicitly.", nameof(body));
        return Context(selected);
    }

    /// <summary>A context-free catalog may use a receiver only when every published occurrence agrees.</summary>
    internal Algorithm? AgreedReceiver(Algorithm body)
    {
        IndexBodies();
        if (_differentReceivers!.Contains(body))
            throw new ArgumentException("Receiver structure depends on the occurrence context.", nameof(body));
        return _receiverBodies!.GetValueOrDefault(body);
    }

    internal StaticScopeKey? ContextualBody(StaticScopeKey parent, Algorithm body, object? region)
    {
        IndexBodies();
        return _contextualBodies!.GetValueOrDefault((parent, body, region));
    }

    private void IndexBodies()
    {
        EnsureUsable();
        if (_exactBodies is null || _indexedVersion != ViewVersion)
        {
            BodyIndexBuilds++;
            var index = new Dictionary<Algorithm, StaticScopeKey?>(ReferenceEqualityComparer.Instance);
            var receivers = new Dictionary<Algorithm, Algorithm?>(ReferenceEqualityComparer.Instance);
            var different = new HashSet<Algorithm>(ReferenceEqualityComparer.Instance);
            var contextual = new Dictionary<(StaticScopeKey Parent, object Body, object? Region), StaticScopeKey>(BodyContextComparer.Instance);
            foreach (var key in Scopes)
            {
                BodyIndexScopeVisits++;
                if (Facts(key) is { Body: { } view } facts)
                {
                    if (!index.TryAdd(view, key)) index[view] = null;
                    if (key.Parent is { } parent) contextual.TryAdd((parent, view, key.BindingRegion), key);
                    var receiver = facts.Receiver is { Kind: StaticFactKind.Structure, Target: { } target }
                        ? Facts(target)?.Body : null;
                    if (!receivers.TryAdd(view, receiver) && !ReferenceEquals(receivers[view], receiver)) different.Add(view);
                }
            }
            _exactBodies = index;
            _receiverBodies = receivers;
            _differentReceivers = different;
            _contextualBodies = contextual;
            _indexedVersion = ViewVersion;
        }
    }
}
