namespace KatLang;

internal enum StaticAstPhase { RawSource, NameResolved, Resolved }

/// <summary>
/// Read-only Q1–Q7 selections. Analysis snapshots and resolved publications share projections, not completion status.
/// Neither implementation retains a producer engine or recomputes reference structure at a consumer.
/// </summary>
internal abstract class StaticLookupFacts
{
    // One complete body index per view version. Sealed facts may be shared by parallel consumers,
    // so every collection is built privately and published together; a reader uses one snapshot.
    private sealed record BodyIndex(int Version, Dictionary<Algorithm, StaticScopeKey?> Exact,
        Dictionary<Algorithm, Algorithm?> Receivers, HashSet<Algorithm> DifferentReceivers,
        Dictionary<(StaticScopeKey Parent, object Body, object? Region), StaticScopeKey> Contextual);
    private BodyIndex? _bodyIndex;
    private readonly Lock _bodyIndexGate = new();
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
    private long _bodyIndexBuilds;
    private long _bodyIndexScopeVisits;
    /// <summary>Published (complete) index snapshots; a failed construction publishes and counts nothing.</summary>
    internal long BodyIndexBuilds => Interlocked.Read(ref _bodyIndexBuilds);
    internal long BodyIndexScopeVisits => Interlocked.Read(ref _bodyIndexScopeVisits);
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
        if (!IndexBodies().Exact.TryGetValue(body, out var selected)) return null;
        if (selected is null)
            throw new ArgumentException("A shared body has several structural contexts; supply its occurrence context explicitly.", nameof(body));
        return Context(selected);
    }

    /// <summary>A context-free catalog may use a receiver only when every published occurrence agrees.</summary>
    internal Algorithm? AgreedReceiver(Algorithm body)
    {
        var index = IndexBodies();
        if (index.DifferentReceivers.Contains(body))
            throw new ArgumentException("Receiver structure depends on the occurrence context.", nameof(body));
        return index.Receivers.GetValueOrDefault(body);
    }

    internal StaticScopeKey? ContextualBody(StaticScopeKey parent, Algorithm body, object? region)
        => IndexBodies().Contextual.GetValueOrDefault((parent, body, region));

    private BodyIndex IndexBodies()
    {
        EnsureUsable();
        // Views change only through single-owner publication (Retarget before Seal, a Q8 projection's
        // own revision); sealed shared facts keep one version, so contended readers build once.
        var version = ViewVersion;
        if (Volatile.Read(ref _bodyIndex) is { } current && current.Version == version) return current;
        lock (_bodyIndexGate)
        {
            if (_bodyIndex is { } published && published.Version == version) return published;
            // Construction reads only Scopes/Facts, never this index, so the gate is not reentered.
            var index = new Dictionary<Algorithm, StaticScopeKey?>(ReferenceEqualityComparer.Instance);
            var receivers = new Dictionary<Algorithm, Algorithm?>(ReferenceEqualityComparer.Instance);
            var different = new HashSet<Algorithm>(ReferenceEqualityComparer.Instance);
            var contextual = new Dictionary<(StaticScopeKey Parent, object Body, object? Region), StaticScopeKey>(BodyContextComparer.Instance);
            long visits = 0;
            foreach (var key in Scopes)
            {
                visits++;
                if (Facts(key) is { Body: { } view } facts)
                {
                    if (!index.TryAdd(view, key)) index[view] = null;
                    if (key.Parent is { } parent) contextual.TryAdd((parent, view, key.BindingRegion), key);
                    var receiver = facts.Receiver is { Kind: StaticFactKind.Structure, Target: { } target }
                        ? Facts(target)?.Body : null;
                    if (!receivers.TryAdd(view, receiver) && !ReferenceEquals(receivers[view], receiver)) different.Add(view);
                }
            }
            var built = new BodyIndex(version, index, receivers, different, contextual);
            Volatile.Write(ref _bodyIndex, built);
            Interlocked.Increment(ref _bodyIndexBuilds);
            Interlocked.Add(ref _bodyIndexScopeVisits, visits);
            return built;
        }
    }
}
