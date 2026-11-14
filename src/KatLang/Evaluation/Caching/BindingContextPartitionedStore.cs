using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;

namespace KatLang.Evaluation.Caching;

/// <summary>
/// IDENTITY-PARTITIONED RUN STORAGE (a C#-only storage policy with no Lean counterpart; it changes no
/// hit, miss, publication, charge, diagnostic or value). A run-scoped, add-only store of cache keys
/// whose entries carry a BINDING-CONTEXT IDENTITY (<see cref="ZeroArgPropertyCacheKey.ValueEnvironmentIdentity"/>:
/// an activation's need-cell list, a value environment, or a planned loop's per-iteration identity)
/// keeps every entry of one identity in that identity's own partition, held by a
/// <see cref="ConditionalWeakTable{TKey, TValue}"/> keyed by the identity OBJECT
/// (<see cref="BindingContextPartitionTable"/>). A partition therefore lives exactly as long as its
/// identity is reachable. Every entry of an exported binding
/// (<see cref="ZeroArgPropertyCacheKey.RunWideEnvironmentIdentity"/>) stays in one strong, run-wide
/// dictionary.
/// <para><b>Why dropping a partition is unobservable.</b> The key comparers compare the identity
/// component by reference (<see cref="ZeroArgPropertyCacheKeyComparer"/>), so a key can equal a stored
/// key only by presenting the very identity object, and every key holds its identity strongly. When an
/// identity becomes unreachable, no live or future key can name it, so its entries could never be
/// read, re-added or removed again. Partitioning is by the identity object, never by a
/// <c>ParameterActivation</c>: CACHE-OWNER-D1 and COLLECT-CACHE-1 share one identity across activations,
/// and those activations keep sharing one partition. Nothing is evicted when an activation exits: a
/// returned activation re-entered through a call reference still holds its identity, and so still
/// reaches its entries.</para>
/// <para><b>Counts.</b> Nothing is removed from a partition that its owner could still present, so the
/// monotonic <see cref="AddedCount"/> equals the entry count an unpartitioned dictionary would report.
/// Callers expose it where they used the dictionary's count.</para>
/// <para>Like the caches that own it: sequential, not thread-safe, and owned by one run (an instance field
/// of the run-scoped cache, attached to no AST, algorithm, scope, prelude or context).</para>
/// </summary>
internal sealed class PartitionedMap<TKey, TValue>
    where TKey : notnull
{
    private readonly IEqualityComparer<TKey> _comparer;
    private readonly Func<TKey, object> _partitionOf;
    private readonly Dictionary<TKey, TValue> _runWide;
    private readonly BindingContextPartitionTable _partitions;
    private readonly int _store;

    /// <summary>A store with a partition table of its own.</summary>
    internal PartitionedMap(IEqualityComparer<TKey> comparer, Func<TKey, object> partitionOf)
        : this(comparer, partitionOf, new BindingContextPartitionTable(storeCount: 1), store: 0)
    {
    }

    /// <summary>
    /// A store whose identity partitions live in slot <paramref name="store"/> of a table it shares with the
    /// other stores of one cache, so one weak-table entry per identity serves all of them.
    /// </summary>
    internal PartitionedMap(
        IEqualityComparer<TKey> comparer,
        Func<TKey, object> partitionOf,
        BindingContextPartitionTable partitions,
        int store)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(store);
        ArgumentOutOfRangeException.ThrowIfGreaterThanOrEqual(store, partitions.StoreCount);
        _comparer = comparer;
        _partitionOf = partitionOf;
        _runWide = new Dictionary<TKey, TValue>(comparer);
        _partitions = partitions;
        _store = store;
    }

    /// <summary>Number of successful additions in this store's lifetime (monotonic).</summary>
    internal long AddedCount { get; private set; }

    internal bool TryGetValue(TKey key, [MaybeNullWhen(false)] out TValue value)
    {
        var identity = _partitionOf(key);
        // An exported key first: the common read of a program's self-contained bindings.
        if (IsRunWide(identity))
            return _runWide.TryGetValue(key, out value);
        if (Find(identity) is { } partition)
            return partition.TryGetValue(key, _comparer, out value);

        value = default;
        return false;
    }

    internal bool ContainsKey(TKey key) => TryGetValue(key, out _);

    internal bool TryAdd(TKey key, TValue value)
    {
        var identity = _partitionOf(key);
        var added = IsRunWide(identity)
            ? _runWide.TryAdd(key, value)
            : GetOrCreatePartition(identity).TryAdd(key, value, _comparer);
        if (added)
            AddedCount++;
        return added;
    }

    internal bool Remove(TKey key)
    {
        var identity = _partitionOf(key);
        if (IsRunWide(identity))
            return _runWide.Remove(key);
        return Find(identity) is { } partition && partition.Remove(key, _comparer);
    }

    /// <summary>
    /// TEST SEAM: the number of this store's identity partitions whose identity is still reachable (the
    /// run-wide dictionary is not counted). A dead identity's partition is never counted.
    /// </summary>
    internal int LivePartitionCount() => _partitions.LivePartitionCount(_store);

    private static bool IsRunWide(object identity)
        => ReferenceEquals(identity, ZeroArgPropertyCacheKey.RunWideEnvironmentIdentity) || identity is null;

    private Partition? Find(object identity)
        => _partitions.Find(identity) is { } slots ? (Partition?)slots[_store] : null;

    private Partition GetOrCreatePartition(object identity)
    {
        var slots = _partitions.GetOrCreate(identity);
        return (Partition?)slots[_store] ?? (Partition)(slots[_store] = new Partition());
    }

    /// <summary>
    /// The entries of one binding-context identity. An activation usually holds one or two local-only
    /// keys, so the first entry is stored inline and a dictionary is allocated only for the rest.
    /// Lookup compares the stored hash code before the comparer's equality, as a dictionary does.
    /// </summary>
    private sealed class Partition
    {
        private TKey? _key;
        private TValue? _value;
        private int _hashCode;
        private bool _hasKey;
        private Dictionary<TKey, TValue>? _more;

        internal bool TryGetValue(TKey key, IEqualityComparer<TKey> comparer, [MaybeNullWhen(false)] out TValue value)
        {
            if (_hasKey && _hashCode == comparer.GetHashCode(key) && comparer.Equals(_key!, key))
            {
                value = _value!;
                return true;
            }

            if (_more is not null)
                return _more.TryGetValue(key, out value);

            value = default;
            return false;
        }

        internal bool TryAdd(TKey key, TValue value, IEqualityComparer<TKey> comparer)
        {
            var hashCode = comparer.GetHashCode(key);
            if (_hasKey && _hashCode == hashCode && comparer.Equals(_key!, key))
                return false;

            if (!_hasKey && (_more is null || !_more.ContainsKey(key)))
            {
                (_key, _value, _hashCode, _hasKey) = (key, value, hashCode, true);
                return true;
            }

            _more ??= new Dictionary<TKey, TValue>(comparer);
            return _more.TryAdd(key, value);
        }

        internal bool Remove(TKey key, IEqualityComparer<TKey> comparer)
        {
            if (_hasKey && _hashCode == comparer.GetHashCode(key) && comparer.Equals(_key!, key))
            {
                (_key, _value, _hashCode, _hasKey) = (default, default, 0, false);
                return true;
            }

            return _more is not null && _more.Remove(key);
        }
    }
}

/// <summary>
/// The set form of <see cref="PartitionedMap{TKey, TValue}"/> for the statistics key sets: the same
/// identity partitioning, run-wide dictionary and monotonic <see cref="AddedCount"/> (the distinct
/// keys an unpartitioned set would have counted).
/// </summary>
internal sealed class PartitionedSet<TKey>
    where TKey : notnull
{
    private readonly PartitionedMap<TKey, bool> _entries;

    internal PartitionedSet(IEqualityComparer<TKey> comparer, Func<TKey, object> partitionOf)
        => _entries = new PartitionedMap<TKey, bool>(comparer, partitionOf);

    /// <summary>A set whose partitions live in slot <paramref name="store"/> of a shared table.</summary>
    internal PartitionedSet(
        IEqualityComparer<TKey> comparer,
        Func<TKey, object> partitionOf,
        BindingContextPartitionTable partitions,
        int store)
        => _entries = new PartitionedMap<TKey, bool>(comparer, partitionOf, partitions, store);

    /// <summary>Number of keys ever added (monotonic): an unpartitioned set's distinct-key count.</summary>
    internal long AddedCount => _entries.AddedCount;

    /// <summary>Adds <paramref name="key"/>; false when an equal key is already present.</summary>
    internal bool Add(TKey key) => _entries.TryAdd(key, true);

    internal bool Contains(TKey key) => _entries.ContainsKey(key);

    internal bool Remove(TKey key) => _entries.Remove(key);

    /// <summary>TEST SEAM: see <see cref="PartitionedMap{TKey, TValue}.LivePartitionCount"/>.</summary>
    internal int LivePartitionCount() => _entries.LivePartitionCount();
}

/// <summary>
/// The weak table behind one or more <see cref="PartitionedMap{TKey, TValue}"/> stores of ONE run-scoped
/// cache: binding-context identity OBJECT → one slot per store (that store's partition, created on its
/// first addition). The table holds an identity weakly and its slots only while the identity is
/// reachable (<see cref="ConditionalWeakTable{TKey, TValue}"/>), so one weak entry per identity serves
/// every store that shares the table — the run-scoped statistics cache's published entries, seen keys
/// and keys missed without a store — instead of one entry per store.
/// <para>No identity or partition is retained outside the weak table. Even one strong last-access
/// shortcut could keep an unbounded chain of otherwise dead binding environments alive.</para>
/// </summary>
internal sealed class BindingContextPartitionTable
{
    private readonly ConditionalWeakTable<object, object?[]> _partitions = new();

    internal BindingContextPartitionTable(int storeCount)
    {
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(storeCount);
        StoreCount = storeCount;
    }

    /// <summary>Number of stores sharing the table (slots per identity).</summary>
    internal int StoreCount { get; }

    /// <summary>The slots of <paramref name="identity"/>, or null when no store has added under it.</summary>
    internal object?[]? Find(object identity)
        => _partitions.TryGetValue(identity, out var slots) ? slots : null;

    /// <summary>The slots of <paramref name="identity"/>, created on its first addition by any store.</summary>
    internal object?[] GetOrCreate(object identity)
    {
        if (!_partitions.TryGetValue(identity, out var slots))
        {
            slots = new object?[StoreCount];
            _partitions.Add(identity, slots);
        }

        return slots;
    }

    /// <summary>
    /// TEST SEAM: the number of reachable identities under which store <paramref name="store"/> holds a
    /// partition. Enumerates the weak table, which never yields an identity that is no longer reachable.
    /// </summary>
    internal int LivePartitionCount(int store)
    {
        var count = 0;
        foreach (var (_, slots) in (IEnumerable<KeyValuePair<object, object?[]>>)_partitions)
        {
            if (slots[store] is not null)
                count++;
        }

        return count;
    }
}

/// <summary>The partition functions of the run-scoped caches' identity-partitioned stores.</summary>
internal static class BindingContextPartitions
{
    /// <summary>A property-cache key's binding-context identity.</summary>
    internal static Func<ZeroArgPropertyCacheKey, object> OfPropertyKey { get; } = static key => key.ValueEnvironmentIdentity;

    /// <summary>A deconstruction shared bind's source entry's binding-context identity.</summary>
    internal static Func<DeconstructionBindingExecution, object> OfDeconstruction { get; } =
        static execution => execution.SourceKey.ValueEnvironmentIdentity;

    /// <summary>A count reported where an unpartitioned collection's <c>int</c> count was, saturated rather than wrapped.</summary>
    internal static int SaturatedCount(long count) => count > int.MaxValue ? int.MaxValue : (int)count;
}
