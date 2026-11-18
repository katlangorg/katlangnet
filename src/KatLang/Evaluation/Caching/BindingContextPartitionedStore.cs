using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime;
using System.Runtime.CompilerServices;

namespace KatLang.Evaluation.Caching;

/// <summary>
/// IDENTITY-PARTITIONED RUN STORAGE (a C#-only storage policy with no Lean counterpart; it changes no
/// hit, miss, publication, charge, diagnostic or value). A run-scoped, add-only store of cache keys
/// whose entries carry a BINDING-CONTEXT IDENTITY (<see cref="ZeroArgPropertyCacheKey.ValueEnvironmentIdentity"/>:
/// an activation's need-cell list, a value environment, or a planned loop's per-iteration identity)
/// keeps every entry of one identity in that identity's own partition, held weakly by a
/// <see cref="BindingContextPartitionTable"/> keyed by the identity OBJECT (a
/// <see cref="ConditionalWeakTable{TKey, TValue}"/>, or the prompt-reclaim form with the same weak
/// semantics). A partition therefore lives exactly as long as its identity is reachable. Every entry
/// of an exported binding (<see cref="ZeroArgPropertyCacheKey.RunWideEnvironmentIdentity"/>) stays in
/// one strong, run-wide dictionary.
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

    /// <summary>
    /// A store with a partition table of its own; <paramref name="promptReclaim"/> selects the table's
    /// reclamation (<see cref="BindingContextPartitionTable"/>).
    /// </summary>
    internal PartitionedMap(IEqualityComparer<TKey> comparer, Func<TKey, object> partitionOf, bool promptReclaim = false)
        : this(comparer, partitionOf, new BindingContextPartitionTable(storeCount: 1, promptReclaim), store: 0)
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

    /// <summary>TEST SEAM: the values stored under the run-wide identity (an exported binding's entries).</summary>
    internal IReadOnlyCollection<TValue> RunWideValues => _runWide.Values;

    /// <summary>TEST SEAM: the entry capacity of a prompt-reclaim partition table (0 for the other form).</summary>
    internal int PromptTableCapacity => _partitions.PromptCapacity;

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

    /// <summary>
    /// A set with a partition table of its own; <paramref name="promptReclaim"/> selects the table's
    /// reclamation (<see cref="BindingContextPartitionTable"/>).
    /// </summary>
    internal PartitionedSet(IEqualityComparer<TKey> comparer, Func<TKey, object> partitionOf, bool promptReclaim = false)
        => _entries = new PartitionedMap<TKey, bool>(comparer, partitionOf, promptReclaim);

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

    /// <summary>TEST SEAM: see <see cref="PartitionedMap{TKey, TValue}.PromptTableCapacity"/>.</summary>
    internal int PromptTableCapacity => _entries.PromptTableCapacity;
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
/// <para><b>Prompt reclamation</b> (<c>promptReclaim</c>). A <see cref="ConditionalWeakTable{TKey, TValue}"/>
/// replaces its container whenever it fills, and each replaced container is a FINALIZABLE object that
/// frees its dead entries' handles only in its second finalization — so in a loop that mints one
/// identity per step, the dead entries wait for full collections and peak memory grows by about 40
/// bytes per step until one happens (measured on the alias cells, November 2026: 54 MB at 10⁵ steps,
/// 90 MB at 10⁶ and 177 MB at 3·10⁶, against a flat 49 MB). The prompt form holds the
/// same weak association in ONE table of its own (<see cref="EphemeronSlots"/>): the same
/// dependent-handle (ephemeron) semantics — a partition is reachable only while its identity is, even
/// when the partition refers back to the identity — with dead entries freed, in place and at once, when
/// the table fills. Which entry a key finds is the same in both forms. Its users: the zero-argument
/// property cache's published entries and statistics key sets (property-cache prompt reclaim,
/// 2026-11-17; a local-only property per loop step measured 61.5 / 109 / 214 MiB peak in Release at
/// 10⁵ / 10⁶ / 3·10⁶ steps with the other form), the deconstruction shared-bind memo and the statistics
/// key set of an uncached run (deconstruction-memo prompt reclaim, 2026-11-18; a local-only
/// deconstruction per loop step measured 63.6 / 101.3 / 156.3 MiB with the other form), the
/// runtime-alias binding cells (ALIAS-CELL-LIFETIME), the per-site callee memos and the observed
/// plan-formation witness. No library store uses the <see cref="ConditionalWeakTable{TKey, TValue}"/>
/// form any more; it remains the stores' default, which the store-level tests exercise.</para>
/// </summary>
internal sealed class BindingContextPartitionTable
{
    private readonly ConditionalWeakTable<object, object?[]>? _partitions;
    private readonly EphemeronSlots? _prompt;

    internal BindingContextPartitionTable(int storeCount, bool promptReclaim = false)
    {
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(storeCount);
        StoreCount = storeCount;
        if (promptReclaim)
            _prompt = new EphemeronSlots();
        else
            _partitions = new ConditionalWeakTable<object, object?[]>();
    }

    /// <summary>Number of stores sharing the table (slots per identity).</summary>
    internal int StoreCount { get; }

    /// <summary>The slots of <paramref name="identity"/>, or null when no store has added under it.</summary>
    internal object?[]? Find(object identity)
        => _prompt is { } prompt
            ? prompt.Find(identity)
            : _partitions!.TryGetValue(identity, out var slots) ? slots : null;

    /// <summary>The slots of <paramref name="identity"/>, created on its first addition by any store.</summary>
    internal object?[] GetOrCreate(object identity)
    {
        if (_prompt is { } prompt)
            return prompt.Find(identity) ?? prompt.Add(identity, new object?[StoreCount]);

        if (!_partitions!.TryGetValue(identity, out var slots))
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
        if (_prompt is { } prompt)
            return prompt.LiveCount(store);

        var count = 0;
        foreach (var (_, slots) in (IEnumerable<KeyValuePair<object, object?[]>>)_partitions!)
        {
            if (slots[store] is not null)
                count++;
        }

        return count;
    }

    /// <summary>TEST SEAM: the entry capacity of the prompt-reclaim table (0 for the other form).</summary>
    internal int PromptCapacity => _prompt?.Capacity ?? 0;

    /// <summary>
    /// TEST SEAM (null in production): called before each array the prompt-reclaim table's reclamation
    /// allocates — it allocates only when it doubles the table —, with which array it is, so a test can fail
    /// that allocation (throw an <see cref="OutOfMemoryException"/>) and check that the table is left exactly
    /// as it was. Only the prompt-reclaim form has the hook.
    /// </summary>
    internal Action<ReclaimAllocation>? PromptReclaimAllocationTestHook
    {
        get => _prompt?.AllocationTestHook;
        set => (_prompt ?? throw new InvalidOperationException("Only a prompt-reclaim table reclaims in place."))
            .AllocationTestHook = value;
    }

    /// <summary>The arrays a reclamation that doubles the prompt-reclaim table allocates (<see cref="PromptReclaimAllocationTestHook"/>).</summary>
    internal enum ReclaimAllocation
    {
        /// <summary>The doubled entry array.</summary>
        Entries,

        /// <summary>The doubled bucket array.</summary>
        Buckets,
    }

    /// <summary>
    /// The PROMPT-RECLAIM weak association identity OBJECT → slots: a chained hash table of
    /// <see cref="DependentHandle"/>s (ephemerons — the slots are reachable through the table only
    /// while their identity is reachable, even when they refer back to it), hashed and compared by
    /// reference. Entries fill a dense prefix; when it is full, every entry whose identity is gone is
    /// disposed and the rest are compacted in place, and the table doubles only when more than half of
    /// it is still alive. So the table holds at most the identities that were alive at the last
    /// reclamation plus those minted since, and nothing waits for a finalizer except the handles a
    /// run still owns when its table becomes unreachable (the one finalizer below).
    /// <para>Sequential, like the stores that use it, and lock-free: the caller serializes access. The
    /// alias cell store, the callee memos and the plan witness do so with their locks (internal test
    /// seams read them from other threads while a run is suspended); the property cache, the
    /// deconstruction shared-bind memo and the uncached statistics set by the run's ONE evaluation flow,
    /// with no lock — no operation here awaits, calls back into evaluation or runs user
    /// code, so the operations of one run never overlap, and an async continuation that moves the flow
    /// to another thread starts only after the previous operation returned (the await hand-off publishes
    /// its writes). A lookup reads a dependent only after matching the target to the identity the caller
    /// holds for the whole lookup; <see cref="Reclaim"/> disposes a handle only once its target is gone,
    /// which no live key can name, and moves only the entries, never a partition a caller holds. The
    /// garbage collector clears a dead entry's target and dependent concurrently in either form; the one
    /// finalizer runs only once the table itself is unreachable, and every operation keeps the table
    /// alive until its last handle access. A DEBUG build checks the sequential premise: an operation that
    /// begins while another is still running throws instead of racing a reclamation.</para>
    /// <para><b>Failure atomicity.</b> If either array allocation in <see cref="Reclaim"/> fails, the
    /// entries, handles and bucket chains retain their original layout. If the subsequent handle allocation
    /// in <see cref="Add"/> fails, the table retains the completed reclamation. In either case the attempted
    /// addition publishes nothing, all live associations remain reachable, and a later addition can retry.</para>
    /// </summary>
    private sealed class EphemeronSlots
    {
        private const int InitialCapacity = 8;

        private struct Entry
        {
            internal DependentHandle Handle;
            internal int HashCode;
            internal int Next; // the next entry of the bucket, as its position plus one; 0 ends the chain
        }

        private int[] _buckets = new int[InitialCapacity]; // an entry's position plus one; 0 is an empty bucket
        private Entry[] _entries = new Entry[InitialCapacity];
        private int _used;
        private int _operating; // 1 while an operation runs; touched only by DEBUG builds (the sequential tripwire)

        // TEST SEAM (null in production): see BindingContextPartitionTable.PromptReclaimAllocationTestHook.
        internal Action<ReclaimAllocation>? AllocationTestHook;

        ~EphemeronSlots()
        {
            var entries = _entries;
            for (var index = 0; index < _used; index++)
                entries[index].Handle.Dispose();
        }

        internal int Capacity => _entries.Length;

        internal object?[]? Find(object identity)
        {
            EnterOperation();
            var hashCode = RuntimeHelpers.GetHashCode(identity);
            for (var index = _buckets[hashCode & (_buckets.Length - 1)]; index != 0; index = _entries[index - 1].Next)
            {
                ref var entry = ref _entries[index - 1];
                if (entry.HashCode != hashCode || !ReferenceEquals(entry.Handle.Target, identity))
                    continue;

                // The caller holds the identity, so its dependent is alive.
                var slots = (object?[]?)entry.Handle.Dependent;
                GC.KeepAlive(identity);
                // The array entry alone does not root its finalizable owner. Keep that owner
                // alive until the native handle has been read, even on the store's last use.
                GC.KeepAlive(this);
                LeaveOperation();
                return slots;
            }

            GC.KeepAlive(this);
            LeaveOperation();
            return null;
        }

        /// <summary>Adds the slots of an identity the table does not hold (the caller looked it up).</summary>
        internal object?[] Add(object identity, object?[] slots)
        {
            EnterOperation();
            // A failed allocation preserves all live associations. Release the tripwire on the way out.
            // In a release build the finally is empty, and the optimizing JIT
            // removes it: the tier-1 code of this method has no exception-handling region.
            try
            {
                if (_used == _entries.Length)
                    Reclaim();

                var hashCode = RuntimeHelpers.GetHashCode(identity);
                ref var entry = ref _entries[_used];
                // The handle is allocated before the entry changes.
                entry.Handle = new DependentHandle(identity, slots);
                entry.HashCode = hashCode;
                var bucket = hashCode & (_buckets.Length - 1);
                entry.Next = _buckets[bucket];
                _buckets[bucket] = ++_used;
                GC.KeepAlive(this);
                return slots;
            }
            finally
            {
                LeaveOperation();
            }
        }

        internal int LiveCount(int store)
        {
            EnterOperation();
            var count = 0;
            for (var index = 0; index < _used; index++)
            {
                var (identity, slots) = _entries[index].Handle.TargetAndDependent;
                if (identity is not null && ((object?[])slots!)[store] is not null)
                    count++;
                GC.KeepAlive(identity);
            }

            GC.KeepAlive(this);
            LeaveOperation();
            return count;
        }

        // THE SEQUENTIAL TRIPWIRE (DEBUG builds; the calls are compiled out of release builds): an
        // operation that begins while another one is still running throws, so a caller that breaks the
        // serialization above fails loudly in the test suites instead of racing a reclamation. The
        // rejected operation touched nothing and releases nothing. Add, the one operation that can fail,
        // releases the tripwire when it fails too: a failed allocation leaves the table usable.
        [Conditional("DEBUG")]
        private void EnterOperation()
        {
            if (Interlocked.Exchange(ref _operating, 1) != 0)
                throw new InvalidOperationException(
                    "Two operations used one prompt-reclaim partition table at once; its users must serialize access.");
        }

        [Conditional("DEBUG")]
        private void LeaveOperation() => Volatile.Write(ref _operating, 0);

        // The table is full: free the entries whose identity is gone, compact the rest to the front
        // and relink the buckets; double the table only when more than half of it is still alive.
        // FAILURE-ATOMIC: the doubled arrays — the only allocations — exist before anything changes,
        // so a failed allocation leaves the entries, their handles and the bucket chains as they were.
        // (Compacting first and doubling after, as this did until 2026-11-18, left chains that named
        // moved entries when the doubling failed: a later lookup missed an identity the table still
        // held, and its next addition stored a second entry for it.)
        private void Reclaim()
        {
            var entries = _entries;
            var used = _used;

            // Count the entries whose identity is alive, changing nothing. The collector can clear more
            // targets before the compaction below, never revive one, so this bounds what it keeps.
            var alive = 0;
            for (var index = 0; index < used; index++)
            {
                if (entries[index].Handle.Target is not null)
                    alive++;
            }

            var compacted = entries;
            var buckets = _buckets;
            if (alive > entries.Length / 2)
            {
                compacted = AllocateForReclaim<Entry>(entries.Length * 2, ReclaimAllocation.Entries);
                buckets = AllocateForReclaim<int>(entries.Length * 2, ReclaimAllocation.Buckets);
            }

            // Nothing below allocates or throws.
            var doubled = !ReferenceEquals(compacted, entries);
            var live = 0;
            for (var index = 0; index < used; index++)
            {
                if (entries[index].Handle.Target is null)
                {
                    entries[index].Handle.Dispose();
                    continue;
                }

                if (doubled || live != index)
                    compacted[live] = entries[index];
                live++;
            }

            if (!doubled)
            {
                // Every slot past the live prefix holds a freed handle or a moved entry's stale copy.
                Array.Clear(entries, live, used - live);
                Array.Clear(buckets);
            }

            // A doubled table drops the old array whole: its copies of the moved handles are never
            // disposed, and the finalizer reads only the current array.
            var mask = buckets.Length - 1;
            for (var index = 0; index < live; index++)
            {
                var bucket = compacted[index].HashCode & mask;
                compacted[index].Next = buckets[bucket];
                buckets[bucket] = index + 1;
            }

            _entries = compacted;
            _buckets = buckets;
            _used = live;
        }

        private T[] AllocateForReclaim<T>(int length, ReclaimAllocation allocation)
        {
            AllocationTestHook?.Invoke(allocation);
            return new T[length];
        }
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
