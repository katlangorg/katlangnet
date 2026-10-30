using System.Runtime.ExceptionServices;

namespace KatLang;

internal enum StaticQueryStepKind : byte
{
    None,
    Value,
    Follow,
}

/// <summary>An ordinary value equation, or a conclusive single-successor reference equation.</summary>
internal readonly record struct StaticQueryStep<TValue>(StaticQueryStepKind Kind, TValue Value);

internal static class StaticQueryStep
{
    public static StaticQueryStep<TValue> Complete<TValue>(TValue value) => new(StaticQueryStepKind.Value, value);

    internal static StaticQueryStep<TValue> Follow<TValue>() => new(StaticQueryStepKind.Follow, default!);
}

/// <summary>
/// Pure, monotone equations over a pointed information order. Read observes a lower bound, not a final answer.
/// Complete must refine earlier answers. Follow declares the entire equation's definite reference successor:
/// it must never be withdrawn or rewired when ordinary inputs refine. Unknown alternatives use ordinary reads
/// and branch agreement until a successor is certain. PathCycleValue is the shared OD-D refusal fact; consumers
/// interpret that verdict at the queried body's identity. See the B3 design, section 3 (IR-04).
/// </summary>
internal interface IStaticQueryDefinition<TKey, TValue>
    where TKey : notnull
{
    StaticQueryStep<TValue> Compute(TKey key, StaticQueryReader<TKey, TValue> reader);

    TValue Initial(TKey key);

    /// <summary>
    /// A costly closed observer may wait until ordinary work is quiescent. Both queues remain FIFO;
    /// an observer can unlock ordinary work, which settles before the next observer. This changes
    /// scheduling only, never the information order, initial facts or reference equations.
    /// </summary>
    bool IsClosureObserver(TKey key) => false;

    TValue PathCycleValue { get; }

    bool ValueEquals(TValue left, TValue right);

    bool IsRefinement(TValue before, TValue after);
}

/// <summary>One computation's ordinary lower-bound reads and conclusive path equation.</summary>
internal sealed class StaticQueryReader<TKey, TValue>(StaticQueryEngine<TKey, TValue> engine)
    where TKey : notnull
{
    public TValue Read(TKey key) => engine.Read(key);

    public StaticQueryStep<TValue> Follow(TKey key) => engine.Follow(key);

    /// <summary>Charges bounded callback graph work/storage to this operation, retaining sticky failure semantics.</summary>
    internal void ChargeAuxiliary(int liveEntries) => engine.ChargeAuxiliary(liveEntries);
}

/// <summary>
/// Cumulative operation bounds. Production consumers must supply finite, operation-scaled work/read/entry limits.
/// MaxRefinements bounds strict changes of any one value, including a domain of unbounded height.
/// </summary>
internal sealed record StaticQueryLimits(
    long MaxEvaluations,
    int MaxRefinements,
    int MaxEntries = int.MaxValue,
    long MaxReads = long.MaxValue,
    long MaxStorageUnits = long.MaxValue)
{
    public static StaticQueryLimits Default { get; } = new(long.MaxValue, 64);
}

internal readonly record struct StaticQueryStatistics(
    long Evaluations, long Computations, long Reads, long ValueChanges,
    long PathEdges, long PathCycles, int MaxPending, int Entries, long Dependencies,
    long AuxiliaryWork = 0, int AuxiliaryPeakEntries = 0, long AdapterWork = 0,
    long StorageUnits = 0, long PeakStorageUnits = 0, long MetadataUnits = 0);

internal sealed class StaticQueryLimitExceededException(string message) : Exception(message);

/// <summary>
/// A demand-driven monotone worklist and a separate graph of confirmed reference steps. Only the latter participates
/// in OD-D cycle detection. Its edges are stable and have outdegree at most one, so disjoint-set union detects a new
/// cycle exactly when an edge joins vertices already in the same weak component. Ordinary dependency SCCs receive
/// no cycle seed: they converge from Initial. Every refinement notifies all current ordinary readers and path
/// predecessors. Newly reached keys become final together at quiescence, never at a head-local decision.
/// No host recursion, provisional cache, chase ancestry, invalidation log or restart-from-bottom mechanism.
/// Not thread-safe. A failed or cancelled operation faults the engine permanently.
/// </summary>
internal sealed class StaticQueryEngine<TKey, TValue>
    where TKey : notnull
{
    private readonly IStaticQueryDefinition<TKey, TValue> _definition;
    private readonly StaticQueryLimits _limits;
    private readonly CancellationToken _cancellationToken;
    private readonly TValue _pathCycleValue;
    private readonly Dictionary<TKey, Entry> _entries;
    private readonly Queue<Entry> _pending = [];
    private readonly Queue<Entry> _observerPending = [];
    private readonly List<Entry> _newEntries = [];
    private readonly HashSet<Entry> _readsThisRun = [];
    private readonly StaticQueryReader<TKey, TValue> _reader;
    private Entry? _running;
    private Entry? _followThisRun;
    private bool _solving;
    private bool _initializing;
    private bool _faulted;
    private ExceptionDispatchInfo? _readerFailure;
    private long _evaluations;
    private long _computations;
    private long _reads;
    private long _valueChanges;
    private long _pathEdges;
    private long _pathCycles;
    private long _dependencies;
    private int _maxPending;
    private long _auxiliaryWork;
    private int _auxiliaryPeakEntries;
    private int _readBufferReservation;
    internal StaticQueryResourceBudget Resources { get; }

    public StaticQueryEngine(
        IStaticQueryDefinition<TKey, TValue> definition, IEqualityComparer<TKey>? comparer = null, StaticQueryLimits? limits = null,
        CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(definition);
        _definition = definition;
        _limits = limits ?? StaticQueryLimits.Default;
        ArgumentOutOfRangeException.ThrowIfNegative(_limits.MaxEvaluations);
        ArgumentOutOfRangeException.ThrowIfNegative(_limits.MaxRefinements);
        ArgumentOutOfRangeException.ThrowIfNegative(_limits.MaxEntries);
        ArgumentOutOfRangeException.ThrowIfNegative(_limits.MaxReads);
        ArgumentOutOfRangeException.ThrowIfNegative(_limits.MaxStorageUnits);
        Resources = new(_limits);
        _cancellationToken = cancellationToken;
        _pathCycleValue = definition.PathCycleValue;
        _entries = new Dictionary<TKey, Entry>(comparer);
        _reader = new StaticQueryReader<TKey, TValue>(this);
    }

    public StaticQueryStatistics Statistics
        => new(_evaluations, _computations, _reads, _valueChanges, _pathEdges, _pathCycles, _maxPending, _entries.Count, _dependencies,
            _auxiliaryWork, _auxiliaryPeakEntries, Resources.AdapterWork, Resources.StorageUnits, Resources.PeakStorageUnits, Resources.MetadataUnits);

    public TValue Get(TKey key)
    {
        EnsureUsable();
        _solving = true;
        try
        {
            _cancellationToken.ThrowIfCancellationRequested();
            var entry = EntryOf(key);
            while (_pending.TryDequeue(out var next) || _observerPending.TryDequeue(out next))
            {
                _cancellationToken.ThrowIfCancellationRequested();
                Resources.Work(cancellationToken: _cancellationToken);
                _evaluations++;
                var dirty = next.Dirty;
                next.Dirty = Dirty.None;
                next.Queued = false;
                if ((dirty & Dirty.Compute) != 0)
                    Compute(next);
                else if (next.Followed is { } target)
                    Publish(next, target.Value);
            }

            foreach (var completed in _newEntries)
            {
                _cancellationToken.ThrowIfCancellationRequested();
                if (completed.Kind == StaticQueryStepKind.None)
                    throw new InvalidOperationException("A static query reached quiescence without an equation.");
                completed.Final = true;
            }
            _newEntries.Clear();
            return entry.Value;
        }
        catch
        {
            _faulted = true;
            Resources.Fail();
            throw;
        }
        finally
        {
            _solving = false;
        }
    }

    /// <summary>Observes an already final fact without computing anything.</summary>
    public bool TryGetFinal(TKey key, out TValue value)
    {
        EnsureUsable();
        if (_entries.TryGetValue(key, out var entry) && entry.Final)
        {
            value = entry.Value;
            return true;
        }
        value = default!;
        return false;
    }

    /// <summary>
    /// Copies quiescent facts for a later, independent operation. The copy contains no reader, queue, cancellation
    /// token or engine reference. A failed solve can never export its partially computed entries.
    /// </summary>
    internal IEnumerable<KeyValuePair<TKey, TValue>> EnumerateFinalValues(CancellationToken cancellationToken = default)
    {
        EnsureUsable();
        foreach (var (key, entry) in _entries)
        {
            cancellationToken.ThrowIfCancellationRequested();
            if (entry.Final) yield return new(key, entry.Value);
        }
    }

    internal TValue Read(TKey key)
    {
        try
        {
            var source = ReaderSource();
            CountRead();
            var target = EntryOf(key);
            if (!_readsThisRun.Contains(target))
            {
                if (_readsThisRun.Count >= _readBufferReservation)
                {
                    Resources.Reserve(2, _cancellationToken);
                    _readBufferReservation++;
                }
                Resources.Reserve(2, _cancellationToken);
                _readsThisRun.Add(target);
                var dependency = new Dependency(source, target, source.Dependencies, target.Readers);
                if (target.Readers is { } first)
                    first.PreviousReader = dependency;
                source.Dependencies = dependency;
                target.Readers = dependency;
                _dependencies++;
            }
            return target.Value;
        }
        catch (Exception error)
        {
            RememberReaderFailure(error);
            throw;
        }
    }

    internal StaticQueryStep<TValue> Follow(TKey key)
    {
        try
        {
            ReaderSource();
            CountRead();
            if (_followThisRun is not null)
                throw new InvalidOperationException("A static query can declare only one path successor per computation.");
            _followThisRun = EntryOf(key);
            return StaticQueryStep.Follow<TValue>();
        }
        catch (Exception error)
        {
            RememberReaderFailure(error);
            throw;
        }
    }

    // A definition cannot turn a failed read (especially a reached bound) into Unknown or a successful equation.
    private void RememberReaderFailure(Exception error)
    {
        if (_solving)
            _readerFailure ??= ExceptionDispatchInfo.Capture(error);
    }

    private Entry ReaderSource()
    {
        _readerFailure?.Throw();
        _cancellationToken.ThrowIfCancellationRequested();
        return !_initializing && _running is { } source
            ? source
            : throw new InvalidOperationException("A static query reader was used outside its query's computation.");
    }

    private void CountRead()
    {
        if (_reads >= _limits.MaxReads)
            throw new StaticQueryLimitExceededException($"The static queries exceeded their read bound ({_limits.MaxReads}).");
        _reads++;
    }

    internal void ChargeAuxiliary(int liveEntries)
    {
        try
        {
            ReaderSource();
            if (liveEntries < 0 || liveEntries > _limits.MaxEntries - _entries.Count)
                throw new StaticQueryLimitExceededException($"The static query callback graph exceeded its entry bound ({_limits.MaxEntries}).");
            Resources.Work(cancellationToken: _cancellationToken);
            Resources.ObserveCallback(16L * liveEntries, _cancellationToken);
            _auxiliaryWork++;
            _auxiliaryPeakEntries = Math.Max(_auxiliaryPeakEntries, liveEntries);
        }
        catch (Exception error)
        {
            RememberReaderFailure(error);
            throw;
        }
    }

    internal void EnsureUsable()
    {
        if (_solving)
            throw new InvalidOperationException("A static query may read other queries only through its reader.");
        if (_faulted)
            throw new InvalidOperationException("The static query engine is faulted: a computation failed, cancelled, or exceeded a bound.");
        Resources.EnsureUsable();
    }

    private Entry EntryOf(TKey key)
    {
        if (_entries.TryGetValue(key, out var known))
            return known;
        if (_entries.Count >= _limits.MaxEntries)
            throw new StaticQueryLimitExceededException($"The static queries exceeded their entry bound ({_limits.MaxEntries}).");
        Resources.Reserve(4, _cancellationToken);
        TValue initial;
        _initializing = true;
        try { initial = _definition.Initial(key); }
        finally { _initializing = false; }
        _cancellationToken.ThrowIfCancellationRequested();
        var entry = new Entry(key, initial);
        entry.InitializeComponent();
        _entries.Add(key, entry);
        _newEntries.Add(entry);
        Schedule(entry, Dirty.Compute);
        return entry;
    }

    private void Schedule(Entry entry, Dirty reason)
    {
        if (entry.Final)
            throw new InvalidOperationException("A finalized static query acquired a changed dependency.");
        entry.Dirty |= reason;
        if (entry.Queued)
            return;
        entry.Queued = true;
        (_definition.IsClosureObserver(entry.Key) ? _observerPending : _pending).Enqueue(entry);
        _maxPending = Math.Max(_maxPending, _pending.Count + _observerPending.Count);
    }

    private void Compute(Entry entry)
    {
        Unsubscribe(entry);
        _readsThisRun.Clear();
        _followThisRun = null;
        _running = entry;
        _computations++;
        StaticQueryStep<TValue> step;
        try { step = _definition.Compute(entry.Key, _reader); }
        finally { _running = null; Resources.EndCallback(); }
        _readerFailure?.Throw();
        _cancellationToken.ThrowIfCancellationRequested();
        switch (step.Kind)
        {
            case StaticQueryStepKind.Value:
                if (_followThisRun is not null || entry.Followed is not null)
                    throw new InvalidOperationException("A declared static path successor cannot be discarded or withdrawn.");
                entry.Kind = step.Kind;
                Publish(entry, step.Value);
                break;
            case StaticQueryStepKind.Follow:
                if (_followThisRun is not { } target)
                    throw new InvalidOperationException("A path equation must declare its successor through the reader.");
                entry.Kind = step.Kind;
                ConnectPath(entry, target);
                Publish(entry, target.Value);
                break;
            default:
                throw new InvalidOperationException("A static query returned no equation.");
        }
    }

    private void Publish(Entry entry, TValue value)
    {
        _cancellationToken.ThrowIfCancellationRequested();
        if (_definition.ValueEquals(entry.Value, value))
            return;
        if (entry.Final)
            throw new InvalidOperationException("A finalized static query changed its value.");
        if (!_definition.IsRefinement(entry.Value, value))
        {
            var error = new InvalidOperationException("A static query produced a value that is not an information refinement.");
            error.Data["QueryKey"] = entry.Key;
            error.Data["Before"] = entry.Value;
            error.Data["After"] = value;
            throw error;
        }
        if (entry.Refinements >= _limits.MaxRefinements)
            throw new StaticQueryLimitExceededException($"A static query exceeded its refinement bound ({_limits.MaxRefinements}).");
        _cancellationToken.ThrowIfCancellationRequested();
        entry.Value = value;
        entry.Refinements++;
        _valueChanges++;
        for (var dependency = entry.Readers; dependency is not null; dependency = dependency.NextReader)
        {
            _cancellationToken.ThrowIfCancellationRequested();
            Schedule(dependency.Source, Dirty.Compute);
        }
        for (var follower = entry.FirstFollower; follower is not null; follower = follower.NextFollower)
        {
            _cancellationToken.ThrowIfCancellationRequested();
            Schedule(follower, Dirty.Propagate);
        }
    }

    private void Unsubscribe(Entry source)
    {
        for (var dependency = source.Dependencies; dependency is not null; dependency = dependency.NextDependency)
        {
            _cancellationToken.ThrowIfCancellationRequested();
            if (dependency.PreviousReader is { } previous)
                previous.NextReader = dependency.NextReader;
            else
                dependency.Target.Readers = dependency.NextReader;
            if (dependency.NextReader is { } next)
                next.PreviousReader = dependency.PreviousReader;
            _dependencies--;
            Resources.Release(2);
        }
        source.Dependencies = null;
    }

    private void ConnectPath(Entry source, Entry target)
    {
        if (source.Followed is { } previous)
        {
            if (!ReferenceEquals(previous, target))
                throw new InvalidOperationException("A confirmed static path successor cannot be rewired.");
            return;
        }
        source.Followed = target;
        source.NextFollower = target.FirstFollower;
        target.FirstFollower = source;
        _pathEdges++;
        var from = ComponentOf(source);
        var to = ComponentOf(target);
        if (from.Cyclic)
            throw new InvalidOperationException("A closed path component unexpectedly had an unconnected source.");
        if (ReferenceEquals(from, to))
        {
            from.Cyclic = true;
            _pathCycles++;
            RefuseComponent(from.Head, from.Tail);
            return;
        }

        // Only the formerly open component needs a refusal when it joins an already cyclic one.
        var newlyCyclicHead = from.Head;
        var newlyCyclicTail = from.Tail;
        var becomesCyclic = to.Cyclic;
        if (from.Size < to.Size)
            (from, to) = (to, from);
        to.Parent = from;
        from.Size += to.Size;
        from.Tail.NextMember = to.Head;
        from.Tail = to.Tail;
        from.Cyclic |= to.Cyclic;
        if (becomesCyclic)
            RefuseComponent(newlyCyclicHead, newlyCyclicTail);
    }

    private Entry ComponentOf(Entry entry)
    {
        while (!ReferenceEquals(entry.Parent, entry))
        {
            _cancellationToken.ThrowIfCancellationRequested();
            entry.Parent = entry.Parent.Parent;
            entry = entry.Parent;
        }
        return entry;
    }

    private void RefuseComponent(Entry head, Entry tail)
    {
        for (var member = head; ; member = member.NextMember!)
        {
            _cancellationToken.ThrowIfCancellationRequested();
            if (member.Followed is null)
                throw new InvalidOperationException("A cyclic reference component contains an unconfirmed path.");
            Publish(member, _pathCycleValue);
            if (ReferenceEquals(member, tail))
                return;
        }
    }

    [Flags]
    private enum Dirty : byte { None = 0, Compute = 1, Propagate = 2 }

    private sealed class Entry(TKey key, TValue value)
    {
        public TKey Key { get; } = key;
        public TValue Value = value;
        public int Refinements;
        public StaticQueryStepKind Kind;
        public bool Final;
        public bool Queued;
        public Dirty Dirty;
        public Dependency? Dependencies;
        public Dependency? Readers;
        public Entry? Followed;
        public Entry? FirstFollower;
        public Entry? NextFollower;
        public Entry Parent = null!;
        public Entry Head = null!;
        public Entry Tail = null!;
        public Entry? NextMember;
        public int Size = 1;
        public bool Cyclic;

        public void InitializeComponent() => Parent = Head = Tail = this;
    }

    // One live ordinary edge, linked by source and doubly linked by target. No per-entry hash tables.
    private sealed class Dependency(Entry source, Entry target, Dependency? nextDependency, Dependency? nextReader)
    {
        public Entry Source { get; } = source;
        public Entry Target { get; } = target;
        public Dependency? NextDependency { get; } = nextDependency;
        public Dependency? PreviousReader;
        public Dependency? NextReader = nextReader;
    }
}
