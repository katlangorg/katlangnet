namespace KatLang;

/// <summary>
/// Numeric operation ledger shared by the engine and its adapters. It retains no engine, syntax,
/// callback, exception or token. Storage units are conservative 64-byte bookkeeping slots, not
/// a claim about total process bytes; source/runtime/editor allocations retain their own policies.
/// </summary>
internal sealed class StaticQueryResourceBudget(StaticQueryLimits limits)
{
    private long _work;
    private long _persistent;
    private long _temporary;
    private long _callback;
    internal long AdapterWork { get; private set; }
    internal long MetadataUnits { get; private set; }
    internal long PeakStorageUnits { get; private set; }
    internal long StorageUnits => _persistent + _temporary + _callback;
    internal bool IsFailed { get; private set; }

    internal void EnsureUsable()
    {
        if (IsFailed) throw new InvalidOperationException("The static operation's resource ledger is failed.");
    }

    internal void Fail() => IsFailed = true;

    private void Check(CancellationToken cancellationToken)
    {
        EnsureUsable();
        try { cancellationToken.ThrowIfCancellationRequested(); }
        catch { Fail(); throw; }
    }

    private void CheckWork(long count)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(count);
        if (count <= limits.MaxEvaluations - _work) return;
        Fail();
        throw new StaticQueryLimitExceededException($"The static operation exceeded its work bound ({limits.MaxEvaluations}).");
    }

    private void CheckStorage(long units)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(units);
        if (units <= limits.MaxStorageUnits - _persistent - _temporary - _callback) return;
        Fail();
        throw new StaticQueryLimitExceededException($"The static operation exceeded its metadata storage bound ({limits.MaxStorageUnits} slots).");
    }

    internal void Work(long count = 1, CancellationToken cancellationToken = default)
    {
        Check(cancellationToken);
        CheckWork(count);
        _work += count;
    }

    internal void Metadata(long units, long work = 1, CancellationToken cancellationToken = default)
    {
        Check(cancellationToken);
        CheckWork(work);
        CheckStorage(units);
        _work += work;
        AdapterWork += work;
        _persistent += units;
        MetadataUnits += units;
        PeakStorageUnits = Math.Max(PeakStorageUnits, StorageUnits);
    }

    internal void Reserve(long units, CancellationToken cancellationToken = default)
    {
        Check(cancellationToken);
        CheckStorage(units);
        _persistent += units;
        PeakStorageUnits = Math.Max(PeakStorageUnits, StorageUnits);
    }

    internal void Release(long units) => _persistent -= units;

    internal void ObserveCallback(long units, CancellationToken cancellationToken = default)
    {
        Check(cancellationToken);
        // One callback runs at a time; its current graph coexists with persistent metadata and leases.
        if (units > _callback) CheckStorage(units - _callback);
        _callback = units;
        PeakStorageUnits = Math.Max(PeakStorageUnits, StorageUnits);
    }

    internal void EndCallback() => _callback = 0;

    internal Lease Temporary() => new(this);

    internal sealed class Lease(StaticQueryResourceBudget budget) : IDisposable
    {
        private long _units;
        public void Add(long units, CancellationToken cancellationToken = default)
        {
            budget.Check(cancellationToken);
            budget.CheckStorage(units);
            budget._temporary += units;
            _units += units;
            budget.PeakStorageUnits = Math.Max(budget.PeakStorageUnits, budget.StorageUnits);
        }
        public void Dispose()
        {
            budget._temporary -= _units;
            _units = 0;
        }
    }
}
