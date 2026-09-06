using System.Collections;
using System.Numerics;

namespace KatLang.Optimizations.Loops;

internal interface IValueEnvironmentCacheIdentityProvider
{
    object CacheIdentity { get; }
}

internal enum LoopKind
{
    While,
    Repeat,
}

internal sealed record LoopPlanTemplate(
    LoopKind Kind,
    Algorithm.User Step,
    int StateArity,
    IReadOnlyList<LoopTempPlan> TempPlans,
    IReadOnlyList<LoopExprPlan> NextStateOutputs,
    LoopExprPlan? ContinuationOutput,
    bool RequiresPerIterationCacheIdentity,
    Evaluator.EvalCtx ParentCtx,
    string? DiagnosticKey);

internal readonly record struct PlannedLoopValue(
    Result? Value,
    Decimal128 NumericValue,
    bool HasNumericValue,
    int EmittedCount)
{
    public static PlannedLoopValue FromResult(Result value)
        => FromResult(value, value.ValueCount());

    public static PlannedLoopValue FromResult(Result value, int emittedCount)
        => value.AsNum() is { } number
            ? new PlannedLoopValue(value, number, true, emittedCount)
            : new PlannedLoopValue(value, Decimal128.Zero, false, emittedCount);

    public static PlannedLoopValue FromNumeric(Decimal128 value)
        => new(null, value, true, 1);

    public Result ToResult()
        => Value ?? new Result.Atom(NumericValue);

    public Decimal128? AsNum()
        => HasNumericValue ? NumericValue : Value?.AsNum();
}

internal sealed class LoopValueEnvironment : IReadOnlyList<(string Name, Result Value)>, IValueEnvironmentCacheIdentityProvider
{
    private readonly IReadOnlyList<string> _stateNames;
    private readonly Result[] _stateSlots;
    private readonly IReadOnlyList<(string Name, Result Value)> _parent;
    private object _cacheIdentity = new();

    public LoopValueEnvironment(
        IReadOnlyList<string> stateNames,
        Result[] stateSlots,
        IReadOnlyList<(string Name, Result Value)> parent)
    {
        _stateNames = stateNames;
        _stateSlots = stateSlots;
        _parent = parent;
    }

    public object CacheIdentity => _cacheIdentity;

    public void BeginIteration()
        => _cacheIdentity = new object();

    public int Count => _stateSlots.Length + _parent.Count;

    public (string Name, Result Value) this[int index]
    {
        get
        {
            if ((uint)index < (uint)_stateSlots.Length)
                return (_stateNames[index], _stateSlots[index]);

            return _parent[index - _stateSlots.Length];
        }
    }

    public IEnumerator<(string Name, Result Value)> GetEnumerator()
    {
        for (var i = 0; i < _stateSlots.Length; i++)
            yield return (_stateNames[i], _stateSlots[i]);

        foreach (var item in _parent)
            yield return item;
    }

    IEnumerator IEnumerable.GetEnumerator()
        => GetEnumerator();
}

internal sealed class LoopRunFrame
{
    private readonly Result[] _stateSlots;
    private readonly Result[] _scratchSlots;
    private readonly Result[] _capturedSlots;
    private readonly Evaluator.CountedResult[] _countedParamSlots;
    private readonly PlannedLoopValue[] _tempSlots;
    private readonly bool[] _tempSlotHasValue;
    private Dictionary<int, PlannedLoopValue>? _callTempMemo;
    private int _tempCallDepth;
    private readonly PlannedLoopValue[] _iterationOutputs;
    private readonly LoopValueEnvironment _valueEnvironment;

    public LoopRunFrame(
        LoopPlanTemplate template,
        IReadOnlyList<(string Name, Result Value)> parentValEnv,
        IReadOnlyList<Result> initialStateValues)
    {
        Template = template;
        var parentCtx = template.ParentCtx;
        IterationCtx = parentCtx.Push(template.Step);
        _stateSlots = initialStateValues.ToArray();
        _scratchSlots = new Result[template.StateArity];
        _capturedSlots = parentValEnv.Select(item => item.Value).ToArray();
        _countedParamSlots = parentCtx.CountedParamEnv.Select(item => item.Value).ToArray();
        _tempSlots = new PlannedLoopValue[template.TempPlans.Count];
        _tempSlotHasValue = new bool[template.TempPlans.Count];
        _iterationOutputs = new PlannedLoopValue[
            template.NextStateOutputs.Count + (template.ContinuationOutput is null ? 0 : 1)];
        _valueEnvironment = new LoopValueEnvironment(template.Step.Params, _stateSlots, parentValEnv);
        Diagnostics = parentCtx.LoopDiagnostics;
        Diagnostics?.RecordLoopPlanExecution(template.DiagnosticKey);
    }

    public LoopPlanTemplate Template { get; }

    public Evaluator.EvalCtx IterationCtx { get; }

    public LoopOptimizationDiagnostics? Diagnostics { get; }

    public IReadOnlyList<(string Name, Result Value)> ValueEnvironment => _valueEnvironment;

    public void BeginIteration()
    {
        if (_tempSlotHasValue.Length != 0)
            Array.Clear(_tempSlotHasValue);

        if (Template.RequiresPerIterationCacheIdentity)
            _valueEnvironment.BeginIteration();
    }

    public Result GetStateSlot(int index)
        => _stateSlots[index];

    public Result GetCapturedSlot(int index)
        => _capturedSlots[index];

    public Evaluator.CountedResult GetCountedParamSlot(int index)
        => _countedParamSlots[index];

    public bool TryGetTempSlot(int index, out PlannedLoopValue value)
    {
        if (_tempCallDepth != 0)
        {
            value = default;
            return _callTempMemo is not null && _callTempMemo.TryGetValue(index, out value);
        }

        value = _tempSlots[index];
        return _tempSlotHasValue[index];
    }

    public void SetTempSlot(int index, PlannedLoopValue value)
    {
        if (_tempCallDepth != 0)
        {
            (_callTempMemo ??= [])[index] = value;
            return;
        }

        _tempSlots[index] = value;
        _tempSlotHasValue[index] = true;
    }

    /// <summary>
    /// Suspends the per-iteration temp memo for the duration of a planned temp CALL
    /// (<see cref="LoopExprPlan.TempCall"/>) and returns the state
    /// <see cref="RestoreTempMemo"/> reinstates. A generic user call runs its callee in
    /// FRESH value, counted, and algorithm environments, and the run's zero-argument
    /// property cache is keyed by their identities: a bare temp read inside the callee
    /// therefore neither hits nor populates the caller's entries, and the call's own reads
    /// memoize only among themselves until it returns. Mirroring that exactly is what
    /// keeps the two strategies' depth peaks and string materialization equal for a temp
    /// that reads another temp. Call memos are sparse and allocated only on a bare-temp
    /// miss. Suspension and restoration touch no root slots and take constant time;
    /// neither copies storage proportional to the step's declared property count.
    /// </summary>
    public Dictionary<int, PlannedLoopValue>? SuspendTempMemo()
    {
        var saved = _callTempMemo;
        _callTempMemo = null;
        _tempCallDepth++;
        return saved;
    }

    /// <summary>Reinstates the memo state <see cref="SuspendTempMemo"/> returned.</summary>
    public void RestoreTempMemo(Dictionary<int, PlannedLoopValue>? saved)
    {
        if (_tempCallDepth == 0)
            throw new InvalidOperationException("No suspended temp memo to restore.");

        _callTempMemo = saved;
        _tempCallDepth--;
    }

    public void SetScratchSlot(int index, Result value)
        => _scratchSlots[index] = value;

    /// <summary>
    /// Retains one evaluated iteration output (state outputs first, the while
    /// continuation last) in a REUSABLE per-frame buffer. Normal iterations only ever
    /// write here — struct copies into a preallocated array, no per-iteration
    /// allocation — and the retained values are read back exclusively by
    /// <c>LoopOptimizer.MaterializeGenericHandoverSlots</c> when an actual handover
    /// branch needs the generic output-slot representation (M16). Handover ends the
    /// optimized loop, so one buffer per frame can never be read after being
    /// overwritten by a later iteration.
    /// </summary>
    public void SetIterationOutput(int index, PlannedLoopValue value)
        => _iterationOutputs[index] = value;

    public PlannedLoopValue GetIterationOutput(int index)
        => _iterationOutputs[index];

    public EvalResult<Evaluator.CountedResult> CurrentStateResult()
        => Evaluator.MakeCheckedLoopStateResult(IterationCtx, _stateSlots);

    public EvalResult<Evaluator.CountedResult> ScratchStateResult()
        => Evaluator.MakeCheckedLoopStateResult(IterationCtx, _scratchSlots);

    public bool TryCommitScratchFast()
    {
        if (_scratchSlots.Length == 1)
        {
            // A single scratch slot whose value packs more than one top-level value means the
            // loop's next-state arity grew; bail to the generic path. Detect that from the
            // value's own top-level item count WITHOUT recursively normalizing it. Recursive
            // normalization would collapse useful one-value sequence structure and diverge
            // from the generic evaluator, which carries each one-value state slot verbatim.
            var value = _scratchSlots[0];
            if (value is Result.SequenceValue(var items) && items.Count > 1)
                return false;

            _stateSlots[0] = value;
            return true;
        }

        // Carry each next-state slot verbatim, matching the generic loop, instead of
        // recursively normalizing (which would collapse explicit empty-sequence nesting).
        for (var i = 0; i < _stateSlots.Length; i++)
            _stateSlots[i] = _scratchSlots[i];
        return true;
    }
}
