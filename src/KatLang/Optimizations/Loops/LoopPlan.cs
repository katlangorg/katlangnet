using System.Collections;

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
    decimal NumericValue,
    bool HasNumericValue,
    int EmittedCount)
{
    public static PlannedLoopValue FromResult(Result value)
        => FromResult(value, value.ValueCount());

    public static PlannedLoopValue FromResult(Result value, int emittedCount)
        => value.AsNum() is { } number
            ? new PlannedLoopValue(value, number, true, emittedCount)
            : new PlannedLoopValue(value, 0m, false, emittedCount);

    public static PlannedLoopValue FromNumeric(decimal value)
        => new(null, value, true, 1);

    public Result ToResult()
        => Value ?? new Result.Atom(NumericValue);

    public decimal? AsNum()
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
        value = _tempSlots[index];
        return _tempSlotHasValue[index];
    }

    public void SetTempSlot(int index, PlannedLoopValue value)
    {
        _tempSlots[index] = value;
        _tempSlotHasValue[index] = true;
    }

    public void SetScratchSlot(int index, Result value)
        => _scratchSlots[index] = value;

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
