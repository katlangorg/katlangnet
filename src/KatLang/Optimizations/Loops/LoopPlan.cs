using KatLang.Evaluation;
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

/// <summary>
/// A planned loop, built once per loop invocation (<c>LoopOptimizer.TryBuildLoopPlanTemplate</c>).
/// <para><see cref="AdmittedHead"/> is the step's ADMITTED head: one snapshot of its caller-owned
/// top-level parameter patterns, taken when the plan is built. It holds one plain fixed capture per
/// state slot, with distinct names (<see cref="StateNames"/>). Everything that binds the state reads
/// this snapshot, never the step's live head: the compiled plans, every iteration's binding context
/// and activated head scope, the pending initial-state reads, and a handover's generic continuation.
/// The generic route likewise binds the snapshot it prepares once per loop invocation
/// (<c>Evaluator.PrepareGenericLoopStep</c>). A host that rewrites the step's head during the loop
/// therefore changes neither route.</para>
/// </summary>
internal sealed record LoopPlanTemplate(
    LoopKind Kind,
    Algorithm.User Step,
    IReadOnlyList<ParameterPattern> AdmittedHead,
    IReadOnlyList<string> StateNames,
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

    /// <summary>
    /// The boxed form of this value. An unboxed numeric value has no <see cref="Result"/> yet, so each
    /// call allocates a new atom. Code that hands on one value several times must box it once
    /// (<see cref="WithResult"/>).
    /// </summary>
    public Result ToResult()
        => Value ?? new Result.Atom(NumericValue);

    /// <summary>
    /// This value with its <see cref="Result"/> boxed once, keeping the unboxed numeric view for the
    /// numeric fast paths. Every <see cref="ToResult"/> of the copy then returns that one object.
    /// </summary>
    public PlannedLoopValue WithResult()
        => Value is null ? this with { Value = new Result.Atom(NumericValue) } : this;

    public Decimal128? AsNum()
        => HasNumericValue ? NumericValue : Value?.AsNum();

    /// <summary>
    /// The Boolean view (<see cref="Result.AsBool"/>): the unboxed numeric representation
    /// never holds a Boolean, so only a boxed <see cref="Result.Bool"/> qualifies.
    /// </summary>
    public bool? AsBool()
        => HasNumericValue ? null : Value?.AsBool();
}

/// <summary>
/// The value environment a planned loop's generic fallbacks read (<see cref="LoopRunFrame.ValueEnvironment"/>):
/// exactly the bindings of the environment the loop was entered with, in their order, under a cache identity of
/// its own that <see cref="BeginIteration"/> refreshes each round of a partially planned loop. It holds no state:
/// the frame binds the state through the need tier (<c>Evaluator.LoopNeedBindingContext</c>).
/// <para><b>A view never wraps a view.</b> A loop that a planned step's own body starts again, which is recursion
/// routed through loop steps (<c>F(n) = repeat(F(n), 1)</c>), builds one frame per level over the previous frame's
/// environment, and such recursion charges no depth (<see cref="EvaluationLimits.MaxDepth"/>). When each view
/// wrapped its parent, the views formed a chain with one link per level. Counting, indexing or enumerating it
/// recursed through every link in frames that no stack probe guards, and every frame enumerated it once, for its
/// captured slots. On a large thread the chain's recursion outgrew the backstop's fixed reserve, and the process
/// died of a stack overflow instead of stopping with <see cref="EvalError.EvaluationStackExhausted"/>. A view
/// built over a view therefore reads that view's bindings directly. The entries and their order are the same, so
/// binding order, shadowing and lookups do not change and nothing is charged. Copying the captured slots then
/// depends only on the number of bindings, independently of the number of enclosing planned frames.</para>
/// </summary>
internal sealed class LoopValueEnvironment : ValEnv, IValueEnvironmentCacheIdentityProvider
{
    // Never itself a LoopValueEnvironment (see the constructor), so every read is one hop deep.
    private readonly ValEnv _bindings;
    private object _cacheIdentity = new();

    public LoopValueEnvironment(ValEnv parent)
        => _bindings = parent is LoopValueEnvironment view ? view._bindings : parent;

    public object CacheIdentity => _cacheIdentity;

    public void BeginIteration()
        => _cacheIdentity = new object();

    public int Count => _bindings.Count;

    public (string Name, Result Value) this[int index] => _bindings[index];

    public IEnumerator<(string Name, Result Value)> GetEnumerator()
        => _bindings.GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator()
        => GetEnumerator();
}

internal sealed class LoopRunFrame
{
    private readonly Result[] _stateSlots;
    private IReadOnlyList<NeedCell>? _pendingState;
    private readonly Result[] _scratchSlots;
    private readonly Result[] _capturedSlots;
    private readonly PlannedLoopValue[] _tempSlots;
    private readonly bool[] _tempSlotHasValue;
    private readonly PlannedLoopValue[] _iterationOutputs;
    private readonly LoopValueEnvironment _valueEnvironment;

    public LoopRunFrame(
        LoopPlanTemplate template,
        ValEnv parentValEnv,
        IReadOnlyList<NeedCell> initialStateValues)
    {
        Template = template;
        var parentCtx = template.ParentCtx;
        IterationCtx = parentCtx.Push(template.Step);
        _stateSlots = new Result[initialStateValues.Count];
        _pendingState = initialStateValues;
        _scratchSlots = new Result[template.StateArity];
        _capturedSlots = parentValEnv.Select(item => item.Value).ToArray();
        _tempSlots = new PlannedLoopValue[template.TempPlans.Count];
        _tempSlotHasValue = new bool[template.TempPlans.Count];
        _iterationOutputs = new PlannedLoopValue[
            template.NextStateOutputs.Count + (template.ContinuationOutput is null ? 0 : 1)];
        _valueEnvironment = new LoopValueEnvironment(parentValEnv);
        Diagnostics = parentCtx.LoopDiagnostics;
        Diagnostics?.RecordLoopPlanExecution(template.DiagnosticKey);
    }

    public LoopPlanTemplate Template { get; }

    public Evaluator.EvalCtx IterationCtx { get; private set; }

    public LoopOptimizationDiagnostics? Diagnostics { get; }

    public ValEnv ValueEnvironment => _valueEnvironment;

    public void BeginIteration()
    {
        if (_tempSlotHasValue.Length != 0)
            Array.Clear(_tempSlotHasValue);

        if (Template.RequiresPerIterationCacheIdentity)
        {
            _valueEnvironment.BeginIteration();
            IterationCtx = Evaluator.EnterAlgorithmBody(
                Template.Step,
                Evaluator.LoopNeedBindingContext(Template.ParentCtx, Template.StateNames, CurrentCells()),
                _valueEnvironment,
                Template.StateNames);
        }
    }

    private IReadOnlyList<NeedCell> CurrentCells()
        => _pendingState ?? _stateSlots.Select(value => NeedCell.Ready(new(value, value.ValueCount()))).ToArray();

    /// <summary>
    /// The value of state slot <paramref name="index"/>. A PENDING initial-state cell is demanded
    /// here, at its first read. A parameter read demands it exactly as the generic read of the step
    /// parameter does (<c>Evaluator.DemandParameter</c>), with the READING reference's span
    /// (<paramref name="readSpan"/>), which positions an unspanned failure of a written-block cell —
    /// a step limit falling on that cell's dispatch checkpoint — where the generic read positions it.
    /// </summary>
    public EvalResult<Result> GetStateSlot(int index, SourceSpan? readSpan, bool parameterUse = true)
    {
        if (_pendingState is null) return EvalResult<Result>.Ok(_stateSlots[index]);
        var demanded = parameterUse
            ? Evaluator.DemandPlannedParameter(_pendingState[index], Template.StateNames[index], readSpan)
            : _pendingState[index].Demand();
        if (demanded.IsError) return demanded.Error;
        _stateSlots[index] = demanded.Value.Value;
        return EvalResult<Result>.Ok(demanded.Value.Value);
    }

    public Result GetCapturedSlot(int index)
        => _capturedSlots[index];

    public bool TryGetTempSlot(int index, out PlannedLoopValue value)
    {
        value = _tempSlots[index];
        return _tempSlotHasValue[index];
    }

    /// <summary>
    /// Establishes the per-iteration memo of local temp <paramref name="index"/> and returns the value
    /// that every consumer of the entry receives: the reads, and the fresh call that first establishes
    /// the entry. The generic property cache stores one <see cref="Result"/> for an entry, so the memo
    /// boxes an unboxed numeric value once (<see cref="PlannedLoopValue.WithResult"/>). Without this, each
    /// output read would box its own atom, and a host comparing two reads by reference would see two
    /// objects. The numeric view stays available to the arithmetic fast paths.
    /// <para>This also boxes arithmetic-only temps. Selective boxing saved one atom per such temp per
    /// iteration. Its timing relative to the inline control varied with JIT tiering (KL-01 measurements
    /// in <c>benchmarks/README.md</c>).</para>
    /// </summary>
    public PlannedLoopValue EstablishTempSlot(int index, PlannedLoopValue value)
    {
        value = value.WithResult();
        _tempSlots[index] = value;
        _tempSlotHasValue[index] = true;
        return value;
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
    {
        for (var index = 0; index < _stateSlots.Length; index++)
        {
            var value = GetStateSlot(index, readSpan: null, parameterUse: false);
            if (value.IsError) return value.Error;
        }
        return Evaluator.MakeCheckedLoopStateResult(IterationCtx, _stateSlots);
    }

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
            _pendingState = null;
            return true;
        }

        // Carry each next-state slot verbatim, matching the generic loop, instead of
        // recursively normalizing (which would collapse explicit empty-sequence nesting).
        for (var i = 0; i < _stateSlots.Length; i++)
            _stateSlots[i] = _scratchSlots[i];
        _pendingState = null;
        return true;
    }
}
