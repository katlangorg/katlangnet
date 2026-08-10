using System.Runtime.CompilerServices;

namespace KatLang.Evaluation;

/// <summary>
/// Run-scoped mutable evaluation budget: the single place where one evaluation run's
/// dynamic depth, consumed steps, materialized item slots, and materialized string units live.
///
/// <para>Exactly one instance is created per top-level run and shared by reference
/// through every copied <c>EvalCtx</c>, so nested calls, callbacks, properties, loops,
/// and the engine's <c>DisplayDecimals</c> evaluation all charge the same budget and
/// none of them can reset it. It is never static, never global, and never reused across
/// independent runs, so two runs — including concurrent runs that share one
/// <see cref="RunOptions"/> or <see cref="EvaluationLimits"/> instance — always start
/// with fresh counters. Thread safety is by isolation: one budget belongs to one run on
/// one thread.</para>
/// </summary>
internal sealed class EvaluationBudget
{
    private readonly int _maxDepth;
    private readonly long _maxSteps;
    private readonly int _maxCollectionItems;
    private readonly long _maxMaterializedItems;
    private readonly int _maxStringLength;
    private readonly long _maxMaterializedStringChars;
    private int _depth;
    private long _steps;
    private long _materializedItems;
    private long _materializedStringChars;

    internal EvaluationBudget(EvaluationLimits limits)
    {
        ArgumentNullException.ThrowIfNull(limits);
        _maxDepth = limits.EffectiveMaxDepth;
        _maxSteps = limits.EffectiveMaxSteps ?? long.MaxValue;
        _maxCollectionItems = limits.EffectiveMaxCollectionItems;
        _maxMaterializedItems = limits.EffectiveMaxMaterializedItems ?? long.MaxValue;
        _maxStringLength = limits.EffectiveMaxStringLength;
        _maxMaterializedStringChars = limits.EffectiveMaxMaterializedStringChars ?? long.MaxValue;
        HasStepLimit = limits.EffectiveMaxSteps is not null;
        HasConfiguredStringLimit = limits.MaxStringLength is not null
            || limits.MaxMaterializedStringChars is not null;
    }

    /// <summary>Creates a fresh budget for one run; <c>null</c> limits mean <see cref="EvaluationLimits.Default"/>.</summary>
    internal static EvaluationBudget Create(EvaluationLimits? limits)
        => new(limits ?? EvaluationLimits.Default);

    /// <summary>The enforced depth limit (the internal ceiling, or a lower configured value).</summary>
    internal int MaxDepth => _maxDepth;

    /// <summary>True when a finite step budget is configured for this run.</summary>
    internal bool HasStepLimit { get; }

    /// <summary>True when the caller explicitly configured either string limit.</summary>
    internal bool HasConfiguredStringLimit { get; }

    /// <summary>Steps consumed so far by this run. Diagnostics and tests only.</summary>
    internal long ConsumedSteps => _steps;

    /// <summary>
    /// Charges one dynamic algorithm invocation: one step of work, one level of depth.
    /// Returns <c>null</c> when the invocation may proceed, in which case — and only
    /// then — the caller MUST balance it with <see cref="ExitInvocation"/> from a
    /// <c>finally</c> block. Returns the structured limit error otherwise, with depth
    /// left unchanged so the failing invocation is never counted as entered.
    /// </summary>
    internal EvalError? TryEnterInvocation()
    {
        if (TryChargeStep() is { } stepError)
            return stepError;

        if (_depth >= _maxDepth)
            return new EvalError.EvaluationDepthExceeded(_maxDepth);

        // Deterministic depth alone cannot be calibrated to be simultaneously useful for
        // real programs and safe for the most stack-expensive evaluation shape on the
        // smallest supported stack (see EvaluationLimits.MaxSupportedDepth). This probe
        // is the machine-dependent backstop that keeps the failure structured: it can
        // only stop evaluation EARLIER than the deterministic limit, never later, so it
        // cannot change the result of any run that stays within host stack headroom.
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        _depth++;
        if (_depth > PeakDepth) PeakDepth = _depth;
        return null;
    }

    /// <summary>
    /// Deepest dynamic invocation nesting this run reached. Observation only: reading it
    /// cannot change what was evaluated, and it is run-scoped like every other counter.
    /// </summary>
    internal int PeakDepth { get; private set; }

    /// <summary>
    /// Charges one level of depth — and NO step — for re-entering an algorithm body
    /// outside a dynamic invocation: builtin argument and control-argument body
    /// evaluation. Argument evaluation is not a unit of semantic work (steps count
    /// dynamic invocations and loop iterations only, and the frozen plain/dot work
    /// parity depends on that), but it IS a level of host recursion: without this
    /// charge a zero-parameter property that reaches itself through a builtin
    /// argument (<c>A = count(A)</c>, <c>A = if(1, A, 0)</c>, <c>A = range(1, A)</c>)
    /// recurses outside every budget chokepoint and terminates the process with an
    /// uncatchable <see cref="StackOverflowException"/>. Same contract as
    /// <see cref="TryEnterInvocation"/>: on <c>null</c>, balance with
    /// <see cref="ExitInvocation"/> from a <c>finally</c> block; on an error the
    /// depth is left unchanged.
    /// </summary>
    internal EvalError? TryEnterArgumentEvaluation()
    {
        if (_depth >= _maxDepth)
            return new EvalError.EvaluationDepthExceeded(_maxDepth);

        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        _depth++;
        if (_depth > PeakDepth) PeakDepth = _depth;
        return null;
    }

    /// <summary>
    /// Leaves a level entered by a successful <see cref="TryEnterInvocation"/> or
    /// <see cref="TryEnterArgumentEvaluation"/>.
    /// </summary>
    internal void ExitInvocation() => _depth--;

    /// <summary>The enforced single-collection item limit.</summary>
    internal int MaxCollectionItems => _maxCollectionItems;

    /// <summary>Item slots materialized so far by this run. Diagnostics and tests only.</summary>
    internal long MaterializedItems => _materializedItems;

    /// <summary>
    /// Checks the single-collection boundary WITHOUT consuming cumulative budget, for a
    /// collection the source asked for but an optimized path will never materialize.
    ///
    /// <para>This is what keeps optimized and generic paths on the same observable
    /// boundary: a fused pipeline such as <c>range(1, N).count</c> must reject the same
    /// N as the generic path, even though it allocates nothing. Because it allocates
    /// nothing it must NOT also consume the cumulative materialization budget — that
    /// would be exactly the double charging a fused pipeline is supposed to avoid.</para>
    /// </summary>
    internal EvalError? CheckCollectionSize(long requestedCount)
        => requestedCount > _maxCollectionItems
            ? new EvalError.CollectionSizeLimitExceeded(_maxCollectionItems, requestedCount)
            : null;

    /// <summary>
    /// RESERVES <paramref name="requestedCount"/> item slots for a collection that is
    /// about to be created. Callers MUST call this before allocating — the whole point
    /// is that a rejected request never allocates — and must abandon construction when
    /// it returns an error.
    ///
    /// <para>Both limits are checked before either counter moves, so a rejected
    /// reservation leaves the cumulative total exactly as it was: a failed operation can
    /// never corrupt the budget or make a later legal collection fail. The cumulative
    /// check is written as a subtraction against the remaining headroom so it cannot
    /// overflow for any <see cref="long"/> request.</para>
    /// </summary>
    internal EvalError? TryReserveCollection(long requestedCount)
    {
        if (requestedCount < 0)
            throw new ArgumentOutOfRangeException(nameof(requestedCount), requestedCount, "Item count cannot be negative.");

        if (requestedCount > _maxCollectionItems)
            return new EvalError.CollectionSizeLimitExceeded(_maxCollectionItems, requestedCount);

        if (requestedCount > _maxMaterializedItems - _materializedItems)
            return new EvalError.MaterializationLimitExceeded(_maxMaterializedItems);

        _materializedItems = checked(_materializedItems + requestedCount);
        return null;
    }

    /// <summary>The enforced single-string length limit, in UTF-16 code units.</summary>
    internal int MaxStringLength => _maxStringLength;

    /// <summary>String code units materialized so far by this run. Diagnostics and tests only.</summary>
    internal long MaterializedStringChars => _materializedStringChars;

    /// <summary>
    /// RESERVES <paramref name="requestedLength"/> UTF-16 code units for a language string
    /// value that is about to be created. Callers reserve before building the string, and
    /// abandon construction when this returns an error.
    ///
    /// <para>Both limits are checked before either counter moves, so a rejected reservation
    /// leaves the cumulative total untouched. The cumulative check subtracts against
    /// remaining headroom, so it cannot overflow for any <see cref="long"/> request.</para>
    /// </summary>
    internal EvalError? TryReserveString(long requestedLength)
    {
        if (requestedLength < 0)
            throw new ArgumentOutOfRangeException(nameof(requestedLength), requestedLength, "Length cannot be negative.");

        if (requestedLength > _maxStringLength)
            return new EvalError.StringSizeLimitExceeded(_maxStringLength, requestedLength);

        if (requestedLength > _maxMaterializedStringChars - _materializedStringChars)
            return new EvalError.StringMaterializationLimitExceeded(_maxMaterializedStringChars);

        _materializedStringChars = checked(_materializedStringChars + requestedLength);
        return null;
    }

    /// <summary>
    /// Charges one unit of semantic work (currently: one dynamic invocation, or one
    /// loop iteration). Returns <c>null</c> when the work may proceed.
    /// </summary>
    internal EvalError? TryChargeStep()
    {
        if (_steps >= _maxSteps)
            return new EvalError.EvaluationStepLimitExceeded(_maxSteps);

        _steps++;
        return null;
    }
}
