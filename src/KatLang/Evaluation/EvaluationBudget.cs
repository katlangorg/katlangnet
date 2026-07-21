using System.Runtime.CompilerServices;

namespace KatLang.Evaluation;

/// <summary>
/// Run-scoped mutable evaluation budget: the single place where one evaluation run's
/// dynamic depth and consumed step count live.
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
    private int _depth;
    private long _steps;

    internal EvaluationBudget(EvaluationLimits limits)
    {
        ArgumentNullException.ThrowIfNull(limits);
        _maxDepth = limits.EffectiveMaxDepth;
        _maxSteps = limits.EffectiveMaxSteps ?? long.MaxValue;
        HasStepLimit = limits.EffectiveMaxSteps is not null;
    }

    /// <summary>Creates a fresh budget for one run; <c>null</c> limits mean <see cref="EvaluationLimits.Default"/>.</summary>
    internal static EvaluationBudget Create(EvaluationLimits? limits)
        => new(limits ?? EvaluationLimits.Default);

    /// <summary>The enforced depth limit (the internal ceiling, or a lower configured value).</summary>
    internal int MaxDepth => _maxDepth;

    /// <summary>True when a finite step budget is configured for this run.</summary>
    internal bool HasStepLimit { get; }

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
        return null;
    }

    /// <summary>Leaves an invocation entered by a successful <see cref="TryEnterInvocation"/>.</summary>
    internal void ExitInvocation() => _depth--;

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
