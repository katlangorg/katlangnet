namespace KatLang;

/// <summary>
/// Result monad for evaluation: either a value or a structured error.
/// Corresponds to the <c>Except Error</c> failure channel of <c>EvalM</c> in the Lean
/// specification (<c>structure EvalM (α : Type) where runState : ExceptT Error (StateM EvalState) α</c>);
/// the <c>StateM EvalState</c> layer (the per-run zero-parameter property cache, which
/// Lean retains across failures) is threaded separately by the C# evaluator, not by this type.
/// <para>Hosts receive it from the <see cref="Evaluator"/> entry points: test <see cref="IsOk"/>
/// or <see cref="IsError"/>, then read <see cref="Value"/> or <see cref="Error"/> (render an error
/// with <see cref="KatLangError.FromEvalError"/>). A program's failure is always an error result,
/// never an exception. <c>default(EvalResult&lt;T&gt;)</c> is not a result of any evaluation — it
/// reads as a success holding <c>default(T)</c> — so only use values the evaluator returned.</para>
/// </summary>
public readonly struct EvalResult<T>
{
    private readonly T? _value;
    private readonly EvalError? _error;

    private EvalResult(T value)
    {
        _value = value;
        _error = null;
    }

    private EvalResult(EvalError error)
    {
        _value = default;
        _error = error;
    }

    /// <summary>True when this result contains a value (no error).</summary>
    public bool IsOk => _error is null;

    /// <summary>True when this result contains an error.</summary>
    public bool IsError => _error is not null;

    /// <summary>The success value. Throws if this is an error.</summary>
    public T Value => IsOk
        ? _value!
        : throw new InvalidOperationException("EvalResult contains an error, not a value.");

    /// <summary>The error. Throws if this is a success.</summary>
    public EvalError Error => _error
        ?? throw new InvalidOperationException("EvalResult contains a value, not an error.");

    /// <summary>Creates a successful result holding <paramref name="value"/>.</summary>
    public static EvalResult<T> Ok(T value) => new(value);

    /// <summary>Creates a failed result holding <paramref name="error"/>.</summary>
    /// <exception cref="ArgumentNullException">
    /// <paramref name="error"/> is null — which would otherwise read as a success.
    /// </exception>
    public static EvalResult<T> Err(EvalError error)
    {
        ArgumentNullException.ThrowIfNull(error);
        return new(error);
    }

    /// <summary>Implicit conversion from <see cref="EvalError"/> for ergonomic error returns.</summary>
    public static implicit operator EvalResult<T>(EvalError error) => Err(error);
}
