namespace KatLang;

/// <summary>
/// Result monad for evaluation: either a value or a structured error.
/// Corresponds to <c>EvalM := Except Error</c> in the Lean specification (line 27).
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

    public static EvalResult<T> Ok(T value) => new(value);
    public static EvalResult<T> Err(EvalError error) => new(error);

    /// <summary>Implicit conversion from <see cref="EvalError"/> for ergonomic error returns.</summary>
    public static implicit operator EvalResult<T>(EvalError error) => Err(error);
}
