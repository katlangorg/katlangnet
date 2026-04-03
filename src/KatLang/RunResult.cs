namespace KatLang;

/// <summary>
/// Discriminated-union result of a KatLang parse+evaluate run.
/// Pattern-match on <see cref="Success"/>, <see cref="ParseFailure"/>, or <see cref="EvalFailure"/>.
/// </summary>
public abstract record RunResult
{
    private RunResult() { }

    /// <summary>True when the run succeeded.</summary>
    public bool IsSuccess => this is Success;

    /// <summary>True when the run failed (parse or eval).</summary>
    public bool IsFailure => this is ParseFailure or EvalFailure;

    /// <summary>Parse and evaluation succeeded.</summary>
    public sealed record Success(
        Algorithm Root,
        Result Value,
        IReadOnlyList<decimal> Atoms) : RunResult;

    /// <summary>Parsing failed — no executable root was produced.</summary>
    public sealed record ParseFailure(
        IReadOnlyList<KatLangError> Errors) : RunResult;

    /// <summary>Evaluation failed after a successful parse.</summary>
    public sealed record EvalFailure(
        Algorithm Root,
        IReadOnlyList<KatLangError> Errors) : RunResult;

    /// <summary>
    /// Returns a human-readable display string: atoms joined by spaces on success,
    /// or newline-joined errors on failure.
    /// </summary>
    public string ToDisplayString() => this switch
    {
        Success s => string.Join(" ", s.Atoms),
        ParseFailure p => string.Join(Environment.NewLine, p.Errors.Select(e => e.ToString())),
        EvalFailure e => string.Join(Environment.NewLine, e.Errors.Select(e => e.ToString())),
        _ => throw new InvalidOperationException("Unknown RunResult variant."),
    };
}
