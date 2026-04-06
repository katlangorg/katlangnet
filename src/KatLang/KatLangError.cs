namespace KatLang;

/// <summary>
/// Unified public error type representing both parse and evaluation errors.
/// </summary>
public sealed class KatLangError
{
    public string Message { get; }
    public int? StartLine { get; }
    public int? StartColumn { get; }
    public int? EndLine { get; }
    public int? EndColumn { get; }

    private KatLangError(string message, int? startLine, int? startColumn, int? endLine, int? endColumn)
    {
        Message = message;
        StartLine = startLine;
        StartColumn = startColumn;
        EndLine = endLine;
        EndColumn = endColumn;
    }

    public static KatLangError FromDiagnostic(Diagnostic diag)
        => new(diag.Message, diag.Span.StartLineNumber, diag.Span.StartColumn,
               diag.Span.EndLineNumber, diag.Span.EndColumn);

    public static KatLangError FromEvalError(EvalError error)
    {
        var message = FormatEvalError(error);
        if (error.Span is { } span)
            return new(message, span.StartLineNumber, span.StartColumn, span.EndLineNumber, span.EndColumn);
        return new(message, null, null, null, null);
    }

    private static string FormatEvalError(EvalError error) => error switch
    {
        EvalError.UnknownName e => $"Unknown name: {e.Name}",
        EvalError.UnknownProperty e => $"Unknown property '{e.PropertyName}' on {e.ObjectDesc}",
        EvalError.NotPublicProperty e => $"Property '{e.PropertyName}' on {e.ObjectDesc} is not public",
        EvalError.NotAnAlgorithm e => $"Not an algorithm: {e.Description}",
        EvalError.IllegalInOpen e => $"Illegal in open: {e.Reason}",
        EvalError.BadOpenForm e => $"Bad open form: {e.Reason}",
        EvalError.IllegalInEval e => $"Illegal in eval: {e.Reason}",
        EvalError.AmbiguousOpen e => $"Ambiguous open '{e.Name}': provided by {string.Join(", ", e.Providers)}",
        EvalError.ArityMismatch e => $"Arity mismatch: expected {e.Expected}, got {e.Actual}",
        EvalError.BadArity => "Bad arity",
        EvalError.TypeMismatch e => $"Type mismatch: {e.Message}",
        EvalError.BadIndex => "Bad index",
        EvalError.DivByZero => "Division by zero",
        EvalError.NoMatchingBranch e => $"No matching branch for '{e.AlgorithmName}'",
        EvalError.NumericOverflow => "Numeric overflow",
        EvalError.UnresolvedImplicitParams e => FormatUnresolvedImplicitParams(e),
        EvalError.WithContext e => $"{e.Context}: {FormatEvalError(e.Inner)}",
        _ => error.ToString()!,
    };

    private static string FormatUnresolvedImplicitParams(EvalError.UnresolvedImplicitParams e)
    {
        var count = e.ParamNames.Count;
        var paramWord = count == 1 ? "parameter" : "parameters";
        var argPhrase = count == 1 ? "argument was" : "arguments were";
        var argWord = count == 1 ? "argument" : "arguments";
        var names = count == 1
            ? $"`{e.ParamNames[0]}`"
            : string.Join(", ", e.ParamNames.Take(count - 1).Select(n => $"`{n}`")) + $" and `{e.ParamNames[^1]}`";
        return $"The program output depends on implicit {paramWord} {names}, but no {argPhrase} provided, so the program cannot be executed (expected {count} {argWord}, got 0)";
    }

    public override string ToString()
    {
        if (StartLine is { } line && StartColumn is { } col)
            return $"[{line}:{col}] {Message}";
        return Message;
    }
}

/// <summary>
/// Exception thrown by convenience methods when parse or evaluation fails.
/// </summary>
public sealed class KatLangException : Exception
{
    public IReadOnlyList<KatLangError> Errors { get; }

    public KatLangException(IReadOnlyList<KatLangError> errors)
        : base(string.Join(Environment.NewLine, errors.Select(e => e.ToString())))
    {
        Errors = errors;
    }
}
