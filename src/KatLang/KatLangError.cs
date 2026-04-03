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
        EvalError.BadIndex => "Bad index",
        EvalError.DivByZero => "Division by zero",
        EvalError.NoMatchingBranch e => $"No matching branch for '{e.AlgorithmName}'",
        EvalError.NumericOverflow => "Numeric overflow",
        EvalError.WithContext e => $"{e.Context}: {FormatEvalError(e.Inner)}",
        _ => error.ToString()!,
    };

    public override string ToString()
    {
        if (StartLine is { } line && StartColumn is { } col)
            return $"[{line}:{col}] {Message}";
        return Message;
    }
}
