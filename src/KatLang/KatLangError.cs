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

    private static string FormatEvalError(EvalError error)
    {
        if (TryFormatDotCallUnknownName(error, out var formattedDotCallError))
            return formattedDotCallError;
        if (TryFormatMissingOutput(error, out var formattedMissingOutput))
            return formattedMissingOutput;
        if (TryFormatArityMismatch(error, out var formattedArityMismatch))
            return formattedArityMismatch;

        return error switch
        {
            EvalError.UnknownName e => $"Unknown name: {e.Name}",
            EvalError.UnknownProperty e => $"Unknown property '{e.PropertyName}' on {e.ObjectDesc}",
            EvalError.NotPublicProperty e => $"Property '{e.PropertyName}' on {e.ObjectDesc} is not public",
            EvalError.NotAnAlgorithm e => $"Not an algorithm: {e.Description}",
            EvalError.IllegalInOpen e => $"Illegal in open: {e.Reason}",
            EvalError.BadOpenForm e => $"Bad open form: {e.Reason}",
            EvalError.IllegalInEval e => $"Illegal in eval: {e.Reason}",
            EvalError.AmbiguousOpen e => $"Ambiguous open '{e.Name}': provided by {string.Join(", ", e.Providers)}",
            EvalError.ArityMismatch e => FormatGenericArityMismatch(e.Expected, e.Actual),
            EvalError.BadArity => "Bad arity",
            EvalError.TypeMismatch e => $"Type mismatch: {e.Message}",
            EvalError.BadIndex => "Bad index",
            EvalError.DivByZero => "Division by zero",
            EvalError.NoMatchingBranch e => $"No matching branch for '{e.AlgorithmName}'",
            EvalError.MissingOutput => FormatGenericMissingOutput(),
            EvalError.NumericOverflow => "Numeric overflow",
            EvalError.UnresolvedImplicitParams e => FormatUnresolvedImplicitParams(e),
            EvalError.WithContext e => $"{e.Context}: {FormatEvalError(e.Inner)}",
            _ => error.ToString()!,
        };
    }

    private static bool TryFormatDotCallUnknownName(EvalError error, out string message)
    {
        message = string.Empty;

        if (error is not EvalError.WithContext { Context: var context, Inner: EvalError.UnknownName(var missingName) })
            return false;

        const string prefix = "while evaluating dotCall .";
        if (!context.StartsWith(prefix, StringComparison.Ordinal))
            return false;

        var delimiterIndex = context.IndexOf(" of ", prefix.Length, StringComparison.Ordinal);
        if (delimiterIndex < 0)
            return false;

        var propertyName = context[prefix.Length..delimiterIndex];
        if (!string.Equals(propertyName, missingName, StringComparison.Ordinal))
            return false;

        var receiverDesc = context[(delimiterIndex + " of ".Length)..];
        message = $"Property '{propertyName}' was not found on `{receiverDesc}`, and no visible algorithm or property named '{propertyName}' can be used with `{receiverDesc}` as the first argument.";
        return true;
    }

    private static bool TryFormatMissingOutput(EvalError error, out string message)
    {
        message = string.Empty;

        if (error is EvalError.MissingOutput)
        {
            message = FormatGenericMissingOutput();
            return true;
        }

        if (error is not EvalError.WithContext { Context: var context, Inner: EvalError.MissingOutput })
            return false;

        if (TryParsePropertyContext(context, out var propertyName))
        {
            message = FormatPropertyMissingOutput(propertyName);
            return true;
        }

        if (TryParseCallContext(context, out var calleeDesc))
        {
            message = FormatReferenceMissingOutput(calleeDesc);
            return true;
        }

        if (TryParseDotCallContext(context, out var receiverDesc, out var dotPropertyName))
        {
            message = string.Equals(dotPropertyName, "string", StringComparison.Ordinal)
                ? FormatReferenceMissingOutput(receiverDesc)
                : FormatReferenceMissingOutput($"{receiverDesc}.{dotPropertyName}");
            return true;
        }

        return false;
    }

    private static bool TryFormatArityMismatch(EvalError error, out string message)
    {
        message = string.Empty;

        if (error is not EvalError.WithContext { Context: var context, Inner: EvalError.ArityMismatch inner })
            return false;

        if (TryParsePropertyContext(context, out var propertyName))
        {
            message = FormatNamedArityMismatch(propertyName, inner.Expected, inner.Actual, preferPropertyName: true);
            return true;
        }

        if (TryParseCallContext(context, out var calleeDesc))
        {
            message = inner.Span is null
                ? FormatNamedArityMismatch(calleeDesc, inner.Expected, inner.Actual, preferPropertyName: IsSimpleIdentifier(calleeDesc))
                : FormatGenericArityMismatch(inner.Expected, inner.Actual);
            return true;
        }

        if (TryParseDotCallContext(context, out var receiverDesc, out var dotPropertyName))
        {
            message = inner.Span is null
                ? $"Property '{dotPropertyName}' on `{receiverDesc}` expects {FormatCount(inner.Expected, "parameter")}, but was called with {FormatCount(inner.Actual, "argument")}."
                : FormatGenericArityMismatch(inner.Expected, inner.Actual);
            return true;
        }

        return false;
    }

    private static bool TryParseCallContext(string context, out string calleeDesc)
    {
        const string prefix = "while evaluating call to ";
        if (context.StartsWith(prefix, StringComparison.Ordinal))
        {
            calleeDesc = context[prefix.Length..];
            return true;
        }

        calleeDesc = string.Empty;
        return false;
    }

    private static bool TryParsePropertyContext(string context, out string propertyName)
    {
        const string prefix = "while evaluating property ";
        if (context.StartsWith(prefix, StringComparison.Ordinal))
        {
            propertyName = context[prefix.Length..];
            return true;
        }

        propertyName = string.Empty;
        return false;
    }

    private static bool TryParseDotCallContext(string context, out string receiverDesc, out string propertyName)
    {
        receiverDesc = string.Empty;
        propertyName = string.Empty;

        const string prefix = "while evaluating dotCall .";
        if (!context.StartsWith(prefix, StringComparison.Ordinal))
            return false;

        var delimiterIndex = context.IndexOf(" of ", prefix.Length, StringComparison.Ordinal);
        if (delimiterIndex < 0)
            return false;

        propertyName = context[prefix.Length..delimiterIndex];
        receiverDesc = context[(delimiterIndex + " of ".Length)..];
        return true;
    }

    private static string FormatNamedArityMismatch(string calleeDesc, int expected, int actual, bool preferPropertyName)
    {
        var subject = preferPropertyName
            ? $"Property '{calleeDesc}'"
            : $"Algorithm `{calleeDesc}`";
        return $"{subject} expects {FormatCount(expected, "parameter")}, but was called with {FormatCount(actual, "argument")}.";
    }

    private static string FormatPropertyMissingOutput(string propertyName)
        => $"Property '{propertyName}' has no output here. Add an Output expression inside '{propertyName}', or use one of its properties, for example `{propertyName}.X`.";

    private static string FormatReferenceMissingOutput(string referenceDesc)
        => IsSimpleIdentifier(referenceDesc)
            ? FormatPropertyMissingOutput(referenceDesc)
            : $"The value `{referenceDesc}` has no output here. Add an Output expression inside it, or use one of its properties.";

    private static string FormatGenericMissingOutput()
        => "This algorithm or group has no output here. Add an Output expression inside it, or use one of its properties.";

    private static string FormatGenericArityMismatch(int expected, int actual)
        => $"Expected {FormatCount(expected, "parameter")}, but was called with {FormatCount(actual, "argument")}.";

    private static string FormatCount(int count, string singularNoun)
        => count == 1 ? $"1 {singularNoun}" : $"{count} {singularNoun}s";

    private static bool IsSimpleIdentifier(string value)
    {
        if (string.IsNullOrEmpty(value) || !(char.IsLetter(value[0]) || value[0] == '_'))
            return false;

        for (var i = 1; i < value.Length; i++)
        {
            if (!(char.IsLetterOrDigit(value[i]) || value[i] == '_'))
                return false;
        }

        return true;
    }

    private static string FormatUnresolvedImplicitParams(EvalError.UnresolvedImplicitParams e)
    {
        var count = e.ParamNames.Count;
        var subject = count == 1 ? "Identifier" : "Identifiers";
        var nameVerb = count == 1 ? "does" : "do";
        var resolutionTarget = count == 1
            ? "a property or other visible name"
            : "properties or other visible names";
        var interpretation = count == 1 ? "an implicit parameter" : "implicit parameters";
        var callerSentence = count == 1 ? "Its value is provided by the caller." : "Their values are provided by the caller.";
        var argPhrase = count == 1 ? "argument was" : "arguments were";
        var argWord = count == 1 ? "argument" : "arguments";
        var names = count == 1
            ? $"'{e.ParamNames[0]}'"
            : string.Join(", ", e.ParamNames.Take(count - 1).Select(n => $"'{n}'")) + $" and '{e.ParamNames[^1]}'";
        return $"{subject} {names} {nameVerb} not resolve to {resolutionTarget} here, so KatLang interprets {(count == 1 ? "it" : "them")} as {interpretation}. {callerSentence} No {argPhrase} provided, so the program cannot be executed (expected {count} {argWord}, got 0).";
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
