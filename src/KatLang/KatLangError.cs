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
        if (TryFormatSpecialOutputAccess(error, out var formattedSpecialOutputAccess))
            return formattedSpecialOutputAccess;
        if (TryFormatLocalOnlyProperty(error, out var formattedLocalOnlyProperty))
            return formattedLocalOnlyProperty;
        if (TryFormatMissingOutput(error, out var formattedMissingOutput))
            return formattedMissingOutput;
        if (TryFormatArityMismatch(error, out var formattedArityMismatch))
            return formattedArityMismatch;
        if (TryFormatUnresolvedImplicitParams(error, out var formattedImplicitParams))
            return formattedImplicitParams;

        return error switch
        {
            EvalError.UnknownName e => $"Unknown name: {e.Name}",
            EvalError.UnknownProperty e => $"Unknown property '{e.PropertyName}' on {e.ObjectDesc}",
            EvalError.NotPublicProperty e => $"Property '{e.PropertyName}' on {e.ObjectDesc} is not public",
            EvalError.LocalOnlyProperty e => FormatLocalOnlyProperty(e.ObjectDesc, e.PropertyName, e.Exposure),
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
            EvalError.SpecialOutputAccess => FormatSpecialOutputAccess(receiverDesc: null),
            EvalError.ExplicitParametersRequireOutput => AlgorithmValidation.ExplicitParametersRequireOutputMessage,
            EvalError.MissingOutput => FormatGenericMissingOutput(),
            EvalError.NumericOverflow => "Numeric overflow",
            EvalError.UnresolvedImplicitParams e => FormatUnresolvedImplicitParams(e),
            EvalError.WithContext e => $"{e.Context}: {FormatEvalError(e.Inner)}",
            _ => error.ToString()!,
        };
    }

    private static bool TryGetTextContext(EvalError error, out string context, out EvalError inner)
    {
        if (error is EvalError.WithContext { ErrorContext: TextErrorContext(var message), Inner: var nestedInner })
        {
            context = message;
            inner = nestedInner;
            return true;
        }

        context = string.Empty;
        inner = null!;
        return false;
    }

    private static bool TryFormatSpecialOutputAccess(EvalError error, out string message)
    {
        message = string.Empty;

        if (error is EvalError.SpecialOutputAccess)
        {
            message = FormatSpecialOutputAccess(receiverDesc: null);
            return true;
        }

        if (error is EvalError.WithContext { ErrorContext: DotCallContext dotContext, Inner: EvalError.SpecialOutputAccess })
        {
            message = string.Equals(dotContext.PropertyName, "Output", StringComparison.Ordinal)
                ? FormatSpecialOutputAccess(dotContext.ReceiverDescription)
                : FormatSpecialOutputAccess(receiverDesc: null);
            return true;
        }

        if (error is not EvalError.WithContext { Inner: EvalError.SpecialOutputAccess })
            return false;

        if (TryGetTextContext(error, out var context, out _)
            && TryParseDotCallContext(context, out var receiverDesc, out var propertyName)
            && string.Equals(propertyName, "Output", StringComparison.Ordinal))
        {
            message = FormatSpecialOutputAccess(receiverDesc);
            return true;
        }

        message = FormatSpecialOutputAccess(receiverDesc: null);
        return true;
    }

    private static bool TryFormatLocalOnlyProperty(EvalError error, out string message)
    {
        message = string.Empty;

        if (error is EvalError.LocalOnlyProperty direct)
        {
            message = FormatLocalOnlyProperty(direct.ObjectDesc, direct.PropertyName, direct.Exposure);
            return true;
        }

        if (error is EvalError.WithContext { Inner: EvalError.LocalOnlyProperty contextual })
        {
            message = FormatLocalOnlyProperty(contextual.ObjectDesc, contextual.PropertyName, contextual.Exposure);
            return true;
        }

        return false;
    }

    private static bool TryFormatDotCallUnknownName(EvalError error, out string message)
    {
        message = string.Empty;

        if (error is EvalError.WithContext { ErrorContext: DotCallContext dotContext, Inner: EvalError.UnknownName(var missingName) }
            && string.Equals(dotContext.PropertyName, missingName, StringComparison.Ordinal))
        {
            message = $"Property '{dotContext.PropertyName}' was not found on `{dotContext.ReceiverDescription}`, and no visible algorithm or property named '{dotContext.PropertyName}' can be used with `{dotContext.ReceiverDescription}` as the first argument.";
            return true;
        }

        if (!TryGetTextContext(error, out var context, out var inner)
            || inner is not EvalError.UnknownName(var legacyMissingName))
            return false;

        const string prefix = "while evaluating dotCall .";
        if (!context.StartsWith(prefix, StringComparison.Ordinal))
            return false;

        var delimiterIndex = context.IndexOf(" of ", prefix.Length, StringComparison.Ordinal);
        if (delimiterIndex < 0)
            return false;

        var propertyName = context[prefix.Length..delimiterIndex];
        if (!string.Equals(propertyName, legacyMissingName, StringComparison.Ordinal))
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

        if (error is EvalError.WithContext { ErrorContext: PropertyEvaluationContext propertyContext, Inner: EvalError.MissingOutput })
        {
            message = FormatPropertyMissingOutput(propertyContext.PropertyName);
            return true;
        }

        if (error is EvalError.WithContext { ErrorContext: CallContext callContext, Inner: EvalError.MissingOutput })
        {
            message = FormatCallMissingOutput(callContext.CalleeDescription);
            return true;
        }

        if (error is EvalError.WithContext { ErrorContext: DotCallContext dotCallContext, Inner: EvalError.MissingOutput })
        {
            message = string.Equals(dotCallContext.PropertyName, "string", StringComparison.Ordinal)
                ? FormatReferenceMissingOutput(dotCallContext.ReceiverDescription)
                : FormatReferenceMissingOutput($"{dotCallContext.ReceiverDescription}.{dotCallContext.PropertyName}");
            return true;
        }

        if (!TryGetTextContext(error, out var context, out var inner)
            || inner is not EvalError.MissingOutput)
            return false;

        if (TryParsePropertyContext(context, out var propertyName))
        {
            message = FormatPropertyMissingOutput(propertyName);
            return true;
        }

        if (TryParseCallContext(context, out var calleeDesc))
        {
            message = FormatCallMissingOutput(calleeDesc);
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

        if (error is EvalError.WithContext { ErrorContext: PropertyEvaluationContext propertyContext, Inner: EvalError.ArityMismatch propertyArity })
        {
            message = FormatNamedArityMismatch(propertyContext.PropertyName, propertyArity.Expected, propertyArity.Actual, preferPropertyName: true);
            return true;
        }

        if (error is EvalError.WithContext { ErrorContext: CallContext callContext, Inner: EvalError.ArityMismatch callArity })
        {
            message = callArity.Span is null
                ? FormatNamedArityMismatch(callContext.CalleeDescription, callArity.Expected, callArity.Actual, preferPropertyName: IsSimpleIdentifier(callContext.CalleeDescription))
                : FormatGenericArityMismatch(callArity.Expected, callArity.Actual);
            return true;
        }

        if (error is EvalError.WithContext { ErrorContext: DotCallContext dotCallContext, Inner: EvalError.ArityMismatch dotCallArity })
        {
            message = dotCallArity.Span is null
                ? $"Property '{dotCallContext.PropertyName}' on `{dotCallContext.ReceiverDescription}` expects {FormatCount(dotCallArity.Expected, "parameter")}, but was called with {FormatCount(dotCallArity.Actual, "argument")}."
                : FormatGenericArityMismatch(dotCallArity.Expected, dotCallArity.Actual);
            return true;
        }

        if (!TryGetTextContext(error, out var context, out var inner)
            || inner is not EvalError.ArityMismatch legacyArity)
            return false;

        if (context.StartsWith("Builtin '", StringComparison.Ordinal))
        {
            message = context;
            return true;
        }

        if (TryParsePropertyContext(context, out var propertyName))
        {
            message = FormatNamedArityMismatch(propertyName, legacyArity.Expected, legacyArity.Actual, preferPropertyName: true);
            return true;
        }

        if (TryParseCallContext(context, out var calleeDesc))
        {
            message = legacyArity.Span is null
                ? FormatNamedArityMismatch(calleeDesc, legacyArity.Expected, legacyArity.Actual, preferPropertyName: IsSimpleIdentifier(calleeDesc))
                : FormatGenericArityMismatch(legacyArity.Expected, legacyArity.Actual);
            return true;
        }

        if (TryParseDotCallContext(context, out var receiverDesc, out var dotPropertyName))
        {
            message = legacyArity.Span is null
                ? $"Property '{dotPropertyName}' on `{receiverDesc}` expects {FormatCount(legacyArity.Expected, "parameter")}, but was called with {FormatCount(legacyArity.Actual, "argument")}."
                : FormatGenericArityMismatch(legacyArity.Expected, legacyArity.Actual);
            return true;
        }

        return false;
    }

    private static bool TryFormatUnresolvedImplicitParams(EvalError error, out string message)
    {
        message = string.Empty;

        if (error is not EvalError.WithContext { ErrorContext: ImplicitParameterContext context, Inner: EvalError.UnresolvedImplicitParams inner })
            return false;

        message = FormatUnresolvedImplicitParams(inner, context.ProvidedArgumentCount);
        return true;
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

    private static string FormatLocalOnlyProperty(string objectDesc, string propertyName, PropertyExposure exposure)
        => exposure switch
        {
            PropertyExposure.LocalOnlyCapturedAncestorParameters =>
                $"Property '{propertyName}' on `{objectDesc}` is local-only because it depends on parameter(s) owned by the enclosing algorithm.",
            PropertyExposure.LocalOnlyConditionalAlgorithm =>
                $"Property '{propertyName}' on `{objectDesc}` is local-only because properties defined inside conditional algorithms are not publicly visible.",
            _ => $"Property '{propertyName}' on `{objectDesc}` is local-only.",
        };

    private static string FormatSpecialOutputAccess(string? receiverDesc)
    {
        const string baseMessage = "Output is the designated result of an algorithm and cannot be accessed through property syntax. Call the algorithm directly instead.";
        return string.IsNullOrWhiteSpace(receiverDesc)
            ? $"{baseMessage} Instead of `Algo.Output(6)`, write `Algo(6)`."
            : $"{baseMessage} Instead of `{receiverDesc}.Output(...)`, write `{receiverDesc}(...)`.";
    }

    private static string FormatReferenceMissingOutput(string referenceDesc)
        => IsSimpleIdentifier(referenceDesc)
            ? FormatPropertyMissingOutput(referenceDesc)
            : $"The value `{referenceDesc}` has no output here. Add an Output expression inside it, or use one of its properties.";

    private static string FormatCallMissingOutput(string calleeDesc)
        => $"Cannot call '{calleeDesc}' because it does not define an output. Add an Output expression inside it, or call one of its properties instead.";

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

    private static string FormatUnresolvedImplicitParams(EvalError.UnresolvedImplicitParams e, int providedArgumentCount = 0)
    {
        var count = e.ParamNames.Count;
        var subject = count == 1 ? "Identifier" : "Identifiers";
        var nameVerb = count == 1 ? "does" : "do";
        var resolutionTarget = count == 1
            ? "a property or other visible name"
            : "properties or other visible names";
        var interpretation = count == 1 ? "an implicit parameter" : "implicit parameters";
        var callerSentence = count == 1 ? "Its value is provided by the caller." : "Their values are provided by the caller.";
        var argWord = count == 1 ? "argument" : "arguments";
        var names = count == 1
            ? $"'{e.ParamNames[0]}'"
            : string.Join(", ", e.ParamNames.Take(count - 1).Select(n => $"'{n}'")) + $" and '{e.ParamNames[^1]}'";
        var missingArgumentSentence = providedArgumentCount == 0
            ? $"No {(count == 1 ? "argument was" : "arguments were")} provided"
            : $"Only {providedArgumentCount} {(providedArgumentCount == 1 ? "argument was" : "arguments were")} provided";
        return $"{subject} {names} {nameVerb} not resolve to {resolutionTarget} here, so KatLang interprets {(count == 1 ? "it" : "them")} as {interpretation}. {callerSentence} {missingArgumentSentence}, so the program cannot be executed (expected {count} {argWord}, got {providedArgumentCount}).";
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
