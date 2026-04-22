namespace KatLang;

/// <summary>
/// Structured runtime error context carried by <see cref="EvalError.WithContext"/>.
/// Each context can still render the legacy prose form used by existing tests
/// and unmigrated formatter fallbacks.
/// </summary>
public abstract record ErrorContext
{
    public abstract string ToLegacyString();

    public sealed override string ToString() => ToLegacyString();
}

public sealed record TextErrorContext(string Message) : ErrorContext
{
    public override string ToLegacyString() => Message;
}

public sealed record PropertyEvaluationContext(string PropertyName) : ErrorContext
{
    public override string ToLegacyString() => $"while evaluating property {PropertyName}";
}

public sealed record DotCallContext(string ReceiverDescription, string PropertyName) : ErrorContext
{
    public override string ToLegacyString() => $"while evaluating dotCall .{PropertyName} of {ReceiverDescription}";
}

public sealed record CallContext(string CalleeDescription) : ErrorContext
{
    public override string ToLegacyString() => $"while evaluating call to {CalleeDescription}";
}

public sealed record OpenResolutionContext(string OpenDescription) : ErrorContext
{
    public override string ToLegacyString() => $"while resolving open: {OpenDescription}";
}

public sealed record ImplicitParameterContext(IReadOnlyList<string> ParamNames, int ProvidedArgumentCount) : ErrorContext
{
    public override string ToLegacyString()
    {
        var subject = ParamNames.Count == 1 ? "implicit parameter" : "implicit parameters";
        var names = ParamNames.Count switch
        {
            0 => "(none)",
            1 => $"'{ParamNames[0]}'",
            2 => $"'{ParamNames[0]}' and '{ParamNames[1]}'",
            _ => string.Join(", ", ParamNames.Take(ParamNames.Count - 1).Select(name => $"'{name}'")) + $", and '{ParamNames[^1]}'",
        };
        var argNoun = ProvidedArgumentCount == 1 ? "argument" : "arguments";
        return $"while evaluating {subject} {names} with {ProvidedArgumentCount} {argNoun}";
    }
}