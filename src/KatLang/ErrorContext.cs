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

public sealed record ProgramEvaluationContext() : ErrorContext
{
    public override string ToLegacyString() => "while evaluating program output";
}

public sealed record DotCallContext(string ReceiverDescription, string PropertyName) : ErrorContext
{
    /// <summary>
    /// True for an extension-dot edge (<c>recv~.Name</c> / <c>recv.~Name</c>):
    /// structural member lookup was bypassed by the written marker, so
    /// member-not-found diagnostics must not claim a property lookup happened.
    /// </summary>
    public bool IsExtension { get; init; }

    public override string ToLegacyString() => $"while evaluating dotCall .{PropertyName} of {ReceiverDescription}";
}

public sealed record CallContext(string CalleeDescription) : ErrorContext
{
    public override string ToLegacyString() => $"while evaluating call to {CalleeDescription}";
}

public sealed record ReduceInitialAccumulatorContext(IReadOnlyList<string> RequiredParameterNames) : ErrorContext
{
    public override string ToLegacyString() => "while preparing reduce initial accumulator";
}

/// <summary>
/// Binding failure of a loop step's state slots. <see cref="StepParameterNames"/>
/// holds the step's TOP-LEVEL parameter display labels (one entry per state
/// slot, so a sequence-value pattern such as <c>(x, y)</c> is ONE entry), not
/// the flattened capture names. The expected state-slot count lives in the
/// inner <see cref="EvalError.ArityMismatch"/>.
/// </summary>
public sealed record LoopStateBindingContext(string LoopName, IReadOnlyList<string> StepParameterNames, int ActualStateValueCount) : ErrorContext
{
    public override string ToLegacyString() => $"while binding {LoopName} step state";
}

public sealed record VariadicLoopStateBindingContext(
    string LoopName,
    IReadOnlyList<string> StepParameterNames,
    int ExpectedMinimumStateValueCount,
    int ActualStateValueCount) : ErrorContext
{
    public override string ToLegacyString() => $"while binding {LoopName} step state";
}

/// <summary>
/// Binding failure of a parser-elaborated assignment deconstruction
/// (<c>x, *y, z = RHS</c>). Diagnostics phrase the failure against the
/// WRITTEN pattern instead of exposing the synthetic inline helper the parser
/// elaborates the assignment into.
/// </summary>
public sealed record DeconstructionBindingContext(
    IReadOnlyList<string> TargetDisplayNames,
    bool HasCollectingTarget) : ErrorContext
{
    public override string ToLegacyString()
        => $"while binding assignment pattern {string.Join(", ", TargetDisplayNames)}";
}

/// <summary>
/// Binding failure of one nested sequence-value parameter pattern group
/// (<c>F((b, c)) = ...</c> receiving the wrong number of values for
/// <c>(b, c)</c>). Wraps ONLY the arity mismatch produced by binding that
/// group's own items, so the failure is attributed to the written pattern
/// instead of the enclosing call's argument count.
/// <see cref="PatternDisplayName"/> is the group's display form, e.g.
/// <c>(b, c)</c>; <see cref="HasCollectingItem"/> is true when the group
/// contains a collecting binding at this level (an "at least N" expectation).
/// </summary>
public sealed record SequenceValueParameterBindingContext(
    string PatternDisplayName,
    bool HasCollectingItem) : ErrorContext
{
    public override string ToLegacyString()
        => $"while binding sequence-value parameter pattern {PatternDisplayName}";
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
