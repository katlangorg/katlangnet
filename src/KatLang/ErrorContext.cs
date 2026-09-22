namespace KatLang;

/// <summary>
/// Structured runtime error context carried by <see cref="EvalError.WithContext"/>:
/// the evaluation frame ("while evaluating call to F", "while binding X step
/// state") in which an inner error occurred.
///
/// <para>A C# <c>closed</c> hierarchy: the records declared in this file are the
/// complete set of structured evaluation-context frames KatLang produces, and no
/// other assembly can derive from it (<c>CS9382</c>). Subclassing is not an
/// extension mechanism — a host that needs to attach free-form descriptive text
/// uses <see cref="TextErrorContext"/> (or the string constructor of
/// <see cref="EvalError.WithContext"/>, which wraps one), the variant that
/// carries arbitrary text.</para>
///
/// <para><see cref="ToLegacyString"/> is each variant's textual projection — the
/// prose <see cref="EvalError.WithContext.Context"/> reports and the message
/// formatter falls back to when it has no message tailored to the
/// (context, inner error) shape.</para>
/// </summary>
public closed record ErrorContext
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

/// <summary>
/// A PARAMETER read that demanded the value of the algorithm bound to it (the
/// argument the caller supplied) and found no output: the failure belongs to the
/// argument, not to the callee whose call context encloses it.
/// </summary>
public sealed record ParameterEvaluationContext(string ParameterName) : ErrorContext
{
    public override string ToLegacyString() => $"while evaluating parameter {ParameterName}";
}

/// <summary>
/// A WRITTEN CALL ARGUMENT that was required to supply a value and whose
/// expression produced no output. The failure belongs to that argument — never to
/// the callee, whose own call context still encloses this frame — and never reads
/// as though the caller had omitted the argument.
///
/// <para>This is the unnamed half of the same blame rule
/// <see cref="PropertyEvaluationContext"/> and <see cref="ParameterEvaluationContext"/>
/// carry for a named argument: a brace block, a capture, a call, a selection, or an
/// operator expression has no name to report, so the written argument is described by
/// its own diagnostic spelling (<c>{...}</c>, <c>(1, {...})</c>, <c>1 + {...}</c>) and
/// positioned at the expression that produced nothing.</para>
///
/// <para>PUBLIC because <see cref="ErrorContext"/> is consumer-exhaustive: a host may
/// switch over its variants with no catch-all arm and have the compiler prove the
/// switch complete, and <see cref="EvalError"/> is the one closed root that
/// deliberately keeps a non-public variant. Adding a frame to this hierarchy is
/// therefore a reviewed public-surface addition, exactly as
/// <see cref="ParameterEvaluationContext"/> was.</para>
/// </summary>
public sealed record ArgumentEvaluationContext(string ArgumentDescription) : ErrorContext
{
    public override string ToLegacyString() => $"while evaluating argument {ArgumentDescription}";
}

public sealed record ProgramEvaluationContext() : ErrorContext
{
    public override string ToLegacyString() => "while evaluating program output";
}

public sealed record DotCallContext(string ReceiverDescription, string PropertyName) : ErrorContext
{
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
