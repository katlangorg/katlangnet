namespace KatLang;

/// <summary>
/// Unified public error type representing parse, evaluation, and display-rendering errors.
/// <see cref="Message"/> is the human-readable rendering; the supported host
/// classification channel is <see cref="Code"/> (with <see cref="Source"/> and
/// <see cref="IsResourceLimit"/> for structured access), never message text.
/// </summary>
public sealed class KatLangError
{
    public string Message { get; }
    public int? StartLine { get; }
    public int? StartColumn { get; }
    public int? EndLine { get; }
    public int? EndColumn { get; }

    /// <summary>
    /// Stable machine-readable classification of this error's semantic family.
    /// For an evaluation error this is <see cref="EvalError.Code"/> of
    /// <see cref="Source"/> (contextual wrappers resolve to the underlying
    /// family); for a front-end error it mirrors the diagnostic's
    /// <see cref="DiagnosticCode"/>. Errors produced by KatLang itself never
    /// carry <see cref="KatLangErrorCode.Unspecified"/>; only an error
    /// projected from an externally constructed diagnostic with an unset code
    /// does.
    /// </summary>
    public KatLangErrorCode Code { get; }

    /// <summary>
    /// The original structured evaluation error this facade was projected from
    /// — the same <see cref="EvalError"/> instance, context wrappers included —
    /// including <see cref="EvalError.DisplayLengthLimitExceeded"/> for display refusal,
    /// or <c>null</c> for an error originating from a front-end
    /// <see cref="Diagnostic"/>, whose stable identity is still available
    /// through <see cref="Code"/>. This preserves the pre-existing public error
    /// hierarchy exactly; it does not add a deep-immutability guarantee to
    /// caller-supplied <see cref="IReadOnlyList{T}"/> payloads or reconstruct
    /// them with different backing identity.
    /// </summary>
    public EvalError? Source { get; }

    /// <summary>
    /// True when this error is a host resource-limit outcome of evaluation or display rendering.
    /// Display overflow is reported by <see cref="DisplayRendering.LimitError"/> and does not
    /// turn a successful evaluation into a <see cref="RunResult.EvalFailure"/>.
    /// Delegates to the one authoritative classifier,
    /// <see cref="EvalError.IsResourceLimit"/>, so it resolves through
    /// contextual wrappers and never inspects message text. Front-end errors
    /// (including source-processing limits, which are diagnostics, not
    /// evaluation outcomes) are never classified as resource limits, and host
    /// cancellation throws <see cref="OperationCanceledException"/> instead of
    /// producing an error value at all.
    /// </summary>
    public bool IsResourceLimit => Source?.IsResourceLimit ?? false;

    private KatLangError(
        string message,
        int? startLine,
        int? startColumn,
        int? endLine,
        int? endColumn,
        KatLangErrorCode code,
        EvalError? source)
    {
        Message = message;
        StartLine = startLine;
        StartColumn = startColumn;
        EndLine = endLine;
        EndColumn = endColumn;
        Code = code;
        Source = source;
    }

    public static KatLangError FromDiagnostic(Diagnostic diag)
        => new(diag.Message, diag.Span.StartLineNumber, diag.Span.StartColumn,
               diag.Span.EndLineNumber, diag.Span.EndColumn,
               MapDiagnosticCode(diag.Code), source: null);

    public static KatLangError FromEvalError(EvalError error)
    {
        var message = AppendInferredImplicitParameterNotes(FormatEvalError(error), error);
        if (error.Span is { } span)
            return new(message, span.StartLineNumber, span.StartColumn, span.EndLineNumber, span.EndColumn, error.Code, error);
        return new(message, null, null, null, null, error.Code, error);
    }

    /// <summary>
    /// Total mapping from front-end <see cref="DiagnosticCode"/> families to the
    /// facade <see cref="KatLangErrorCode"/>. The mapping is name-preserving:
    /// every declared diagnostic family has the same-named facade member
    /// (mechanically pinned by tests), and <see cref="DiagnosticCode.Unspecified"/>
    /// maps to <see cref="KatLangErrorCode.Unspecified"/>. An undeclared numeric
    /// value (an external cast) also maps to Unspecified — the compatibility
    /// state for host-created diagnostics. A declared future family without an
    /// explicit arm fails loudly instead of leaking Unspecified from a
    /// KatLang-produced diagnostic.
    /// </summary>
    internal static KatLangErrorCode MapDiagnosticCode(DiagnosticCode code)
        => code switch
        {
            DiagnosticCode.Unspecified => KatLangErrorCode.Unspecified,
            DiagnosticCode.UnexpectedCharacter => KatLangErrorCode.UnexpectedCharacter,
            DiagnosticCode.UnterminatedStringLiteral => KatLangErrorCode.UnterminatedStringLiteral,
            DiagnosticCode.NumberLiteralTooLarge => KatLangErrorCode.NumberLiteralTooLarge,
            DiagnosticCode.UnexpectedToken => KatLangErrorCode.UnexpectedToken,
            DiagnosticCode.UnsupportedSemicolon => KatLangErrorCode.UnsupportedSemicolon,
            DiagnosticCode.NestingTooDeep => KatLangErrorCode.NestingTooDeep,
            DiagnosticCode.ExpressionChainTooDeep => KatLangErrorCode.ExpressionChainTooDeep,
            DiagnosticCode.DuplicateProperty => KatLangErrorCode.DuplicateProperty,
            DiagnosticCode.DeclarationInParentheses => KatLangErrorCode.DeclarationInParentheses,
            DiagnosticCode.InvalidOpenDeclaration => KatLangErrorCode.InvalidOpenDeclaration,
            DiagnosticCode.InvalidOpenTargetList => KatLangErrorCode.InvalidOpenTargetList,
            DiagnosticCode.BadOpenForm => KatLangErrorCode.BadOpenForm,
            DiagnosticCode.DuplicateBranchPattern => KatLangErrorCode.DuplicateBranchPattern,
            DiagnosticCode.BranchArityMismatch => KatLangErrorCode.BranchArityMismatch,
            DiagnosticCode.BranchOutputArityMismatch => KatLangErrorCode.BranchOutputArityMismatch,
            DiagnosticCode.ClauseVisibilityMismatch => KatLangErrorCode.ClauseVisibilityMismatch,
            DiagnosticCode.InvalidGraceMarker => KatLangErrorCode.InvalidGraceMarker,
            DiagnosticCode.InvalidCollectMarker => KatLangErrorCode.InvalidCollectMarker,
            DiagnosticCode.InvalidCollectingBinding => KatLangErrorCode.InvalidCollectingBinding,
            DiagnosticCode.MisplacedSpread => KatLangErrorCode.MisplacedSpread,
            DiagnosticCode.ArityMismatch => KatLangErrorCode.ArityMismatch,
            DiagnosticCode.ExplicitParametersRequireOutput => KatLangErrorCode.ExplicitParametersRequireOutput,
            DiagnosticCode.UndeclaredIdentifier => KatLangErrorCode.UndeclaredIdentifier,
            DiagnosticCode.AstDepthLimitExceeded => KatLangErrorCode.AstDepthLimitExceeded,
            DiagnosticCode.AstCycleDetected => KatLangErrorCode.AstCycleDetected,
            DiagnosticCode.SourceLengthExceeded => KatLangErrorCode.SourceLengthExceeded,
            DiagnosticCode.AggregateSourceLengthExceeded => KatLangErrorCode.AggregateSourceLengthExceeded,
            DiagnosticCode.ModuleImportDepthExceeded => KatLangErrorCode.ModuleImportDepthExceeded,
            DiagnosticCode.ModuleCountExceeded => KatLangErrorCode.ModuleCountExceeded,
            DiagnosticCode.ModuleNestingTooDeep => KatLangErrorCode.ModuleNestingTooDeep,
            DiagnosticCode.ModuleElaborationStackExhausted => KatLangErrorCode.ModuleElaborationStackExhausted,
            DiagnosticCode.InvalidLoadDirective => KatLangErrorCode.InvalidLoadDirective,
            DiagnosticCode.InvalidLoadUrl => KatLangErrorCode.InvalidLoadUrl,
            DiagnosticCode.LoadCycle => KatLangErrorCode.LoadCycle,
            DiagnosticCode.LoadFetchFailed => KatLangErrorCode.LoadFetchFailed,
            DiagnosticCode.InvalidLoadedSource => KatLangErrorCode.InvalidLoadedSource,
            DiagnosticCode.LoadElaborationUnavailable => KatLangErrorCode.LoadElaborationUnavailable,
            DiagnosticCode.InternalError => KatLangErrorCode.InternalError,
            DiagnosticCode.ParameterPropertyCollision => KatLangErrorCode.ParameterPropertyCollision,
            DiagnosticCode.InvalidSpreadMarker => KatLangErrorCode.InvalidSpreadMarker,
            DiagnosticCode.UnseparatedSameLineItem => KatLangErrorCode.UnseparatedSameLineItem,
            DiagnosticCode.OpenTargetIsParameter => KatLangErrorCode.OpenTargetIsParameter,
            DiagnosticCode.InvalidNumberLiteral => KatLangErrorCode.InvalidNumberLiteral,
            DiagnosticCode.IllegalInOpen => KatLangErrorCode.IllegalInOpen,
            _ when !Enum.IsDefined(code) => KatLangErrorCode.Unspecified,
            _ => throw new InvalidOperationException(
                $"Unhandled declared {nameof(DiagnosticCode)} family in {nameof(KatLangError)}: {code}. "
                + $"Map it to a {nameof(KatLangErrorCode)} family explicitly."),
        };

    /// <summary>
    /// Appends the diagnostic notes carried by an arity/unresolved-parameter
    /// error whose callee parameters were inferred from unresolved identifiers
    /// (see <see cref="ImplicitParameterProvenance"/>), so the rendered message
    /// identifies the original misspelled names, their source locations, and
    /// conservative near-miss suggestions instead of hiding them behind a
    /// generic count mismatch.
    /// <list type="bullet">
    /// <item>Unresolved-implicit-parameter failures already enumerate the
    /// inferred names, so only suggestions are appended — plus, for a name
    /// that was the misspelled member of a dot edge on a statically known
    /// receiver, the receiver-aware explanation (a single such name already
    /// carries it in the main message; see <see cref="FormatUnresolvedImplicitParams"/>).</item>
    /// <item>An arity mismatch with a rendered signature already displays the
    /// parameter names, so only informative notes — a suggestion, or a
    /// receiver-aware origin — are appended; the signatureless
    /// property/value-access phrasing hides the names entirely, so every note
    /// is rendered with its origin location.</item>
    /// </list>
    /// </summary>
    private static string AppendInferredImplicitParameterNotes(string message, EvalError error)
    {
        var terminal = error;
        while (terminal is EvalError.WithContext withContext)
            terminal = withContext.Inner;

        switch (terminal)
        {
            case EvalError.UnresolvedImplicitParams { InferredImplicitParameters: { Count: > 0 } notes } unresolved:
                {
                    var single = unresolved.ParamNames.Count == 1;
                    var builder = new System.Text.StringBuilder(message);
                    foreach (var note in notes)
                    {
                        if (!single && note.DotMemberOrigin is { } origin)
                        {
                            builder.Append('\n');
                            builder.Append(FormatDotMemberFallbackInference(note.Name, origin.ReceiverDescription, note.Span));
                        }

                        if (note.SuggestedName is not { } suggestion)
                            continue;

                        builder.Append('\n');
                        builder.Append(single
                            ? $"Did you mean '{suggestion}'?"
                            : $"Did you mean '{suggestion}' instead of '{note.Name}'?");
                    }

                    return builder.ToString();
                }

            case EvalError.ArityMismatch { InferredImplicitParameters: { Count: > 0 } notes } arity:
                {
                    var signatureShown = arity.Signature is not null;
                    var builder = new System.Text.StringBuilder(message);
                    foreach (var note in notes)
                    {
                        if (signatureShown && note.SuggestedName is null && note.DotMemberOrigin is null)
                            continue;

                        builder.Append('\n');
                        builder.Append(note.Span is { } noteSpan
                            ? $"An implicit parameter '{note.Name}' was inferred at [{noteSpan.StartLineNumber}:{noteSpan.StartColumn}]."
                            : $"An implicit parameter '{note.Name}' was inferred from an unresolved name.");
                        if (note.DotMemberOrigin is { } origin)
                        {
                            builder.Append('\n');
                            builder.Append(FormatDotMemberFallbackInference(note.Name, origin.ReceiverDescription, at: null));
                        }

                        if (note.SuggestedName is { } suggestion)
                            builder.Append($"\nDid you mean '{suggestion}'?");
                    }

                    return builder.ToString();
                }

            default:
                return message;
        }
    }

    private static string FormatEvalError(EvalError error)
    {
        if (TryFormatDotCallUnknownName(error, out var formattedDotCallError))
            return formattedDotCallError;
        if (TryFormatLocalOnlyProperty(error, out var formattedLocalOnlyProperty))
            return formattedLocalOnlyProperty;
        if (TryFormatMissingOutput(error, out var formattedMissingOutput))
            return formattedMissingOutput;
        if (TryFormatLoopStateArityMismatch(error, out var formattedLoopStateArityMismatch))
            return formattedLoopStateArityMismatch;
        if (TryFormatDeconstructionBindingMismatch(error, out var formattedDeconstructionMismatch))
            return formattedDeconstructionMismatch;
        if (TryFormatSequenceValuePatternBindingMismatch(error, out var formattedSequenceValuePatternMismatch))
            return formattedSequenceValuePatternMismatch;
        if (TryFormatArityMismatch(error, out var formattedArityMismatch))
            return formattedArityMismatch;
        if (TryFormatUnresolvedImplicitParams(error, out var formattedImplicitParams))
            return formattedImplicitParams;
        if (TryFormatReduceInitialAccumulator(error, out var formattedReduceInitialAccumulator))
            return formattedReduceInitialAccumulator;

        return error switch
        {
            EvalError.UnknownName e => $"Unknown name: {e.Name}",
            EvalError.UnknownProperty e => $"Unknown property '{e.PropertyName}' on {e.ObjectDesc}",
            EvalError.NotPublicProperty e => $"Property '{e.PropertyName}' on {e.ObjectDesc} is not public",
            EvalError.LocalOnlyProperty e => FormatLocalOnlyProperty(e.ObjectDesc, e.PropertyName, e.Exposure, e.RequiredParameters),
            EvalError.NotAnAlgorithm e => FormatNotAnAlgorithm(e.Description),
            EvalError.IllegalInOpen e => $"Illegal in open: {e.Reason}",
            EvalError.BadOpenForm e => $"Bad open form: {e.Reason}",
            EvalError.IllegalInEval e => $"Illegal in eval: {e.Reason}",
            EvalError.AmbiguousOpen e => $"Ambiguous open '{e.Name}': provided by {string.Join(", ", e.Providers)}",
            EvalError.ArityMismatch e => FormatArityMismatch(e),
            EvalError.VariadicArityMismatch e => FormatVariadicArityMismatch(e),
            EvalError.BadArity => "Bad arity",
            EvalError.TypeMismatch e => $"Type mismatch: {e.Message}",
            EvalError.BadIndex => "Bad index",
            EvalError.DivByZero => "Division by zero",
            EvalError.NoMatchingBranch e => $"No matching branch for '{e.AlgorithmName}'",
            EvalError.BranchArityMismatch e =>
                $"All branches of conditional algorithm '{e.AlgorithmName}' must have the same top-level pattern arity. " +
                $"Expected {e.Expected} (from first branch), but a branch has arity {e.Actual}",
            EvalError.BranchOutputArityMismatch e =>
                $"All branches of conditional algorithm '{e.AlgorithmName}' must have the same top-level output arity. " +
                $"Expected {e.Expected} (from first branch), but a branch has output arity {e.Actual}",
            EvalError.ExplicitParametersRequireOutput => AlgorithmValidation.ExplicitParametersRequireOutputMessage,
            EvalError.MissingOutput => FormatGenericMissingOutput(),
            EvalError.SpreadMissingOutput => FormatSpreadMissingOutput(),
            EvalError.UnresolvedImplicitParams e => FormatUnresolvedImplicitParams(e),
            EvalError.EvaluationDepthExceeded e => $"Evaluation recursion limit of {e.Limit} was exceeded",
            EvalError.EvaluationStepLimitExceeded e => $"Evaluation step limit of {e.Limit} was exceeded",
            EvalError.CollectionSizeLimitExceeded e =>
                $"Collection size limit of {e.Limit} items was exceeded; requested {e.Requested} items",
            EvalError.MaterializationLimitExceeded e =>
                $"Evaluation materialization limit of {e.Limit} items was exceeded",
            EvalError.StringSizeLimitExceeded e =>
                $"String size limit of {e.Limit} UTF-16 code units was exceeded; requested {e.Requested}",
            EvalError.StringMaterializationLimitExceeded e =>
                $"Evaluation string materialization limit of {e.Limit} UTF-16 code units was exceeded",
            EvalError.DisplayLengthLimitExceeded e =>
                $"Display output limit of {e.Limit} UTF-16 code units was exceeded",
            EvalError.EvaluationStackExhausted =>
                "Evaluation stopped to protect the host stack. "
                + "Reduce how deeply this program calls into itself, or configure a lower evaluation depth limit",
            // "Weighted units", not "nodes": the structural depth budget weighs
            // dot-call links at 3 and internal sequence joins at 0 on the evaluator
            // gates (see EvalError.AstDepthLimitExceeded), so the limit is not a
            // literal node count.
            EvalError.AstDepthLimitExceeded e =>
                $"Structural AST depth limit of {e.Limit} weighted units was exceeded: the program tree is nested too deeply to process safely. "
                + "This is separate from the runtime recursion limit on algorithm invocations. Split the program into smaller properties",
            EvalError.AstCycleDetected =>
                "The program tree contains a reference cycle, so it is not a valid KatLang program structure. "
                + "KatLang ASTs must be acyclic: shared subtrees are allowed, but no node may reach itself through its own children",
            EvalError.ModuleRegionMaterializationFailed e => FormatModuleRegionMaterializationFailed(e),
            EvalError.WithContext e => $"{e.Context}: {FormatEvalError(e.Inner)}",
            _ => error.ToString()!,
        };
    }

    /// <summary>
    /// The demand-time module diagnostics of a selected conditional branch, worded exactly
    /// as the equivalent eager load reports them: the primary diagnostic's own message first,
    /// then any further error messages on their own lines.
    /// </summary>
    private static string FormatModuleRegionMaterializationFailed(EvalError.ModuleRegionMaterializationFailed error)
    {
        var primary = error.Primary;
        var lines = new List<string> { primary.Message };
        foreach (var diagnostic in error.Diagnostics)
        {
            if (!ReferenceEquals(diagnostic, primary) && diagnostic.Severity == DiagnosticSeverity.Error)
                lines.Add(diagnostic.Message);
        }

        return string.Join(Environment.NewLine, lines);
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

    private static bool TryFormatLocalOnlyProperty(EvalError error, out string message)
    {
        message = string.Empty;

        if (error is EvalError.LocalOnlyProperty direct)
        {
            message = FormatLocalOnlyProperty(direct.ObjectDesc, direct.PropertyName, direct.Exposure, direct.RequiredParameters);
            return true;
        }

        if (error is EvalError.WithContext { Inner: EvalError.LocalOnlyProperty contextual })
        {
            message = FormatLocalOnlyProperty(contextual.ObjectDesc, contextual.PropertyName, contextual.Exposure, contextual.RequiredParameters);
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
            message = FormatDotCallUnknownName(dotContext.PropertyName, dotContext.ReceiverDescription);
            return true;
        }

        // Legacy host prose compatibility: the same semantic shape recognized
        // from a text context, rendered through the SAME builder.
        if (!TryGetTextContext(error, out var context, out var inner)
            || inner is not EvalError.UnknownName(var legacyMissingName)
            || !TryParseDotCallContext(context, out var receiverDesc, out var propertyName)
            || !string.Equals(propertyName, legacyMissingName, StringComparison.Ordinal))
            return false;

        message = FormatDotCallUnknownName(propertyName, receiverDesc);
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

        if (error is EvalError.WithContext { ErrorContext: ParameterEvaluationContext parameterContext, Inner: EvalError.MissingOutput })
        {
            message = FormatParameterMissingOutput(parameterContext.ParameterName);
            return true;
        }

        if (error is EvalError.WithContext { ErrorContext: ProgramEvaluationContext, Inner: EvalError.MissingOutput })
        {
            message = FormatProgramMissingOutput();
            return true;
        }

        if (error is EvalError.WithContext { ErrorContext: CallContext callContext, Inner: EvalError.MissingOutput })
        {
            message = FormatCallMissingOutput(callContext.CalleeDescription);
            return true;
        }

        if (error is EvalError.WithContext { ErrorContext: DotCallContext dotCallContext, Inner: EvalError.MissingOutput })
        {
            message = FormatDotCallMissingOutput(dotCallContext.ReceiverDescription, dotCallContext.PropertyName);
            return true;
        }

        // Legacy host prose compatibility: each recognized text context maps to
        // the structured shape above and renders through that shape's builder.
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
            message = FormatDotCallMissingOutput(receiverDesc, dotPropertyName);
            return true;
        }

        return false;
    }

    private static bool TryFormatArityMismatch(EvalError error, out string message)
    {
        message = string.Empty;

        if (error is EvalError.WithContext { ErrorContext: PropertyEvaluationContext propertyContext, Inner: EvalError.ArityMismatch propertyArity })
        {
            message = FormatPropertyArityMismatch(propertyArity, propertyContext.PropertyName);
            return true;
        }

        if (error is EvalError.WithContext { ErrorContext: CallContext callContext, Inner: EvalError.ArityMismatch callArity })
        {
            message = FormatCallArityMismatch(callArity, callContext.CalleeDescription);
            return true;
        }

        if (error is EvalError.WithContext { ErrorContext: DotCallContext dotCallContext, Inner: EvalError.ArityMismatch dotCallArity })
        {
            message = FormatDotCallArityMismatch(dotCallArity, dotCallContext.ReceiverDescription, dotCallContext.PropertyName);
            return true;
        }

        // Legacy host prose compatibility: each recognized text context maps to
        // the structured shape above and renders through that shape's builder.
        // (A former `Builtin '...'` arm that echoed the context verbatim had no
        // producer — builtin arity is a parser diagnostic — and was removed.)
        if (!TryGetTextContext(error, out var context, out var inner)
            || inner is not EvalError.ArityMismatch legacyArity)
            return false;

        if (TryParsePropertyContext(context, out var propertyName))
        {
            message = FormatPropertyArityMismatch(legacyArity, propertyName);
            return true;
        }

        if (TryParseCallContext(context, out var calleeDesc))
        {
            message = FormatCallArityMismatch(legacyArity, calleeDesc);
            return true;
        }

        if (TryParseDotCallContext(context, out var receiverDesc, out var dotPropertyName))
        {
            message = FormatDotCallArityMismatch(legacyArity, receiverDesc, dotPropertyName);
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

    private static bool TryFormatReduceInitialAccumulator(EvalError error, out string message)
    {
        if (FindReduceInitialAccumulatorContext(error) is { } context)
        {
            message = FormatReduceInitialAccumulator(context.RequiredParameterNames);
            return true;
        }

        message = string.Empty;
        return false;
    }

    private static ReduceInitialAccumulatorContext? FindReduceInitialAccumulatorContext(EvalError error)
    {
        while (error is EvalError.WithContext context)
        {
            if (context.ErrorContext is ReduceInitialAccumulatorContext reduceContext
                && context.Inner is EvalError.BadArity)
            {
                return reduceContext;
            }

            error = context.Inner;
        }

        return null;
    }

    /// <summary>
    /// Phrase an assignment-deconstruction binding failure against the WRITTEN
    /// pattern (<c>a, *rest, z = RHS</c>) instead of the synthetic inline
    /// helper the parser elaborated the assignment into. The context may be
    /// nested under ordinary call/property evaluation contexts, so the chain
    /// is searched.
    /// </summary>
    private static bool TryFormatDeconstructionBindingMismatch(EvalError error, out string message)
    {
        var current = error;
        while (current is EvalError.WithContext context)
        {
            if (context.ErrorContext is DeconstructionBindingContext deconstruction
                && context.Inner is EvalError.ArityMismatch mismatch)
            {
                var pattern = string.Join(", ", deconstruction.TargetDisplayNames);
                var expectation = deconstruction.HasCollectingTarget
                    ? $"at least {FormatCount(mismatch.Expected, "value")}"
                    : FormatCount(mismatch.Expected, "value");
                message = $"Assignment pattern `{pattern}` expects {expectation} from the right-hand side, but it supplied {FormatCount(mismatch.Actual, "value")}.";
                return true;
            }

            current = context.Inner;
        }

        message = string.Empty;
        return false;
    }

    /// <summary>
    /// Phrase a nested sequence-value parameter pattern's arity failure against
    /// the WRITTEN pattern (<c>F((b, c))</c> receiving three values) instead of
    /// the enclosing call's argument count. The context may be nested under
    /// ordinary call/dot-call/property contexts, so the chain is searched.
    /// </summary>
    private static bool TryFormatSequenceValuePatternBindingMismatch(EvalError error, out string message)
    {
        var current = error;
        while (current is EvalError.WithContext context)
        {
            if (context.ErrorContext is SequenceValueParameterBindingContext pattern
                && context.Inner is EvalError.ArityMismatch mismatch)
            {
                var expectation = pattern.HasCollectingItem
                    ? $"at least {FormatCount(mismatch.Expected, "value")}"
                    : FormatCount(mismatch.Expected, "value");
                message = $"Sequence-value parameter pattern `{pattern.PatternDisplayName}` expects {expectation}, but received {FormatCount(mismatch.Actual, "value")}.";
                return true;
            }

            current = context.Inner;
        }

        message = string.Empty;
        return false;
    }

    private static bool TryFormatLoopStateArityMismatch(EvalError error, out string message)
    {
        if (error is EvalError.WithContext { ErrorContext: LoopStateBindingContext context, Inner: EvalError.ArityMismatch loopMismatch })
        {
            message = FormatLoopStateArityMismatch(context, loopMismatch);
            return true;
        }

        if (error is EvalError.WithContext { ErrorContext: VariadicLoopStateBindingContext variadicContext, Inner: EvalError.ArityMismatch })
        {
            message = FormatVariadicLoopStateArityMismatch(variadicContext);
            return true;
        }

        message = string.Empty;
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

    // ── Per-shape message builders ──────────────────────────────────────────
    // ONE builder per semantic error shape. The structured-context branches and
    // the legacy host-prose compatibility branches above both funnel through
    // these, so the two construction paths can never render one shape
    // differently (pinned by KatLangErrorLegacyContextTests). Recognition of a
    // legacy prose context yields the shape's PAYLOAD (names, descriptions) and
    // nothing else: a builder never re-parses a message.

    /// <summary>
    /// The ONE spelling of "this receiver has no such member", shared by the
    /// closed-list runtime failure (<see cref="FormatDotCallUnknownName"/>, where
    /// the fallback found no callable either) and the receiver-aware provenance
    /// of an inferred implicit parameter
    /// (<see cref="FormatDotMemberFallbackInference"/>, where the fallback name was
    /// promoted instead). Both describe the same dot-edge fact; they differ only
    /// in what the lexical fallback then did.
    /// </summary>
    private static string FormatDotMemberNotFound(string propertyName, string receiverDesc)
        => $"Property '{propertyName}' was not found on `{receiverDesc}`";

    private static string FormatDotCallUnknownName(string propertyName, string receiverDesc)
        => $"{FormatDotMemberNotFound(propertyName, receiverDesc)}, and no visible algorithm or property named '{propertyName}' can be used with `{receiverDesc}` as the first argument.";

    /// <summary>
    /// The receiver-aware explanation of an implicit parameter that came from a
    /// missing member on a statically known receiver: the member is absent, so
    /// the dot edge's lexical fallback was the selected resolution, and its
    /// callable name is what the front end promoted (the promotion itself is
    /// stated by the surrounding message). <paramref name="at"/> names the member
    /// token when the error's own position does not already point there.
    /// </summary>
    private static string FormatDotMemberFallbackInference(string memberName, string receiverDesc, SourceSpan? at)
    {
        var location = at is { } span ? $" at [{span.StartLineNumber}:{span.StartColumn}]" : string.Empty;
        return $"{FormatDotMemberNotFound(memberName, receiverDesc)}{location}, so the dotted call fell back to a lexical callable named '{memberName}'.";
    }

    /// <summary>
    /// The <c>string</c> intrinsic renders receiver-only because it is a dot-only
    /// value conversion (no <c>.string</c> property reference).
    /// </summary>
    private static string FormatDotCallMissingOutput(string receiverDesc, string propertyName)
        => string.Equals(propertyName, "string", StringComparison.Ordinal)
            ? FormatReferenceMissingOutput(receiverDesc)
            : FormatReferenceMissingOutput($"{receiverDesc}.{propertyName}");

    private static string FormatPropertyArityMismatch(EvalError.ArityMismatch arity, string propertyName)
        => FormatArityMismatch(arity, propertyName, preferPropertyName: true);

    /// <summary>
    /// Signature first, exactly as the dot-call arm: a builtin value demand inside a call
    /// (`F(v) = v + sum`) carries the Lean-aligned placeholder <c>Expected = 0</c> beside
    /// its real signature, and rendering the raw pair read "Expected 0 parameters, but was
    /// called with 0 arguments". A located error without a signature keeps the generic text.
    /// </summary>
    private static string FormatCallArityMismatch(EvalError.ArityMismatch arity, string calleeDesc)
        => arity.Signature is not null
            ? FormatArityMismatch(arity)
            : arity.Span is null
                ? FormatArityMismatch(arity, calleeDesc, preferPropertyName: IsSimpleIdentifier(calleeDesc))
                : FormatGenericArityMismatch(arity.Expected, arity.Actual);

    /// <summary>
    /// Signature first: builtin arity errors deliberately carry the Lean-aligned
    /// placeholder <c>Expected = 0</c> beside their real signature, so rendering
    /// raw <c>Expected</c> would claim "expects 0 parameters". Signatureless
    /// structural property errors keep the receiver-specific fallback.
    /// </summary>
    private static string FormatDotCallArityMismatch(EvalError.ArityMismatch arity, string receiverDesc, string propertyName)
        => arity.Signature is not null
            ? FormatArityMismatch(arity)
            : arity.Span is null
                ? $"Property '{propertyName}' on `{receiverDesc}` expects {FormatCount(arity.Expected, "parameter")}, but was called with {FormatCount(arity.Actual, "argument")}."
                : FormatGenericArityMismatch(arity.Expected, arity.Actual);

    private static string FormatNamedArityMismatch(string calleeDesc, int expected, int actual, bool preferPropertyName)
    {
        var subject = preferPropertyName
            ? $"Property '{calleeDesc}'"
            : $"Algorithm `{calleeDesc}`";
        return $"{subject} expects {FormatCount(expected, "parameter")}, but was called with {FormatCount(actual, "argument")}.";
    }

    private static string FormatArityMismatch(EvalError.ArityMismatch arity)
        => arity.Signature is { } signature
            ? CallableSignatureDiagnostics.FormatBadArity(signature, WrittenArgumentCount(arity, signature))
            : FormatGenericArityMismatch(arity.Expected, arity.Actual);

    /// <summary>
    /// The number of WRITTEN arguments a signature-worded arity message reports. The
    /// Lean-modeled payload of a flat fixed user call that received too few slots is the
    /// VALUE-tier view (`Expected` = the parameters still to bind on the value channel,
    /// `Actual` = the value slots), which leaves out every slot bound only on the algorithm
    /// channel — an output-less algorithm argument — so rendering `Actual` beside the
    /// signature's full parameter count undercounted the call (`R(a, b) = b` with
    /// `R(Obj)` said "called with 0 arguments"). The payload's difference is the number
    /// of parameters no slot reached, so the written count is the signature's parameter
    /// count minus it. Applied only where that view can arise: a user callable's fixed
    /// flat parameter list with `Expected` below its parameter count; every other payload
    /// (families, collecting parameters, builtins, too many slots) already counts written
    /// slots and is rendered as is.
    /// </summary>
    private static int WrittenArgumentCount(EvalError.ArityMismatch arity, CallableSignature signature)
    {
        var facts = signature.ArityFacts;
        var fixedFlatUserList = signature.Parameters.Count > 0
            && signature.Parameters.All(static parameter => parameter.Source != CallableParameterSource.Builtin)
            && facts.MaxTopLevelArgumentCount == facts.MinTopLevelArgumentCount
            && facts.MinTopLevelArgumentCount == signature.FlattenedParameterCount;
        if (!fixedFlatUserList || arity.Expected >= signature.FlattenedParameterCount || arity.Actual > arity.Expected)
            return arity.Actual;

        return signature.FlattenedParameterCount - (arity.Expected - arity.Actual);
    }

    private static string FormatArityMismatch(EvalError.ArityMismatch arity, string calleeDesc, bool preferPropertyName)
        => arity.Signature is { } signature
            ? CallableSignatureDiagnostics.FormatBadArity(signature, WrittenArgumentCount(arity, signature))
            : FormatNamedArityMismatch(calleeDesc, arity.Expected, arity.Actual, preferPropertyName);

    /// <summary>
    /// The two STRUCTURED not-callable descriptions the evaluators share with Lean
    /// (<c>param(name)</c>, <c>num(value)</c>) are rendered in KatLang terms — the payload
    /// is unchanged, only its presentation; every other description names the expression
    /// shape as before.
    /// </summary>
    private static string FormatNotAnAlgorithm(string description)
    {
        if (description.StartsWith("param(", StringComparison.Ordinal) && description.EndsWith(')'))
        {
            var name = description[6..^1];
            return $"Parameter '{name}' is not callable here: it is bound to a value, not to an algorithm. Pass an algorithm for '{name}', or read it as a value.";
        }

        if (description.StartsWith("num(", StringComparison.Ordinal) && description.EndsWith(')'))
            return $"The number {description[4..^1]} is not callable.";

        return $"Not an algorithm: {description}";
    }

    private static string FormatPropertyMissingOutput(string propertyName)
        => $"Property '{propertyName}' has no defined output.\nAdd an output expression to '{propertyName}', or use `()` if the empty sequence value was intended. To use one of its properties, write `{propertyName}.X`.";

    /// <summary>
    /// The argument bound to a parameter had no output when the parameter was read for
    /// its value: blame the argument, never the callee (whose own call context still
    /// encloses this message).
    /// </summary>
    private static string FormatParameterMissingOutput(string parameterName)
        => $"Parameter '{parameterName}' has no defined output: the argument bound to it is an algorithm without an output expression.\nAdd an output expression to that argument, or use `()` if the empty sequence value was intended.";

    private static string FormatParameterList(IReadOnlyList<string> names)
        => names.Count == 1
            ? $"parameter '{names[0]}'"
            : $"parameters {string.Join(", ", names.Select(static name => $"'{name}'"))}";

    private static string FormatLocalOnlyProperty(string objectDesc, string propertyName, PropertyExposure exposure, IReadOnlyList<string>? requiredParameters)
        => exposure switch
        {
            PropertyExposure.LocalOnlyCapturedAncestorParameters when requiredParameters is { Count: > 0 } =>
                $"Property '{propertyName}' on `{objectDesc}` is local-only because it depends on {FormatParameterList(requiredParameters)}, and a required owner activation is unavailable in this lexical context.",
            PropertyExposure.LocalOnlyCapturedAncestorParameters =>
                $"Property '{propertyName}' on `{objectDesc}` is local-only because it depends on parameter(s) owned by the enclosing algorithm.",
            PropertyExposure.LocalOnlyConditionalAlgorithm =>
                $"Property '{propertyName}' on `{objectDesc}` is local-only because properties defined inside conditional algorithms are not publicly visible.",
            _ => $"Property '{propertyName}' on `{objectDesc}` is local-only.",
        };

    private static string FormatReferenceMissingOutput(string referenceDesc)
        => IsSimpleIdentifier(referenceDesc)
            ? FormatPropertyMissingOutput(referenceDesc)
            : $"The value `{referenceDesc}` has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To use one of its properties, access it explicitly.";

    private static string FormatCallMissingOutput(string calleeDesc)
        => $"Cannot call '{calleeDesc}' because it has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To call one of its properties, use property access instead.";

    private static string FormatGenericMissingOutput()
        => $"Algorithm has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended.";

    private static string FormatProgramMissingOutput()
        => RunResult.NoProgramOutput.DefaultMessage;

    private static string FormatSpreadMissingOutput()
        => "Cannot spread because the spread operand has no defined output.\nUse `()*` if you intended to spread zero items.";

    private static string FormatGenericArityMismatch(int expected, int actual)
        => $"Expected {FormatCount(expected, "parameter")}, but was called with {FormatCount(actual, "argument")}.";

    private static string FormatVariadicArityMismatch(EvalError.VariadicArityMismatch error)
        => error.Signature is { } signature
            ? $"Callable `{signature.DisplayText}` expects at least {FormatCount(error.ExpectedMinimum, "item")}, but received {FormatCount(error.Actual, "item")}."
            : $"Property `{error.CalleeName}` expects at least {FormatCount(error.ExpectedMinimum, "item")}, but received {FormatCount(error.Actual, "item")}.";

    private static string FormatLoopStateArityMismatch(LoopStateBindingContext context, EvalError.ArityMismatch mismatch)
    {
        // The inner mismatch's Expected is the numeric source of truth (the
        // binder-computed top-level state-slot count); the context's names are
        // the matching top-level parameter display labels, so a patterned step
        // `Step((x, y))` reports ONE state value for the ONE pattern "(x, y)".
        // When the counts differ (a top-level collecting pattern's underflow
        // reports only the fixed slots as expected), omit the numeric parameter
        // count so the displayed count and displayed list never disagree.
        var expected = mismatch.Expected;
        var names = context.StepParameterNames;
        var parameterDetail = names.Count == 0
            ? "because the step has no parameters"
            : names.Count == expected
                ? $"for {FormatCount(names.Count, "parameter")} {FormatQuotedList(names)}"
                : $"for parameters {FormatQuotedList(names)}";

        return $"`{context.LoopName}` step expects {FormatCount(expected, "state value")} {parameterDetail}, but the current loop state has {FormatCount(context.ActualStateValueCount, "state value")}. Loop state values are bound positionally to the step's implicit parameters. If this is a nested step, remember that names already bound by an enclosing algorithm are captured, not added as step parameters; use a distinct state-slot name such as `candidate` when threading an outer value through the loop state.";
    }

    private static string FormatVariadicLoopStateArityMismatch(VariadicLoopStateBindingContext context)
        => $"`{context.LoopName}` variadic step expects at least {FormatCount(context.ExpectedMinimumStateValueCount, "state value")} for fixed parameter(s) {FormatQuotedList(context.StepParameterNames)}, but the current loop state has {FormatCount(context.ActualStateValueCount, "state value")}. A collecting loop parameter collects the remaining state values as an exact list with `*name`; ordinary implicit parameters still bind one state value each.";

    private static string FormatReduceInitialAccumulator(IReadOnlyList<string> requiredParameterNames)
    {
        var parameterDetail = requiredParameterNames.Count == 0
            ? "The last argument cannot be evaluated as the starting accumulator."
            : $"The last argument is an algorithm that still needs {FormatQuotedList(requiredParameterNames)}, so it cannot be evaluated as the starting accumulator.";

        return $"`reduce` is `reduce(collection, reducer, initial)`: the last argument must be an initial accumulator value. {parameterDetail} If that algorithm is the reducer, add an initial accumulator after it, for example `reduce(..., reducer, 0)`.";
    }

    private static string FormatCount(int count, string singularNoun)
        => count == 1 ? $"1 {singularNoun}" : $"{count} {singularNoun}s";

    private static string FormatQuotedList(IReadOnlyList<string> values)
        => values.Count switch
        {
            0 => string.Empty,
            1 => $"'{values[0]}'",
            2 => $"'{values[0]}' and '{values[1]}'",
            _ => string.Join(", ", values.Take(values.Count - 1).Select(value => $"'{value}'")) + $", and '{values[^1]}'",
        };

    /// <summary>
    /// Display heuristic: whether a callee/reference DESCRIPTION reads as one bare
    /// name (so a diagnostic may say "Property 'X'") rather than as a rendered
    /// expression. Shape-only via the lexer's one identifier character policy —
    /// deliberately no keyword exclusion, because a host-built AST may legally
    /// name a property with a keyword spelling and its description should still
    /// render as that name.
    /// </summary>
    private static bool IsSimpleIdentifier(string value)
        => !string.IsNullOrEmpty(value) && Lexer.IsIdentifierShaped(value);

    /// <summary>
    /// When the ONE unresolved parameter was the misspelled member of a dot edge
    /// on a statically known receiver, the message leads with that receiver-aware
    /// fact (the member is absent, the dotted call fell back to a lexical
    /// callable of that name) before the ordinary promotion/arity sentences, in
    /// the order the reader needs them. Several unresolved names keep the
    /// enumerating message and get their receiver-aware notes appended per name
    /// (<see cref="AppendInferredImplicitParameterNotes"/>).
    /// </summary>
    private static string FormatUnresolvedImplicitParams(EvalError.UnresolvedImplicitParams e, int providedArgumentCount = 0)
    {
        var count = e.ParamNames.Count;
        var dotMemberNote = count == 1 ? SingleDotMemberOriginNote(e) : null;
        var nameVerb = count == 1 ? "does" : "do";
        var resolutionTarget = count == 1
            ? "a property or other visible name"
            : "properties or other visible names";
        var interpretation = count == 1 ? "an implicit parameter" : "implicit parameters";
        var callerSentence = count == 1 ? "Its value is provided by the caller." : "Their values are provided by the caller.";
        var argWord = count == 1 ? "argument" : "arguments";
        var subject = count == 1
            ? dotMemberNote is null ? $"Identifier '{e.ParamNames[0]}'" : "That name"
            : "Identifiers " + string.Join(", ", e.ParamNames.Take(count - 1).Select(n => $"'{n}'")) + $" and '{e.ParamNames[^1]}'";
        var preface = dotMemberNote is null
            ? string.Empty
            : FormatDotMemberFallbackInference(dotMemberNote.Name, dotMemberNote.DotMemberOrigin!.ReceiverDescription, at: null) + " ";
        var missingArgumentSentence = providedArgumentCount == 0
            ? $"No {(count == 1 ? "argument was" : "arguments were")} provided"
            : $"Only {providedArgumentCount} {(providedArgumentCount == 1 ? "argument was" : "arguments were")} provided";
        return $"{preface}{subject} {nameVerb} not resolve to {resolutionTarget} here, so KatLang interprets {(count == 1 ? "it" : "them")} as {interpretation}. {callerSentence} {missingArgumentSentence}, so the program cannot be executed (expected {count} {argWord}, got {providedArgumentCount}).";
    }

    /// <summary>
    /// The provenance note of a single-parameter unresolved-implicit-parameter
    /// error whose parameter came from a missing member on a statically known
    /// receiver; <c>null</c> when the parameter has no such origin.
    /// </summary>
    private static ImplicitParameterProvenance? SingleDotMemberOriginNote(EvalError.UnresolvedImplicitParams e)
    {
        if (e.ParamNames.Count != 1 || e.InferredImplicitParameters is not { } notes)
            return null;

        foreach (var note in notes)
        {
            if (note.DotMemberOrigin is not null && string.Equals(note.Name, e.ParamNames[0], StringComparison.Ordinal))
                return note;
        }

        return null;
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
