using System.Text;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;

namespace KatLang;

internal readonly record struct DisplayOptions(int? Decimals, int MaxDisplayLength)
{
    public static DisplayOptions Default { get; } = new(null, EvaluationLimits.MaxSupportedDisplayLength);
}

/// <summary>
/// Bounded display sink. Rendering appends incrementally and checks BEFORE every append,
/// so the forbidden output is never constructed: the writer stops at the first append that
/// would cross the limit and reports it, rather than building an oversized string and
/// measuring it afterwards.
///
/// <para>Lengths are UTF-16 code units, matching <see cref="string.Length"/>, the source
/// span column model, and actual CLR string storage. EVERY append is charged its actual
/// length, including the platform newline between top-level rows, so the returned string
/// can never exceed the limit — an exact bound on the real output is worth more than a
/// canonical abstraction of it. The consequence is that a many-row rendering can cross the
/// boundary at a different row on a CRLF host (2 units per separator) than on an LF host
/// (1 unit); both return a complete bounded overflow indication rather than partial text.</para>
///
/// <para>The replacement marker is also bounded. The complete limit message is returned
/// when it fits; otherwise a complete one-character marker is returned when possible,
/// and a zero-length limit returns the empty string.</para>
/// </summary>
internal sealed class BoundedDisplayWriter(int limit) : IDisplaySink
{
    private readonly StringBuilder _builder = new();
    private long _charged;

    /// <summary>True once an append was refused; no further output is produced.</summary>
    public bool LimitExceeded { get; private set; }

    public bool Append(string text)
    {
        if (LimitExceeded) return false;
        if (text.Length > limit - _charged)
        {
            LimitExceeded = true;
            return false;
        }

        _charged += text.Length;
        _builder.Append(text);
        return true;
    }

    /// <summary>
    /// Appends a repeated character (formatter indentation), charged one unit
    /// per repetition like every other append — without materializing an
    /// intermediate string.
    /// </summary>
    public bool Append(char c, int count)
    {
        if (LimitExceeded) return false;
        if (count > limit - _charged)
        {
            LimitExceeded = true;
            return false;
        }

        _charged += count;
        _builder.Append(c, count);
        return true;
    }

    /// <summary>Writes the platform newline between top-level rows, charged its actual length.</summary>
    public bool AppendRowSeparator() => Append(Environment.NewLine);

    public override string ToString() => _builder.ToString();
}

/// <summary>
/// Discriminated-union result of a KatLang parse+evaluate run.
/// Pattern-match on <see cref="Success"/>, <see cref="NoProgramOutput"/>,
/// <see cref="ParseFailure"/>, or <see cref="EvalFailure"/>.
/// </summary>
public abstract record RunResult
{
    private RunResult() { }

    internal DisplayOptions DisplayOptions { get; init; } = DisplayOptions.Default;

    /// <summary>True when the run succeeded.</summary>
    public bool IsSuccess => this is Success;

    /// <summary>True when the run completed without program output.</summary>
    public bool IsNoProgramOutput => this is NoProgramOutput;

    /// <summary>True when the run failed with parse or evaluation errors.</summary>
    public bool IsFailure => this is ParseFailure or EvalFailure;

    /// <summary>Parse and evaluation succeeded.</summary>
    public sealed record Success(
        Algorithm Root,
        Result Value,
        IReadOnlyList<decimal> Atoms) : RunResult
    {
        internal int EmittedCount { get; init; } = Value.ValueCount();

        /// <summary>
        /// The separately produced top-level output rows, exactly as canonical
        /// display derives them. <see cref="Value"/> alone cannot represent the
        /// root-output boundary: a program emitting two rows (<c>A()</c>
        /// newline <c>B()</c>) and a program emitting one sequence value
        /// (<c>(A() B())</c>) can produce the SAME structural <see cref="Value"/>
        /// — this view keeps them distinguishable. Zero rows means the program
        /// evaluated successfully with empty output (for example a spread
        /// contributing zero items); one row is the whole <see cref="Value"/>
        /// (an explicitly emitted empty string, empty sequence, or empty list
        /// each stay one visible row); several rows are the value's top-level
        /// items in emission order.
        ///
        /// <para>The view is read-only over finished values and is derived on
        /// access without caching: the multi-row case returns the value's
        /// existing backing list, the single-row case allocates one
        /// single-element wrapper, and the zero-row case returns an empty
        /// singleton.</para>
        ///
        /// <para>The evaluator's exact emitted-slot count is used here as a
        /// zero/one/many discriminator, not as this view's indexable count. A
        /// projected expression may emit several slots inside one combined
        /// top-level display row, so <c>OutputRows.Count</c> need not equal that
        /// internal arity count. <see cref="OutputRows"/> is authoritative for
        /// presentation.</para>
        /// </summary>
        public IReadOnlyList<Result> OutputRows => EmittedCount switch
        {
            0 => Array.Empty<Result>(),
            1 => Array.AsReadOnly([Value]),
            _ => Value.ToItems(),
        };
    }

    /// <summary>Parse and evaluation completed, but the top-level program did not define output.</summary>
    public sealed record NoProgramOutput(
        Algorithm Root,
        KatLangError Diagnostic) : RunResult
    {
        public const string DefaultMessage =
            "No output defined.\n" +
            "This program defines properties, but does not specify what to return.\n" +
            "Add an output expression, or use `()` if the empty sequence value was intended.";

        public string Message => Diagnostic.Message;
    }

    /// <summary>Parsing failed — no executable root was produced.</summary>
    public sealed record ParseFailure(
        IReadOnlyList<KatLangError> Errors) : RunResult;

    /// <summary>Evaluation failed after a successful parse.</summary>
    public sealed record EvalFailure(
        Algorithm Root,
        IReadOnlyList<KatLangError> Errors) : RunResult;

    /// <summary>
    /// Returns a human-readable display string.
    /// On success: multiple top-level outputs are separated for readability;
    /// sequence values keep parentheses.
    /// On failure: newline-joined error messages.
    ///
    /// Rendering is strictly bounded (see <see cref="BoundedDisplayWriter"/>): the returned
    /// string never exceeds the effective <see cref="EvaluationLimits.MaxDisplayLength"/>.
    /// On overflow the partial rendering is discarded. The complete limit message is used
    /// when it fits, otherwise the complete <c>…</c> marker is used when one UTF-16 unit
    /// fits, otherwise the result is empty. Structured values and diagnostics are unchanged;
    /// truncated previews for editor UI belong in a separate, explicitly named API.
    /// </summary>
    public string ToDisplayString() => this switch
    {
        Success s => FormatSuccess(s),
        NoProgramOutput n => FormatText(n.Message, n.DisplayOptions.MaxDisplayLength),
        ParseFailure p => FormatErrors(p.Errors, p.DisplayOptions.MaxDisplayLength),
        EvalFailure e => FormatErrors(e.Errors, e.DisplayOptions.MaxDisplayLength),
        _ => throw new InvalidOperationException("Unknown RunResult variant."),
    };

    private static string FormatSuccess(Success success)
    {
        var writer = new BoundedDisplayWriter(success.DisplayOptions.MaxDisplayLength);
        AppendSuccessRows(success.OutputRows, success.DisplayOptions, writer);
        return Finish(writer, success.DisplayOptions.MaxDisplayLength);
    }

    /// <summary>
    /// Canonical success rendering shared byte-for-byte by
    /// <see cref="ToDisplayString"/> and the <c>exact</c> output formatter
    /// (the <c>exact</c> output formatter): platform-newline row
    /// separators over <see cref="Success.OutputRows"/>, each row in canonical
    /// inline form.
    /// </summary>
    internal static bool AppendSuccessRows(
        IReadOnlyList<Result> rows,
        DisplayOptions displayOptions,
        BoundedDisplayWriter writer)
    {
        for (var i = 0; i < rows.Count; i++)
        {
            if (i > 0 && !writer.AppendRowSeparator()) return false;
            if (!AppendValue(rows[i], displayOptions, writer)) return false;
        }

        return true;
    }

    /// <summary>
    /// Errors are rendered through the same configured bounded writer.
    /// The structured diagnostics are never dropped or rewritten to fit — only the final
    /// public rendering surface is bounded. Shared with every output formatter,
    /// so failures render identically regardless of the selected formatter.
    /// </summary>
    internal static string FormatErrors(IReadOnlyList<KatLangError> errors, int limit)
    {
        var writer = new BoundedDisplayWriter(limit);

        for (var i = 0; i < errors.Count; i++)
        {
            if (i > 0 && !writer.AppendRowSeparator()) break;
            if (!writer.Append(errors[i].ToString())) break;
        }

        return Finish(writer, limit);
    }

    internal static string FormatText(string text, int limit)
    {
        var writer = new BoundedDisplayWriter(limit);
        writer.Append(text);
        return Finish(writer, limit);
    }

    internal static string Finish(BoundedDisplayWriter writer, int limit)
    {
        if (!writer.LimitExceeded)
            return writer.ToString();

        var message = KatLangError.FromEvalError(new EvalError.DisplayLengthLimitExceeded(limit)).Message;
        if (message.Length <= limit)
            return message;

        const string marker = "…";
        return marker.Length <= limit ? marker : string.Empty;
    }

    /// <summary>
    /// Appends one value's canonical display form. The implementation is the
    /// shared formatter-neutral iterative renderer
    /// (<see cref="ValueTextRenderer.AppendValue"/>) with the raw string
    /// strategy. Presentation formatters reuse the renderer by supplying their
    /// own string-leaf policy; canonical display has no dependency on formatter
    /// types or options. See the depth/breadth traversal note on
    /// <see cref="Result"/>.
    /// </summary>
    internal static bool AppendValue(Result value, DisplayOptions displayOptions, BoundedDisplayWriter writer)
        => ValueTextRenderer.AppendValue(value, displayOptions, RawStringTextPolicy.Instance, writer);
}

/// <summary>
/// Public façade for KatLang: parse and evaluate in one step.
/// Hides internal details such as <see cref="Expr.AlgorithmExpr"/> wrapping.
/// For advanced/internal use, <see cref="Parser"/> and <see cref="Evaluator"/> remain available.
/// </summary>
public static class KatLangEngine
{
    private const string DisplayDecimalsPropertyName = "DisplayDecimals";
    private const int MaxDisplayDecimals = 99;

    /// <summary>
    /// Parse and evaluate KatLang source code, returning a unified <see cref="RunResult"/>.
    /// <see cref="RunOptions.SourceProcessingCancellationToken"/> applies through front-end source
    /// and module processing only; evaluation is governed separately by
    /// <see cref="RunOptions.EvaluationLimits"/> and cooperatively cancelled by
    /// <see cref="RunOptions.EvaluationCancellationToken"/>.
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// The configured source-processing token was cancelled during front-end processing,
    /// or the configured evaluation token was cancelled before or during evaluation
    /// (including the additional-error evaluation performed for evaluable load
    /// failures). Cancellation is never converted into a <see cref="RunResult"/>.
    /// </exception>
    /// <exception cref="InvalidOperationException">
    /// <see cref="RunOptions.HostOperations"/> contains an ASYNCHRONOUS operation,
    /// which this synchronous entry point cannot suspend for — use
    /// <see cref="RunAsync"/>. Thrown before any parsing or evaluation.
    /// </exception>
    public static RunResult Run(string source, RunOptions? options = null)
    {
        var hostOperations = options?.HostOperations;
        // Fail fast on a configuration this synchronous entry point can never honor:
        // an asynchronous host operation completes only by suspending evaluation.
        if (hostOperations?.ContainsAsynchronousOperations == true)
        {
            throw new InvalidOperationException(
                "RunOptions.HostOperations contains an asynchronous operation; use KatLangEngine.RunAsync " +
                "(or an async convenience entry point), or configure only synchronous host operations.");
        }

        var limits = options?.EvaluationLimits ?? EvaluationLimits.Default;
        var evaluationCancellationToken = options?.EvaluationCancellationToken ?? default;
        var diagnosticDisplayOptions = new DisplayOptions(null, limits.EffectiveMaxDisplayLength);
        var frontEndResult = FrontEndPipeline.Process(source, options);

        if (frontEndResult.HasErrors)
        {
            return FrontEndFailureResult(
                frontEndResult,
                diagnosticDisplayOptions,
                frontEndResult.CanEvaluateAfterLoadErrors
                    ? EvaluateForAdditionalErrors(
                        frontEndResult.ElaboratedRoot,
                        options?.EvaluationLimits,
                        hostOperations,
                        evaluationCancellationToken)
                    : []);
        }

        var zeroArgPropertyResultCache = new RunScopedZeroArgPropertyResultCache();

        // One budget for the whole run: the program output and the DisplayDecimals
        // property are evaluated under the same run-scoped budget, so neither can reset
        // or escape the other's accounting.
        var evalResult = Evaluator.RunCountedWithTopLevelProperty(
            new Expr.AlgorithmExpr(frontEndResult.ElaboratedRoot),
            DisplayDecimalsPropertyName,
            zeroArgPropertyResultCache,
            options?.EvaluationLimits,
            hostOperations,
            evaluationCancellationToken);

        return ProjectEvaluationOutcome(
            frontEndResult, evalResult, limits, diagnosticDisplayOptions, evaluationCancellationToken);
    }

    /// <summary>
    /// Asynchronous counterpart of <see cref="Run(string, RunOptions?)"/> with identical
    /// result and error projection semantics.
    ///
    /// <para>Parsing, module loading, and front-end elaboration remain SYNCHRONOUS —
    /// they run inline on the calling thread before the returned task's first
    /// suspension opportunity, governed as before by
    /// <see cref="RunOptions.SourceProcessingCancellationToken"/> and
    /// <see cref="RunOptions.SourceProcessingLimits"/>. Evaluation goes through the
    /// evaluator's async surface: unless <see cref="RunOptions.HostOperations"/>
    /// contains an ASYNCHRONOUS operation, the whole run completes synchronously on
    /// the calling thread. This method never schedules work onto another thread and
    /// never yields artificially — thread placement and scheduling remain the host's
    /// responsibility. With asynchronous host operations configured, an incomplete
    /// host awaitable genuinely suspends the run and resumes it — exactly once, at the
    /// same point — when the operation completes (see <see cref="HostOperation"/> for
    /// the full contract).</para>
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// Same cancellation contract as <see cref="Run(string, RunOptions?)"/>; as with any
    /// async API, the exception is delivered through the returned task.
    /// </exception>
    public static async Task<RunResult> RunAsync(string source, RunOptions? options = null)
    {
        // MIRROR OF Run(string, RunOptions?) — keep in lock-step; only the evaluation
        // calls are awaited, through the evaluator's async entry points.
        var hostOperations = options?.HostOperations;
        var limits = options?.EvaluationLimits ?? EvaluationLimits.Default;
        var evaluationCancellationToken = options?.EvaluationCancellationToken ?? default;
        var diagnosticDisplayOptions = new DisplayOptions(null, limits.EffectiveMaxDisplayLength);
        var frontEndResult = FrontEndPipeline.Process(source, options);

        if (frontEndResult.HasErrors)
        {
            return FrontEndFailureResult(
                frontEndResult,
                diagnosticDisplayOptions,
                frontEndResult.CanEvaluateAfterLoadErrors
                    ? await EvaluateForAdditionalErrorsAsync(
                        frontEndResult.ElaboratedRoot,
                        options?.EvaluationLimits,
                        hostOperations,
                        evaluationCancellationToken).ConfigureAwait(false)
                    : []);
        }

        // An asynchronous host-operation configuration routes the run through the
        // evaluator's async twin path, which awaits the property seam — so it gets the
        // async-capable run-scoped cache. Every other configuration (including purely
        // synchronous host operations) keeps the ordinary cache and with it the
        // synchronous fast path.
        IZeroArgPropertyResultCache zeroArgPropertyResultCache =
            hostOperations?.ContainsAsynchronousOperations == true
                ? new RunScopedAsyncZeroArgPropertyResultCache()
                : new RunScopedZeroArgPropertyResultCache();

        // One budget for the whole run, exactly as in Run.
        var evalResult = await Evaluator.RunCountedWithTopLevelPropertyAsync(
            new Expr.AlgorithmExpr(frontEndResult.ElaboratedRoot),
            DisplayDecimalsPropertyName,
            zeroArgPropertyResultCache,
            options?.EvaluationLimits,
            hostOperations,
            evaluationCancellationToken).ConfigureAwait(false);

        return ProjectEvaluationOutcome(
            frontEndResult, evalResult, limits, diagnosticDisplayOptions, evaluationCancellationToken);
    }

    /// <summary>
    /// Shared front-end failure projection for <see cref="Run"/> and
    /// <see cref="RunAsync"/>: the front end's error diagnostics plus any
    /// additional-error evaluation results, in that order.
    /// </summary>
    private static RunResult.ParseFailure FrontEndFailureResult(
        FrontEndResult frontEndResult,
        DisplayOptions diagnosticDisplayOptions,
        IReadOnlyList<KatLangError> additionalEvaluationErrors)
    {
        var parseErrors = frontEndResult.Diagnostics
            .Where(d => d.Severity == DiagnosticSeverity.Error)
            .Select(KatLangError.FromDiagnostic)
            .ToList();
        parseErrors.AddRange(additionalEvaluationErrors);

        return new RunResult.ParseFailure(parseErrors)
        {
            DisplayOptions = diagnosticDisplayOptions,
        };
    }

    /// <summary>
    /// Shared post-evaluation projection for <see cref="Run"/> and
    /// <see cref="RunAsync"/>: error classification, DisplayDecimals handling, bounded
    /// host-atom projection, and success construction — byte-for-byte the former inline
    /// body of <see cref="Run"/>.
    /// </summary>
    private static RunResult ProjectEvaluationOutcome(
        FrontEndResult frontEndResult,
        EvalResult<Evaluator.CountedRootProgramResult> evalResult,
        EvaluationLimits limits,
        DisplayOptions diagnosticDisplayOptions,
        CancellationToken evaluationCancellationToken)
    {
        if (evalResult.IsError)
        {
            var evalError = KatLangError.FromEvalError(evalResult.Error);
            if (IsTopLevelNoProgramOutput(evalResult.Error))
                return new RunResult.NoProgramOutput(frontEndResult.ElaboratedRoot, evalError)
                {
                    DisplayOptions = diagnosticDisplayOptions,
                };

            var evalErrors = new[] { evalError };
            return new RunResult.EvalFailure(frontEndResult.ElaboratedRoot, evalErrors)
            {
                DisplayOptions = diagnosticDisplayOptions,
            };
        }

        // The run's configured rendering limit travels with the result, so ToDisplayString
        // stays bounded without RunResult having to reach back for the RunOptions.
        var displayOptionsResult = CreateDisplayOptions(
            evalResult.Value.TopLevelProperty,
            FindTopLevelPropertyDeclarationSpan(frontEndResult.ElaboratedRoot, DisplayDecimalsPropertyName),
            limits.EffectiveMaxDisplayLength);
        if (displayOptionsResult.IsError)
        {
            return new RunResult.EvalFailure(
                frontEndResult.ElaboratedRoot,
                [KatLangError.FromEvalError(displayOptionsResult.Error)])
            {
                DisplayOptions = diagnosticDisplayOptions,
            };
        }

        // Host-atom projection is part of the run's materialization accounting: it opens
        // BOTH sequence and list boundaries recursively, so a modest result value can
        // project into an enormous host list. Bounding it here means a successful
        // evaluation cannot be followed by an unbounded allocation on the way out.
        var hostAtomLimit = limits.EffectiveMaxCollectionItems;
        var projected = evalResult.Value.Output.Value.TryToHostAtoms(hostAtomLimit, out var hostAtoms);
        evaluationCancellationToken.ThrowIfCancellationRequested();
        if (!projected)
        {
            return new RunResult.EvalFailure(
                frontEndResult.ElaboratedRoot,
                [KatLangError.FromEvalError(new EvalError.CollectionSizeLimitExceeded(hostAtomLimit, hostAtomLimit + 1L))])
            {
                DisplayOptions = diagnosticDisplayOptions,
            };
        }

        return new RunResult.Success(
            frontEndResult.ElaboratedRoot,
            evalResult.Value.Output.Value,
            hostAtoms)
        {
            EmittedCount = evalResult.Value.Output.EmittedCount,
            DisplayOptions = displayOptionsResult.Value,
        };
    }

    /// <summary>
    /// Parse and evaluate, returning the flat list of atoms on success.
    /// Throws <see cref="KatLangException"/> on parse or evaluation failure.
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// The configured source-processing token was cancelled during front-end processing,
    /// or the configured evaluation token was cancelled before or during evaluation —
    /// cancellation propagates and is never wrapped in a <see cref="KatLangException"/>.
    /// </exception>
    public static IReadOnlyList<decimal> EvaluateToAtoms(string source, RunOptions? options = null)
    {
        return Run(source, options) switch
        {
            RunResult.Success s => s.Atoms,
            RunResult.NoProgramOutput n => throw new KatLangException([n.Diagnostic]),
            RunResult.ParseFailure p => throw new KatLangException(p.Errors),
            RunResult.EvalFailure e => throw new KatLangException(e.Errors),
            _ => throw new InvalidOperationException("Unknown RunResult variant."),
        };
    }

    /// <summary>
    /// Asynchronous counterpart of <see cref="EvaluateToAtoms"/>: a thin projection
    /// over <see cref="RunAsync"/> with identical success and failure semantics.
    /// Like <see cref="RunAsync"/>, it completes synchronously unless
    /// <see cref="RunOptions.HostOperations"/> contains an asynchronous operation
    /// whose awaitable genuinely suspends the run.
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// Same cancellation contract as <see cref="EvaluateToAtoms"/>; delivered through
    /// the returned task.
    /// </exception>
    public static async Task<IReadOnlyList<decimal>> EvaluateToAtomsAsync(string source, RunOptions? options = null)
    {
        // MIRROR OF EvaluateToAtoms — keep in lock-step.
        return await RunAsync(source, options).ConfigureAwait(false) switch
        {
            RunResult.Success s => s.Atoms,
            RunResult.NoProgramOutput n => throw new KatLangException([n.Diagnostic]),
            RunResult.ParseFailure p => throw new KatLangException(p.Errors),
            RunResult.EvalFailure e => throw new KatLangException(e.Errors),
            _ => throw new InvalidOperationException("Unknown RunResult variant."),
        };
    }

    /// <summary>
    /// Parse and evaluate, returning atoms joined by spaces as a display string.
    /// Returns error text on failure instead of throwing.
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// The configured source-processing token was cancelled during front-end processing,
    /// or the configured evaluation token was cancelled before or during evaluation —
    /// cancellation propagates and is never rendered into the error string.
    /// </exception>
    public static string EvaluateToString(string source, RunOptions? options = null)
        => Run(source, options) switch
        {
            RunResult.Success s => FormatAtomsJoined(s),
            var r => r.ToDisplayString(),
        };

    /// <summary>
    /// Asynchronous counterpart of <see cref="EvaluateToString"/>: a thin projection
    /// over <see cref="RunAsync"/> with identical rendering and failure semantics.
    /// Like <see cref="RunAsync"/>, it completes synchronously unless
    /// <see cref="RunOptions.HostOperations"/> contains an asynchronous operation
    /// whose awaitable genuinely suspends the run.
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// Same cancellation contract as <see cref="EvaluateToString"/>; delivered through
    /// the returned task.
    /// </exception>
    public static async Task<string> EvaluateToStringAsync(string source, RunOptions? options = null)
        // MIRROR OF EvaluateToString — keep in lock-step.
        => await RunAsync(source, options).ConfigureAwait(false) switch
        {
            RunResult.Success s => FormatAtomsJoined(s),
            var r => r.ToDisplayString(),
        };

    /// <summary>
    /// Space-joined host atoms, bounded by the same rendered-output limit as structured
    /// display. Atom count is already bounded by the collection limits, but atom TEXT is
    /// not, so the join is written incrementally rather than materialized and measured.
    /// </summary>
    private static string FormatAtomsJoined(RunResult.Success success)
    {
        var writer = new BoundedDisplayWriter(success.DisplayOptions.MaxDisplayLength);

        for (var i = 0; i < success.Atoms.Count; i++)
        {
            if (i > 0 && !writer.Append(" ")) break;
            if (!writer.Append(ValueTextRenderer.FormatAtom(success.Atoms[i], success.DisplayOptions))) break;
        }

        return RunResult.Finish(writer, success.DisplayOptions.MaxDisplayLength);
    }

    private static SourceSpan? FindTopLevelPropertyDeclarationSpan(Algorithm root, string name)
    {
        foreach (var property in root.Properties)
        {
            if (property.Name == name)
                return property.DeclarationSpans.FirstOrDefault();
        }

        return null;
    }

    private static EvalResult<DisplayOptions> CreateDisplayOptions(
        Evaluator.CountedResult? displayDecimals,
        SourceSpan? span,
        int maxDisplayLength)
    {
        if (displayDecimals is not { } counted)
            return EvalResult<DisplayOptions>.Ok(new DisplayOptions(null, maxDisplayLength));

        var value = counted.Value.AsNum();
        if (counted.EmittedCount != 1 || value is null)
            return DisplayDecimalsError("DisplayDecimals must be a single numeric value.", span);

        if (value.Value < 0)
            return DisplayDecimalsError("DisplayDecimals must be a non-negative integer.", span);

        if (value.Value != Math.Truncate(value.Value))
            return DisplayDecimalsError("DisplayDecimals must be an integer.", span);

        if (value.Value > MaxDisplayDecimals)
            return DisplayDecimalsError($"DisplayDecimals must be between 0 and {MaxDisplayDecimals}.", span);

        try
        {
            return EvalResult<DisplayOptions>.Ok(new DisplayOptions(decimal.ToInt32(value.Value), maxDisplayLength));
        }
        catch (OverflowException)
        {
            return DisplayDecimalsError("DisplayDecimals must fit in a non-negative integer.", span);
        }
    }

    private static EvalError DisplayDecimalsError(string message, SourceSpan? span)
        => new EvalError.IllegalInEval(message) { Span = span };

    private static bool IsTopLevelNoProgramOutput(EvalError error)
        => error is EvalError.WithContext
        {
            ErrorContext: ProgramEvaluationContext,
            Inner: EvalError.MissingOutput,
        };

    private static IReadOnlyList<KatLangError> EvaluateForAdditionalErrors(
        Algorithm root, EvaluationLimits? limits, HostOperations? hostOperations, CancellationToken cancellationToken)
    {
        var evalResult = Evaluator.RunCounted(
            new Expr.AlgorithmExpr(root),
            new RunScopedZeroArgPropertyResultCache(),
            limits,
            hostOperations,
            cancellationToken);
        if (!evalResult.IsError || IsTopLevelNoProgramOutput(evalResult.Error))
            return [];

        return [KatLangError.FromEvalError(evalResult.Error)];
    }

    /// <summary>MIRROR OF <see cref="EvaluateForAdditionalErrors"/> — keep in lock-step.</summary>
    private static async Task<IReadOnlyList<KatLangError>> EvaluateForAdditionalErrorsAsync(
        Algorithm root, EvaluationLimits? limits, HostOperations? hostOperations, CancellationToken cancellationToken)
    {
        var evalResult = await Evaluator.RunCountedAsync(
            new Expr.AlgorithmExpr(root),
            hostOperations?.ContainsAsynchronousOperations == true
                ? new RunScopedAsyncZeroArgPropertyResultCache()
                : new RunScopedZeroArgPropertyResultCache(),
            limits,
            hostOperations,
            cancellationToken).ConfigureAwait(false);
        if (!evalResult.IsError || IsTopLevelNoProgramOutput(evalResult.Error))
            return [];

        return [KatLangError.FromEvalError(evalResult.Error)];
    }
}
