using System.Globalization;
using System.Text;
using KatLang.Evaluation.Caching;

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
internal sealed class BoundedDisplayWriter(int limit)
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
        var rows = TopLevelDisplayRows(success.Value, success.EmittedCount);

        for (var i = 0; i < rows.Count; i++)
        {
            if (i > 0 && !writer.AppendRowSeparator()) break;
            if (!AppendValue(rows[i], success.DisplayOptions, writer)) break;
        }

        return Finish(writer, success.DisplayOptions.MaxDisplayLength);
    }

    /// <summary>
    /// Errors are rendered through the same configured bounded writer.
    /// The structured diagnostics are never dropped or rewritten to fit — only the final
    /// public rendering surface is bounded.
    /// </summary>
    private static string FormatErrors(IReadOnlyList<KatLangError> errors, int limit)
    {
        var writer = new BoundedDisplayWriter(limit);

        for (var i = 0; i < errors.Count; i++)
        {
            if (i > 0 && !writer.AppendRowSeparator()) break;
            if (!writer.Append(errors[i].ToString())) break;
        }

        return Finish(writer, limit);
    }

    private static string FormatText(string text, int limit)
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

    private static IReadOnlyList<Result> TopLevelDisplayRows(Result value, int emittedCount)
        => emittedCount switch
        {
            0 => [],
            1 => [value],
            _ => value.ToItems(),
        };

    /// <summary>
    /// Appends one value's display form, ITERATIVELY. Recursion plus
    /// <c>Select(...).Join(...)</c> would build every child string before the parent could
    /// know its own size — the exact shape that lets a legal but deeply shared value
    /// allocate far beyond the limit — and would also recurse as deeply as the value
    /// nests, which for host-constructed <see cref="Result"/> trees is unbounded by the
    /// parser. Indexed continuation frames keep auxiliary traversal storage proportional
    /// to nesting depth, not collection breadth, so a wide value does not allocate a
    /// pending entry for every sibling before the writer can enforce its length limit.
    /// </summary>
    internal static bool AppendValue(Result value, DisplayOptions displayOptions, BoundedDisplayWriter writer)
    {
        IReadOnlyList<Result> items;
        string close;
        switch (value)
        {
            case Result.Atom atom:
                return writer.Append(FormatAtom(atom.Value, displayOptions));
            case Result.Str str:
                return writer.Append(str.Value);
            case Result.SequenceValue sequence:
                if (!writer.Append("(")) return false;
                items = sequence.Items;
                close = ")";
                break;
            case Result.ListValue list:
                if (!writer.Append("[")) return false;
                items = list.Items;
                close = "]";
                break;
            default:
                return true;
        }

        var suspended = new Stack<(IReadOnlyList<Result> Items, int Next, string Close)>();
        var next = 0;

        while (true)
        {
            if (next >= items.Count)
            {
                if (!writer.Append(close)) return false;
                if (suspended.Count == 0) return true;
                (items, next, close) = suspended.Pop();
                continue;
            }

            if (next > 0 && !writer.Append(", ")) return false;
            var child = items[next];
            next++;

            switch (child)
            {
                case Result.Atom atom:
                    if (!writer.Append(FormatAtom(atom.Value, displayOptions))) return false;
                    break;
                case Result.Str str:
                    if (!writer.Append(str.Value)) return false;
                    break;
                case Result.SequenceValue sequence:
                    if (!writer.Append("(")) return false;
                    suspended.Push((items, next, close));
                    (items, next, close) = (sequence.Items, 0, ")");
                    break;
                case Result.ListValue list:
                    if (!writer.Append("[")) return false;
                    suspended.Push((items, next, close));
                    (items, next, close) = (list.Items, 0, "]");
                    break;
                default:
                    break;
            }
        }
    }

    internal static string FormatAtom(decimal value, DisplayOptions displayOptions)
    {
        // Canonical KatLang value display is culture-invariant on every path:
        // the decimal point is always `.` so fractional atoms can never
        // collide with the `, ` element separator of sequence/list rendering,
        // and output is identical on every machine (matching the lexer,
        // `.string`, diagnostics, and the differential harness).
        if (displayOptions.Decimals is not { } decimals)
            return value.ToString(CultureInfo.InvariantCulture);

        if (value == Math.Truncate(value) && DecimalScale(value) == 0)
            return value.ToString(CultureInfo.InvariantCulture);

        var format = "F" + decimals.ToString(CultureInfo.InvariantCulture);
        return value.ToString(format, CultureInfo.InvariantCulture);
    }

    private static int DecimalScale(decimal value)
        => (decimal.GetBits(value)[3] >> 16) & 0xFF;
}

/// <summary>
/// Public façade for KatLang: parse and evaluate in one step.
/// Hides internal details such as <see cref="Expr.Block"/> wrapping.
/// For advanced/internal use, <see cref="Parser"/> and <see cref="Evaluator"/> remain available.
/// </summary>
public static class KatLangEngine
{
    private const string DisplayDecimalsPropertyName = "DisplayDecimals";
    private const int MaxDisplayDecimals = 99;

    /// <summary>
    /// Parse and evaluate KatLang source code, returning a unified <see cref="RunResult"/>.
    /// </summary>
    public static RunResult Run(string source, RunOptions? options = null)
    {
        var limits = options?.EvaluationLimits ?? EvaluationLimits.Default;
        var diagnosticDisplayOptions = new DisplayOptions(null, limits.EffectiveMaxDisplayLength);
        var frontEndResult = FrontEndPipeline.Process(source, options);

        if (frontEndResult.HasErrors)
        {
            var parseErrors = frontEndResult.Diagnostics
                .Where(d => d.Severity == DiagnosticSeverity.Error)
                .Select(KatLangError.FromDiagnostic)
                .ToList();
            if (frontEndResult.CanEvaluateAfterLoadErrors)
                parseErrors.AddRange(EvaluateForAdditionalErrors(frontEndResult.ElaboratedRoot, options?.EvaluationLimits));

            return new RunResult.ParseFailure(parseErrors)
            {
                DisplayOptions = diagnosticDisplayOptions,
            };
        }

        var zeroArgPropertyResultCache = new RunScopedZeroArgPropertyResultCache();

        // One budget for the whole run: the program output and the DisplayDecimals
        // property are evaluated under the same run-scoped budget, so neither can reset
        // or escape the other's accounting.
        var evalResult = Evaluator.RunCountedWithTopLevelProperty(
            new Expr.Block(frontEndResult.ElaboratedRoot),
            DisplayDecimalsPropertyName,
            zeroArgPropertyResultCache,
            options?.EvaluationLimits);

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
        if (!evalResult.Value.Output.Value.TryToHostAtoms(hostAtomLimit, out var hostAtoms))
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
    /// Parse and evaluate, returning atoms joined by spaces as a display string.
    /// Returns error text on failure instead of throwing.
    /// </summary>
    public static string EvaluateToString(string source, RunOptions? options = null)
        => Run(source, options) switch
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
            if (!writer.Append(RunResult.FormatAtom(success.Atoms[i], success.DisplayOptions))) break;
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

    private static IReadOnlyList<KatLangError> EvaluateForAdditionalErrors(Algorithm root, EvaluationLimits? limits)
    {
        var evalResult = Evaluator.RunCounted(
            new Expr.Block(root),
            new RunScopedZeroArgPropertyResultCache(),
            limits);
        if (!evalResult.IsError || IsTopLevelNoProgramOutput(evalResult.Error))
            return [];

        return [KatLangError.FromEvalError(evalResult.Error)];
    }
}
