using System.Globalization;
using KatLang.Evaluation.Caching;

namespace KatLang;

internal readonly record struct DisplayOptions(int? Decimals)
{
    public static DisplayOptions Default { get; } = new(null);
}

/// <summary>
/// Discriminated-union result of a KatLang parse+evaluate run.
/// Pattern-match on <see cref="Success"/>, <see cref="NoProgramOutput"/>,
/// <see cref="ParseFailure"/>, or <see cref="EvalFailure"/>.
/// </summary>
public abstract record RunResult
{
    private RunResult() { }

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

        internal DisplayOptions DisplayOptions { get; init; } = DisplayOptions.Default;
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
    /// </summary>
    public string ToDisplayString() => this switch
    {
        Success s => FormatSuccess(s),
        NoProgramOutput n => n.Message,
        ParseFailure p => string.Join(Environment.NewLine, p.Errors.Select(e => e.ToString())),
        EvalFailure e => string.Join(Environment.NewLine, e.Errors.Select(e => e.ToString())),
        _ => throw new InvalidOperationException("Unknown RunResult variant."),
    };

    private static string FormatSuccess(Success success)
    {
        var rows = TopLevelDisplayRows(success.Value, success.EmittedCount);
        return string.Join(Environment.NewLine, rows.Select(row => Format(row, success.DisplayOptions)));
    }

    private static IReadOnlyList<Result> TopLevelDisplayRows(Result value, int emittedCount)
        => emittedCount switch
        {
            0 => [],
            1 => [value],
            _ => value.ToItems(),
        };

    private static string Format(Result result, DisplayOptions displayOptions) => result switch
    {
        Result.Atom a => FormatAtom(a.Value, displayOptions),
        Result.Str s => s.Value,
        Result.SequenceValue g => $"({string.Join(", ", g.Items.Select(item => Format(item, displayOptions)))})",
        Result.ListValue l => $"[{string.Join(", ", l.Items.Select(item => Format(item, displayOptions)))}]",
        _ => "",
    };

    internal static string FormatAtom(decimal value, DisplayOptions displayOptions)
    {
        if (displayOptions.Decimals is not { } decimals)
            return value.ToString();

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
        var frontEndResult = FrontEndPipeline.Process(source, options);

        if (frontEndResult.HasErrors)
        {
            var parseErrors = frontEndResult.Diagnostics
                .Where(d => d.Severity == DiagnosticSeverity.Error)
                .Select(KatLangError.FromDiagnostic)
                .ToList();
            if (frontEndResult.CanEvaluateAfterLoadErrors)
                parseErrors.AddRange(EvaluateForAdditionalErrors(frontEndResult.ElaboratedRoot));

            return new RunResult.ParseFailure(parseErrors);
        }

        var zeroArgPropertyResultCache = new RunScopedZeroArgPropertyResultCache();
        var evalResult = Evaluator.RunCountedWithTopLevelProperty(
            new Expr.Block(frontEndResult.ElaboratedRoot),
            DisplayDecimalsPropertyName,
            zeroArgPropertyResultCache);

        if (evalResult.IsError)
        {
            var evalError = KatLangError.FromEvalError(evalResult.Error);
            if (IsTopLevelNoProgramOutput(evalResult.Error))
                return new RunResult.NoProgramOutput(frontEndResult.ElaboratedRoot, evalError);

            var evalErrors = new[] { evalError };
            return new RunResult.EvalFailure(frontEndResult.ElaboratedRoot, evalErrors);
        }

        var displayOptionsResult = CreateDisplayOptions(
            evalResult.Value.TopLevelProperty,
            FindTopLevelPropertyDeclarationSpan(frontEndResult.ElaboratedRoot, DisplayDecimalsPropertyName));
        if (displayOptionsResult.IsError)
        {
            return new RunResult.EvalFailure(
                frontEndResult.ElaboratedRoot,
                [KatLangError.FromEvalError(displayOptionsResult.Error)]);
        }

        return new RunResult.Success(
            frontEndResult.ElaboratedRoot,
            evalResult.Value.Output.Value,
            evalResult.Value.Output.Value.ToHostAtoms())
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
            RunResult.Success s => string.Join(" ", s.Atoms.Select(atom => RunResult.FormatAtom(atom, s.DisplayOptions))),
            var r => r.ToDisplayString(),
        };

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
        SourceSpan? span)
    {
        if (displayDecimals is not { } counted)
            return EvalResult<DisplayOptions>.Ok(DisplayOptions.Default);

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
            return EvalResult<DisplayOptions>.Ok(new DisplayOptions(decimal.ToInt32(value.Value)));
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

    private static IReadOnlyList<KatLangError> EvaluateForAdditionalErrors(Algorithm root)
    {
        var evalResult = Evaluator.RunCounted(new Expr.Block(root));
        if (!evalResult.IsError || IsTopLevelNoProgramOutput(evalResult.Error))
            return [];

        return [KatLangError.FromEvalError(evalResult.Error)];
    }
}
