namespace KatLang;

/// <summary>
/// Discriminated-union result of a KatLang parse+evaluate run.
/// Pattern-match on <see cref="Success"/>, <see cref="ParseFailure"/>, or <see cref="EvalFailure"/>.
/// </summary>
public abstract record RunResult
{
    private RunResult() { }

    /// <summary>True when the run succeeded.</summary>
    public bool IsSuccess => this is Success;

    /// <summary>True when the run failed (parse or eval).</summary>
    public bool IsFailure => this is ParseFailure or EvalFailure;

    /// <summary>Parse and evaluation succeeded.</summary>
    public sealed record Success(
        Algorithm Root,
        Result Value,
        IReadOnlyList<decimal> Atoms) : RunResult;

    /// <summary>Parsing failed — no executable root was produced.</summary>
    public sealed record ParseFailure(
        IReadOnlyList<KatLangError> Errors) : RunResult;

    /// <summary>Evaluation failed after a successful parse.</summary>
    public sealed record EvalFailure(
        Algorithm Root,
        IReadOnlyList<KatLangError> Errors) : RunResult;

    /// <summary>
    /// Returns a human-readable display string.
    /// On success: each top-level item on its own line; nested groups formatted with parentheses.
    /// On failure: newline-joined error messages.
    /// </summary>
    public string ToDisplayString() => this switch
    {
        Success s when s.Value is Result.Group g => string.Join(Environment.NewLine, g.Items.Select(Format)),
        Success s => Format(s.Value),
        ParseFailure p => string.Join(Environment.NewLine, p.Errors.Select(e => e.ToString())),
        EvalFailure e => string.Join(Environment.NewLine, e.Errors.Select(e => e.ToString())),
        _ => throw new InvalidOperationException("Unknown RunResult variant."),
    };

    private static string Format(Result result) => result switch
    {
        Result.Atom a => a.Value.ToString(),
        Result.Group g => $"({string.Join(", ", g.Items.Select(Format))})",
        _ => "",
    };
}

/// <summary>
/// Public façade for KatLang: parse and evaluate in one step.
/// Hides internal details such as <see cref="Expr.Block"/> wrapping.
/// For advanced/internal use, <see cref="Parser"/> and <see cref="Evaluator"/> remain available.
/// </summary>
public static class KatLangEngine
{
    /// <summary>
    /// Parse and evaluate KatLang source code, returning a unified <see cref="RunResult"/>.
    /// </summary>
    public static RunResult Run(string source, RunOptions? options = null)
    {
        var parseResult = Parser.Parse(source, options);

        if (parseResult.HasErrors)
        {
            var parseErrors = parseResult.Diagnostics
                .Where(d => d.Severity == DiagnosticSeverity.Error)
                .Select(KatLangError.FromDiagnostic)
                .ToList();
            return new RunResult.ParseFailure(parseErrors);
        }

        var evalResult = Evaluator.Run(new Expr.Block(parseResult.Root));

        if (evalResult.IsError)
        {
            var evalErrors = new[] { KatLangError.FromEvalError(evalResult.Error) };
            return new RunResult.EvalFailure(parseResult.Root, evalErrors);
        }

        return new RunResult.Success(parseResult.Root, evalResult.Value, evalResult.Value.ToAtoms());
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
            RunResult.Success s => string.Join(" ", s.Atoms),
            var r => r.ToDisplayString(),
        };
}
