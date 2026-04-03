namespace KatLang;

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
        var parseOptions = options?.ToParseOptions();
        var parseResult = parseOptions is not null
            ? Parser.Parse(source, parseOptions)
            : Parser.Parse(source);

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
        => Run(source, options).ToDisplayString();
}
