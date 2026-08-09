namespace KatLang.Tests;

/// <summary>
/// Diagnostic provenance for a source-based test: which language-processing
/// STAGE produced the outcome a test is asserting.
///
/// <para>
/// Track 12 found a regression test named for an evaluator branch
/// (<c>NotPublicProperty</c>) whose source the PARSER rejected. Its helper built
/// an AST with <c>Parser.Parse(source).Root</c> and evaluated the recovery tree,
/// so the test passed on an unrelated failure and never reached the branch it
/// named. The helper shape — parse, take <c>.Root</c>, discard
/// <c>Diagnostics</c> — is the root cause, and it appears throughout the suite.
/// </para>
///
/// <para>
/// This type makes the stages separately observable so a test cannot assert on
/// stage 3 while stages 1-2 were already invalid:
/// <list type="number">
/// <item>lexer/parser + front-end diagnostics (<see cref="Diagnostics"/>)</item>
/// <item>the elaborated AST actually handed to the evaluator (<see cref="Root"/>)</item>
/// <item>the evaluator outcome (<see cref="Evaluate"/>)</item>
/// </list>
/// </para>
///
/// <para>
/// Use <see cref="ParseValid"/> for ordinary source-language tests — it fails
/// loudly if the front end produced any diagnostic. Use
/// <see cref="ParseAllowingDiagnostics"/> only where malformed source is the
/// point (recovery, fuzzing, editor tooling), which states that intent at the
/// call site instead of hiding it in a shared helper.
/// </para>
/// </summary>
public sealed record SourceProvenance(string Source, ParseResult Parsed)
{
    public IReadOnlyList<Diagnostic> Diagnostics => Parsed.Diagnostics;

    public bool HasFrontEndErrors => Parsed.HasErrors;

    public Algorithm Root => Parsed.Root;

    /// <summary>
    /// Parses and REQUIRES a clean front end. Any parser or elaboration
    /// diagnostic fails the test immediately, naming the diagnostics, so an
    /// evaluator assertion can never stand on a recovery tree.
    /// </summary>
    public static SourceProvenance ParseValid(string source)
    {
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
        {
            Assert.Fail(
                "Source-language test requires a clean front end, but parsing/elaboration reported:"
                + Environment.NewLine
                + string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => "  - " + d.Message.Split('\n')[0]))
                + Environment.NewLine + "Source:" + Environment.NewLine + source);
        }

        return new SourceProvenance(source, parsed);
    }

    /// <summary>
    /// Parses WITHOUT requiring success. For tests whose subject is malformed
    /// source: parser recovery, fuzz corpora, editor tooling, and evaluator
    /// defense against trees the front end would never produce.
    /// </summary>
    public static SourceProvenance ParseAllowingDiagnostics(string source)
        => new(source, Parser.Parse(source));

    /// <summary>
    /// Raw-syntax root for tests that inspect the pre-elaboration tree
    /// (<c>Parser.ParseSyntax</c>, a different result type from
    /// <c>Parser.Parse</c>). Same contract as <see cref="ParseValid"/>: a
    /// syntax-shape test must still prove the parser accepted the source before
    /// the tree is used as evidence. Returns the root directly because the raw
    /// boundary has no elaboration stage to expose separately.
    /// </summary>
    public static Algorithm ParseSyntaxValidRoot(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        if (parsed.HasErrors)
        {
            Assert.Fail(
                "Raw-syntax test requires a clean parse, but the parser reported:"
                + Environment.NewLine
                + string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => "  - " + d.Message.Split('\n')[0]))
                + Environment.NewLine + "Source:" + Environment.NewLine + source);
        }

        return parsed.Root;
    }

    /// <summary>
    /// Raw-syntax root WITHOUT requiring a clean parse — for parser tests whose
    /// subject is malformed input and recovery-tree shape.
    /// </summary>
    public static Algorithm ParseSyntaxAllowingDiagnosticsRoot(string source)
        => Parser.ParseSyntax(source).Root;

    /// <summary>Evaluates the elaborated AST (stage 3).</summary>
    public EvalResult<Result> Evaluate() => Evaluator.Run(new Expr.Block(Root));

    /// <summary>The innermost evaluator error, with context frames unwrapped.</summary>
    public EvalError ExpectEvaluationError()
    {
        var result = Evaluate();
        if (!result.IsError)
            Assert.Fail($"Expected an evaluation failure but got: {result.Value}");

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    /// <summary>
    /// Asserts the innermost evaluator error is <typeparamref name="TError"/>,
    /// which is what makes a test EVALUATOR coverage rather than merely
    /// "something failed somewhere".
    /// </summary>
    public TError ExpectEvaluationError<TError>() where TError : EvalError
    {
        var error = ExpectEvaluationError();
        if (error is not TError typed)
        {
            Assert.Fail(
                $"Expected evaluator error {typeof(TError).Name} but the innermost error was "
                + $"{error.GetType().Name}: {KatLangError.FromEvalError(error).Message.Split('\n')[0]}"
                + Environment.NewLine + "Source:" + Environment.NewLine + Source);
            return null!;
        }

        return typed;
    }

    /// <summary>
    /// Asserts the FRONT END rejected the source, and returns the diagnostics.
    /// The counterpart to <see cref="ExpectEvaluationError{TError}"/>: a test
    /// should say which layer it is testing.
    /// </summary>
    public static IReadOnlyList<Diagnostic> ExpectFrontEndError(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.True(
            parsed.HasErrors,
            $"Expected a parser/elaboration diagnostic, but the front end accepted:{Environment.NewLine}{source}");
        return parsed.Diagnostics;
    }
}
