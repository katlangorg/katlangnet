namespace KatLang.CLI;

/// <summary>
/// The CLI's ONE stderr channel. Every diagnostic the CLI prints goes through it, so text that
/// came from outside the CLI — a command-line argument, a file path, an exception message, a
/// program's own source or values echoed by a KatLang diagnostic — can never put a terminal
/// control sequence on the user's terminal. Only <see cref="CliApplication.RunAsync"/> holds the
/// raw stderr <see cref="TextWriter"/>; everything below it receives this writer.
///
/// <para>Raw text always goes through <see cref="WriteLine"/>, including its CR/LF.
/// Structured diagnostics go through <see cref="WriteDiagnostic"/> or
/// <see cref="WriteFailure"/>: KatLang's owning renderer inserts structural separators
/// AFTER escaping its untrusted fragments. No already formatted string is trusted to
/// distinguish a renderer's newline from one embedded in a program value.</para>
/// <para>This is presentation policy only: the structured <see cref="Diagnostic"/> and
/// <see cref="KatLangError"/> data are never changed, and successful program output (stdout)
/// is not written through this channel.</para>
/// </summary>
internal sealed class DiagnosticWriter(TextWriter error)
{
    /// <summary>Writes one CLI-composed line; any line break inside it is escaped.</summary>
    public void WriteLine(string line) => error.WriteLine(TerminalSafeText.EscapeLine(line));

    /// <summary>
    /// Keep the established CR/LF-to-space normalization and whitespace trim, but escape
    /// other unsafe characters before trimming so tabs, NEL and Unicode separators remain
    /// visible even at the edges of a host message.
    /// </summary>
    public void WriteUnexpectedError(Exception exception)
    {
        var normalized = exception.Message
            .Replace("\r\n", " ", StringComparison.Ordinal)
            .Replace('\r', ' ')
            .Replace('\n', ' ');
        var message = TerminalSafeText.EscapeLine(normalized).Trim();
        if (message.Length == 0)
            message = "An unexpected error occurred.";
        error.WriteLine($"{CommandLine.ProgramName}: unexpected error: {message}");
    }

    /// <summary>
    /// Escapes diagnostic fragments before KatLang adds explanatory line breaks — the public
    /// <see cref="KatLangError.ToTerminalSafeString"/> rendering every embedding host can use.
    /// </summary>
    public void WriteDiagnostic(KatLangError diagnostic)
        => error.WriteLine(diagnostic.ToTerminalSafeString());

    /// <summary>
    /// Retains the run's original display-limit decision and diagnostic order. Escaping can
    /// expand the admitted text by at most six per code unit; it never bypasses a refusal.
    /// Stream the admitted diagnostics so no additional joined escaped copy is needed.
    /// </summary>
    public void WriteFailure(RunResult failure)
    {
        var errors = failure switch
        {
            RunResult.ParseFailure parsed => parsed.Errors,
            RunResult.EvalFailure evaluated => evaluated.Errors,
            _ => throw new ArgumentException("Expected a failed run.", nameof(failure)),
        };
        var rendering = failure.RenderDisplay();
        if (rendering.LimitExceeded || errors.Count == 0)
        {
            WriteLine(rendering.Text);
            return;
        }

        for (var i = 0; i < errors.Count; i++)
        {
            if (i > 0)
                error.Write(Environment.NewLine);
            error.Write(errors[i].ToTerminalSafeString());
        }
        error.WriteLine();
    }
}

/// <summary>
/// The CLI's name for KatLang's one terminal-safe escaping policy
/// (<see cref="KatLang.Rendering.TerminalSafeText"/>): the CLI escapes its own raw text —
/// command-line arguments, paths, option values, host exception messages — exactly as
/// <see cref="KatLangError.ToTerminalSafeString"/> escapes diagnostic fragments.
/// </summary>
internal static class TerminalSafeText
{
    /// <summary>Escapes every unsafe code unit, line breaks included: the result is one line.</summary>
    public static string EscapeLine(string text) => KatLang.Rendering.TerminalSafeText.EscapeLine(text);
}
