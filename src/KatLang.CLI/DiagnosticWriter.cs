using System.Globalization;
using System.Text;

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

    /// <summary>Escapes diagnostic fragments before KatLang adds explanatory line breaks.</summary>
    public void WriteDiagnostic(KatLangError diagnostic)
        => error.WriteLine(diagnostic.RenderDiagnostic(TerminalSafeText.EscapeLine));

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
            error.Write(errors[i].RenderDiagnostic(TerminalSafeText.EscapeLine));
        }
        error.WriteLine();
    }
}

/// <summary>
/// Terminal-safe rendering of diagnostic text, compatible with the escaping KatLang already
/// applies to downloader messages in module-loading diagnostics: every UTF-16 code unit that a
/// terminal could act on or that would hide or reorder text is shown as a visible
/// <c>\uXXXX</c> escape (four uppercase hexadecimal digits, invariant formatting) instead of
/// being deleted, so hostile or malformed input stays diagnosable. Escaped are:
/// <list type="bullet">
/// <item>controls (Unicode category <c>Cc</c>): C0 including NUL, BEL, backspace, tab, CR, LF and
/// ESC; DEL; and C1 including the 8-bit CSI (<c>U+009B</c>) and OSC (<c>U+009D</c>)
/// introducers;</item>
/// <item>format characters (<c>Cf</c>): bidirectional embeddings, overrides and isolates,
/// zero-width characters, the byte-order mark — supplementary ones too, as both code units;</item>
/// <item>the line and paragraph separators <c>U+2028</c> and <c>U+2029</c>;</item>
/// <item>unpaired surrogate code units.</item>
/// </list>
/// Everything else — Latvian, Greek, Cyrillic or CJK letters, valid supplementary characters,
/// visible punctuation, and the backslash — is kept as is. Because the output of an escape
/// contains no unsafe character, escaping already-escaped text (such as the <c>\u001B</c> a
/// module-loading diagnostic contains) returns it unchanged: there is no double escaping.
/// The scan is linear; text that needs no escaping is returned as the same instance, and an
/// escape expands one code unit to six, so the output is at most six times the input.
/// </summary>
internal static class TerminalSafeText
{
    private const string HexDigits = "0123456789ABCDEF";

    /// <summary>Escapes every unsafe code unit, line breaks included: the result is one line.</summary>
    public static string EscapeLine(string text)
    {
        StringBuilder? builder = null;
        var copied = 0;
        var index = 0;
        while (index < text.Length)
        {
            var ch = text[index];
            int width;
            bool unsafeText;
            if (char.IsHighSurrogate(ch) && index + 1 < text.Length && char.IsLowSurrogate(text[index + 1]))
            {
                width = 2;
                unsafeText = char.GetUnicodeCategory(text, index) == UnicodeCategory.Format;
            }
            else
            {
                width = 1;
                unsafeText = NeedsEscape(ch);
            }

            if (unsafeText)
            {
                builder ??= new StringBuilder(text.Length + 16);
                builder.Append(text, copied, index - copied);
                for (var unit = index; unit < index + width; unit++)
                    AppendEscape(builder, text[unit]);
                copied = index + width;
            }

            index += width;
        }

        return builder is null
            ? text
            : builder.Append(text, copied, text.Length - copied).ToString();
    }

    private static bool NeedsEscape(char ch)
    {
        if (char.IsControl(ch) || char.IsSurrogate(ch))
            return true;

        return char.GetUnicodeCategory(ch)
            is UnicodeCategory.Format
            or UnicodeCategory.LineSeparator
            or UnicodeCategory.ParagraphSeparator;
    }

    private static void AppendEscape(StringBuilder builder, char ch)
        => builder
            .Append('\\')
            .Append('u')
            .Append(HexDigits[(ch >> 12) & 0xF])
            .Append(HexDigits[(ch >> 8) & 0xF])
            .Append(HexDigits[(ch >> 4) & 0xF])
            .Append(HexDigits[ch & 0xF]);
}
