using System.Globalization;
using System.Text;

namespace KatLang.Rendering;

/// <summary>
/// The ONE terminal-safe escaping policy: <see cref="KatLangError.ToTerminalSafeString"/> renders
/// every untrusted diagnostic fragment through it, and the CLI's stderr channel delegates to it.
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
