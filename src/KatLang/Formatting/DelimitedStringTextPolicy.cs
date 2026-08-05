using System.Buffers;
using KatLang.Rendering;

namespace KatLang.Formatting;

/// <summary>String-leaf presentation shared by Readable and Concise.</summary>
internal sealed class DelimitedStringTextPolicy(StringDelimiterMode mode) : IStringTextPolicy
{
    private static readonly SearchValues<char> UnquotableChars = SearchValues.Create("'\n\r");

    public bool Append(string value, IDisplaySink sink)
    {
        if (!UsesDelimiters(value))
            return sink.Append(value);

        return sink.Append("'") && sink.Append(value) && sink.Append("'");
    }

    internal long TokenLength(string value)
        => UsesDelimiters(value) ? (long)value.Length + 2 : value.Length;

    /// <summary>
    /// Whether this string can stand as ONE safe Concise token in a layout
    /// that removed the surrounding sequence punctuation — text that cannot be
    /// confused with a separator, a neighbouring token, structural
    /// punctuation, or canonical atom output. This is a per-value structural
    /// decision, deliberately separate from the quoting policy itself: the
    /// delimiter mode only changes WHAT the rendered token is, and safety is
    /// judged on that exact token.
    ///
    /// <para>Under <see cref="StringDelimiterMode.Never"/> the token is the
    /// raw content, so it is safe exactly when the content would never need
    /// delimiters: non-empty, no whitespace or control characters, none of
    /// <c>, ( ) [ ] '</c>, and not numeric-looking. Ordinary labels such as
    /// <c>neto</c> or <c>net_salary</c> are safe; ambiguous raw strings make
    /// the CONTAINING sequence keep its parentheses instead of being quoted
    /// (<c>Never</c> forbids added delimiters) or altered.</para>
    ///
    /// <para>Under the quoting modes a delimited token is self-bounding, so
    /// only content that still blurs line/join boundaries (whitespace,
    /// control characters, commas) or that needs delimiters it cannot
    /// faithfully receive remains unsafe. The scan is early-exit and never
    /// copies the string; measurement and emission share this one predicate,
    /// so they cannot disagree.</para>
    /// </summary>
    internal bool IsTokenSafe(string value)
    {
        if (mode == StringDelimiterMode.Never)
            return !NeedsDelimiters(value);

        if (value.Length == 0)
            return UsesDelimiters(value);

        if (NeedsDelimiters(value) && !CanDelimitFaithfully(value))
            return false;

        foreach (var c in value)
        {
            if (char.IsWhiteSpace(c) || char.IsControl(c) || c == ',')
                return false;
        }

        return true;
    }

    private bool UsesDelimiters(string value) => mode switch
    {
        StringDelimiterMode.Always => CanDelimitFaithfully(value),
        StringDelimiterMode.WhenNeeded => NeedsDelimiters(value) && CanDelimitFaithfully(value),
        _ => false,
    };

    private static bool CanDelimitFaithfully(string value)
        => !value.AsSpan().ContainsAny(UnquotableChars);

    private static bool NeedsDelimiters(string value)
    {
        if (value.Length == 0)
            return true;

        foreach (var c in value)
        {
            if (char.IsWhiteSpace(c) || char.IsControl(c))
                return true;
            if (c is ',' or '(' or ')' or '[' or ']' or '\'')
                return true;
        }

        return LooksNumeric(value);
    }

    private static bool LooksNumeric(string value)
    {
        // Syntax recognition, not numeric conversion: overflow-sized and
        // exponent-form text is still visually numeric and should stay
        // distinguishable from atom output. ASCII is intentional because
        // canonical invariant atom text uses ASCII digits.
        var span = value.AsSpan();
        var i = 0;
        if (i < span.Length && span[i] is '+' or '-') i++;

        var integralDigits = 0;
        while (i < span.Length && span[i] is >= '0' and <= '9')
        {
            integralDigits++;
            i++;
        }

        var fractionalDigits = 0;
        if (i < span.Length && span[i] == '.')
        {
            i++;
            while (i < span.Length && span[i] is >= '0' and <= '9')
            {
                fractionalDigits++;
                i++;
            }
        }

        if (integralDigits + fractionalDigits == 0) return false;
        if (i < span.Length && span[i] is 'e' or 'E')
        {
            i++;
            if (i < span.Length && span[i] is '+' or '-') i++;
            var exponentStart = i;
            while (i < span.Length && span[i] is >= '0' and <= '9') i++;
            if (i == exponentStart) return false;
        }

        return i == span.Length;
    }
}
