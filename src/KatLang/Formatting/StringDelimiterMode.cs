namespace KatLang.Formatting;

/// <summary>
/// String-delimiter policy for the layout formatters (<c>readable</c> and
/// <c>concise</c>). The policy controls only whether a string value is
/// surrounded by KatLang single-quote delimiters — the string CONTENT is
/// always emitted byte-for-byte (no trimming, no case changes, no whitespace
/// normalization, and no special handling of any character such as <c>_</c>).
///
/// <para>The <c>exact</c> formatter ignores this policy: canonical KatLang
/// display renders strings as their raw content without quotes.</para>
///
/// <para>KatLang has no escape syntax, so a string containing a single quote,
/// a line feed, or a carriage return cannot be quoted faithfully. Such
/// host-built strings fall back to the canonical raw rendering under every
/// policy.</para>
/// </summary>
public enum StringDelimiterMode
{
    /// <summary>
    /// Render every string as its raw content, exactly like canonical display.
    /// An empty string renders as an empty text run (which on its own output
    /// row is a visually blank line).
    ///
    /// <para>This mode suppresses added string quote delimiters ONLY — it does
    /// not force the <c>concise</c> formatter to retain all sequence
    /// punctuation. Concise independently removes sequence punctuation where
    /// the concrete raw item representations preserve safe boundaries: ordinary
    /// raw labels such as <c>neto</c> or <c>net_salary</c> still participate in
    /// delimiter removal, while an ambiguous raw string (empty,
    /// whitespace-bearing, comma-bearing, structural-looking, quote-bearing, or
    /// numeric-looking) makes the CONTAINING sequence keep its parentheses and
    /// canonical separators — the best available boundary information when
    /// quoting is forbidden. Lists always keep their brackets, empty sequences
    /// stay visible as <c>()</c>, root and nesting boundaries take priority
    /// over compactness, and no punctuation is ever invented.</para>
    /// </summary>
    Never,

    /// <summary>
    /// Render ordinary textual strings raw, and add single-quote delimiters
    /// only where the raw content would obscure item boundaries or the value
    /// kind: the empty string, strings containing whitespace,
    /// numeric-looking strings (including signed, fractional, and exponent
    /// forms, regardless of numeric overflow), strings containing structural characters
    /// (<c>,</c> <c>(</c> <c>)</c> <c>[</c> <c>]</c> <c>'</c>), and strings
    /// containing control characters. Quoting whitespace-bearing strings keeps
    /// one string such as <c>'income tax'</c> visibly distinct from two adjacent
    /// values laid out as <c>income tax</c>.
    /// </summary>
    WhenNeeded,

    /// <summary>
    /// Surround every string with single-quote delimiters wherever that can be
    /// done faithfully; unquotable host-built strings fall back to raw.
    /// </summary>
    Always,
}
