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
    /// <para>Concise uses the raw string's width and line breaks to choose a
    /// layout. Different values can produce the same display text.</para>
    /// </summary>
    Never,

    /// <summary>
    /// Render ordinary textual strings raw, and add single-quote delimiters
    /// only where the raw content would obscure item boundaries or the value
    /// kind: the empty string, strings containing whitespace,
    /// numeric-looking strings (including signed, fractional, exponent, and
    /// KatLang digit-separator forms, regardless of numeric overflow, and the
    /// non-finite atom spellings <c>NaN</c>, <c>Infinity</c>, <c>-Infinity</c>), strings
    /// containing structural characters
    /// (<c>,</c> <c>(</c> <c>)</c> <c>[</c> <c>]</c> <c>'</c>), strings
    /// containing control characters, invisible Unicode format characters
    /// (bidi controls, zero-width spaces, byte-order marks, soft hyphens), and
    /// unpaired surrogates. Quoting whitespace-bearing strings keeps one string
    /// such as <c>'income tax'</c> visibly distinct from two adjacent values
    /// laid out as <c>income tax</c>. A quoted string can join a Concise line
    /// when it fits, as in <c>'income tax' 3</c>.
    /// </summary>
    WhenNeeded,

    /// <summary>
    /// Surround every string with single-quote delimiters wherever that can be
    /// done faithfully; unquotable host-built strings fall back to raw.
    /// </summary>
    Always,
}
