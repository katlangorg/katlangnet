using System.Globalization;

namespace KatLang.CLI;

/// <summary>
/// KatLang code links, which <c>--code-link</c> prints: a program carried in a katlang.org URL,
/// <c>https://katlang.org/#code/&lt;payload&gt;</c> with
/// <c>payload = LZString.compressToEncodedURIComponent(source)</c> from lz-string 1.5.0
/// (<see cref="LzString"/>). Opening one shows the program in the Playground and runs it.
///
/// <para>The contract is katlangweb's <c>docs/code-links.md</c>, and its reference
/// implementation katlangweb's <c>KatLangWeb/wwwroot/js/katlang-code-link.js</c>: the limits
/// here are that file's, and a source is checked against them in its order. The source is
/// encoded exactly as given, as UTF-16 code units, with nothing normalized: line breaks, tabs,
/// trailing spaces and a final line break are part of the program, and the payload, whose
/// characters a URL fragment allows as they are, is not percent-encoded.</para>
/// </summary>
internal static class CodeLink
{
    /// <summary>What every line <c>--code-link</c> writes starts with.</summary>
    public const string LinePrefix = "katlang-link: ";

    /// <summary>What a link line carries after <see cref="LinePrefix"/> before the payload.</summary>
    public const string UrlPrefix = "https://katlang.org/#code/";

    /// <summary>
    /// What a line for a program with no link carries after <see cref="LinePrefix"/>, before
    /// the reason.
    /// </summary>
    public const string NoLinkPrefix = "none: ";

    /// <summary>The longest source a code link carries, in UTF-16 code units (<c>MAX_SOURCE_LENGTH</c>).</summary>
    public const int MaxSourceLength = 50_000;

    /// <summary>The longest payload a code link carries, in characters (<c>MAX_PAYLOAD_LENGTH</c>).</summary>
    public const int MaxPayloadLength = 8_192;

    /// <summary>
    /// The one line <c>--code-link</c> writes for <paramref name="source"/>, without its line
    /// break: <c>katlang-link: https://katlang.org/#code/&lt;payload&gt;</c>, or
    /// <c>katlang-link: none: &lt;reason&gt;</c> for a program that cannot be a code link — an
    /// empty one, one longer than <see cref="MaxSourceLength"/> code units (which is never
    /// encoded), or one whose payload is longer than <see cref="MaxPayloadLength"/> characters.
    /// </summary>
    public static string Line(string source)
    {
        ArgumentNullException.ThrowIfNull(source);

        if (source.Length == 0)
            return LinePrefix + NoLinkPrefix + "the program is empty.";

        if (source.Length > MaxSourceLength)
        {
            return LinePrefix + NoLinkPrefix +
                $"the program is {Count(source.Length)} UTF-16 code units long, " +
                $"more than the {Count(MaxSourceLength)} a code link can carry.";
        }

        var payload = LzString.CompressToEncodedUriComponent(source);
        if (payload.Length > MaxPayloadLength)
        {
            return LinePrefix + NoLinkPrefix +
                $"the program's link payload would be {Count(payload.Length)} characters long, " +
                $"more than the {Count(MaxPayloadLength)} a code link can carry.";
        }

        return LinePrefix + UrlPrefix + payload;
    }

    private static string Count(int value) => value.ToString("N0", CultureInfo.InvariantCulture);
}
