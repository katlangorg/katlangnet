using System.Globalization;

namespace KatLang.CLI;

/// <summary>
/// The CLI's wording for KatLang code links (<see cref="CodeLink"/>, the KatLang package's):
/// the one line <c>--code-link</c> writes, and the reason <c>source</c> gives for a link it
/// cannot read. The format, its limits and every verdict are the package's; only the text is
/// decided here, and it is exact, because tools read these lines (the KatLang agent skill
/// among them). Every line is printable ASCII: a payload's alphabet and the fixed text below.
/// </summary>
internal static class CodeLinkText
{
    /// <summary>What every line <c>--code-link</c> writes starts with.</summary>
    public const string LinePrefix = "katlang-link: ";

    /// <summary>
    /// What a line for a program with no link carries after <see cref="LinePrefix"/>, before
    /// the reason.
    /// </summary>
    public const string NoLinkPrefix = "none: ";

    /// <summary>
    /// The one line <c>--code-link</c> writes for <paramref name="source"/>, without its line
    /// break: <c>katlang-link: https://katlang.org/#1/&lt;payload&gt;</c>, or
    /// <c>katlang-link: none: &lt;reason&gt;</c> for a program that cannot be a code link — an
    /// empty one, one longer than <see cref="CodeLink.MaxSourceLength"/> code units (which is
    /// never encoded), or one whose payload is longer than
    /// <see cref="CodeLink.MaxPayloadLength"/> characters.
    /// </summary>
    public static string Line(string source)
    {
        var text = CodeLink.Encode(source) switch
        {
            CodeLinkEncoding.Link link => link.Url,
            CodeLinkEncoding.EmptyProgram => NoLinkPrefix + "the program is empty.",
            CodeLinkEncoding.SourceTooLong tooLong => NoLinkPrefix +
                $"the program is {Count(tooLong.SourceLength)} UTF-16 code units long, " +
                $"more than the {Count(CodeLink.MaxSourceLength)} a code link can carry.",
            CodeLinkEncoding.PayloadTooLong tooLong => NoLinkPrefix +
                $"the program's link payload would be {Count(tooLong.PayloadLength)} characters long, " +
                $"more than the {Count(CodeLink.MaxPayloadLength)} a code link can carry.",
        };
        return LinePrefix + text;
    }

    /// <summary>
    /// Why <c>source</c> cannot read a link, as the text after <c>invalid code link: </c>: one
    /// fixed sentence for each <see cref="CodeLinkRefusal"/>.
    /// </summary>
    public static string RefusalReason(CodeLinkRefusal reason) => reason switch
    {
        CodeLinkRefusal.NotACodeLink => "it has no #<format>/<payload> fragment.",
        CodeLinkRefusal.EmptyPayload => "its payload is empty.",
        CodeLinkRefusal.PayloadTooLong => $"its payload is longer than {Count(CodeLink.MaxPayloadLength)} characters.",
        CodeLinkRefusal.InvalidCharacter => "its payload has a character that code links do not use.",
        CodeLinkRefusal.UnsupportedVersion => "its format is not one this KatLang reads; a newer KatLang may read it.",
        CodeLinkRefusal.Damaged => "its payload is damaged or cut short.",
        CodeLinkRefusal.SourceTooLong => $"its program is longer than {Count(CodeLink.MaxSourceLength)} UTF-16 code units.",
        CodeLinkRefusal.NotCanonical => "its payload does not re-encode to itself, so it was changed.",
        _ => throw new ArgumentOutOfRangeException(nameof(reason), reason, "Unknown code link refusal."),
    };

    private static string Count(int value) => value.ToString("N0", CultureInfo.InvariantCulture);
}
