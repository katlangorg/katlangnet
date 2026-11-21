using System.Diagnostics.CodeAnalysis;

namespace KatLang;

/// <summary>
/// KatLang code links: a program carried in a katlang.org URL,
/// <c>https://katlang.org/#&lt;format&gt;/&lt;payload&gt;</c>, for example
/// <c>https://katlang.org/#1/4MWjDBlNE4PH</c>. Opening one shows the program in the Playground
/// and runs it. <see cref="Encode"/> makes a program's link, and <see cref="DecodeLink"/> and
/// <see cref="Decode"/> read the program back, with every check a reader makes before it opens
/// a link.
///
/// <para>The link's fragment is the number of the format the payload is in, a <c>/</c>, and the
/// payload. The format is KatLang's own, specified in <c>docs/design/code-link-format.md</c>:
/// the payload is the program compressed, in the URL-safe alphabet <c>A–Z a–z 0–9 - _</c>.
/// The reader checks a 12-bit check value and requires the canonical payload for the named
/// format. Each program that fits the limits has one canonical payload in that format.
/// An edit can still produce a valid link to a different program. Only the owner introduces a
/// new format, independently of language changes. <see cref="CurrentFormat"/> then names it,
/// <see cref="Encode"/> writes it, and reading keeps every earlier format, so links already
/// shared keep opening.</para>
///
/// <para>A program is a sequence of UTF-16 code units, and nothing in it is interpreted or
/// normalized: line breaks, tabs, trailing spaces and a final line break are part of the
/// program, and a surrogate, paired or not, is carried exactly.</para>
///
/// <para>This is a host and tooling format, not KatLang semantics: nothing here parses or runs
/// a program, and a link carries only source text (no results, settings or identity). Anyone
/// who has a link can read its program. The methods keep no state of their own beyond the
/// format's fixed starting state, built once per process, and are safe to call
/// concurrently.</para>
/// </summary>
public static class CodeLink
{
    /// <summary>
    /// The longest payload a code link carries, in characters. With the 23 characters of
    /// <c>https://katlang.org/#1/</c> a canonical link is then at most 1,993 characters long:
    /// under 2,000, the length beyond which some browsers, mail and chat programs cut links
    /// short or refuse them, with a small reserve.
    /// </summary>
    public const int MaxPayloadLength = 1_970;

    /// <summary>
    /// The longest program a code link carries, in UTF-16 code units. A payload of
    /// <see cref="MaxPayloadLength"/> characters holds about 4,000 to 5,500 characters of
    /// ordinary KatLang, and more only for text that repeats itself; the limit stays well above
    /// that, and bounds the work of reading a link to three bytes per code unit.
    /// </summary>
    public const int MaxSourceLength = 20_000;

    /// <summary>The address of the Playground that canonical code links open.</summary>
    public const string CanonicalBaseUrl = "https://katlang.org/";

    /// <summary>
    /// The format <see cref="Encode"/> writes. Formats are numbered from 1; a new one is the
    /// owner's decision, and readers keep every earlier one.
    /// </summary>
    public const int CurrentFormat = CodeLinkFormat.Number;

    // A format number is one to nine decimal digits, the first not zero.
    private const int MaxFormatDigits = 9;

    /// <summary>
    /// The code link of the program <paramref name="source"/>, or why it has none. The checks
    /// are made in this order: an empty program has no link; a program longer than
    /// <see cref="MaxSourceLength"/> code units has none and is never encoded; and one whose
    /// payload would be longer than <see cref="MaxPayloadLength"/> characters has none either.
    /// The payload is in <see cref="CurrentFormat"/>.
    /// </summary>
    /// <exception cref="ArgumentNullException"><paramref name="source"/> is <c>null</c>.</exception>
    public static CodeLinkEncoding Encode(string source)
    {
        ArgumentNullException.ThrowIfNull(source);

        if (source.Length == 0)
            return new CodeLinkEncoding.EmptyProgram();

        if (source.Length > MaxSourceLength)
            return new CodeLinkEncoding.SourceTooLong(source.Length);

        var payload = CodeLinkFormat.Encode(source);
        return payload.Length > MaxPayloadLength
            ? new CodeLinkEncoding.PayloadTooLong(payload.Length)
            : new CodeLinkEncoding.Link(CurrentFormat, payload);
    }

    /// <summary>
    /// The program the payload <paramref name="payload"/> of the format
    /// <paramref name="format"/> carries, or why it is refused. The checks are made in this
    /// order, and the first that fails is the refusal (<see cref="CodeLinkRefusal"/>):
    /// <list type="number">
    /// <item>The format is one this KatLang reads (format 1). A link in a newer format is
    /// refused as <see cref="CodeLinkRefusal.UnsupportedVersion"/>.</item>
    /// <item>The payload is not empty, and at most <see cref="MaxPayloadLength"/> characters
    /// long.</item>
    /// <item>Every character is one of <c>A–Z a–z 0–9 - _</c>. Nothing is percent-decoded or
    /// trimmed: no character of a payload ever needs it.</item>
    /// <item>The stream decodes to a program of at most <see cref="MaxSourceLength"/> code
    /// units whose check value matches.</item>
    /// <item>Re-encoding the program in that format gives the payload back exactly.</item>
    /// </list>
    ///
    /// <para>The work is bounded however the payload was made: it is linear in the program
    /// length the stream announces, which a reader refuses above three bytes per code unit of
    /// <see cref="MaxSourceLength"/>, and reading stops at the first byte that cannot belong to
    /// a program a link carries.</para>
    /// </summary>
    /// <exception cref="ArgumentNullException"><paramref name="payload"/> is <c>null</c>.</exception>
    public static CodeLinkDecoding Decode(int format, string payload)
    {
        ArgumentNullException.ThrowIfNull(payload);
        return DecodePayload(format, payload, 0);
    }

    /// <summary>
    /// Whether the link <paramref name="link"/> is a code link, and if so its format and
    /// payload: its fragment, everything after the first <c>#</c>, is a format number (one to
    /// nine ASCII decimal digits, the first not zero), a <c>/</c>, and the payload, possibly empty and
    /// as the link holds it (<see cref="Decode"/> decides what it says), so a later <c>#</c> is
    /// part of the payload. Only the fragment is read: the link's origin, path and query are not
    /// checked, and a host that opens links applies its own route policy.
    /// </summary>
    /// <exception cref="ArgumentNullException"><paramref name="link"/> is <c>null</c>.</exception>
    public static bool TryGetPayload(string link, out int format, [NotNullWhen(true)] out string? payload)
    {
        ArgumentNullException.ThrowIfNull(link);
        if (!TryReadFragment(link, out format, out var start))
        {
            payload = null;
            return false;
        }

        payload = link[start..];
        return true;
    }

    /// <summary>
    /// The program the link <paramref name="link"/> carries, or why it is refused:
    /// <see cref="TryGetPayload"/>, then <see cref="Decode"/>. A link whose fragment is not
    /// <c>&lt;format&gt;/&lt;payload&gt;</c> is refused as
    /// <see cref="CodeLinkRefusal.NotACodeLink"/>, links in the earlier <c>#code/</c> format
    /// included. The link is read exactly as given, with nothing trimmed.
    /// </summary>
    /// <exception cref="ArgumentNullException"><paramref name="link"/> is <c>null</c>.</exception>
    public static CodeLinkDecoding DecodeLink(string link)
    {
        ArgumentNullException.ThrowIfNull(link);
        return TryReadFragment(link, out var format, out var start)
            ? DecodePayload(format, link, start)
            : Refuse(CodeLinkRefusal.NotACodeLink);
    }

    private static CodeLinkDecoding DecodePayload(int format, string input, int payloadStart)
    {
        if (format != CodeLinkFormat.Number)
            return Refuse(CodeLinkRefusal.UnsupportedVersion);

        var length = input.Length - payloadStart;
        if (length == 0)
            return Refuse(CodeLinkRefusal.EmptyPayload);

        // Checked before the payload is copied out of a link.
        if (length > MaxPayloadLength)
            return Refuse(CodeLinkRefusal.PayloadTooLong);

        for (var i = payloadStart; i < input.Length; i++)
        {
            if (CodeLinkFormat.DigitOf(input[i]) < 0)
                return Refuse(CodeLinkRefusal.InvalidCharacter);
        }

        return CodeLinkFormat.Read(payloadStart == 0 ? input : input[payloadStart..]);
    }

    /// <summary>
    /// Reads a code-link fragment: the format number after the first <c>#</c>, and where the
    /// payload starts, after the <c>/</c> that ends the number.
    /// </summary>
    private static bool TryReadFragment(string link, out int format, out int payloadStart)
    {
        format = 0;
        payloadStart = -1;

        var hash = link.IndexOf('#');
        if (hash < 0)
            return false;

        var start = hash + 1;
        var end = start;
        var number = 0;
        while (end < link.Length && end - start < MaxFormatDigits && char.IsAsciiDigit(link[end]))
        {
            number = number * 10 + (link[end] - '0');
            end++;
        }

        if (end == start || link[start] == '0' || end == link.Length || link[end] != '/')
            return false;

        format = number;
        payloadStart = end + 1;
        return true;
    }

    private static CodeLinkDecoding.Refused Refuse(CodeLinkRefusal reason) => new(reason);
}
