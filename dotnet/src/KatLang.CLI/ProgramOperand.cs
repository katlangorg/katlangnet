namespace KatLang.CLI;

/// <summary>Where the program of a <c>run</c>, <c>check</c> or <c>source</c> operand comes from.</summary>
internal enum ProgramOperandKind
{
    /// <summary>A file path, read from disk.</summary>
    File,

    /// <summary>
    /// A code link: the program is in the link itself, decoded offline by
    /// <see cref="CodeLink.DecodeLink"/>. Never downloaded.
    /// </summary>
    CodeLink,

    /// <summary>A program URL: the program is downloaded as text from an HTTPS address.</summary>
    ProgramUrl,
}

/// <summary>
/// The ONE place the CLI decides what an operand names. Only the way the program text is
/// obtained differs between the three kinds; everything after that is the same command.
///
/// <list type="bullet">
///   <item>For <c>run</c> and <c>check</c>, an operand that starts with <c>https://</c> or
///   <c>http://</c> (ASCII, letter case ignored) is a link. Every other operand is a file
///   path, as before, also after a bare <c>--</c>; a file whose path really starts that way
///   is still reachable as <c>./https:…</c>.</item>
///   <item>For <c>source</c> the operand is always a link.</item>
///   <item>A link with a <c>#</c> is read as a code link and is NEVER downloaded: a fragment
///   never reaches a server, so it can only mean a program carried in the link, and
///   <c>#&lt;format&gt;/&lt;payload&gt;</c> is the one such form — whatever origin, path or query
///   comes before the <c>#</c>. A fragment of any other shape is therefore an invalid code
///   link (<see cref="CodeLinkRefusal.NotACodeLink"/>), with the sentence <c>source</c> has
///   always used, instead of a download of whatever page the address before it names: an
///   old <c>#code/</c> link, for example, would otherwise fetch the Playground's HTML.</item>
///   <item>Every other web link is a program URL.</item>
///   <item>A <c>source</c> operand that is no web link and has no fragment is read as a code
///   link too, and is refused as one, as before.</item>
/// </list>
/// </summary>
internal static class ProgramOperand
{
    public static ProgramOperandKind Classify(CliCommandKind command, string operand)
    {
        var isWebLink = IsWebLink(operand);
        if (command != CliCommandKind.Source && !isWebLink)
            return ProgramOperandKind.File;

        return isWebLink && !operand.Contains('#')
            ? ProgramOperandKind.ProgramUrl
            : ProgramOperandKind.CodeLink;
    }

    /// <summary>Whether <paramref name="operand"/> starts with <c>https://</c> or <c>http://</c>.</summary>
    public static bool IsWebLink(string operand)
        => operand.StartsWith("https://", StringComparison.OrdinalIgnoreCase)
            || operand.StartsWith("http://", StringComparison.OrdinalIgnoreCase);
}

/// <summary>
/// A program URL operand: the address the CLI downloads for it, and how the CLI echoes it.
/// Whether the address may be downloaded at all is the downloader's decision
/// (<see cref="HttpSourceDownloader"/>): this type only names the address.
/// </summary>
internal static class ProgramUrl
{
    /// <summary>The site whose shared-program pages the CLI knows: katlang.org and its subdomains.</summary>
    private const string SharingSite = "katlang.org";

    private const string SharePagePrefix = "/a/";

    private const string RawCodePrefix = "/api/a/";

    /// <summary>
    /// The address to download for <paramref name="link"/>: the link as given, except for the
    /// one route the CLI knows. A shared program's page, <c>https://&lt;host&gt;/a/&lt;shareId&gt;</c>
    /// on katlang.org or a subdomain of it, is HTML; its raw-code sibling
    /// <c>https://&lt;same host&gt;/api/a/&lt;shareId&gt;</c> is the same program as text, so that is
    /// what is downloaded, and the page never is. The share id is a GUID in either letter
    /// case; a query and one trailing <c>/</c> are dropped. On any other host <c>/a/…</c> is
    /// an ordinary path, and so is any other path on katlang.org.
    /// </summary>
    public static string DownloadAddress(string link)
    {
        if (!Uri.TryCreate(link, UriKind.Absolute, out var address)
            || address.Scheme != Uri.UriSchemeHttps
            || address.HostNameType != UriHostNameType.Dns
            || HasUserInformation(address))
        {
            // Not a page the CLI knows; the downloader judges the link as given.
            return link;
        }

        var host = address.Host.ToLowerInvariant();
        if (host != SharingSite && !host.EndsWith("." + SharingSite, StringComparison.Ordinal))
            return link;

        var path = address.AbsolutePath;
        if (!path.StartsWith(SharePagePrefix, StringComparison.Ordinal))
            return link;

        var shareId = path[SharePagePrefix.Length..];
        if (shareId.EndsWith('/'))
            shareId = shareId[..^1];

        if (!Guid.TryParseExact(shareId, "D", out _))
            return link;

        var port = address.IsDefaultPort ? string.Empty : ":" + address.Port.ToString(System.Globalization.CultureInfo.InvariantCulture);
        return $"https://{host}{port}{RawCodePrefix}{shareId}";
    }

    /// <summary>
    /// <paramref name="link"/> as an error line quotes it: as given, except that user
    /// information (<c>user@</c>, <c>user:password@</c>) is shown as <c>&lt;redacted&gt;</c>. The
    /// refused part is a credential, so it is never written back. The cut is textual — the
    /// text between <c>://</c> and the last <c>@</c> of the authority — because a link with
    /// user information may not parse at all.
    /// </summary>
    public static string Echo(string link)
    {
        var scheme = link.IndexOf("://", StringComparison.Ordinal);
        if (scheme < 0)
            return link;

        var authorityStart = scheme + 3;
        var authorityEnd = link.AsSpan(authorityStart).IndexOfAny("/?#\\");
        authorityEnd = authorityEnd < 0 ? link.Length : authorityStart + authorityEnd;

        var at = link.LastIndexOf('@', authorityEnd - 1, authorityEnd - authorityStart);
        return at < 0
            ? link
            : string.Concat(link.AsSpan(0, authorityStart), "<redacted>", link.AsSpan(at));
    }

    private static bool HasUserInformation(Uri address)
        => address.UserInfo.Length != 0
            || address.GetLeftPart(UriPartial.Authority).Contains('@', StringComparison.Ordinal);
}
