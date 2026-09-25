using System.Globalization;
using System.Text;

namespace KatLang;

/// <summary>
/// [HOST] The ONE owner of the module load-target contract: which source-written <c>load</c>
/// targets (and <c>open '…'</c> targets, which elaborate to the same call) KatLang admits, and the
/// CANONICAL MODULE URL an admitted target becomes. The canonical URL is at once the module's
/// identity — the per-URL module cache key and the cycle-detection key — the exact text handed to
/// <see cref="RunOptions.DownloadCode"/>, and the name every later diagnostic uses, so policy,
/// identity, transport, and reporting can never disagree about which resource a load means.
///
/// <para><b>Admission</b>, decided BEFORE the downloader is invoked, on the target as
/// <see cref="Uri"/> parses it — never on the written text:</para>
/// <list type="number">
///   <item>An absolute URI whose scheme is <c>https</c> (the scheme is case-insensitive).</item>
///   <item>No user information (<c>user@</c> or <c>user:password@</c>): credentials have no
///   place in module source, would reach the transport, and would be echoed in
///   diagnostics.</item>
///   <item>A host that is a DNS name with a valid IDNA form, or an IPv4 or IPv6 literal (an
///   IPv6 zone index is refused). A DNS host is judged — and forwarded — in its ASCII form
///   (<see cref="Uri.IdnHost"/>): the form every transport resolves. That conversion is the
///   runtime's own and varies by platform and globalization mode (under invariant
///   globalization .NET encodes code points without UTS46 mapping), so the same written name
///   can be refused on one platform and admitted as a different punycode name on another —
///   but because the downloader receives exactly the ASCII host that was judged, the verdict
///   and the request never disagree, and only DNS name characters can survive it. Comparing
///   the raw Unicode spelling instead admitted names such as <c>evil.test</c> + U+FF0F FULLWIDTH
///   SOLIDUS + <c>.katlang.org</c>, whose Unicode text ends with an allowed suffix while the
///   name has no DNS form at all, so a transport that NFKC-normalizes the authority would
///   split it at the solidus into a different host.</item>
///   <item>The host is allowed: a DNS host equals an allowed DNS entry or is a subdomain of one
///   (a whole-label suffix: <c>sub.ex.com</c> under <c>ex.com</c>, never <c>notex.com</c> or
///   <c>ex.com.evil.net</c>); an IP host equals an allowed IP entry exactly (no suffix rule).
///   Both sides are compared in canonical form (IDNA ASCII, letter case ignored; the IP
///   literal's canonical text), so <c>bücher.example</c> and <c>xn--bcher-kva.example</c>
///   are the same host. A trailing dot is significant: <c>ex.com.</c> is matched only by an
///   entry that is itself spelled with the trailing dot. The port is not part of the host:
///   ANY port of an allowed host is admitted.</item>
/// </list>
///
/// <para><b>Canonical module URL</b>: <c>https://</c>, the canonical host, the port when it is
/// not 443, and the escaped path and query exactly as <see cref="Uri"/> normalizes them (dot
/// segments resolved, host letter case folded, path case kept). The FRAGMENT is removed: it is
/// never sent in an HTTPS request (RFC 3986 §3.5 separates it before dereferencing), so two
/// spellings that differ only in their fragment name one module — one download, one cache
/// entry, one cycle identity. The canonical URL is printable ASCII and re-parses to itself; a
/// target for which that does not hold is refused as invalid rather than handed on.</para>
///
/// <para>This is host policy with no Lean counterpart (Lean models neither parsing nor module
/// loading). It governs the SOURCE-WRITTEN target only: what a host downloader does with the
/// URL afterwards — DNS resolution, redirects, proxies, credentials — is the host's
/// responsibility (see <see cref="RunOptions.AllowedHosts"/>).</para>
/// </summary>
internal static class ModuleLoadTarget
{
    /// <summary>The allow-list used when <see cref="RunOptions.AllowedHosts"/> is null.</summary>
    internal const string DefaultAllowedHost = "katlang.org";

    /// <summary>
    /// Longest written-target excerpt a diagnostic echoes (UTF-16 code units, before escaping):
    /// enough to recognize the target, bounded so a huge literal is not repeated in full.
    /// </summary>
    internal const int MaxEchoedTargetLength = 200;

    /// <summary>
    /// Longest excerpt of a downloader exception message a failed-fetch diagnostic echoes. The
    /// downloader is host code, but its message can carry remote-controlled text (an HTTP
    /// reason phrase, a response excerpt), so it is bounded and its control and format
    /// characters are escaped.
    /// </summary>
    internal const int MaxEchoedHostMessageLength = 500;

    /// <summary>A refused target: the structured code and the message the load site reports.</summary>
    internal readonly record struct Rejection(DiagnosticCode Code, string Message);

    /// <summary>
    /// Decides one source-written target. On admission <paramref name="moduleUrl"/> is the
    /// canonical module URL; otherwise <paramref name="rejection"/> says why, and the downloader
    /// must not be invoked.
    /// </summary>
    internal static bool TryAdmit(
        string writtenUrl,
        AllowedHosts allowedHosts,
        out string moduleUrl,
        out Rejection rejection)
    {
        moduleUrl = string.Empty;

        if (!Uri.TryCreate(writtenUrl, UriKind.Absolute, out var uri))
        {
            // A malformed port/host can prevent parsing BEFORE UserInfo is available.
            // Redaction is deliberately conservative; it never decides admission.
            rejection = Invalid(writtenUrl.Contains('@', StringComparison.Ordinal)
                ? "load: invalid URL; target omitted because it may contain user information."
                : $"load: invalid URL '{EchoWrittenText(writtenUrl)}'.");
            return false;
        }

        // Uri reports the scheme in lower case, so HTTPS:// and https:// are one scheme.
        if (uri.Scheme != Uri.UriSchemeHttps)
        {
            rejection = Invalid($"load: only HTTPS URLs are allowed (got '{EchoWrittenText(uri.Scheme)}').");
            return false;
        }

        // Deliberately not echoed: the refused part is a credential.
        // Uri.UserInfo alone cannot distinguish absent from explicitly empty userinfo.
        if (uri.UserInfo.Length != 0 || uri.GetLeftPart(UriPartial.Authority).Contains('@', StringComparison.Ordinal))
        {
            rejection = Invalid(
                "load: a module URL must not contain user information; remove the 'user@' or 'user:password@' part before the host.");
            return false;
        }

        if (!TryCanonicalHost(uri, out var host, out var isIpLiteral))
        {
            rejection = Invalid(
                $"load: invalid URL '{EchoWrittenText(writtenUrl)}': its host is not a valid DNS name or IP address.");
            return false;
        }

        if (!allowedHosts.Admits(host, isIpLiteral))
        {
            // The canonical host is printable ASCII (IDNA form or an IP literal), so it is
            // safe to echo whatever the written spelling was.
            rejection = Invalid($"load: domain not allowed: '{host}'.");
            return false;
        }

        var canonical = string.Concat(
            "https://",
            host,
            uri.IsDefaultPort ? string.Empty : ":" + uri.Port.ToString(CultureInfo.InvariantCulture),
            uri.PathAndQuery);

        // Fail closed if the canonical form is not a stable, printable-ASCII rendering of the
        // very target that was judged: the downloader and every diagnostic receive this text.
        if (!IsPrintableAscii(canonical)
            || !Uri.TryCreate(canonical, UriKind.Absolute, out var reparsed)
            || reparsed.AbsoluteUri != canonical
            || reparsed.Port != uri.Port
            || !TryCanonicalHost(reparsed, out var reparsedHost, out var reparsedIsIp)
            || reparsedHost != host
            || reparsedIsIp != isIpLiteral)
        {
            rejection = Invalid($"load: invalid URL '{EchoWrittenText(writtenUrl)}'.");
            return false;
        }

        moduleUrl = canonical;
        rejection = default;
        return true;
    }

    /// <summary>
    /// The canonical host of a parsed URI, or false when it has none: a DNS name in its
    /// lower-case ASCII IDNA form (false when the name has no valid IDNA form), an IPv4
    /// literal in dotted-quad form, or an IPv6 literal in bracketed compressed form (false
    /// for a zone index). Every other host kind is refused.
    /// </summary>
    private static bool TryCanonicalHost(Uri uri, out string host, out bool isIpLiteral)
    {
        host = string.Empty;
        isIpLiteral = false;
        switch (uri.HostNameType)
        {
            case UriHostNameType.Dns:
            {
                string ascii;
                try
                {
                    ascii = uri.IdnHost;
                }
                catch (UriFormatException)
                {
                    // Uri accepted the Unicode spelling, but it has no IDNA (DNS) form.
                    return false;
                }

                // The IDNA conversion is the runtime's and differs by platform and mode: the
                // Windows implementation refuses a fullwidth solidus, ICU can MAP it to '/', and
                // invariant globalization encodes it into a punycode label. Whatever it produced,
                // only DNS name characters may remain — never an authority delimiter.
                if (ascii.Length == 0 || !IsDnsNameText(ascii))
                    return false;

                host = ascii.ToLowerInvariant();
                return true;
            }

            case UriHostNameType.IPv4:
                host = uri.Host;
                isIpLiteral = true;
                return true;

            case UriHostNameType.IPv6:
                // Uri.Host drops a zone index ("%eth0") that IdnHost keeps; a link-local zone
                // names nothing a remote module could live at, and silently dropping it would
                // change the address, so refuse it.
                if (uri.IdnHost.Contains('%', StringComparison.Ordinal))
                    return false;

                host = uri.Host;
                isIpLiteral = true;
                return true;

            default:
                return false;
        }
    }

    /// <summary>
    /// ASCII letters, digits, <c>-</c>, <c>_</c> (which <see cref="Uri"/> accepts in names), and
    /// the <c>.</c> separator: the only characters of a DNS name a transport resolves.
    /// </summary>
    internal static bool IsDnsNameText(string text)
    {
        foreach (var ch in text)
        {
            if (ch is not ((>= 'a' and <= 'z') or (>= 'A' and <= 'Z') or (>= '0' and <= '9') or '-' or '_' or '.'))
                return false;
        }

        return true;
    }

    private static bool IsPrintableAscii(string text)
    {
        foreach (var ch in text)
        {
            if (ch is < '!' or > '~')
                return false;
        }

        return true;
    }

    private static Rejection Invalid(string message) => new(DiagnosticCode.InvalidLoadUrl, message);

    /// <summary>
    /// Renders source-written target text for a diagnostic: at most
    /// <see cref="MaxEchoedTargetLength"/> code units (then <c>...</c>), with every code unit
    /// outside printable ASCII shown as a <c>\uXXXX</c> escape. A refused target's text is
    /// evidence, so it must read exactly as written: a string literal can neither inject
    /// terminal control sequences nor reorder the message around it, and an authority-delimiter
    /// lookalike (a fullwidth solidus, which a legacy console code page even renders as
    /// <c>/</c>) stays visibly distinct from the delimiter it imitates. Malformed targets
    /// containing an at sign are omitted instead, since parsing cannot safely isolate userinfo.
    /// </summary>
    internal static string EchoWrittenText(string text) => Echo(text, MaxEchoedTargetLength, escapeNonAscii: true);

    /// <summary>
    /// Renders a downloader exception message for a failed-fetch diagnostic, bounded to
    /// <see cref="MaxEchoedHostMessageLength"/> code units (then <c>...</c>), with every
    /// control, format (for example a bidirectional override), line- or paragraph-separator,
    /// and unpaired surrogate code unit shown as a <c>\uXXXX</c> escape; other text — a
    /// localized system message included — is kept. A null message renders as empty.
    /// </summary>
    internal static string EchoHostMessage(string? message) => Echo(message ?? string.Empty, MaxEchoedHostMessageLength, escapeNonAscii: false);

    private static string Echo(string text, int maxLength, bool escapeNonAscii)
    {
        var builder = new StringBuilder(Math.Min(text.Length, maxLength) + 8);
        var index = 0;
        while (index < text.Length)
        {
            if (index >= maxLength)
            {
                builder.Append("...");
                break;
            }

            var ch = text[index];
            if (!escapeNonAscii
                && char.IsHighSurrogate(ch) && index + 1 < Math.Min(text.Length, maxLength)
                && char.IsLowSurrogate(text[index + 1])
                && char.GetUnicodeCategory(text, index) != UnicodeCategory.Format)
            {
                builder.Append(ch).Append(text[index + 1]);
                index += 2;
                continue;
            }

            if (escapeNonAscii ? ch is < ' ' or > '~' : NeedsEscape(ch))
                builder.Append("\\u").Append(((int)ch).ToString("X4", CultureInfo.InvariantCulture));
            else
                builder.Append(ch);

            index++;
        }

        return builder.ToString();
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

    /// <summary>
    /// The canonical allow-list: DNS entries in lower-case ASCII IDNA form and IP entries in
    /// canonical literal form, built from <see cref="RunOptions.AllowedHosts"/> (or the
    /// <see cref="DefaultAllowedHost"/> default). An entry is written as a bare host — a DNS
    /// name or an IP literal (IPv6 with or without brackets) — and surrounding whitespace is
    /// ignored. An entry that is not a host (blank, a URL, <c>host:port</c>, a wildcard, a name
    /// with no IDNA form) admits NOTHING: the options boundary refuses blank entries before a
    /// loader exists (<see cref="FrontEndPipeline.NormalizeAllowedHosts"/>), and every other
    /// unusable entry fails closed here.
    /// </summary>
    internal sealed class AllowedHosts
    {
        private readonly HashSet<string> _dnsNames = new(StringComparer.Ordinal);
        private readonly HashSet<string> _ipLiterals = new(StringComparer.Ordinal);

        private AllowedHosts()
        {
        }

        internal static AllowedHosts From(IEnumerable<string?>? entries)
        {
            var hosts = new AllowedHosts();
            foreach (var entry in entries ?? [DefaultAllowedHost])
            {
                if (TryCanonicalEntry(entry, out var host, out var isIpLiteral))
                    (isIpLiteral ? hosts._ipLiterals : hosts._dnsNames).Add(host);
            }

            return hosts;
        }

        /// <summary>
        /// Whether a canonical host is admitted: an IP literal only by an equal IP entry; a DNS
        /// name by an equal DNS entry or by one that is a whole-label suffix of it.
        /// </summary>
        internal bool Admits(string canonicalHost, bool isIpLiteral)
        {
            if (isIpLiteral)
                return _ipLiterals.Contains(canonicalHost);

            if (_dnsNames.Contains(canonicalHost))
                return true;

            // Every proper whole-label suffix: "a.b.ex.com" tries "b.ex.com", "ex.com", "com".
            // The empty suffix after a trailing dot is never an entry (entries are non-blank).
            for (var dot = canonicalHost.IndexOf('.'); dot >= 0; dot = canonicalHost.IndexOf('.', dot + 1))
            {
                var suffix = canonicalHost[(dot + 1)..];
                if (suffix.Length != 0 && _dnsNames.Contains(suffix))
                    return true;
            }

            return false;
        }

        private static bool TryCanonicalEntry(string? entry, out string host, out bool isIpLiteral)
        {
            host = string.Empty;
            isIpLiteral = false;
            if (string.IsNullOrWhiteSpace(entry))
                return false;

            var trimmed = entry.Trim();
            var kind = Uri.CheckHostName(trimmed);
            string authority;
            switch (kind)
            {
                case UriHostNameType.Dns:
                case UriHostNameType.IPv4:
                    authority = trimmed;
                    break;
                case UriHostNameType.IPv6:
                    authority = trimmed.StartsWith('[') ? trimmed : "[" + trimmed + "]";
                    break;
                default:
                    return false;
            }

            // Parse the bare host exactly as a load target's host is parsed, so both sides of
            // the comparison come from ONE parser; anything that parses as more than a host
            // (user information, a port, a path) is not an entry.
            if (!Uri.TryCreate("https://" + authority + "/", UriKind.Absolute, out var parsed)
                || parsed.HostNameType != kind
                || parsed.UserInfo.Length != 0
                || !parsed.IsDefaultPort
                || parsed.PathAndQuery != "/"
                || parsed.Fragment.Length != 0)
            {
                return false;
            }

            return TryCanonicalHost(parsed, out host, out isIpLiteral);
        }
    }
}
