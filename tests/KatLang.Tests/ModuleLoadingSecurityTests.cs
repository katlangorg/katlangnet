using System.Collections.Concurrent;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// #13 module loading / security / resource audit — the load-target contract
/// (<see cref="ModuleLoadTarget"/>) and the per-download module budget, observed through the
/// public parse and run entry points with deterministic in-memory downloaders that RECORD every
/// request (no network). Every refusal is asserted by its concrete effect — the downloader was
/// never invoked, the exact URL it was invoked with, the call count — never by "the parse failed"
/// alone: a failure after an illicit request is still a broken boundary.
/// Host policy with no Lean counterpart (Lean models neither parsing nor module loading).
/// </summary>
public sealed class ModuleLoadingSecurityTests
{
    private const string Trusted = "trusted.example";

    private static string U(int codePoint) => char.ConvertFromUtf32(codePoint);

    /// <summary>Records every downloader request, in order, with the token it received.</summary>
    private sealed class RecordingDownloader(Func<string, string>? respond = null)
    {
        private readonly Func<string, string> _respond = respond ?? (_ => "public V = 1");

        public ConcurrentQueue<string> Requests { get; } = new();

        public ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            Requests.Enqueue(url);
            return ValueTask.FromResult(_respond(url));
        }
    }

    private static async Task<(ParseResult Parsed, RecordingDownloader Downloader)> ParseLoading(
        string source,
        IEnumerable<string>? allowedHosts = null,
        Func<string, string>? respond = null,
        SourceProcessingLimits? limits = null)
    {
        var downloader = new RecordingDownloader(respond);
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            DownloadCode = downloader.Download,
            AllowedHosts = allowedHosts ?? [Trusted],
            SourceProcessingLimits = limits,
        });
        return (parsed, downloader);
    }

    private static Diagnostic SingleError(ParseResult parsed)
        => Assert.Single(parsed.Diagnostics, diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);

    private static void AssertNoDiagnostics(ParseResult parsed)
        => Assert.True(parsed.Diagnostics.Count == 0, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));

    // ── 1. Host allow-list: the parsed host, canonical, whole labels ──────────

    [Theory]
    [InlineData("https://trusted.example/m.kat", "https://trusted.example/m.kat")]
    [InlineData("https://TRUSTED.EXAMPLE/m.kat", "https://trusted.example/m.kat")]
    [InlineData("HTTPS://trusted.example/m.kat", "https://trusted.example/m.kat")]
    [InlineData("hTTpS://Trusted.Example/m.kat", "https://trusted.example/m.kat")]
    [InlineData("https://sub.trusted.example/m.kat", "https://sub.trusted.example/m.kat")]
    [InlineData("https://a.b.sub.trusted.example/m.kat", "https://a.b.sub.trusted.example/m.kat")]
    [InlineData("https://trusted.example:443/m.kat", "https://trusted.example/m.kat")]
    [InlineData("https://trusted.example:8443/m.kat", "https://trusted.example:8443/m.kat")]
    [InlineData("https://trusted.example", "https://trusted.example/")]
    [InlineData(" https://trusted.example/m.kat ", "https://trusted.example/m.kat")]
    public async Task AllowedTarget_IsRequestedOnce_InItsCanonicalForm(string written, string requested)
    {
        var (parsed, downloader) = await ParseLoading($"M = load('{written}')\nM.V");

        AssertNoDiagnostics(parsed);
        Assert.Equal([requested], downloader.Requests);
    }

    [Theory]
    [InlineData("https://eviltrusted.example/m.kat", "eviltrusted.example")]
    [InlineData("https://trusted.example.evil.test/m.kat", "trusted.example.evil.test")]
    [InlineData("https://xtrusted.example/m.kat", "xtrusted.example")]
    [InlineData("https://example/m.kat", "example")]
    // Root-anchored (trailing-dot) spelling: DNS treats it as the same name, but the allow-list
    // is textual on the canonical host and fails CLOSED — only a trailing-dot entry admits it.
    [InlineData("https://trusted.example./m.kat", "trusted.example.")]
    [InlineData("https://sub.trusted.example./m.kat", "sub.trusted.example.")]
    public async Task HostConfusion_IsRefusedBeforeTheDownloader(string written, string canonicalHost)
    {
        var (parsed, downloader) = await ParseLoading($"M = load('{written}')\nM.V");

        var error = SingleError(parsed);
        Assert.Equal(DiagnosticCode.InvalidLoadUrl, error.Code);
        Assert.Equal($"load: domain not allowed: '{canonicalHost}'.", error.Message);
        Assert.Empty(downloader.Requests);
    }

    [Theory]
    [InlineData("https://evil.test@trusted.example/m.kat", "evil.test")]
    [InlineData("https://trusted.example@evil.test/m.kat", "trusted.example")]
    [InlineData("https://alice:s3cr3t-t0ken@trusted.example/m.kat", "s3cr3t-t0ken")]
    [InlineData("https://:s3cr3t-t0ken@trusted.example/m.kat", "s3cr3t-t0ken")]
    [InlineData("https://alice%3As3cr3t@trusted.example/m.kat", "s3cr3t")]
    public async Task UserInformation_IsRefused_AndTheCredentialIsNeverEchoed(string written, string secret)
    {
        var (parsed, downloader) = await ParseLoading($"M = load('{written}')\nM.V");

        Assert.Empty(downloader.Requests);
        var error = SingleError(parsed);
        Assert.Equal(DiagnosticCode.InvalidLoadUrl, error.Code);
        Assert.DoesNotContain(secret, error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain(written, error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task EmptyUserInformation_IsRefusedBeforeTheTransport()
    {
        // "https://@host/" has an EMPTY user-information part: Uri reports none and keeps the
        // '@' in AbsoluteUri. The no-userinfo contract includes this empty form.
        var (parsed, downloader) = await ParseLoading("M = load('https://@trusted.example/m.kat')\nM.V");

        Assert.Equal(DiagnosticCode.InvalidLoadUrl, SingleError(parsed).Code);
        Assert.Empty(downloader.Requests);
    }

    [Theory]
    [InlineData("http://trusted.example/m.kat", "http")]
    [InlineData("file:///C:/m.kat", "file")]
    [InlineData("ftp://trusted.example/m.kat", "ftp")]
    [InlineData("ws://trusted.example/m.kat", "ws")]
    [InlineData("data:text/plain,public V = 1", "data")]
    [InlineData("javascript:alert(1)", "javascript")]
    [InlineData("custom://trusted.example/m.kat", "custom")]
    public async Task NonHttpsScheme_IsRefusedBeforeTheDownloader(string written, string scheme)
    {
        var (parsed, downloader) = await ParseLoading($"M = load('{written}')\nM.V");

        var error = SingleError(parsed);
        Assert.Equal(DiagnosticCode.InvalidLoadUrl, error.Code);
        Assert.Equal($"load: only HTTPS URLs are allowed (got '{scheme}').", error.Message);
        Assert.Empty(downloader.Requests);
    }

    [Theory]
    [InlineData(@"https:\\trusted.example\m.kat")]
    [InlineData("https:/trusted.example/m.kat")]
    [InlineData("https:trusted.example/m.kat")]
    [InlineData("https:///trusted.example/m.kat")]
    [InlineData(@"https://trusted.example\@evil.test/m.kat")]
    [InlineData(@"https://evil.test\@trusted.example/m.kat")]
    [InlineData("https://evil.test%40trusted.example/m.kat")]
    [InlineData("https://trusted.example%2F.evil.test/m.kat")]
    [InlineData("https://trusted.example:99999/m.kat")]
    [InlineData("https://tru sted.example/m.kat")]
    [InlineData("trusted.example/m.kat")]
    [InlineData("//trusted.example/m.kat")]
    [InlineData("")]
    public async Task MalformedTarget_IsRefusedBeforeTheDownloader(string written)
    {
        var (parsed, downloader) = await ParseLoading($"M = load('{written}')\nM.V");

        Assert.Equal(DiagnosticCode.InvalidLoadUrl, SingleError(parsed).Code);
        Assert.Empty(downloader.Requests);
    }

    // ── 2. IDN: the host is judged — and forwarded — in its DNS (IDNA) form ──

    [Fact]
    public async Task UnicodeAndPunycodeSpellings_AreOneHost_OnBothSidesOfTheAllowList()
    {
        var unicodeHost = "b" + U(0xFC) + "cher.example";
        const string asciiHost = "xn--bcher-kva.example";

        foreach (var (entry, writtenHost) in new[]
        {
            (unicodeHost, unicodeHost),
            (unicodeHost, asciiHost),
            (asciiHost, unicodeHost),
            (asciiHost, asciiHost),
        })
        {
            var (parsed, downloader) = await ParseLoading($"M = load('https://{writtenHost}/m.kat')\nM.V", [entry]);

            AssertNoDiagnostics(parsed);
            // The transport receives ONE ASCII spelling: no second IDNA interpretation downstream.
            Assert.Equal([$"https://{asciiHost}/m.kat"], downloader.Requests);
        }
    }

    public static TheoryData<string> AuthorityDelimiterLookalikes() => new()
    {
        U(0xFF0F), // FULLWIDTH SOLIDUS          -> '/' under NFKC
        U(0xFF03), // FULLWIDTH NUMBER SIGN      -> '#'
        U(0xFF1F), // FULLWIDTH QUESTION MARK    -> '?'
        U(0xFF1A), // FULLWIDTH COLON            -> ':'
        U(0xFF20), // FULLWIDTH COMMERCIAL AT    -> '@'
    };

    [Theory]
    [MemberData(nameof(AuthorityDelimiterLookalikes))]
    public async Task HostWithAnAuthorityDelimiterLookalike_IsRefused_ThoughItsTextEndsWithAnAllowedSuffix(string lookalike)
    {
        // SEC: the former policy compared Uri.Host (raw Unicode) and admitted
        // "evil.test<U+FF0F>.trusted.example" because its TEXT ends with ".trusted.example" — while the
        // name has no DNS form at all (Uri.IdnHost throws), and an NFKC-normalizing transport
        // would split the authority at the lookalike and connect to evil.test.
        var written = $"https://evil.test{lookalike}.{Trusted}/m.kat";
        var (parsed, downloader) = await ParseLoading($"M = load('{written}')\nM.V");

        Assert.Empty(downloader.Requests);
        var error = SingleError(parsed);
        Assert.Equal(DiagnosticCode.InvalidLoadUrl, error.Code);
        Assert.Contains("its host is not a valid DNS name or IP address", error.Message, StringComparison.Ordinal);
        // The echo shows the lookalike as an escape: the refused text never reads as a delimiter.
        Assert.Contains("\\u" + ((int)lookalike[0]).ToString("X4", System.Globalization.CultureInfo.InvariantCulture), error.Message, StringComparison.Ordinal);
        Assert.All(error.Message, ch => Assert.InRange(ch, ' ', '~'));
    }

    [Theory]
    [InlineData("trusted.example", true)]
    [InlineData("xn--bcher-kva.example", true)]
    [InlineData("a_b.sub-1.trusted.example.", true)]
    [InlineData("evil.test/.trusted.example", false)] // where ICU MAPS U+FF0F instead of refusing it
    [InlineData("evil.test#.trusted.example", false)]
    [InlineData("evil.test?.trusted.example", false)]
    [InlineData("evil.test:443.trusted.example", false)]
    [InlineData("evil.test@trusted.example", false)]
    [InlineData("evil.test\\.trusted.example", false)]
    [InlineData("evil test.example", false)]
    [InlineData("bücher.example", false)]
    [InlineData("", true)]
    public void IdnaResult_MustBeDnsNameText_WhateverThePlatformConversionProduced(string ascii, bool isDnsText)
        // The IDNA conversion differs by platform (Windows refuses a fullwidth solidus, ICU can
        // map it to '/', invariant globalization punycode-encodes it); the guard behind it
        // admits only DNS name characters, so no platform's result can carry an authority
        // delimiter into the canonical URL. (Emptiness is refused separately.)
        => Assert.Equal(isDnsText, ModuleLoadTarget.IsDnsNameText(ascii));

    [Theory]
    [InlineData(0xFF0E)] // FULLWIDTH FULL STOP
    [InlineData(0x3002)] // IDEOGRAPHIC FULL STOP
    [InlineData(0xFF61)] // HALFWIDTH IDEOGRAPHIC FULL STOP
    public async Task IdnaLabelSeparatorSpelling_IsTheSameAllowedHost(int separator)
    {
        var (parsed, downloader) = await ParseLoading($"M = load('https://trusted{U(separator)}example/m.kat')\nM.V");

        AssertNoDiagnostics(parsed);
        Assert.Equal(["https://trusted.example/m.kat"], downloader.Requests);
    }

    [Fact]
    public async Task IdnaMappedLetter_IsTheSameAllowedHost_AndAValidDistinctLetterIsNot()
    {
        // LATIN SMALL LETTER LONG S maps to 's' under IDNA: the transport resolves trusted.example.
        var (mapped, mappedRequests) = await ParseLoading($"M = load('https://tru{U(0x17F)}ted.example/m.kat')\nM.V");
        AssertNoDiagnostics(mapped);
        Assert.Equal(["https://trusted.example/m.kat"], mappedRequests.Requests);

        // LATIN SMALL LETTER DOTLESS I is a VALID, distinct IDNA letter: "gıthub.io" is the
        // punycode host xn--gthub-n4a.io, never github.io, however the text looks.
        var (distinct, distinctRequests) = await ParseLoading(
            $"M = load('https://g{U(0x131)}thub.io/m.kat')\nM.V", ["github.io"]);
        Assert.Empty(distinctRequests.Requests);
        Assert.Equal("load: domain not allowed: 'xn--gthub-n4a.io'.", SingleError(distinct).Message);
    }

    // ── 3. IP literals: canonical form, exact match only ─────────────────────

    [Theory]
    [InlineData("https://127.0.0.1/m.kat")]
    [InlineData("https://127.1/m.kat")]
    [InlineData("https://2130706433/m.kat")]
    [InlineData("https://0x7f.1/m.kat")]
    [InlineData("https://0177.0.0.1/m.kat")]
    public async Task Ipv4Spellings_AreCanonicalized_AndMatchAnExactEntry(string written)
    {
        var (parsed, downloader) = await ParseLoading($"M = load('{written}')\nM.V", ["127.0.0.1"]);

        AssertNoDiagnostics(parsed);
        Assert.Equal(["https://127.0.0.1/m.kat"], downloader.Requests);
    }

    [Theory]
    [InlineData("0.1")]
    [InlineData("0.0.1")]
    [InlineData("1")]
    [InlineData("127.0.0.2")]
    [InlineData("localhost")]
    public async Task IpHost_IsNeverAdmittedBySuffixOrByADifferentEntry(string entry)
    {
        // The former subdomain arm applied to IP text: entry "0.1" admitted 127.0.0.1.
        var (parsed, downloader) = await ParseLoading("M = load('https://127.0.0.1/m.kat')\nM.V", [entry]);

        Assert.Empty(downloader.Requests);
        Assert.Equal("load: domain not allowed: '127.0.0.1'.", SingleError(parsed).Message);
    }

    [Theory]
    [InlineData("::1", "https://[::1]/m.kat", "https://[::1]/m.kat")]
    [InlineData("[::1]", "https://[::1]/m.kat", "https://[::1]/m.kat")]
    [InlineData("2001:DB8::1", "https://[2001:db8:0::1]:8443/m.kat", "https://[2001:db8::1]:8443/m.kat")]
    [InlineData("[2001:db8::1]", "https://[2001:DB8::1]/m.kat", "https://[2001:db8::1]/m.kat")]
    public async Task Ipv6Literals_MatchInCanonicalForm_KeepingBracketsAndPort(string entry, string written, string requested)
    {
        var (parsed, downloader) = await ParseLoading($"M = load('{written}')\nM.V", [entry]);

        AssertNoDiagnostics(parsed);
        Assert.Equal([requested], downloader.Requests);
    }

    [Fact]
    public async Task Ipv6ZoneIndex_IsRefused_RatherThanSilentlyDropped()
    {
        var (parsed, downloader) = await ParseLoading("M = load('https://[fe80::1%25eth0]/m.kat')\nM.V", ["fe80::1"]);

        Assert.Empty(downloader.Requests);
        Assert.Contains("its host is not a valid DNS name or IP address", SingleError(parsed).Message, StringComparison.Ordinal);
    }

    // ── 4. Allow-list entries ─────────────────────────────────────────────────

    [Theory]
    [InlineData("https://trusted.example")]
    [InlineData("trusted.example:443")]
    [InlineData("*.trusted.example")]
    [InlineData("trusted.example/")]
    [InlineData("user@trusted.example")]
    [InlineData(".trusted.example")]
    public async Task EntryThatIsNotAHost_AdmitsNothing(string entry)
    {
        var (parsed, downloader) = await ParseLoading($"M = load('https://{Trusted}/m.kat')\nM.V", [entry]);

        Assert.Empty(downloader.Requests);
        Assert.Equal($"load: domain not allowed: '{Trusted}'.", SingleError(parsed).Message);
    }

    [Fact]
    public async Task DefaultAllowList_IsKatlangOrgAndItsSubdomainsOnly()
    {
        var downloader = new RecordingDownloader();
        var options = new RunOptions { DownloadCode = downloader.Download };

        AssertNoDiagnostics(await Parser.ParseAsync("A = load('https://katlang.org/a.kat')\nB = load('https://cdn.katlang.org/b.kat')\n1", options));
        Assert.Equal(["https://katlang.org/a.kat", "https://cdn.katlang.org/b.kat"], downloader.Requests);

        var refused = await Parser.ParseAsync("C = load('https://katlang.org.evil.test/c.kat')\n1", options);
        Assert.Equal(2, downloader.Requests.Count);
        Assert.Equal("load: domain not allowed: 'katlang.org.evil.test'.", SingleError(refused).Message);
    }

    // ── 5. Module identity: one canonical URL for cache, cycle, and transport ──

    [Fact]
    public async Task EquivalentSpellings_AreOneModule_OneRequest()
    {
        string[] spellings =
        [
            "https://trusted.example/lib/m.kat",
            "HTTPS://TRUSTED.EXAMPLE:443/lib/m.kat",
            "https://trusted.example/lib/x/../m.kat",
            "https://trusted.example/lib/./m.kat",
            "https://trusted.example/lib/x/%2e%2e/m.kat",
            "https://trusted.example/lib/m.kat#one",
            "https://trusted.example/lib/m.kat#two",
            $"https://trusted{U(0xFF0E)}example/lib/m.kat",
        ];
        var source = string.Concat(spellings.Select((spelling, index) => $"M{index} = load('{spelling}')\n")) + "M0.V";

        var (parsed, downloader) = await ParseLoading(source, limits: new SourceProcessingLimits { MaxModuleCount = 1 });

        AssertNoDiagnostics(parsed);
        Assert.Equal(["https://trusted.example/lib/m.kat"], downloader.Requests);
    }

    [Fact]
    public async Task DistinctResources_StayDistinctModules()
    {
        string[] spellings =
        [
            "https://trusted.example/lib/m.kat",
            "https://trusted.example/lib/m.kat?v=1",
            "https://trusted.example/lib/m.kat?v=2",
            "https://trusted.example/lib/M.kat",
            "https://trusted.example//lib/m.kat",
            "https://trusted.example/lib%2fm.kat",
            "https://trusted.example:8443/lib/m.kat",
            "https://sub.trusted.example/lib/m.kat",
        ];
        var source = string.Concat(spellings.Select((spelling, index) => $"M{index} = load('{spelling}')\n")) + "M0.V";

        var (parsed, downloader) = await ParseLoading(source);

        AssertNoDiagnostics(parsed);
        Assert.Equal(spellings.Length, downloader.Requests.Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(spellings.Length, downloader.Requests.Count);
    }

    [Fact]
    public async Task FragmentAlias_OfTheModuleBeingLoaded_IsACycle_WithoutASecondDownload()
    {
        const string url = "https://trusted.example/self.kat";
        var (parsed, downloader) = await ParseLoading(
            $"M = load('{url}')\nM.V",
            respond: _ => $"public V = 1\nAgain = load('{url}#again')");

        Assert.Equal([url], downloader.Requests);
        var error = SingleError(parsed);
        Assert.Equal(DiagnosticCode.LoadCycle, error.Code);
        Assert.Equal($"load cycle detected: {url}", error.Message);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(5)]
    public async Task CycleOfAnyLength_IsDetected_WithOneDownloadPerModule(int length)
    {
        // Each module names its successor with an upper-case scheme and host (the path keeps its
        // case, which IS part of the identity), so the cycle closes through a spelling variant.
        string Url(int index) => $"https://trusted.example/cycle/{index % length}.kat";
        string Variant(int index) => $"HTTPS://TRUSTED.EXAMPLE:443/cycle/{index % length}.kat";
        var (parsed, downloader) = await ParseLoading(
            $"M = load('{Url(0)}')\n1",
            respond: url =>
            {
                var index = int.Parse(url["https://trusted.example/cycle/".Length..^".kat".Length]);
                return $"public V = 1\nNext = load('{Variant(index + 1)}')";
            });

        Assert.Equal(length, downloader.Requests.Count);
        Assert.Equal(length, downloader.Requests.Distinct(StringComparer.Ordinal).Count());
        var error = SingleError(parsed);
        Assert.Equal(DiagnosticCode.LoadCycle, error.Code);
    }

    // ── 6. What diagnostics echo ─────────────────────────────────────────────

    [Fact]
    public async Task InvalidTargetEcho_EscapesControlAndBidiCharacters_AndIsBounded()
    {
        var hostile = U(0x1B) + "[2J" + U(0x1B) + "[31mFAKE" + U(0x202E) + U(0x2028) + U(0x7) + (char)0xD800 + "x";
        var (parsed, _) = await ParseLoading($"M = load('{hostile}')\nM.V");

        var message = SingleError(parsed).Message;
        Assert.Contains("\\u001B[2J\\u001B[31mFAKE\\u202E\\u2028\\u0007\\uD800x", message, StringComparison.Ordinal);
        Assert.All(message, ch => Assert.InRange(ch, ' ', '~'));
        Assert.DoesNotContain(message, ch => char.IsControl(ch) || char.IsSurrogate(ch) || ch is '\u202E' or '\u2028');

        var huge = new string('z', 100_000);
        var (longParsed, _) = await ParseLoading($"M = load('{huge}')\nM.V");
        var longMessage = SingleError(longParsed).Message;
        Assert.InRange(longMessage.Length, 1, ModuleLoadTarget.MaxEchoedTargetLength + 64);
        Assert.EndsWith("...'.", longMessage, StringComparison.Ordinal);
    }

    [Fact]
    public async Task DownloaderExceptionEcho_IsBoundedAndEscaped()
    {
        var reason = "HTTP 404 " + U(0x1B) + "[2J" + new string('r', 10_000);
        var (parsed, downloader) = await ParseLoading(
            $"M = load('https://{Trusted}/m.kat')\nM.V",
            respond: _ => throw new InvalidOperationException(reason));

        Assert.Single(downloader.Requests);
        var error = SingleError(parsed);
        Assert.Equal(DiagnosticCode.LoadFetchFailed, error.Code);
        Assert.StartsWith($"load: failed to fetch 'https://{Trusted}/m.kat': HTTP 404 \\u001B[2J", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain(error.Message, char.IsControl);
        Assert.InRange(error.Message.Length, 1, ModuleLoadTarget.MaxEchoedHostMessageLength + 100);
    }

    // ── 7. Resource bounds: every download consumes a module slot ────────────

    [Theory]
    [InlineData(1_000, null)]
    [InlineData(1_000, 7)]
    public async Task RetryStorm_OfOneFailingTarget_IsBoundedByTheModuleCeiling(int sites, int? maxModuleCount)
    {
        // RES: a failed download used to be free and was re-fetched at every load site, so a
        // source bounded only by its length (~2 MiB ≈ 70k sites) drove as many transport requests.
        var source = string.Concat(Enumerable.Range(0, sites).Select(i => $"A{i} = load('https://{Trusted}/missing.kat')\n")) + "1";
        var limits = maxModuleCount is { } count ? new SourceProcessingLimits { MaxModuleCount = count } : null;

        var (parsed, downloader) = await ParseLoading(
            source,
            respond: _ => throw new HttpRequestException("404"),
            limits: limits);

        var ceiling = maxModuleCount ?? SourceProcessingLimits.MaxSupportedModuleCount;
        Assert.Equal(ceiling, downloader.Requests.Count);
        Assert.Equal(ceiling, parsed.Diagnostics.Count(d => d.Code == DiagnosticCode.LoadFetchFailed));
        Assert.Equal(sites - ceiling, parsed.Diagnostics.Count(d => d.Code == DiagnosticCode.ModuleCountExceeded));
        Assert.Equal(sites, parsed.Diagnostics.Count);
    }

    [Fact]
    public async Task DistinctFailingTargets_OversizedTexts_AndAggregateRejections_AreBoundedByTheSameCeiling()
    {
        const int sites = 600;
        var ceiling = SourceProcessingLimits.MaxSupportedModuleCount;
        string Program(string stem) => string.Concat(Enumerable.Range(0, sites).Select(i => $"A{i} = load('https://{Trusted}/{stem}/{i}.kat')\n")) + "1";

        var (failing, failingDownloads) = await ParseLoading(Program("fail"), respond: _ => throw new HttpRequestException("404"));
        Assert.Equal(ceiling, failingDownloads.Requests.Count);
        Assert.Equal(ceiling, failingDownloads.Requests.Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(sites, failing.Diagnostics.Count);

        // The per-source ceiling admits the root itself; every module text is one unit over it.
        var bigRoot = Program("big");
        var oversized = new string('x', bigRoot.Length + 1);
        var (big, bigDownloads) = await ParseLoading(
            bigRoot,
            respond: _ => oversized,
            limits: new SourceProcessingLimits { MaxSourceLength = bigRoot.Length });
        Assert.Equal(ceiling, bigDownloads.Requests.Count);
        Assert.Equal(ceiling, big.Diagnostics.Count(d => d.Code == DiagnosticCode.SourceLengthExceeded));

        var module = "public V = 1" + new string(' ', 1_000);
        var root = Program("agg");
        var (aggregate, aggregateDownloads) = await ParseLoading(
            root,
            respond: _ => module,
            limits: new SourceProcessingLimits { MaxAggregateSourceLength = root.Length + 3 * module.Length });
        Assert.Equal(ceiling, aggregateDownloads.Requests.Count);
        Assert.Equal(ceiling - 3, aggregate.Diagnostics.Count(d => d.Code == DiagnosticCode.AggregateSourceLengthExceeded));
    }

    [Fact]
    public async Task FailingLoadsInsideAcceptedModules_ShareTheRootBudget()
    {
        // Fan-out below the root: each accepted module writes many failing loads. The nested
        // requests draw on the one run budget — no descendant starts from a fresh one.
        var (parsed, downloader) = await ParseLoading(
            $"A = load('https://{Trusted}/fan/a.kat')\nB = load('https://{Trusted}/fan/b.kat')\n1",
            respond: url => url.Contains("/fan/", StringComparison.Ordinal)
                ? string.Concat(Enumerable.Range(0, 400).Select(i => $"F{i} = load('https://{Trusted}/missing/{i}.kat')\n")) + "public V = 1"
                : throw new HttpRequestException("404"),
            limits: new SourceProcessingLimits { MaxModuleCount = 50 });

        Assert.Equal(50, downloader.Requests.Count);
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.ModuleCountExceeded);
    }

    // ── 8. Policy is recursive: descendants are judged exactly like the root ──

    public static TheoryData<string> RefusedNestedTargets() => new()
    {
        "https://evil.test/n.kat",
        "http://trusted.example/n.kat",
        "https://alice:secret@trusted.example/n.kat",
        $"https://evil.test{U(0xFF0F)}.trusted.example/n.kat",
        "https://trusted.example.evil.test/n.kat",
    };

    [Theory]
    [MemberData(nameof(RefusedNestedTargets))]
    public async Task NestedTargetInAnAllowedModule_IsRefusedBeforeTheDownloader(string nested)
    {
        const string outer = "https://trusted.example/outer.kat";
        var source = $"M = load('{outer}')\nM.V";
        var (parsed, downloader) = await ParseLoading(source, respond: url => url == outer
            ? $"public V = 1\nN = load('{nested}')"
            : "public V = 2");

        Assert.Equal([outer], downloader.Requests);
        var error = SingleError(parsed);
        Assert.Equal(DiagnosticCode.InvalidLoadUrl, error.Code);
        // Positioned at the IMPORT SITE in this document, never at module coordinates.
        Assert.Equal(new SourcePosition(1, 5), Assert.NotNull(error.Span).Start);
        Assert.DoesNotContain("secret", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(RefusedNestedTargets))]
    public async Task NestedTargetInADeferredBranchModule_IsRefusedWhenSelected_AndNeverRequested(string nested)
    {
        const string outer = "https://trusted.example/deferred-outer.kat";
        var source = $"F(0) = 0\nF(n) = {{\n    M = load('{outer}')\n    M.V\n}}\n";
        var downloader = new RecordingDownloader(url => url == outer ? $"public V = 1\nN = load('{nested}')" : "public V = 2");
        var options = new RunOptions { DownloadCode = downloader.Download, AllowedHosts = [Trusted] };

        var unselected = await KatLangEngine.RunAsync(source + "F(0)", options);
        Assert.Equal("0", unselected.ToDisplayString());
        Assert.Empty(downloader.Requests);

        var selected = await KatLangEngine.RunAsync(source + "F(1)", options);
        var failure = Assert.IsType<RunResult.EvalFailure>(selected);
        Assert.Equal(KatLangErrorCode.InvalidLoadUrl, Assert.Single(failure.Errors).Code);
        Assert.Equal([outer], downloader.Requests);
    }

    // ── 9. An initial front-end failure never enters the evaluator ───────────

    [Theory]
    [InlineData("public Good = 1\npublic Broken = (\npublic Later = 2")]
    [InlineData("public Good = 1\n'unterminated\npublic Later = 2")]
    [InlineData("public Good = 1\npublic Good = 2")]
    [InlineData("public Good = Nested.V\nNested = load('https://trusted.example/missing.kat')")]
    public async Task InvalidLoadedModule_BlocksEvaluation_WithNoHostEffect_AndNoPartialExport(string moduleSource)
    {
        var probes = 0;
        string? servedModule = null;
        var downloader = new RecordingDownloader(url => url.EndsWith("/m.kat", StringComparison.Ordinal)
            ? servedModule!
            : throw new HttpRequestException("404"));
        var options = new RunOptions
        {
            DownloadCode = downloader.Download,
            AllowedHosts = [Trusted],
            RandomSeed = 7,
            HostOperations = HostOperations.Create(HostOperation.Create("Probe", (_, _) =>
            {
                Interlocked.Increment(ref probes);
                return new Result.Atom(1);
            })),
        };

        // The caller itself is valid, and its host effect and random draw are written FIRST.
        var caller = $"Probe + Math.Random(0, 1) * 0\nM = load('https://{Trusted}/m.kat')\nM.Good";

        // Discriminator: with a valid module the same caller runs, and the probe is live.
        servedModule = "public Good = 5";
        var valid = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(caller, options));
        Assert.Equal(new Decimal128[] { 1m, 5m }, valid.Atoms);
        Assert.Equal(1, Volatile.Read(ref probes));

        servedModule = moduleSource;
        var failure = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(caller, options));
        Assert.NotEmpty(failure.Errors);
        Assert.Equal(1, Volatile.Read(ref probes));

        // Tooling sees the failure too, and a failed module is never cached: its second site
        // re-requests it (within the module budget) rather than splicing a partial export.
        var requestsBefore = downloader.Requests.Count;
        var parsed = await Parser.ParseAsync($"M = load('https://{Trusted}/m.kat')\nN = load('https://{Trusted}/m.kat')\nM.Good", options);
        Assert.True(parsed.HasErrors);
        Assert.Equal(2, downloader.Requests.Skip(requestsBefore).Count(url => url.EndsWith("/m.kat", StringComparison.Ordinal)));
    }

    [Fact]
    public async Task DeferredModuleFailure_StopsTheSelectedPath_AfterEarlierEffects_WithoutRollingThemBack()
    {
        // The eager gate covers INITIAL source processing only. A deferred branch loads when
        // evaluation selects it; effects evaluated before that selection have happened, and a
        // failing materialization stops the run there — KatLang promises no transaction.
        var probes = 0;
        var downloader = new RecordingDownloader(_ => "public V = (");
        var options = new RunOptions
        {
            DownloadCode = downloader.Download,
            AllowedHosts = [Trusted],
            HostOperations = HostOperations.Create(HostOperation.Create("Probe", (_, _) =>
            {
                Interlocked.Increment(ref probes);
                return new Result.Atom(1);
            })),
        };
        var source = $"F(0) = 0\nF(n) = {{\n    M = load('https://{Trusted}/deferred.kat')\n    M.V\n}}\nProbe\nF(Probe)";

        var parsed = await Parser.ParseAsync(source, options);
        AssertNoDiagnostics(parsed);
        Assert.Empty(downloader.Requests);
        Assert.Equal(0, Volatile.Read(ref probes));

        var result = await KatLangEngine.RunAsync(source, options);

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Equal(KatLangErrorCode.InvalidLoadedSource, Assert.Single(failure.Errors).Code);
        Assert.Single(downloader.Requests);
        Assert.True(Volatile.Read(ref probes) >= 1, "the effect evaluated before the selection happened");
    }

    // ── 10. Loaded code runs with the run's capabilities, only at evaluation ──

    [Fact]
    public async Task LoadedModule_SeesTheRunsHostOperations_ButFrontEndPreparationInvokesNone()
    {
        var probes = 0;
        var downloader = new RecordingDownloader(_ => "public V = Probe(20) + 1");
        var options = new RunOptions
        {
            DownloadCode = downloader.Download,
            AllowedHosts = [Trusted],
            HostOperations = HostOperations.Create(HostOperation.Create(
                "Probe",
                (arguments, _) =>
                {
                    Interlocked.Increment(ref probes);
                    return arguments[0];
                },
                "x")),
        };

        var parsed = await Parser.ParseAsync($"M = load('https://{Trusted}/cap.kat')\nM.V", options);
        AssertNoDiagnostics(parsed);
        Assert.Equal(0, Volatile.Read(ref probes));

        foreach (var spelling in new[] { $"M = load('https://{Trusted}/cap.kat')\nM.V", $"open 'https://{Trusted}/cap.kat'\nV" })
        {
            var result = await KatLangEngine.RunAsync(spelling, options);
            Assert.Equal("21", Assert.IsType<RunResult.Success>(result).ToDisplayString());
        }

        Assert.Equal(2, Volatile.Read(ref probes));
    }

    // ── 11. Isolation: nothing a run loads is visible to another run ─────────

    [Fact]
    public async Task SameTargetAcrossRuns_UsesEachRunsOwnDownloaderAndPolicy()
    {
        const string source = "M = load('https://trusted.example/iso.kat')\nM.V";
        var first = new RecordingDownloader(_ => "public V = 1");
        var second = new RecordingDownloader(_ => "public V = 2");

        Assert.Equal("1", (await KatLangEngine.RunAsync(source, new RunOptions { DownloadCode = first.Download, AllowedHosts = [Trusted] })).ToDisplayString());
        Assert.Equal("2", (await KatLangEngine.RunAsync(source, new RunOptions { DownloadCode = second.Download, AllowedHosts = [Trusted] })).ToDisplayString());

        // A narrower policy on a later run is not bypassed by anything an earlier run loaded.
        var narrowed = new RecordingDownloader(_ => "public V = 3");
        var refused = await KatLangEngine.RunAsync(source, new RunOptions { DownloadCode = narrowed.Download, AllowedHosts = ["other.example"] });
        Assert.Equal(KatLangErrorCode.InvalidLoadUrl, Assert.Single(Assert.IsType<RunResult.ParseFailure>(refused).Errors).Code);
        Assert.Empty(narrowed.Requests);
        Assert.Single(first.Requests);
        Assert.Single(second.Requests);
    }

    [Fact]
    public async Task ConcurrentRuns_SharingOneOptionsObject_KeepPerRunModuleState()
    {
        const int runs = 16;
        var requests = new ConcurrentQueue<string>();
        using var gate = new SemaphoreSlim(0);
        var options = new RunOptions
        {
            AllowedHosts = [Trusted],
            DownloadCode = async (url, cancellationToken) =>
            {
                requests.Enqueue(url);
                await gate.WaitAsync(cancellationToken);
                return $"public V = {url[^5]}";
            },
        };

        var tasks = Enumerable.Range(0, runs)
            .Select(i => KatLangEngine.RunAsync($"M = load('https://{Trusted}/c/m{i % 10}.kat')\nM.V", options))
            .ToArray();
        gate.Release(runs);
        var results = await Task.WhenAll(tasks);

        for (var i = 0; i < runs; i++)
            Assert.Equal((i % 10).ToString(System.Globalization.CultureInfo.InvariantCulture), results[i].ToDisplayString());
        // One request per run: no run was served another run's module.
        Assert.Equal(runs, requests.Count);
    }

    [Fact]
    public async Task ConcurrentRuns_WithDifferentDownloaders_ForOneUrl_EachSeeOnlyTheirOwnModule()
    {
        const int runs = 12;
        using var gate = new SemaphoreSlim(0);
        RunOptions OptionsServing(int value) => new()
        {
            AllowedHosts = [Trusted],
            DownloadCode = async (_, cancellationToken) =>
            {
                await gate.WaitAsync(cancellationToken);
                return $"public V = {value}";
            },
        };

        var tasks = Enumerable.Range(0, runs)
            .Select(i => KatLangEngine.RunAsync($"M = load('https://{Trusted}/same.kat')\nM.V", OptionsServing(i)))
            .ToArray();
        gate.Release(runs);
        var results = await Task.WhenAll(tasks);

        for (var i = 0; i < runs; i++)
            Assert.Equal(i.ToString(System.Globalization.CultureInfo.InvariantCulture), results[i].ToDisplayString());
    }

    [Fact]
    public async Task ManyRefusedTargets_NeverReachTheDownloader_AndCostOneDiagnosticEach()
    {
        const int sites = 5_000;
        var source = string.Concat(Enumerable.Range(0, sites).Select(i => i % 2 == 0
            ? $"A{i} = load('https://evil.test/{i}.kat')\n"
            : $"A{i} = load('http://{Trusted}/{i}.kat')\n")) + "1";

        var (parsed, downloader) = await ParseLoading(source);

        Assert.Empty(downloader.Requests);
        Assert.Equal(sites, parsed.Diagnostics.Count);
        Assert.All(parsed.Diagnostics, d => Assert.Equal(DiagnosticCode.InvalidLoadUrl, d.Code));
    }

    [Fact]
    public async Task HostileModuleText_CostsOneDiagnosticPerLoad_WhateverItsOwnErrorCount()
    {
        // A module's own parse diagnostics never cross into the loading document: an invalid
        // module is ONE InvalidLoadedSource at its load site, so a text of thousands of errors
        // cannot amplify the importer's diagnostics.
        var garbage = string.Concat(Enumerable.Repeat("@ ) ] } 'x\n", 5_000));
        var (parsed, downloader) = await ParseLoading(
            $"A = load('https://{Trusted}/garbage.kat')\nB = load('https://{Trusted}/garbage.kat')\n1",
            respond: _ => garbage);

        Assert.Equal(2, downloader.Requests.Count);
        Assert.Equal(2, parsed.Diagnostics.Count);
        Assert.All(parsed.Diagnostics, d => Assert.Equal(DiagnosticCode.InvalidLoadedSource, d.Code));
    }

    [Fact]
    public async Task DownloaderThatReentersKatLang_DoesNotDisturbTheLoadingRun()
    {
        // The downloader is host code and may itself run KatLang (even a loading run): every
        // run owns its loader, cache, and budget, so neither run observes the other's state.
        RunOptions? inner = null;
        var outer = new RunOptions
        {
            AllowedHosts = [Trusted],
            DownloadCode = async (url, _) =>
            {
                var nested = await KatLangEngine.RunAsync($"N = load('https://{Trusted}/inner.kat')\nN.V + 40", inner);
                return $"public V = {nested.ToDisplayString()}";
            },
        };
        inner = new RunOptions
        {
            AllowedHosts = [Trusted],
            DownloadCode = (_, _) => ValueTask.FromResult("public V = 2"),
        };

        var result = await KatLangEngine.RunAsync($"M = load('https://{Trusted}/outer.kat')\nM.V", outer);

        Assert.Equal("42", Assert.IsType<RunResult.Success>(result).ToDisplayString());
    }

    // ── 12. Default-off ──────────────────────────────────────────────────────

    [Fact]
    public async Task WithoutADownloader_NoConfigurationCanLoad()
    {
        const string source = "M = load('https://katlang.org/m.kat')\nM.V";
        foreach (var options in new RunOptions?[] { null, new RunOptions(), new RunOptions { AllowedHosts = ["katlang.org"] } })
        {
            var syncParsed = Parser.Parse(source, options);
            Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, SingleError(syncParsed).Code);
            var asyncParsed = await Parser.ParseAsync(source, options);
            Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, SingleError(asyncParsed).Code);
            Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, options));
            Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options));
        }
    }
}
