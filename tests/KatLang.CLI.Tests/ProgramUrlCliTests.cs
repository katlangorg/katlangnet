using System.Net;
using System.Text;

namespace KatLang.CLI.Tests;

/// <summary>
/// A program URL as the operand of <c>run</c>, <c>check</c> and <c>source</c>: a web link with
/// no <c>#</c>, whose program is downloaded as text. Naming the address is the request to
/// download it, so no option is needed; once the text is in hand the command is what it is for
/// a file. Two downloaders stand in for the network, and neither opens a connection:
/// a recording function (address to text), for everything that happens around the download;
/// and the real <see cref="HttpSourceDownloader"/> over an in-memory handler
/// (<see cref="StubHttpHandler"/>), for the download's own rules.
/// </summary>
public sealed class ProgramUrlCliTests
{
    private const int Success = 0;
    private const int Failure = 1;

    /// <summary>A published shared program's id.</summary>
    private const string ShareId = "019ead4b-d41d-7564-ba11-c177f917a0fe";

    private const string RawCodeUrl = "https://katlang.org/api/a/" + ShareId;
    private const string SharePageUrl = "https://katlang.org/a/" + ShareId;
    private const string ElsewhereUrl = "https://raw.example.net/user/repo/main/program.kat";

    /// <summary>Prints 42.</summary>
    private const string Program = "A = 6\nB = 7\nA * B\n";

    private static RecordingDownloader Serving(string url, string text)
        => new(new Dictionary<string, string> { [url] = text });

    private static string LinkLineOf(string source)
        => "katlang-link: " + Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(source)).Url;

    // ── The program is downloaded and runs ──────────────────────────────────

    [Theory]
    [InlineData(RawCodeUrl)]
    [InlineData(ElsewhereUrl)]
    [InlineData("https://gist.example.org/user/0123abcd/raw/program.kat?version=2&x=%20y")]
    [InlineData("https://katlang.org/demo/program.kat")]
    [InlineData("https://example.com:8443/p")]
    public async Task Run_Check_AndSource_ReadAProgramUrl(string url)
    {
        var downloader = Serving(url, Program);

        var run = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "run", url);
        var check = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "check", url);
        var source = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "source", url);

        Assert.Equal((Success, "42" + Environment.NewLine, ""), (run.ExitCode, run.Output, run.Error));
        Assert.Equal((Success, "", ""), (check.ExitCode, check.Output, check.Error));
        // The program exactly as read: no line break is added.
        Assert.Equal((Success, Program, ""), (source.ExitCode, source.Output, source.Error));
        // One download per command, of the address as given, and nothing else.
        Assert.Equal([url, url, url], downloader.RequestedUrls);
    }

    [Fact]
    public async Task NoOptionIsNeeded_ToDownloadTheProgramTheOperandNames()
    {
        // --allow-loading is the opt-in for what a PROGRAM names. The operand is the user's own
        // explicit request, so it is downloaded with or without the flag, identically.
        var downloader = Serving(ElsewhereUrl, Program);

        var without = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "run", ElsewhereUrl);
        var with = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "run", ElsewhereUrl, "--allow-loading");

        Assert.Equal((Success, "42", ""), (without.ExitCode, without.TrimmedOutput, without.Error));
        Assert.Equal((without.ExitCode, without.Output, without.Error), (with.ExitCode, with.Output, with.Error));
        Assert.Equal([ElsewhereUrl, ElsewhereUrl], downloader.RequestedUrls);
    }

    public static TheoryData<string> ProgramsLikeFiles => new()
    {
        Program,
        "A = 1\r\nB = 2\r\nA + B\r\n",
        "# Aprēķina cenu ar PVN\nCena = 100\nPVN = 21\nCena + PVN\n'Sveika, pasaule! āčēģīķļņšūž'\n",
        "1 / 0\n",
        "A = (1, 2\nB = ]\n",
        "1\r2",
        "Math.RandomInt(1, 1000000)\n1 / 3\n",
        "",
        "   \n\n",
        "MaxDecimalPlaces = 2\n1 / 3\n",
    };

    [Theory]
    [MemberData(nameof(ProgramsLikeFiles))]
    public async Task OnceRead_TheCommandIsExactlyWhatItIsForAFileWithTheSameText(string program)
    {
        var downloader = Serving(ElsewhereUrl, program);
        using var file = new ExactProgramFile(program);

        (string Command, string[] Options)[] invocations =
        [
            ("run", new[] { "--random-seed", "7", "--code-link" }),
            ("run", new[] { "--random-seed", "7", "--max-decimal-places", "3", "--min-decimal-places", "1" }),
            ("check", new[] { "--code-link" }),
            ("check", Array.Empty<string>()),
        ];

        foreach (var (command, options) in invocations)
        {
            var fromUrl = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, [command, ElsewhereUrl, .. options]);
            var fromFile = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, [command, file.Path, .. options]);

            Assert.Equal((fromFile.ExitCode, fromFile.Output, fromFile.Error), (fromUrl.ExitCode, fromUrl.Output, fromUrl.Error));
        }
    }

    [Fact]
    public async Task CodeLink_OfAProgramUrl_IsALinkOfTheDownloadedText_ASnapshot()
    {
        // --code-link encodes the source that ran: the text as downloaded. The link carries
        // that text itself, so a later edit to the shared program does not change it.
        const string edited = "A = 6\nB = 8\nA * B\n";
        var text = Program;
        Func<string, CancellationToken, ValueTask<string>> downloader = (_, _) => ValueTask.FromResult(text);

        var first = await Cli.InvokeWithDownloaderAsync(downloader, "run", SharePageUrl, "--code-link");
        text = edited;
        var second = await Cli.InvokeWithDownloaderAsync(downloader, "run", SharePageUrl, "--code-link");

        Assert.Equal((Success, "42", LinkLineOf(Program)), (first.ExitCode, first.TrimmedOutput, first.TrimmedError));
        Assert.Equal((Success, "48", LinkLineOf(edited)), (second.ExitCode, second.TrimmedOutput, second.TrimmedError));

        // The first link still opens the first text, offline.
        var snapshot = first.TrimmedError["katlang-link: ".Length..];
        var reopened = await Cli.InvokeWithDownloaderAsync(new RecordingDownloader().DownloadAsync, "run", snapshot);
        Assert.Equal((Success, "42", ""), (reopened.ExitCode, reopened.TrimmedOutput, reopened.Error));
    }

    [Fact]
    public async Task CodeLink_IsWrittenForCheckToo_AndForAProgramWithNoLink()
    {
        var check = await Cli.InvokeWithDownloaderAsync(Serving(ElsewhereUrl, Program).DownloadAsync, "check", ElsewhereUrl, "--code-link");
        var empty = await Cli.InvokeWithDownloaderAsync(Serving(ElsewhereUrl, "").DownloadAsync, "run", ElsewhereUrl, "--code-link");

        Assert.Equal((Success, "", LinkLineOf(Program)), (check.ExitCode, check.Output, check.TrimmedError));
        Assert.Equal((Success, "", "katlang-link: none: the program is empty."), (empty.ExitCode, empty.Output, empty.TrimmedError));
    }

    [Fact]
    public async Task Source_WritesADownloadedProgramExactly_AndTakesNoOption()
    {
        const string text = "# Rēķins\r\nSumma = 12\r\n\tSumma * 2   \r\n";
        var downloader = Serving(ElsewhereUrl, text);

        var written = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "source", ElsewhereUrl);
        var afterTerminator = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "source", "--", ElsewhereUrl);
        var withOption = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "source", ElsewhereUrl, "--allow-loading");

        Assert.Equal((Success, text, ""), (written.ExitCode, written.Output, written.Error));
        Assert.Equal((Success, text, ""), (afterTerminator.ExitCode, afterTerminator.Output, afterTerminator.Error));
        Assert.Equal((Failure, ""), (withOption.ExitCode, withOption.Output));
        Assert.Equal(
            "katlang: option '--allow-loading' is not valid for 'source': source reads a link and runs nothing.\n" + HelpText.UsageHint,
            withOption.TrimmedError);
        // The refused command line downloaded nothing.
        Assert.Equal([ElsewhereUrl, ElsewhereUrl], downloader.RequestedUrls);
    }

    [Fact]
    public async Task Source_RunsNothing_AndLoadsNothing()
    {
        const string text = "Lib = load('https://modules.example.net/lib.kat')\nLoop(n) = n + 1, true\nLoop(0).while\n";
        var downloader = Serving(ElsewhereUrl, text);

        var result = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "source", ElsewhereUrl);

        Assert.Equal((Success, text, ""), (result.ExitCode, result.Output, result.Error));
        Assert.Equal(ElsewhereUrl, Assert.Single(downloader.RequestedUrls));
    }

    // ── A shared program's page ─────────────────────────────────────────────

    public static TheoryData<string, string> SharePages => new()
    {
        { SharePageUrl, RawCodeUrl },
        { SharePageUrl + "/", RawCodeUrl },
        { SharePageUrl + "?utm_source=chat&ref=1", RawCodeUrl },
        { SharePageUrl + "/?x=1", RawCodeUrl },
        { "HTTPS://KATLANG.ORG/a/" + ShareId, RawCodeUrl },
        { "https://katlang.org:443/a/" + ShareId, RawCodeUrl },
        // The id is a GUID in either letter case, sent as written.
        { "https://katlang.org/a/019EAD4B-D41D-7564-BA11-C177F917A0FE", "https://katlang.org/api/a/019EAD4B-D41D-7564-BA11-C177F917A0FE" },
        { "https://katlang.org/a/019ead4b-D41D-7564-ba11-C177F917A0FE", "https://katlang.org/api/a/019ead4b-D41D-7564-ba11-C177F917A0FE" },
        // Any subdomain, on the same host and port.
        { "https://www.katlang.org/a/" + ShareId, "https://www.katlang.org/api/a/" + ShareId },
        { "https://Staging.Eu.KatLang.org/a/" + ShareId + "/", "https://staging.eu.katlang.org/api/a/" + ShareId },
        { "https://katlang.org:8443/a/" + ShareId, "https://katlang.org:8443/api/a/" + ShareId },
    };

    [Theory]
    [MemberData(nameof(SharePages))]
    public async Task ASharedProgramsPage_IsReadFromItsRawCodeAddress_AndThePageIsNeverDownloaded(string page, string rawCode)
    {
        // The page is HTML; its raw-code sibling is the same program as text.
        Assert.Equal(rawCode, ProgramUrl.DownloadAddress(page));
        var downloader = Serving(rawCode, Program);

        var run = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "run", page);
        var check = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "check", page);
        var source = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "source", page);

        Assert.Equal((Success, "42", ""), (run.ExitCode, run.TrimmedOutput, run.Error));
        Assert.Equal((Success, "", ""), (check.ExitCode, check.Output, check.Error));
        Assert.Equal((Success, Program, ""), (source.ExitCode, source.Output, source.Error));
        Assert.Equal([rawCode, rawCode, rawCode], downloader.RequestedUrls);
    }

    [Theory]
    // On any other host /a/… is an ordinary path.
    [InlineData("https://example.com/a/" + ShareId)]
    [InlineData("https://katlang.org.example.com/a/" + ShareId)]
    [InlineData("https://notkatlang.org/a/" + ShareId)]
    [InlineData("https://katlang.org.evil.test/a/" + ShareId)]
    [InlineData("https://katlang.org./a/" + ShareId)]
    // And on katlang.org only /a/<GUID> is a share page.
    [InlineData("https://katlang.org/a/not-a-share-id")]
    [InlineData("https://katlang.org/a/")]
    [InlineData("https://katlang.org/a/" + ShareId + "/edit")]
    [InlineData("https://katlang.org/a/019ead4bd41d7564ba11c177f917a0fe")]
    [InlineData("https://katlang.org/A/" + ShareId)]
    [InlineData("https://katlang.org/x/a/" + ShareId)]
    [InlineData("https://katlang.org/tutorial")]
    // The raw-code address itself, and a query on it, go as given.
    [InlineData(RawCodeUrl)]
    [InlineData(RawCodeUrl + "?download=1")]
    public async Task EveryOtherAddress_IsDownloadedAsGiven(string url)
    {
        Assert.Equal(url, ProgramUrl.DownloadAddress(url));
        var downloader = Serving(url, Program);

        var result = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "run", url);

        Assert.Equal((Success, "42", ""), (result.ExitCode, result.TrimmedOutput, result.Error));
        Assert.Equal(url, Assert.Single(downloader.RequestedUrls));
    }

    [Theory]
    // A link the downloader will refuse is handed to it as given, never rewritten into one it accepts.
    [InlineData("http://katlang.org/a/" + ShareId)]
    [InlineData("https://user:secret@katlang.org/a/" + ShareId)]
    [InlineData("https://@katlang.org/a/" + ShareId)]
    public void ALinkTheDownloaderRefuses_IsNeverRewritten(string url)
        => Assert.Equal(url, ProgramUrl.DownloadAddress(url));

    [Fact]
    public async Task ASharedProgramThatDoesNotExist_IsNotFound_NamedAsTheUserWroteIt()
    {
        var handler = new StubHttpHandler(new Dictionary<string, string>());
        using var transport = handler.Transport();

        foreach (var command in new[] { "run", "check", "source" })
        {
            var page = await Cli.InvokeWithTransportAsync(transport, command, SharePageUrl);
            var rawCode = await Cli.InvokeWithTransportAsync(transport, command, RawCodeUrl);

            // Private, unshared or unknown: one line, with the link as given.
            Assert.Equal((Failure, "", $"katlang: not found: '{SharePageUrl}'." + Environment.NewLine), (page.ExitCode, page.Output, page.Error));
            Assert.Equal((Failure, "", $"katlang: not found: '{RawCodeUrl}'." + Environment.NewLine), (rawCode.ExitCode, rawCode.Output, rawCode.Error));
        }

        // Both forms asked the raw-code address; the HTML page was never requested.
        Assert.All(handler.RequestedUrls, requested => Assert.Equal(RawCodeUrl, requested));
        Assert.Equal(6, handler.RequestedUrls.Count);
    }

    // ── Only KatLang source text runs ───────────────────────────────────────

    [Theory]
    [InlineData("text/plain")]
    [InlineData("text/plain; charset=utf-8")]
    [InlineData("TEXT/PLAIN; CHARSET=UTF-8")]
    [InlineData("text/plain;charset=us-ascii")]
    [InlineData("application/octet-stream")]
    [InlineData("Application/Octet-Stream")]
    public async Task SourceText_IsAccepted(string contentType)
    {
        var handler = new StubHttpHandler(() => StubHttpHandler.Text(Program, contentType));
        using var transport = handler.Transport();

        var run = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl);
        var check = await Cli.InvokeWithTransportAsync(transport, "check", ElsewhereUrl);
        var source = await Cli.InvokeWithTransportAsync(transport, "source", ElsewhereUrl);

        Assert.Equal((Success, "42", ""), (run.ExitCode, run.TrimmedOutput, run.Error));
        Assert.Equal((Success, "", ""), (check.ExitCode, check.Output, check.Error));
        Assert.Equal((Success, Program, ""), (source.ExitCode, source.Output, source.Error));
        Assert.Equal([ElsewhereUrl, ElsewhereUrl, ElsewhereUrl], handler.RequestedUrls);
    }

    [Theory]
    [InlineData("text/html; charset=utf-8", "text/html")]
    [InlineData("TEXT/HTML", "text/html")]
    [InlineData("application/json", "application/json")]
    [InlineData("application/xml", "application/xml")]
    [InlineData("text/xml; charset=utf-8", "text/xml")]
    [InlineData("image/png", "image/png")]
    [InlineData("application/pdf", "application/pdf")]
    [InlineData("text/javascript", "text/javascript")]
    [InlineData("text/x-katlang", "text/x-katlang")]
    [InlineData("text/plainly", "text/plainly")]
    [InlineData("application/octet-stream-like", "application/octet-stream-like")]
    [InlineData(null, "no Content-Type")]
    [InlineData("not a media type", "a Content-Type that cannot be read")]
    [InlineData("text", "a Content-Type that cannot be read")]
    public async Task AnythingElse_IsRefused_BeforeAnythingRuns(string? contentType, string returned)
    {
        // The body is a valid program that would print 42: it must not run, whatever it is.
        var handler = new StubHttpHandler(() => StubHttpHandler.Text(Program, contentType));
        using var transport = handler.Transport();
        var expected = $"katlang: not KatLang source: '{ElsewhereUrl}' returned {returned}." + Environment.NewLine;

        foreach (var command in new[] { "run", "check", "source" })
        {
            var result = await Cli.InvokeWithTransportAsync(transport, command, ElsewhereUrl);

            Assert.Equal((Failure, "", expected), (result.ExitCode, result.Output, result.Error));
        }

        // No source was read: no katlang-link line, and no usage hint.
        var withLink = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl, "--code-link");
        Assert.Equal((Failure, "", expected), (withLink.ExitCode, withLink.Output, withLink.Error));
    }

    [Fact]
    public async Task AWebPage_SuchAsTheSiteItself_IsNotKatLangSource()
    {
        var handler = new StubHttpHandler(() => StubHttpHandler.Text("<!DOCTYPE html><html><body>KatLang</body></html>", "text/html; charset=utf-8"));
        using var transport = handler.Transport();

        var result = await Cli.InvokeWithTransportAsync(transport, "run", "https://katlang.org/");

        Assert.Equal(
            (Failure, "", "katlang: not KatLang source: 'https://katlang.org/' returned text/html." + Environment.NewLine),
            (result.ExitCode, result.Output, result.Error));
        Assert.Equal("https://katlang.org/", Assert.Single(handler.RequestedUrls));
    }

    [Fact]
    public async Task TheRefusal_IsDecidedFromTheHeaders_SoTheBodyIsNeverRead()
    {
        // A page larger than the body limit is still "not KatLang source", not "too large".
        var content = new CountingContent(new byte[(int)HttpSourceDownloader.MaxResponseBodyBytes + 1], "text/html");
        var handler = new StubHttpHandler(() => new HttpResponseMessage(HttpStatusCode.OK) { Content = content });
        using var transport = handler.Transport();

        var result = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl);

        Assert.Equal($"katlang: not KatLang source: '{ElsewhereUrl}' returned text/html." + Environment.NewLine, result.Error);
        Assert.Equal(0, content.SerializeCalls);
    }

    [Fact]
    public async Task AnOverlongMediaType_IsEchoedBounded()
    {
        var subtype = new string('x', 5_000);
        var handler = new StubHttpHandler(() => StubHttpHandler.Text(Program, "text/" + subtype));
        using var transport = handler.Transport();

        var result = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl);

        var echoed = ("text/" + subtype)[..DownloadException.MaxEchoedMediaTypeLength] + "...";
        Assert.Equal($"katlang: not KatLang source: '{ElsewhereUrl}' returned {echoed}." + Environment.NewLine, result.Error);
    }

    [Fact]
    public async Task TextThatIsNotValidKatLang_IsAProgramWithErrors_ReportedByKatLangItself()
    {
        // text/plain that is not KatLang is not a download failure: it is a program, and its
        // diagnostics are exactly the ones a file with that text gets.
        const string text = "This is a README, not a program.\n\"double quotes\" {{{\n";
        var handler = new StubHttpHandler(() => StubHttpHandler.Text(text));
        using var transport = handler.Transport();
        using var file = new ExactProgramFile(text);

        foreach (var command in new[] { "run", "check" })
        {
            var fromUrl = await Cli.InvokeWithTransportAsync(transport, command, ElsewhereUrl);
            var fromFile = await Cli.InvokeAsync(command, file.Path);

            Assert.Equal(Failure, fromUrl.ExitCode);
            Assert.Equal("", fromUrl.Output);
            Assert.DoesNotContain("not KatLang source", fromUrl.Error);
            Assert.DoesNotContain("cannot download", fromUrl.Error);
            Assert.Matches(@"^\[\d+:\d+\] ", fromUrl.Error);
            Assert.Equal((fromFile.ExitCode, fromFile.Output, fromFile.Error), (fromUrl.ExitCode, fromUrl.Output, fromUrl.Error));
        }
    }

    // ── Decoding ────────────────────────────────────────────────────────────

    public static TheoryData<string, string> Encodings => new()
    {
        { "utf-8", "text/plain; charset=utf-8" },
        { "utf-8", "text/plain" },
        { "utf-8", "application/octet-stream" },
        { "utf-8-bom", "text/plain" },
        { "utf-8-bom", "text/plain; charset=utf-8" },
        { "utf-8-bom", "application/octet-stream" },
        { "utf-16", "text/plain; charset=utf-16" },
        { "utf-16-bom", "text/plain" },
        { "utf-16-bom", "text/plain; charset=utf-16" },
        { "utf-16be-bom", "application/octet-stream" },
        { "utf-32-bom", "text/plain" },
    };

    [Theory]
    [MemberData(nameof(Encodings))]
    public async Task ALatvianBody_IsDecodedAsTheResponseStates_AndOneByteOrderMarkIsDropped(string encoding, string contentType)
    {
        // The charset, else a byte order mark, else UTF-8 — and one leading mark dropped, as for
        // a file. --code-link shows the text that ran: the program, with no mark.
        const string text = "# Aprēķina cenu ar PVN: āčēģīķļņšūž ĀČĒĢĪĶĻŅŠŪŽ\n'Sveika, pasaule!'\n";
        byte[] body = encoding switch
        {
            "utf-8" => Encoding.UTF8.GetBytes(text),
            "utf-8-bom" => [.. Encoding.UTF8.GetPreamble(), .. Encoding.UTF8.GetBytes(text)],
            "utf-16" => Encoding.Unicode.GetBytes(text),
            "utf-16-bom" => [.. Encoding.Unicode.GetPreamble(), .. Encoding.Unicode.GetBytes(text)],
            "utf-16be-bom" => [.. Encoding.BigEndianUnicode.GetPreamble(), .. Encoding.BigEndianUnicode.GetBytes(text)],
            "utf-32-bom" => [.. Encoding.UTF32.GetPreamble(), .. Encoding.UTF32.GetBytes(text)],
            _ => throw new ArgumentOutOfRangeException(nameof(encoding)),
        };
        var handler = new StubHttpHandler(() => StubHttpHandler.Bytes(body, contentType));
        using var transport = handler.Transport();

        var run = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl, "--code-link");
        var source = await Cli.InvokeWithTransportAsync(transport, "source", ElsewhereUrl);

        Assert.Equal((Success, "Sveika, pasaule!", LinkLineOf(text)), (run.ExitCode, run.TrimmedOutput, run.TrimmedError));
        Assert.Equal((Success, text, ""), (source.ExitCode, source.Output, source.Error));
    }

    [Fact]
    public async Task ACharsetOtherThanUtf8_DecodesItsOwnBytes()
    {
        // é is one byte in ISO-8859-1, and that byte alone is not valid UTF-8.
        const string text = "'café'\n";
        var handler = new StubHttpHandler(() => StubHttpHandler.Bytes(Encoding.Latin1.GetBytes(text), "text/plain; charset=iso-8859-1"));
        using var transport = handler.Transport();

        var result = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl, "--code-link");

        Assert.Equal((Success, "café", LinkLineOf(text)), (result.ExitCode, result.TrimmedOutput, result.TrimmedError));
    }

    [Fact]
    public async Task AProgramThatItselfStartsWithTheMark_KeepsIt_BehindTheOneThatIsDropped()
    {
        // Two marks in the body: the first is the encoding's and is dropped, the second is text.
        const string text = "\uFEFF6 * 7\n";
        byte[] body = [.. Encoding.UTF8.GetPreamble(), .. Encoding.UTF8.GetBytes(text)];
        var handler = new StubHttpHandler(() => StubHttpHandler.Bytes(body, "text/plain; charset=utf-8"));
        using var transport = handler.Transport();
        using var file = new ExactProgramFile(text);

        var fromUrl = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl, "--code-link");
        var fromFile = await Cli.InvokeAsync("run", file.Path, "--code-link");

        Assert.Equal(LinkLineOf(text), fromUrl.TrimmedError.Split('\n')[^1]);
        Assert.Equal((fromFile.ExitCode, fromFile.Output, fromFile.Error), (fromUrl.ExitCode, fromUrl.Output, fromUrl.Error));
    }

    [Fact]
    public async Task AnUnsupportedCharacterSet_IsAFailedDownload()
    {
        var handler = new StubHttpHandler(() => StubHttpHandler.Bytes(Encoding.ASCII.GetBytes(Program), "text/plain; charset=no-such-charset"));
        using var transport = handler.Transport();

        var result = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl);

        Assert.Equal(
            (Failure, "", $"katlang: cannot download '{ElsewhereUrl}': the response names a character set that is not supported." + Environment.NewLine),
            (result.ExitCode, result.Output, result.Error));
    }

    // ── A download that fails ───────────────────────────────────────────────

    public static TheoryData<int, string> Statuses => new()
    {
        { 500, "the server responded with HTTP status 500; only 200 (OK) is accepted." },
        { 503, "the server responded with HTTP status 503; only 200 (OK) is accepted." },
        { 403, "the server responded with HTTP status 403; only 200 (OK) is accepted." },
        { 401, "the server responded with HTTP status 401; only 200 (OK) is accepted." },
        { 410, "the server responded with HTTP status 410; only 200 (OK) is accepted." },
        { 204, "the server responded with HTTP status 204; only 200 (OK) is accepted." },
        { 206, "the server responded with HTTP status 206; only 200 (OK) is accepted." },
        { 301, "the server responded with a redirect (HTTP status 301), and redirects are not allowed." },
        { 302, "the server responded with a redirect (HTTP status 302), and redirects are not allowed." },
        { 307, "the server responded with a redirect (HTTP status 307), and redirects are not allowed." },
        { 308, "the server responded with a redirect (HTTP status 308), and redirects are not allowed." },
    };

    [Theory]
    [MemberData(nameof(Statuses))]
    public async Task AnyStatusButOk_IsAFailedDownload_InTheCliOwnWords(int status, string reason)
    {
        // A redirect names a second address; it is refused, never followed.
        const string elsewhere = "https://redirected.example.org/program.kat";
        var handler = new StubHttpHandler(request => request.RequestUri!.AbsoluteUri == ElsewhereUrl
            ? StubHttpHandler.Status((HttpStatusCode)status, status is >= 300 and < 400 ? elsewhere : null)
            : StubHttpHandler.Text(Program));
        using var transport = handler.Transport();
        var expected = $"katlang: cannot download '{ElsewhereUrl}': {reason}" + Environment.NewLine;

        foreach (var command in new[] { "run", "check", "source" })
        {
            var result = await Cli.InvokeWithTransportAsync(transport, command, ElsewhereUrl);

            Assert.Equal((Failure, "", expected), (result.ExitCode, result.Output, result.Error));
        }

        var withLink = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl, "--code-link");
        Assert.Equal((Failure, "", expected), (withLink.ExitCode, withLink.Output, withLink.Error));
        Assert.All(handler.RequestedUrls, requested => Assert.Equal(ElsewhereUrl, requested));
    }

    [Fact]
    public async Task NotFound_IsItsOwnLine_ForAnyAddress()
    {
        var handler = new StubHttpHandler(() => StubHttpHandler.Status(HttpStatusCode.NotFound));
        using var transport = handler.Transport();

        var result = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl, "--code-link");

        Assert.Equal(
            (Failure, "", $"katlang: not found: '{ElsewhereUrl}'." + Environment.NewLine),
            (result.ExitCode, result.Output, result.Error));
    }

    [Fact]
    public async Task ABodyOverOneMebibyte_IsRefused_AndOneOfExactlyThatSizeRuns()
    {
        // A program padded with a comment to exactly the byte ceiling, and to one byte over it.
        const string head = "6 * 7\n#";
        var limit = (int)HttpSourceDownloader.MaxResponseBodyBytes;
        var atLimit = head + new string('x', limit - head.Length);
        var overLimit = atLimit + "x";
        var handler = new StubHttpHandler(request => StubHttpHandler.Text(request.RequestUri!.AbsolutePath == "/at" ? atLimit : overLimit));
        using var transport = handler.Transport();

        var accepted = await Cli.InvokeWithTransportAsync(transport, "run", "https://example.com/at");
        var refused = await Cli.InvokeWithTransportAsync(transport, "run", "https://example.com/over");

        Assert.Equal((Success, "42", ""), (accepted.ExitCode, accepted.TrimmedOutput, accepted.Error));
        Assert.Equal(
            (Failure, "", "katlang: cannot download 'https://example.com/over': the declared Content-Length of 1048577 bytes exceeds the 1048576-byte limit." + Environment.NewLine),
            (refused.ExitCode, refused.Output, refused.Error));
    }

    [Fact]
    public async Task ABodyOfUnknownLength_IsRefusedWhenItCrossesTheLimit()
    {
        var content = new CountingContent(new byte[(int)HttpSourceDownloader.MaxResponseBodyBytes + 1], "text/plain", declareLength: false);
        var handler = new StubHttpHandler(() => new HttpResponseMessage(HttpStatusCode.OK) { Content = content });
        using var transport = handler.Transport();

        var result = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl);

        Assert.Equal(
            (Failure, "", $"katlang: cannot download '{ElsewhereUrl}': the response body exceeds the 1048576-byte limit." + Environment.NewLine),
            (result.ExitCode, result.Output, result.Error));
    }

    [Fact]
    public async Task ADownloadPastTheDeadline_IsAFailedDownload_NotACancellation()
    {
        using var transport = new HttpSourceDownloader(
            HttpSourceDownloader.MaxResponseBodyBytes, TimeSpan.FromMilliseconds(300), new NeverRespondingHandler());

        var result = await Cli.InvokeWithTransportAsync(transport, "run", ElsewhereUrl, "--code-link");

        Assert.Equal(
            (Failure, "", $"katlang: cannot download '{ElsewhereUrl}': the download did not complete within 0.3 seconds." + Environment.NewLine),
            (result.ExitCode, result.Output, result.Error));
    }

    [Fact]
    public void TheShippedDeadlineAndLimit_AreTheOnesTheLinesName()
    {
        Assert.Equal(TimeSpan.FromSeconds(15), HttpSourceDownloader.DownloadTimeout);
        Assert.Equal(1_048_576L, HttpSourceDownloader.MaxResponseBodyBytes);
        Assert.Equal(
            "the download did not complete within 15 seconds.",
            DownloadException.DeadlineExceeded(HttpSourceDownloader.DownloadTimeout).Message);
        Assert.Equal(
            "the response body exceeds the 1048576-byte limit.",
            DownloadException.BodyTooLarge(HttpSourceDownloader.MaxResponseBodyBytes).Message);
    }

    [Fact]
    public async Task CancellationDuringTheDownload_IsReportedAsCancelled()
    {
        var handler = new NeverRespondingHandler();
        using var transport = new HttpSourceDownloader(HttpSourceDownloader.MaxResponseBodyBytes, TimeSpan.FromMinutes(5), handler);
        using var cancellation = new CancellationTokenSource();
        var output = new StringWriter();
        var error = new StringWriter();

        var run = CliApplication.RunAsync(["run", ElsewhereUrl, "--code-link"], output, error, transport, cancellation.Token);
        await handler.Started.Task.WaitAsync(TimeSpan.FromSeconds(60));
        await cancellation.CancelAsync();
        var exitCode = await run.WaitAsync(TimeSpan.FromSeconds(60));

        Assert.Equal(Failure, exitCode);
        Assert.Equal("", output.ToString());
        Assert.Equal("katlang: cancelled." + Environment.NewLine, error.ToString());
    }

    [Theory]
    [InlineData("http://example.com/program.kat")]
    [InlineData("HTTP://EXAMPLE.COM/program.kat")]
    [InlineData("http://katlang.org/api/a/" + ShareId)]
    [InlineData("http://katlang.org/a/" + ShareId)]
    [InlineData("http://127.0.0.1/program.kat")]
    [InlineData("http://169.254.169.254/latest/meta-data/")]
    public async Task PlainHttp_IsRefused_NeverUpgraded_AndNothingIsRequested(string url)
    {
        var handler = new StubHttpHandler(() => StubHttpHandler.Text(Program));
        using var transport = handler.Transport();
        var expected = $"katlang: cannot download '{url}': only HTTPS addresses are downloaded." + Environment.NewLine;

        foreach (var command in new[] { "run", "check", "source" })
        {
            var result = await Cli.InvokeWithTransportAsync(transport, command, url);

            Assert.Equal((Failure, "", expected), (result.ExitCode, result.Output, result.Error));
        }

        Assert.Empty(handler.RequestedUrls);
    }

    [Theory]
    [InlineData("https://alice:s3cret@example.com/program.kat", "https://<redacted>@example.com/program.kat")]
    [InlineData("https://alice@example.com/program.kat", "https://<redacted>@example.com/program.kat")]
    [InlineData("https://:s3cret@katlang.org/a/" + ShareId, "https://<redacted>@katlang.org/a/" + ShareId)]
    [InlineData("https://@example.com/program.kat", "https://<redacted>@example.com/program.kat")]
    [InlineData("https://katlang.org:s3cret@evil.example.net/program.kat", "https://<redacted>@evil.example.net/program.kat")]
    public async Task UserInformation_IsRefused_AndTheCredentialIsNeverWrittenBack(string url, string echoed)
    {
        var handler = new StubHttpHandler(() => StubHttpHandler.Text(Program));
        using var transport = handler.Transport();

        var result = await Cli.InvokeWithTransportAsync(transport, "run", url, "--code-link");

        Assert.Equal(
            (Failure, "", $"katlang: cannot download '{echoed}': it contains user information ('user@' or 'user:password@')." + Environment.NewLine),
            (result.ExitCode, result.Output, result.Error));
        Assert.DoesNotContain("s3cret", result.Error);
        Assert.DoesNotContain("alice", result.Error);
        Assert.Empty(handler.RequestedUrls);
    }

    [Theory]
    [InlineData("https://", "https://")]
    [InlineData("https://exa mple.com/program.kat", "https://exa mple.com/program.kat")]
    [InlineData("https://example.com:99999/program.kat", "https://example.com:99999/program.kat")]
    [InlineData("https://[::1/program.kat", "https://[::1/program.kat")]
    public async Task AnAddressThatIsNoAddress_IsRefused(string url, string echoed)
    {
        var handler = new StubHttpHandler(() => StubHttpHandler.Text(Program));
        using var transport = handler.Transport();

        var result = await Cli.InvokeWithTransportAsync(transport, "run", url);

        Assert.Equal(
            (Failure, "", $"katlang: cannot download '{echoed}': it is not a valid address." + Environment.NewLine),
            (result.ExitCode, result.Output, result.Error));
        Assert.Empty(handler.RequestedUrls);
    }

    public static TheoryData<string, string> NonPublicAddresses => new()
    {
        { "https://127.0.0.1/x.kat", "127.0.0.1" },
        { "https://127.0.0.1:8443/x.kat", "127.0.0.1" },
        { "https://10.0.0.1/x.kat", "10.0.0.1" },
        { "https://192.168.1.1/x.kat", "192.168.1.1" },
        { "https://172.16.0.1/x.kat", "172.16.0.1" },
        { "https://169.254.169.254/latest/meta-data/", "169.254.169.254" },
        { "https://100.64.0.1/x.kat", "100.64.0.1" },
        { "https://0.0.0.0/x.kat", "0.0.0.0" },
        { "https://224.0.0.1/x.kat", "224.0.0.1" },
        { "https://255.255.255.255/x.kat", "255.255.255.255" },
        // Every spelling of a literal is one address.
        { "https://127.1/x.kat", "127.0.0.1" },
        { "https://2130706433/x.kat", "127.0.0.1" },
        { "https://0x7f.1/x.kat", "127.0.0.1" },
        { "https://0177.0.0.1/x.kat", "127.0.0.1" },
        { "https://[::1]/x.kat", "::1" },
        { "https://[::]/x.kat", "::" },
        { "https://[fe80::1]/x.kat", "fe80::1" },
        { "https://[fc00::1]/x.kat", "fc00::1" },
        { "https://[fd12:3456:789a::1]/x.kat", "fd12:3456:789a::1" },
        { "https://[ff02::1]/x.kat", "ff02::1" },
        { "https://[::ffff:127.0.0.1]/x.kat", "::ffff:127.0.0.1" },
        { "https://[::ffff:10.0.0.1]/x.kat", "::ffff:10.0.0.1" },
        { "https://[::ffff:169.254.169.254]/x.kat", "::ffff:169.254.169.254" },
        { "https://[64:ff9b::7f00:1]/x.kat", "64:ff9b::7f00:1" },
    };

    [Theory]
    [MemberData(nameof(NonPublicAddresses))]
    public async Task ANonPublicAddress_IsRefusedBeforeAnyRequest(string url, string address)
    {
        var handler = new StubHttpHandler(() => StubHttpHandler.Text(Program));
        using var transport = handler.Transport();
        // The address as the platform writes it, whatever the spelling in the link.
        var shown = IPAddress.Parse(address).ToString();
        var expected = $"katlang: cannot download '{url}': its host is not at a public address ({shown})." + Environment.NewLine;

        foreach (var command in new[] { "run", "check", "source" })
        {
            var result = await Cli.InvokeWithTransportAsync(transport, command, url);

            Assert.Equal((Failure, "", expected), (result.ExitCode, result.Output, result.Error));
        }

        Assert.Empty(handler.RequestedUrls);
    }

    [Fact]
    public async Task ASubstituteDownloadersFailure_IsOneFixedLine_WithNoneOfItsText()
    {
        // Only the CLI's own downloader words a failure; another one's message is not printed.
        Func<string, CancellationToken, ValueTask<string>> failing =
            (_, _) => ValueTask.FromException<string>(new InvalidOperationException("\u001b[31mplanted text\r\nkatlang: forged line"));

        var result = await Cli.InvokeWithDownloaderAsync(failing, "run", ElsewhereUrl, "--code-link");

        Assert.Equal(
            (Failure, "", $"katlang: cannot download '{ElsewhereUrl}': the download failed." + Environment.NewLine),
            (result.ExitCode, result.Output, result.Error));
    }

    [Fact]
    public async Task TheLinkIsEchoedThroughTheTerminalSafeChannel()
    {
        // The link is the user's own text, and may hold anything: as one CLI line, its control
        // and format characters are shown as escapes.
        var url = "https://example.com/\u001b[2J\u202Eprogram.kat\r\nkatlang: forged line";
        var downloader = new RecordingDownloader();

        var result = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "run", url);

        Assert.Equal(
            "katlang: cannot download 'https://example.com/\\u001B[2J\\u202Eprogram.kat\\u000D\\u000Akatlang: forged line': the download failed."
            + Environment.NewLine,
            result.Error);
        Assert.Equal(url, Assert.Single(downloader.RequestedUrls));
    }

    [Theory]
    [InlineData("https://example.com/p.kat", "https://example.com/p.kat")]
    [InlineData("https://u:p@example.com/p.kat", "https://<redacted>@example.com/p.kat")]
    [InlineData("https://u:p@a@b@example.com/p@q.kat?x=@", "https://<redacted>@example.com/p@q.kat?x=@")]
    [InlineData("https://example.com/p@q.kat", "https://example.com/p@q.kat")]
    [InlineData("https://example.com?x=u:p@q", "https://example.com?x=u:p@q")]
    [InlineData("https://u:p@example.com", "https://<redacted>@example.com")]
    [InlineData(@"https://u:p@example.com\path", @"https://<redacted>@example.com\path")]
    [InlineData("https://", "https://")]
    [InlineData("no scheme at all @ here", "no scheme at all @ here")]
    public void Echo_ShowsTheLinkAsGiven_WithUserInformationRedacted(string link, string echoed)
        => Assert.Equal(echoed, ProgramUrl.Echo(link));

    // ── Modules ─────────────────────────────────────────────────────────────

    private const string ModuleUrl = "https://modules.example.net/lib/tax.kat";
    private const string LoadingProgram = "open '" + ModuleUrl + "'\nRate * 2\n";

    [Fact]
    public async Task ADownloadedProgram_LoadsAModuleFromAnyHost_OnlyWithAllowLoading()
    {
        var pages = new Dictionary<string, string> { [ElsewhereUrl] = LoadingProgram, [ModuleUrl] = "public Rate = 21" };

        // Without the flag only the program the user named is downloaded: the host a program
        // names is never contacted.
        var plainHandler = new StubHttpHandler(pages);
        using var plain = plainHandler.Transport();
        foreach (var command in new[] { "run", "check" })
        {
            var result = await Cli.InvokeWithTransportAsync(plain, command, ElsewhereUrl);

            Assert.Equal((Failure, ""), (result.ExitCode, result.Output));
            Assert.Contains("module elaboration is unavailable", result.TrimmedError);
        }

        Assert.Equal([ElsewhereUrl, ElsewhereUrl], plainHandler.RequestedUrls);

        // With it, the module comes through the same downloader, from a host that is not katlang.org.
        var loadingHandler = new StubHttpHandler(pages);
        using var loading = loadingHandler.Transport();
        var run = await Cli.InvokeWithTransportAsync(loading, "run", ElsewhereUrl, "--allow-loading");
        var check = await Cli.InvokeWithTransportAsync(loading, "check", "--allow-loading", ElsewhereUrl);

        Assert.Equal((Success, "42", ""), (run.ExitCode, run.TrimmedOutput, run.Error));
        Assert.Equal((Success, "", ""), (check.ExitCode, check.Output, check.Error));
        Assert.Equal([ElsewhereUrl, ModuleUrl, ElsewhereUrl, ModuleUrl], loadingHandler.RequestedUrls);
    }

    [Theory]
    [InlineData("eval")]
    [InlineData("run")]
    public async Task AModule_LoadsFromAHostThatIsNotKatlangOrg_ThroughTheGuardedDownloader(string command)
    {
        var handler = new StubHttpHandler(new Dictionary<string, string> { [ModuleUrl] = "public Rate = 21" });
        using var transport = handler.Transport();
        using var file = new TempSourceFile(LoadingProgram);
        var operand = command == "eval" ? LoadingProgram : file.Path;

        var without = await Cli.InvokeWithTransportAsync(transport, command, operand);
        var with = await Cli.InvokeWithTransportAsync(transport, command, operand, "--allow-loading");

        Assert.Equal((Failure, ""), (without.ExitCode, without.Output));
        Assert.Contains("module elaboration is unavailable", without.TrimmedError);
        Assert.Equal((Success, "42", ""), (with.ExitCode, with.TrimmedOutput, with.Error));
        Assert.Equal(ModuleUrl, Assert.Single(handler.RequestedUrls));
    }

    [Fact]
    public async Task AModulesMediaType_IsNotJudged_OnlyAProgramUrlsIs()
    {
        // The content-type rule belongs to the program the operand names. A module is fetched
        // because the user allowed loading, from wherever a program names, and module servers
        // have never had to state a type: its text is judged as KatLang by KatLang.
        var handler = new StubHttpHandler(() => StubHttpHandler.Text("public Rate = 21", "text/html"));
        using var transport = handler.Transport();

        var result = await Cli.InvokeWithTransportAsync(transport, "eval", LoadingProgram, "--allow-loading");

        Assert.Equal((Success, "42", ""), (result.ExitCode, result.TrimmedOutput, result.Error));
    }

    public static TheoryData<string, string> RefusedModuleTargets => new()
    {
        { "https://127.0.0.1/m.kat", "load: failed to fetch 'https://127.0.0.1/m.kat': its host is not at a public address (127.0.0.1)." },
        { "https://10.0.0.1/m.kat", "load: failed to fetch 'https://10.0.0.1/m.kat': its host is not at a public address (10.0.0.1)." },
        { "https://192.168.1.1/m.kat", "load: failed to fetch 'https://192.168.1.1/m.kat': its host is not at a public address (192.168.1.1)." },
        { "https://169.254.169.254/m.kat", "load: failed to fetch 'https://169.254.169.254/m.kat': its host is not at a public address (169.254.169.254)." },
        { "https://[::1]/m.kat", "load: failed to fetch 'https://[::1]/m.kat': its host is not at a public address (::1)." },
        { "https://[fe80::1]/m.kat", "load: failed to fetch 'https://[fe80::1]/m.kat': its host is not at a public address (fe80::1)." },
        // KatLang's own checks of a load target are unchanged by admitting every host.
        { "http://modules.example.net/m.kat", "load: only HTTPS URLs are allowed (got 'http')." },
        { "https://alice:s3cret@modules.example.net/m.kat", "load: a module URL must not contain user information; remove the 'user@' or 'user:password@' part before the host." },
    };

    [Theory]
    [MemberData(nameof(RefusedModuleTargets))]
    public async Task AModuleTarget_PassesTheSameGuardrails_BeforeAnyRequest(string target, string diagnostic)
    {
        var handler = new StubHttpHandler(() => StubHttpHandler.Text("public Rate = 21"));
        using var transport = handler.Transport();

        var result = await Cli.InvokeWithTransportAsync(transport, "eval", $"open '{target}'\nRate\n", "--allow-loading");

        Assert.Equal((Failure, ""), (result.ExitCode, result.Output));
        Assert.EndsWith(diagnostic, result.TrimmedError, StringComparison.Ordinal);
        Assert.Empty(handler.RequestedUrls);
    }

    [Fact]
    public async Task AModuleDownloadThatFails_IsALoadDiagnostic_InTheSameWords()
    {
        var responses = new Dictionary<string, Func<HttpResponseMessage>>
        {
            ["/missing.kat"] = () => StubHttpHandler.Status(HttpStatusCode.NotFound),
            ["/moved.kat"] = () => StubHttpHandler.Status(HttpStatusCode.Found, "https://elsewhere.example.org/m.kat"),
            ["/large.kat"] = () => StubHttpHandler.Bytes(new byte[(int)HttpSourceDownloader.MaxResponseBodyBytes + 1], "text/plain"),
        };
        var handler = new StubHttpHandler(request => responses[request.RequestUri!.AbsolutePath]());
        using var transport = handler.Transport();

        async Task<string> LoadAsync(string path)
        {
            var result = await Cli.InvokeWithTransportAsync(
                transport, "eval", $"open 'https://modules.example.net{path}'\n1\n", "--allow-loading");
            Assert.Equal((Failure, ""), (result.ExitCode, result.Output));
            return result.TrimmedError;
        }

        Assert.EndsWith(
            "load: failed to fetch 'https://modules.example.net/missing.kat': the server responded with HTTP status 404; only 200 (OK) is accepted.",
            await LoadAsync("/missing.kat"));
        Assert.EndsWith(
            "load: failed to fetch 'https://modules.example.net/moved.kat': the server responded with a redirect (HTTP status 302), and redirects are not allowed.",
            await LoadAsync("/moved.kat"));
        Assert.EndsWith(
            "load: failed to fetch 'https://modules.example.net/large.kat': the declared Content-Length of 1048577 bytes exceeds the 1048576-byte limit.",
            await LoadAsync("/large.kat"));
        Assert.DoesNotContain("https://elsewhere.example.org/m.kat", handler.RequestedUrls);
    }

    // ── Support ─────────────────────────────────────────────────────────────

    /// <summary>A response that never arrives; <see cref="Started"/> completes when a request waits for it.</summary>
    private sealed class NeverRespondingHandler : HttpMessageHandler
    {
        public TaskCompletionSource Started { get; } = new(TaskCreationOptions.RunContinuationsAsynchronously);

        protected override async Task<HttpResponseMessage> SendAsync(HttpRequestMessage request, CancellationToken cancellationToken)
        {
            Started.TrySetResult();
            await Task.Delay(Timeout.InfiniteTimeSpan, cancellationToken);
            throw new InvalidOperationException("unreachable");
        }
    }

    /// <summary>A body that counts how often it was asked for its bytes, with or without a declared length.</summary>
    private sealed class CountingContent : HttpContent
    {
        private readonly byte[] _body;
        private readonly bool _declareLength;

        public CountingContent(byte[] body, string mediaType, bool declareLength = true)
        {
            _body = body;
            _declareLength = declareLength;
            Headers.ContentType = new System.Net.Http.Headers.MediaTypeHeaderValue(mediaType);
        }

        public int SerializeCalls { get; private set; }

        protected override async Task SerializeToStreamAsync(Stream stream, TransportContext? context)
        {
            SerializeCalls++;
            await stream.WriteAsync(_body);
        }

        protected override bool TryComputeLength(out long length)
        {
            length = _body.Length;
            return _declareLength;
        }
    }
}
