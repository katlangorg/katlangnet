using System.Net;
using System.Text.RegularExpressions;

namespace KatLang.CLI.Tests;

/// <summary>
/// What the CLI says about program links, in <c>--help</c> and in its guide, against what it
/// does: the usage lines, the two kinds of link, the download rules with their shipped bounds,
/// and every exact stderr line. Tools read those lines (the KatLang agent skill among them), so
/// each documented sentence is the sentence the code produces.
/// </summary>
public sealed class ProgramLinkDocumentationTests
{
    private static async Task<(string Help, string Prose)> HelpAsync()
    {
        var result = await Cli.InvokeAsync("--help");
        Assert.Equal((0, ""), (result.ExitCode, result.Error));
        return (result.TrimmedOutput, Regex.Replace(result.TrimmedOutput, @"\s+", " "));
    }

    [Fact]
    public async Task Help_UsageLines_NameTheLinkOperand()
    {
        var (help, _) = await HelpAsync();

        Assert.StartsWith(
            "Usage:\n"
            + "  katlang run <file|link> [--allow-loading] [--random-seed <integer>]\n"
            + "                          [--min-decimal-places <integer>]\n"
            + "                          [--max-decimal-places <integer>] [--code-link]\n"
            + "  katlang eval <source> [--allow-loading] [--random-seed <integer>]\n"
            + "                        [--min-decimal-places <integer>]\n"
            + "                        [--max-decimal-places <integer>] [--code-link]\n"
            + "  katlang check <file|link> [--allow-loading] [--code-link]\n"
            + "  katlang source <link>\n"
            + "\n"
            + "Options:\n",
            help);
        // eval takes source text, never a link.
        Assert.DoesNotContain("eval <source|link>", help);
        Assert.DoesNotContain("<file>", help);
    }

    [Fact]
    public async Task Help_AllowLoading_SaysModulesComeFromAnyPublicHttpsAddress()
    {
        var (help, prose) = await HelpAsync();

        Assert.Contains(
            "\n  --allow-loading    Allow the program to download and run KatLang\n"
            + "                     modules (load and open '<url>').\n",
            help);
        Assert.Contains(
            "Disabled by default. Modules are fetched over HTTPS from any public address: "
            + "an address on this machine or on a private network is refused, and so are redirects.",
            prose);
        Assert.Contains(
            $"Each download has an absolute deadline of {HttpSourceDownloader.DownloadTimeout.TotalSeconds:0} seconds for request and body acquisition.",
            prose);
        var bytes = HttpSourceDownloader.MaxResponseBodyBytes.ToString("N0", System.Globalization.CultureInfo.InvariantCulture);
        Assert.Contains(
            $"Each module is limited to 1 MiB ({bytes} content bytes), excluding HTTP headers and chunk framing.",
            prose);
        Assert.Contains("Without this option a program contacts no host it names.", prose);
        Assert.DoesNotContain("subdomains", help);
    }

    [Fact]
    public async Task Help_DocumentsReadingAProgramLink()
    {
        var (help, prose) = await HelpAsync();

        // The section, and that run and check take links too.
        Assert.Contains(
            "\nReading a program link:\n  run, check and source take a program link in place of a file: an\n",
            help);
        Assert.DoesNotContain("Reading a code link:", help);
        Assert.Contains(
            "run, check and source take a program link in place of a file: an operand that starts with "
            + "https:// or http:// (source reads every operand as a link).",
            prose);
        Assert.Contains(
            "Once the program is read, run and check do exactly what they do with a file that holds the same text, "
            + "and --code-link gives the link of the text that was read.",
            prose);
        Assert.Contains("There are two kinds of link, told apart by the address.", prose);

        // A code link: in the link, decoded here, never downloaded.
        Assert.Contains(
            "\n  code link          The program is in the link itself, after a #:\n"
            + "                       https://katlang.org/#<format>/<payload>\n",
            help);
        Assert.Contains("whatever comes before the #. It is decoded here and nothing is downloaded.", prose);
        Assert.Contains("The program runs exactly as the link carries it, every line break and character included.", prose);
        Assert.Contains(
            "(it is damaged, cut short, changed or over a limit, or its # starts no code link) "
            + "fails with exit status 1 and one line on stderr:",
            prose);
        Assert.Contains("\n                       katlang: invalid code link: <reason>\n", help);

        // A program URL: downloaded, with the same rules, the accepted content types, and the /a/<id> page.
        Assert.Contains("\n  program URL        Any link without a #. The program is downloaded\n", help);
        Assert.Contains(
            "The program is downloaded as text, with no option needed, under the rules of --allow-loading: "
            + $"HTTPS only, a public address only, no redirects, 1 MiB, {HttpSourceDownloader.DownloadTimeout.TotalSeconds:0} seconds.",
            prose);
        Assert.Contains(
            "The response must be text/plain or application/octet-stream: "
            + "a web page or any other content is refused before anything runs.",
            prose);
        Assert.Contains(
            "\n                     A shared program's page on katlang.org,\n"
            + "                       https://katlang.org/a/<id>\n"
            + "                     is read from its text address,\n"
            + "                       https://katlang.org/api/a/<id>\n",
            help);
        Assert.Contains(
            "\n                     A link that gives no program fails with exit\n"
            + "                     status 1 and one of these lines on stderr:\n"
            + "                       katlang: not found: '<link>'.\n"
            + "                       katlang: not KatLang source: '<link>' returned <type>.\n"
            + "                       katlang: cannot download '<link>': <reason>\n",
            help);

        // run and check evaluate what source will not print.
        Assert.Contains("run and check evaluate such a program as it is.", prose);
        Assert.Contains(
            "An unpaired surrogate is written as U+FFFD in an output row and as a \\uXXXX escape in a diagnostic.",
            prose);

        Assert.All(help.Split('\n'), line => Assert.True(line.Length <= 80, $"help line exceeds 80 columns: '{line}'"));
        Assert.All(help, character => Assert.True(character is '\n' or (>= ' ' and <= '~'), $"help is not plain ASCII: U+{(int)character:X4}"));
    }

    [Fact]
    public void TheDocumentedLines_AreTheLinesTheCodeWrites()
    {
        const string link = "<link>";

        Assert.Equal(
            "katlang: not found: '<link>'.",
            CliApplication.DownloadFailureLine(link, DownloadException.UnexpectedStatus(HttpStatusCode.NotFound)));
        Assert.Equal(
            "katlang: not KatLang source: '<link>' returned text/html.",
            CliApplication.DownloadFailureLine(link, DownloadException.NotKatLangSource("text/html")));
        Assert.Equal(
            "katlang: not KatLang source: '<link>' returned no Content-Type.",
            CliApplication.DownloadFailureLine(link, DownloadException.NotKatLangSource(null)));
        Assert.Equal(
            "katlang: not KatLang source: '<link>' returned a Content-Type that cannot be read.",
            CliApplication.DownloadFailureLine(link, DownloadException.NotKatLangSource(null, unreadable: true)));
        Assert.Equal(
            "katlang: cannot download '<link>': only HTTPS addresses are downloaded.",
            CliApplication.DownloadFailureLine(link, DownloadException.NotHttps()));
        Assert.Equal(
            "katlang: cannot download '<link>': the download failed.",
            CliApplication.DownloadFailureLine(link, new HttpRequestException("anything")));
        Assert.Equal(
            "katlang: cannot download '<link>': the download failed.",
            CliApplication.DownloadFailureLine(link, failure: null));

        // Every sentence of the downloader is one line of printable ASCII that ends with a period.
        Assert.All(DocumentedReasons().Select(reason => reason.Sentence), sentence =>
        {
            Assert.EndsWith(".", sentence, StringComparison.Ordinal);
            Assert.All(sentence, character => Assert.InRange(character, ' ', '~'));
            Assert.True(char.IsLower(sentence[0]), sentence);
        });
    }

    [Fact]
    public void CliGuide_DocumentsProgramLinks_AndEveryExactLine()
    {
        var guide = File.ReadAllText(RepositoryFile("docs/cli.md"));

        // Both kinds of link, with their examples.
        Assert.Contains("katlang run \"https://katlang.org/#1/4MWjDBlNE4PH\"", guide, StringComparison.Ordinal);
        Assert.Contains("prints `25`", guide, StringComparison.Ordinal);
        Assert.Contains("katlang run \"https://katlang.org/a/019ead4b-d41d-7564-ba11-c177f917a0fe\"", guide, StringComparison.Ordinal);
        Assert.Contains("katlang source \"https://katlang.org/a/019ead4b-d41d-7564-ba11-c177f917a0fe\"", guide, StringComparison.Ordinal);
        Assert.Contains("`https://katlang.org/api/a/<id>`", guide, StringComparison.Ordinal);
        Assert.Contains("`text/plain`, in any character set, or `application/octet-stream`", guide, StringComparison.Ordinal);

        // The refusal and download error lines.
        Assert.Contains("`katlang: invalid code link: <reason>`", guide, StringComparison.Ordinal);
        Assert.Contains("`katlang: not found: '<link>'.`", guide, StringComparison.Ordinal);
        Assert.Contains("`katlang: not KatLang source: '<link>' returned text/html.`", guide, StringComparison.Ordinal);
        Assert.Contains("`katlang: cannot download '<link>': <reason>`", guide, StringComparison.Ordinal);
        Assert.Contains("`no Content-Type`", guide, StringComparison.Ordinal);
        Assert.Contains("`a Content-Type that cannot be read`", guide, StringComparison.Ordinal);
        Assert.Contains("`load: failed to fetch '<url>': <reason>`", guide, StringComparison.Ordinal);
        Assert.All(
            DocumentedReasons(),
            reason => Assert.True(
                guide.Contains("`" + reason.Documented + "`", StringComparison.Ordinal),
                $"docs/cli.md does not list the download reason: {reason.Documented}"));

        // Where modules may come from: the CLI admits any public HTTPS host, and the library's
        // guide names the one typed way a host does the same.
        Assert.Contains("a module may come from **any public HTTPS host**", guide, StringComparison.Ordinal);
        Assert.Contains("the system proxy settings are not used", guide, StringComparison.Ordinal);
        Assert.Contains("`RunOptions.AllowAnyHost = true`", File.ReadAllText(RepositoryFile("docs/dotnet.md")), StringComparison.Ordinal);
        foreach (var document in new[] { "README.md", "docs/cli.md", "docs/dotnet.md" })
            Assert.DoesNotContain("on an allowed host (`katlang.org` and its subdomains)", File.ReadAllText(RepositoryFile(document)), StringComparison.Ordinal);
    }

    [Fact]
    public void Tutorial_SaysThatRunTakesALink_AndWhereModulesMayComeFrom()
    {
        var tutorial = File.ReadAllText(RepositoryFile("tutorial.md"));

        Assert.Contains("use `katlang source \"<link>\"`", tutorial, StringComparison.Ordinal);
        Assert.Contains("`katlang run \"<link>\"` runs the program of a code link", tutorial, StringComparison.Ordinal);
        Assert.Contains("(`https://katlang.org/a/...`)", tutorial, StringComparison.Ordinal);
        Assert.Contains("the command-line tool, with `--allow-loading`, allows any host on the public internet", tutorial, StringComparison.Ordinal);
        Assert.DoesNotContain("by default `katlang.org` and its subdomains", tutorial, StringComparison.Ordinal);
    }

    /// <summary>
    /// Every sentence a <see cref="DownloadException"/> can carry, and how the CLI guide writes it:
    /// with a placeholder where the sentence holds a value.
    /// </summary>
    private static IEnumerable<(string Sentence, string Documented)> DocumentedReasons()
    {
        static (string, string) Fixed(DownloadException exception) => (exception.Message, exception.Message);
        var limit = HttpSourceDownloader.MaxResponseBodyBytes;

        yield return Fixed(DownloadException.InvalidAddress());
        yield return Fixed(DownloadException.NotHttps());
        yield return Fixed(DownloadException.UserInformation());
        yield return Fixed(DownloadException.NameResolution());
        yield return Fixed(DownloadException.ConnectionFailed());
        yield return Fixed(DownloadException.RequestFailed(new HttpRequestException(HttpRequestError.SecureConnectionError)));
        yield return Fixed(DownloadException.RequestFailed(new HttpRequestException(HttpRequestError.Unknown)));
        yield return Fixed(DownloadException.BodyTooLarge(limit));
        yield return Fixed(DownloadException.DeadlineExceeded(HttpSourceDownloader.DownloadTimeout));
        yield return Fixed(DownloadException.UnsupportedCharacterSet());

        var address = DownloadException.NonPublicAddress(IPAddress.Loopback).Message;
        yield return (address, address.Replace("(127.0.0.1)", "(<address>)", StringComparison.Ordinal));
        var redirect = DownloadException.Redirect(HttpStatusCode.Found).Message;
        yield return (redirect, redirect.Replace("status 302", "status <status>", StringComparison.Ordinal));
        var status = DownloadException.UnexpectedStatus(HttpStatusCode.InternalServerError).Message;
        yield return (status, status.Replace("status 500", "status <status>", StringComparison.Ordinal));
        var declared = DownloadException.DeclaredLengthTooLarge(7, limit).Message;
        yield return (declared, declared.Replace("of 7 bytes", "of <bytes> bytes", StringComparison.Ordinal));
    }

    [Fact]
    public void TheDocumentedReasons_CoverEveryDownloadFailure()
    {
        // A new kind of failure needs its sentence in the CLI guide: this list is what the guide
        // test reads, and it must reach every kind but the one worded on its own line.
        var covered = new HashSet<DownloadFailure>
        {
            DownloadException.InvalidAddress().Failure,
            DownloadException.NotHttps().Failure,
            DownloadException.UserInformation().Failure,
            DownloadException.NonPublicAddress(IPAddress.Loopback).Failure,
            DownloadException.NameResolution().Failure,
            DownloadException.ConnectionFailed().Failure,
            DownloadException.RequestFailed(new HttpRequestException(HttpRequestError.SecureConnectionError)).Failure,
            DownloadException.RequestFailed(new HttpRequestException(HttpRequestError.Unknown)).Failure,
            DownloadException.Redirect(HttpStatusCode.Found).Failure,
            DownloadException.UnexpectedStatus(HttpStatusCode.InternalServerError).Failure,
            DownloadException.DeclaredLengthTooLarge(7, 6).Failure,
            DownloadException.DeadlineExceeded(TimeSpan.FromSeconds(1)).Failure,
            DownloadException.UnsupportedCharacterSet().Failure,
            DownloadException.NotKatLangSource("text/html").Failure,
        };

        Assert.Equal(Enum.GetValues<DownloadFailure>().Order(), covered.Order());
        Assert.Equal(DownloadFailure.NameResolution, DownloadException.RequestFailed(new HttpRequestException(HttpRequestError.NameResolutionError)).Failure);
        Assert.Equal(DownloadFailure.ConnectionFailed, DownloadException.RequestFailed(new HttpRequestException(HttpRequestError.ConnectionError)).Failure);
    }

    private static string RepositoryFile(string relativePath)
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "KatLang.slnx")))
            directory = directory.Parent;
        Assert.NotNull(directory);

        return Path.Combine(directory.FullName, relativePath);
    }
}
