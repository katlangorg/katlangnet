using System.Text;
using KatLang.Tests.CodeLinks;

namespace KatLang.CLI.Tests;

/// <summary>
/// A code link as the operand of <c>run</c> and <c>check</c>: the program is in the link, so it
/// is decoded offline and then the command is exactly what it is for a file that holds the
/// same text — byte-identical stdout, stderr and exit status. A link that carries no program
/// is one fixed line on stderr and exit status 1, and the downloader is never asked.
/// </summary>
public sealed class CodeLinkOperandCliTests
{
    private const int Success = 0;
    private const int Failure = 1;
    private const string LinkPrefix = "https://katlang.org/#1/";

    /// <summary>The documented link: it opens <c>100 - 3 * 5 ^ 2</c>.</summary>
    private const string DocumentedLink = LinkPrefix + "4MWjDBlNE4PH";

    /// <summary>A published shared program's id, as an address a code link can follow.</summary>
    private const string ShareId = "019ead4b-d41d-7564-ba11-c177f917a0fe";

    /// <summary>
    /// A bound on one invocation that no fixture program approaches: a program that never ended
    /// would otherwise hang the suite, and here it fails an equality instead.
    /// </summary>
    private static readonly TimeSpan InvocationBound = TimeSpan.FromMinutes(2);

    private static string LinkOf(string fixtureCase) => LinkPrefix + CodeLinkFixtures.Generated(fixtureCase).Payload;

    private static string InvalidLinkLine(CodeLinkRefusal reason)
        => "katlang: invalid code link: " + CodeLinkText.RefusalReason(reason);

    /// <summary>One invocation whose downloader records every request, under <see cref="InvocationBound"/>.</summary>
    private static async Task<(CliResult Result, IReadOnlyList<string> Downloads)> InvokeAsync(params string[] args)
    {
        var downloader = new RecordingDownloader();
        using var bound = new CancellationTokenSource(InvocationBound);
        var output = new StringWriter();
        var error = new StringWriter();
        var exitCode = await CliApplication.RunAsync(args, output, error, downloader.DownloadAsync, bound.Token);
        return (new CliResult(exitCode, output.ToString(), error.ToString()), downloader.RequestedUrls);
    }

    private static void AssertSameRun(CliResult fromFile, CliResult fromLink, string what)
    {
        Assert.True(
            fromFile.ExitCode == fromLink.ExitCode && fromFile.Output == fromLink.Output && fromFile.Error == fromLink.Error,
            $"{what}: the link ran differently from the file.\n"
            + $"file: exit {fromFile.ExitCode}, stdout {Show(fromFile.Output)}, stderr {Show(fromFile.Error)}\n"
            + $"link: exit {fromLink.ExitCode}, stdout {Show(fromLink.Output)}, stderr {Show(fromLink.Error)}");
    }

    private static string Show(string text)
    {
        var shown = new StringBuilder("\"");
        foreach (var ch in text.Length <= 400 ? text : text[..400] + "…")
            shown.Append(ch is >= ' ' and <= '~' ? ch.ToString() : $"\\u{(int)ch:X4}");
        return shown.Append('"').ToString();
    }

    private static bool IsWellFormed(string text)
    {
        for (var i = 0; i < text.Length; i++)
        {
            if (char.IsHighSurrogate(text[i]) && i + 1 < text.Length && char.IsLowSurrogate(text[i + 1]))
                i++;
            else if (char.IsSurrogate(text[i]))
                return false;
        }

        return true;
    }

    // ── The program runs ────────────────────────────────────────────────────

    [Fact]
    public async Task Run_OfTheDocumentedLink_PrintsItsResult()
    {
        var (result, downloads) = await InvokeAsync("run", DocumentedLink);

        Assert.Equal((Success, "25" + Environment.NewLine, ""), (result.ExitCode, result.Output, result.Error));
        Assert.Empty(downloads);
    }

    [Fact]
    public async Task Check_OfTheDocumentedLink_SucceedsSilently()
    {
        var (result, downloads) = await InvokeAsync("check", DocumentedLink);

        Assert.Equal((Success, "", ""), (result.ExitCode, result.Output, result.Error));
        Assert.Empty(downloads);
    }

    /// <summary>The six vectors of katlangweb's <c>docs/code-links.md</c>: source, link and result.</summary>
    public static TheoryData<string, string, string> DocumentedVectors => new()
    {
        { "1", "https://katlang.org/#1/ML4", "1" },
        { "100 - 3 * 5 ^ 2", "https://katlang.org/#1/4MWjDBlNE4PH", "25" },
        { "A = 1\r\nB = 2\r\nA + B\r\n", "https://katlang.org/#1/9Sj55xXYp6jJZ2-pb", "3" },
        {
            "# One resistor is connected to a 4V power supply.\n\nU = 4\nI = 0.5\nU / I\n",
            "https://katlang.org/#1/_cNbIecaKh_JZHh11cpnx_LxQDEhixebQoJhewkz40JmmWfbxt6_Zt6jn42xeH",
            "8"
        },
        {
            "# Latviski: āčēģīķļņšūž ĀČĒĢĪĶĻŅŠŪŽ\n'Sveika, pasaule!'",
            "https://katlang.org/#1/_ZtbNNBRDFBp0XNdkXFhYCcMFcSoKtr2V2RQ0WSqtYr9sEtKq15vGA6u46YpzmtIKn1ZMox0qXLhYEOcUqSbZMgQ-K",
            "Sveika, pasaule!"
        },
        {
            "Values = 22, 66, 154\n# {braces} and ~tildes~ | pipes\nValues.sum",
            "https://katlang.org/#1/-AN8dipS4HIHzGaLEtew0MgQojoBh7ERxKHgv3a9aUy51EL4F",
            "242"
        },
    };

    [Theory]
    [MemberData(nameof(DocumentedVectors))]
    public async Task ADocumentedVector_RunsAndChecks_ExactlyAsAFileWithItsSource(string source, string link, string expectedOutput)
    {
        // The link is that source's, and the source is that link's.
        Assert.Equal(link, Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(source)).Url);
        Assert.Equal(source, Assert.IsType<CodeLinkDecoding.Program>(CodeLink.DecodeLink(link)).Source);
        using var file = new ExactProgramFile(source);

        var (fromLink, downloads) = await InvokeAsync("run", link);
        var (fromFile, _) = await InvokeAsync("run", file.Path);
        var (checkedLink, checkDownloads) = await InvokeAsync("check", link);
        var (checkedFile, _) = await InvokeAsync("check", file.Path);

        Assert.Equal((Success, expectedOutput + Environment.NewLine, ""), (fromLink.ExitCode, fromLink.Output, fromLink.Error));
        AssertSameRun(fromFile, fromLink, "run");
        Assert.Equal((Success, "", ""), (checkedLink.ExitCode, checkedLink.Output, checkedLink.Error));
        AssertSameRun(checkedFile, checkedLink, "check");
        Assert.Empty(downloads);
        Assert.Empty(checkDownloads);
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task EveryFixtureLink_RunsAndChecks_ExactlyAsAFileWithTheSameText(string command)
    {
        // The whole encoder corpus: tutorial programs in every line-ending form, programs that
        // fail to parse or to evaluate, loops, Latvian and other scripts, control characters,
        // and text up to both limits. A file cannot hold an unpaired surrogate, so those
        // programs have their own tests below.
        var compared = 0;
        foreach (var @case in CodeLinkFixtures.GeneratedCases.Where(@case => @case.Status == "ok" && IsWellFormed(@case.Source)))
        {
            using var file = new ExactProgramFile(@case.Source);
            string[] options = command == "run" ? ["--random-seed", "1"] : [];

            var (fromLink, downloads) = await InvokeAsync([command, LinkPrefix + @case.Payload, .. options]);
            var (fromFile, _) = await InvokeAsync([command, file.Path, .. options]);

            AssertSameRun(fromFile, fromLink, $"{command} of fixture case '{@case.Name}'");
            Assert.Empty(downloads);
            compared++;
        }

        Assert.True(compared >= 680, $"{compared} fixture programs were compared");
    }

    [Theory]
    [InlineData("lines-lf")]
    [InlineData("lines-lf-final")]
    [InlineData("lines-crlf")]
    [InlineData("lines-crlf-final")]
    [InlineData("lines-cr")]
    [InlineData("lines-mixed")]
    [InlineData("lines-tabs")]
    [InlineData("lines-trailing-spaces")]
    [InlineData("lines-unicode-separators")]
    [InlineData("latvian-comment")]
    [InlineData("latvian-strings")]
    [InlineData("latvian-crlf")]
    [InlineData("emoji-in-string")]
    [InlineData("controls-in-program")]
    [InlineData("program-error")]
    [InlineData("program-parse-error")]
    [InlineData("program-while")]
    [InlineData("source-20000")]
    public async Task TheProgramIsExactlyWhatTheLinkCarries_AndItsOwnLinkIsTheLinkItCameFrom(string name)
    {
        // --code-link encodes the source that ran. For a code link that is the link's own
        // program, so the line names the canonical link again — for the file with the same
        // text too: one program, whichever way it was read.
        var @case = CodeLinkFixtures.Generated(name);
        var link = LinkPrefix + @case.Payload;
        using var file = new ExactProgramFile(@case.Source);

        var (fromLink, downloads) = await InvokeAsync("run", link, "--code-link");
        var (fromFile, _) = await InvokeAsync("run", file.Path, "--code-link");

        AssertSameRun(fromFile, fromLink, name);
        Assert.Equal("katlang-link: " + link, fromLink.TrimmedError.Split('\n')[^1]);
        Assert.Empty(downloads);
    }

    [Fact]
    public async Task ALoneCarriageReturn_IsNotALineBreak_SoTheProgramFailsExactlyLikeTheOriginal()
    {
        // 1 CR 2: a carriage return alone is whitespace, never a line break, so this is two
        // items on one line with no comma between them. Nothing may turn the CR into a line
        // break on the way: the link's program fails exactly as the file's does.
        const string link = "https://katlang.org/#1/jNQRjh2r";
        const string source = "1\r2";
        Assert.Equal(source, Assert.IsType<CodeLinkDecoding.Program>(CodeLink.DecodeLink(link)).Source);
        using var file = new ExactProgramFile(source);

        foreach (var command in new[] { "run", "check" })
        {
            var (fromLink, _) = await InvokeAsync(command, link);
            var (fromFile, _) = await InvokeAsync(command, file.Path);

            Assert.Equal(Failure, fromLink.ExitCode);
            Assert.Equal("", fromLink.Output);
            Assert.NotEqual("", fromLink.Error);
            AssertSameRun(fromFile, fromLink, command);
        }

        // With a real line break the same two numbers are two rows.
        var (twoRows, _) = await InvokeAsync("run", Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode("1\n2")).Url);
        Assert.Equal((Success, "1\n2"), (twoRows.ExitCode, twoRows.TrimmedOutput));
    }

    [Theory]
    [InlineData("payload-1970")]
    [InlineData("comment-payload-1970")]
    public async Task TheLongestValidLink_Runs(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);
        var link = LinkPrefix + @case.Payload;
        Assert.Equal(CodeLink.MaxPayloadLength, @case.Payload.Length);
        Assert.Equal(1_993, link.Length);
        using var file = new ExactProgramFile(@case.Source);

        foreach (var command in new[] { "run", "check" })
        {
            var (fromLink, downloads) = await InvokeAsync(command, link);
            var (fromFile, _) = await InvokeAsync(command, file.Path);

            AssertSameRun(fromFile, fromLink, command);
            Assert.Empty(downloads);
        }
    }

    [Theory]
    [InlineData("\uFEFF6 * 7")]
    [InlineData("\uFEFF\uFEFF6 * 7")]
    [InlineData("\uFEFF")]
    public async Task ALeadingByteOrderMark_IsPartOfALinksProgram_WhereAFileDropsOne(string source)
    {
        // A link carries a program's code units exactly, so a leading U+FEFF stays and the
        // program runs with it, as the Playground runs it. A file drops ONE leading byte order
        // mark, so the file that holds the same program has one more in front.
        var link = Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(source)).Url;
        using var file = new ExactProgramFile(source);
        using var withoutTheExtraMark = new TempSourceFile(source);

        var (fromLink, _) = await InvokeAsync("run", link, "--code-link");
        var (fromFile, _) = await InvokeAsync("run", file.Path, "--code-link");
        var (fromShortFile, _) = await InvokeAsync("run", withoutTheExtraMark.Path, "--code-link");

        AssertSameRun(fromFile, fromLink, "run");
        Assert.Equal("katlang-link: " + link, fromLink.TrimmedError.Split('\n')[^1]);

        // The file with no extra mark is a different program: the text after the mark.
        var rest = source[1..];
        var restLine = rest.Length == 0
            ? "katlang-link: none: the program is empty."
            : "katlang-link: " + Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(rest)).Url;
        Assert.Equal(restLine, fromShortFile.TrimmedError.Split('\n')[^1]);
    }

    // ── A link that carries no program ──────────────────────────────────────

    public static TheoryData<string, CodeLinkRefusal> RefusedLinks()
    {
        var data = new TheoryData<string, CodeLinkRefusal>
        {
            // The unreleased #code/ format, and every other fragment that starts no code link.
            { "https://katlang.org/#code/IwBhAIFpwZnAqcBWcA9cAmIA", CodeLinkRefusal.NotACodeLink },
            { "https://katlang.org/#c1/4MWjDBlNE4PH", CodeLinkRefusal.NotACodeLink },
            { "https://katlang.org/#01/4MWjDBlNE4PH", CodeLinkRefusal.NotACodeLink },
            { "https://katlang.org/#1", CodeLinkRefusal.NotACodeLink },
            { "https://katlang.org/#", CodeLinkRefusal.NotACodeLink },
            { "https://example.com/program.kat#L10", CodeLinkRefusal.NotACodeLink },
            { $"https://katlang.org/a/{ShareId}#top", CodeLinkRefusal.NotACodeLink },
            { "https://katlang.org/#1/", CodeLinkRefusal.EmptyPayload },
            { LinkPrefix + CodeLinkFixtures.Generated("payload-1971").Payload, CodeLinkRefusal.PayloadTooLong },
            // A payload followed by the punctuation of the sentence it was pasted from.
            { DocumentedLink + ".", CodeLinkRefusal.InvalidCharacter },
            { DocumentedLink + ")", CodeLinkRefusal.InvalidCharacter },
            { DocumentedLink + ",", CodeLinkRefusal.InvalidCharacter },
            { DocumentedLink + "%", CodeLinkRefusal.InvalidCharacter },
            { DocumentedLink + " ", CodeLinkRefusal.InvalidCharacter },
            { "https://katlang.org/#1/4MWjDBl#NE4PH", CodeLinkRefusal.InvalidCharacter },
            { "https://katlang.org/#2/4MWjDBlNE4PH", CodeLinkRefusal.UnsupportedVersion },
            { "https://katlang.org/#1/4MWjDBlNE4P", CodeLinkRefusal.Damaged },
            { "https://katlang.org/#1/A", CodeLinkRefusal.Damaged },
            // A payload of 20,001 "a", made with the format's reference implementation.
            { LinkPrefix + "__2O8I9GolghMVOv6xtq6e", CodeLinkRefusal.SourceTooLong },
            { DocumentedLink + "A", CodeLinkRefusal.NotCanonical },
        };
        return data;
    }

    [Fact]
    public void TheRefusedLinks_CoverEveryCodeLinkRefusal()
        => Assert.Equal(
            Enum.GetValues<CodeLinkRefusal>().Order(),
            RefusedLinks().Select(row => (CodeLinkRefusal)row[1]).Distinct().Order());

    [Theory]
    [MemberData(nameof(RefusedLinks))]
    public async Task ARefusedLink_IsOneLineOnStderr_NothingOnStdout_AndNoDownload(string link, CodeLinkRefusal reason)
    {
        var expected = InvalidLinkLine(reason) + Environment.NewLine;

        foreach (var command in new[] { "run", "check" })
        {
            var (plain, downloads) = await InvokeAsync(command, link);
            // No source was read, so there is no katlang-link line either, as for a missing file.
            var (withLinkOption, linkDownloads) = await InvokeAsync(command, link, "--code-link");
            var (withLoading, loadingDownloads) = await InvokeAsync(command, "--allow-loading", "--", link);

            // The command line was valid: no usage hint follows.
            Assert.Equal((Failure, "", expected), (plain.ExitCode, plain.Output, plain.Error));
            Assert.Equal((Failure, "", expected), (withLinkOption.ExitCode, withLinkOption.Output, withLinkOption.Error));
            Assert.Equal((Failure, "", expected), (withLoading.ExitCode, withLoading.Output, withLoading.Error));
            Assert.Empty(downloads);
            Assert.Empty(linkDownloads);
            Assert.Empty(loadingDownloads);
        }
    }

    [Fact]
    public async Task ARefusedLink_IsReportedLikeAMissingFile_WithNoUsageHint()
    {
        var (link, _) = await InvokeAsync("run", "https://katlang.org/#1/4MWjDBlNE4P", "--code-link");
        var (file, _) = await InvokeAsync("run", TempSourceFile.MissingPath(), "--code-link");

        Assert.Equal("katlang: invalid code link: its payload is damaged or cut short." + Environment.NewLine, link.Error);
        Assert.Single(file.TrimmedError.Split('\n'));
        Assert.StartsWith("katlang: file not found: ", file.Error);
        Assert.DoesNotContain(HelpText.UsageHint, link.Error + file.Error);
        Assert.DoesNotContain("katlang-link:", link.Error + file.Error);
    }

    [Fact]
    public async Task ARefusal_NeverEchoesTheLink()
    {
        // The reasons are fixed text: nothing of the link, which may hold anything, reaches
        // the terminal.
        var hostile = "https://katlang.org/\u001b[31m\u202E#1/\u001b]0;title\u0007\r\nkatlang: forged line";

        var (result, _) = await InvokeAsync("run", hostile);

        Assert.Equal((Failure, ""), (result.ExitCode, result.Output));
        Assert.Equal(InvalidLinkLine(CodeLinkRefusal.InvalidCharacter) + Environment.NewLine, result.Error);
    }

    // ── A code link never touches the network ───────────────────────────────

    [Theory]
    [InlineData("https://katlang.org/#1/4MWjDBlNE4PH")]
    [InlineData("HTTPS://KATLANG.ORG/#1/4MWjDBlNE4PH")]
    [InlineData("http://localhost:5218/#1/4MWjDBlNE4PH")]
    [InlineData("https://katlang.org/a/" + ShareId + "#1/4MWjDBlNE4PH")]
    [InlineData("https://katlang.org/api/a/" + ShareId + "#1/4MWjDBlNE4PH")]
    [InlineData("https://katlang.org/?utm_source=chat#1/4MWjDBlNE4PH")]
    [InlineData("https://user:secret@example.com:8443/any/path?x=1#1/4MWjDBlNE4PH")]
    [InlineData("https://127.0.0.1/#1/4MWjDBlNE4PH")]
    public async Task ACodeLink_IsReadByItsFragmentAlone_AndNeverDownloaded(string link)
    {
        // Whatever origin, path or query comes before the #, the program is the fragment's:
        // a shared program's page address with a code link behind it is the code link.
        foreach (var options in new string[][] { [], ["--allow-loading"], ["--code-link"] })
        {
            var (run, runDownloads) = await InvokeAsync(["run", link, .. options]);
            var (check, checkDownloads) = await InvokeAsync(["check", link, .. options.Where(option => option != "--code-link")]);

            Assert.Equal((Success, "25"), (run.ExitCode, run.TrimmedOutput));
            Assert.Equal((Success, "", ""), (check.ExitCode, check.Output, check.Error));
            Assert.Empty(runDownloads);
            Assert.Empty(checkDownloads);
        }
    }

    [Fact]
    public async Task ACodeLinksProgram_LoadsModulesOnlyWithAllowLoading()
    {
        // Once read, a link's program is a program like any other: its own load needs the flag.
        const string moduleUrl = "https://modules.example.net/lib.kat";
        var link = Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode($"open '{moduleUrl}'\nVal + 1\n")).Url;
        var downloader = new RecordingDownloader(new Dictionary<string, string> { [moduleUrl] = "public Val = 41" });

        var without = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "run", link);
        Assert.Equal((Failure, ""), (without.ExitCode, without.Output));
        Assert.Contains("module elaboration is unavailable", without.TrimmedError);
        Assert.Empty(downloader.RequestedUrls);

        var with = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "run", link, "--allow-loading");
        Assert.Equal((Success, "42", ""), (with.ExitCode, with.TrimmedOutput, with.Error));
        Assert.Equal(moduleUrl, Assert.Single(downloader.RequestedUrls));
    }

    // ── A program with an unpaired surrogate ────────────────────────────────

    [Theory]
    [InlineData("lone-high")]
    [InlineData("lone-low")]
    [InlineData("lone-reversed-pair")]
    [InlineData("lone-high-at-end")]
    [InlineData("lone-low-at-start")]
    [InlineData("lone-in-program")]
    [InlineData("lone-repeated")]
    [InlineData("lone-mixed-with-pairs")]
    public async Task AProgramWithAnUnpairedSurrogate_IsEvaluatedAsItIs_AndNeitherStreamCarriesOne(string name)
    {
        // source refuses to print such a program, because UTF-8 cannot represent it. run and
        // check do not refuse it: they evaluate the program as it is, as the Playground does.
        var @case = CodeLinkFixtures.Generated(name);
        Assert.False(IsWellFormed(@case.Source));
        var link = LinkPrefix + @case.Payload;

        var (run, downloads) = await InvokeAsync("run", link, "--code-link");
        var (check, _) = await InvokeAsync("check", link);
        // The same code units as an eval argument: the very same program, read another way.
        var (eval, _) = await InvokeAsync("eval", "--code-link", "--", @case.Source);

        AssertSameRun(eval, run, "run");
        Assert.DoesNotContain("cannot print the program", run.Error + check.Error);
        // What ran is the link's program, unpaired surrogate included: its link is this link.
        Assert.Equal("katlang-link: " + link, run.TrimmedError.Split('\n')[^1]);
        Assert.Equal(run.ExitCode, check.ExitCode);
        foreach (var stream in new[] { run.Output, run.Error, check.Output, check.Error })
            Assert.True(IsWellFormed(stream), $"a stream carries an unpaired surrogate: {Show(stream)}");
        Assert.Empty(downloads);
    }

    [Fact]
    public async Task AnUnpairedSurrogate_InAnOutputRow_IsWrittenAsTheReplacementCharacter()
    {
        // A = a lone high surrogate, B = a lone low one, both in strings: a valid program whose
        // two output rows each hold one. Stdout gets U+FFFD in its place, the substitute every
        // UTF-8 encoder writes; nothing is reported, and the exit status is success.
        var @case = CodeLinkFixtures.Generated("lone-in-program");
        Assert.Equal("A = '\uD800'\nB = '\uDC00'\nA, B\n", @case.Source);

        var (result, _) = await InvokeAsync("run", LinkPrefix + @case.Payload);

        Assert.Equal((Success, "\uFFFD\n\uFFFD", ""), (result.ExitCode, result.TrimmedOutput, result.Error));
    }

    [Fact]
    public async Task OnlyAnUnpairedSurrogateIsSubstituted_AWellFormedPairIsKept()
    {
        // Rows of a loop, not of a theory: neither an attribute argument nor serialized theory
        // data can carry an unpaired surrogate.
        (string Source, string ExpectedRow)[] programs =
        [
            ("'a\uD83Db'", "a\uFFFDb"),
            ("'\uDE00'", "\uFFFD"),
            ("'\uD83D\uDE00'", "\uD83D\uDE00"),
            ("'\uD83D\uD83D\uDE00\uDE00'", "\uFFFD\uD83D\uDE00\uFFFD"),
            ("'\uDE00\uD83D'", "\uFFFD\uFFFD"),
            ("'no surrogate at all'", "no surrogate at all"),
        ];

        foreach (var (source, expectedRow) in programs)
        {
            var link = Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(source)).Url;

            var (fromLink, _) = await InvokeAsync("run", link);
            var (fromEval, _) = await InvokeAsync("eval", "--", source);

            Assert.Equal((Success, expectedRow + Environment.NewLine, ""), (fromLink.ExitCode, fromLink.Output, fromLink.Error));
            AssertSameRun(fromEval, fromLink, "run");
            Assert.Equal(expectedRow, CliApplication.WellFormed(source[1..^1]));
        }
    }

    [Fact]
    public void WellFormedText_IsReturnedAsTheSameInstance()
    {
        const string text = "Sveika, pasaule! \uD83D\uDE00 āčē";

        Assert.Same(text, CliApplication.WellFormed(text));
        Assert.Same("", CliApplication.WellFormed(""));
    }

    [Fact]
    public async Task AnUnpairedSurrogate_OutsideAString_IsNamedByItsCodePoint()
    {
        // The program is one lone high surrogate, which is no KatLang token: KatLang's own
        // diagnostic names the code unit, so the message is well-formed text already.
        var @case = CodeLinkFixtures.Generated("lone-high");
        Assert.Equal("\uD800", @case.Source);

        foreach (var command in new[] { "run", "check" })
        {
            var (result, _) = await InvokeAsync(command, LinkPrefix + @case.Payload);

            Assert.Equal((Failure, ""), (result.ExitCode, result.Output));
            Assert.Contains("U+D800 (an unpaired surrogate code unit)", result.Error, StringComparison.Ordinal);
            Assert.All(result.Error, character => Assert.False(char.IsSurrogate(character)));
            Assert.DoesNotContain("unexpected error", result.Error);
        }
    }

    [Fact]
    public async Task AnUnpairedSurrogate_InADiagnostic_IsShownAsAnEscape()
    {
        // The if-condition type mismatch echoes the offending string value verbatim, and the
        // value holds a lone surrogate: the stderr channel shows it as a visible \uXXXX escape,
        // never as the code unit itself.
        const string source = "if('a\uD800b', 1, 2)";
        var link = Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(source)).Url;

        var (result, _) = await InvokeAsync("run", link);
        var (fromEval, _) = await InvokeAsync("eval", "--", source);

        Assert.Equal((Failure, ""), (result.ExitCode, result.Output));
        Assert.EndsWith("'a\\uD800b'", result.TrimmedError, StringComparison.Ordinal);
        Assert.Single(result.TrimmedError.Split('\n'));
        Assert.All(result.Error, character => Assert.False(char.IsSurrogate(character)));
        AssertSameRun(fromEval, result, "run");

        // check parses and elaborates without evaluating: this program has nothing to report.
        var (checkedLink, _) = await InvokeAsync("check", link);
        Assert.Equal((Success, "", ""), (checkedLink.ExitCode, checkedLink.Output, checkedLink.Error));
    }

    // ── The operand ─────────────────────────────────────────────────────────

    public static TheoryData<string[]> LinkArgumentOrders => new()
    {
        new[] { "run", DocumentedLink },
        new[] { "run", "--", DocumentedLink },
        new[] { "--", "run", DocumentedLink },
        new[] { "run", "--random-seed", "5", DocumentedLink },
        new[] { "run", DocumentedLink, "--random-seed", "5" },
        new[] { "--max-decimal-places", "3", "run", DocumentedLink, "--min-decimal-places", "0" },
        new[] { "--allow-loading", "run", DocumentedLink },
        new[] { "run", "--allow-loading", "--", DocumentedLink },
        new[] { "run", DocumentedLink, "--allow-loading" },
    };

    [Theory]
    [MemberData(nameof(LinkArgumentOrders))]
    public async Task ALinkIsAnOperandLikeAnyOther_BeforeOrAfterTheOptions_AndAfterTheTerminator(string[] args)
    {
        var (result, downloads) = await InvokeAsync(args);

        Assert.Equal((Success, "25", ""), (result.ExitCode, result.TrimmedOutput, result.Error));
        Assert.Empty(downloads);
    }

    [Theory]
    [InlineData(new[] { "run", DocumentedLink, DocumentedLink }, "katlang: unexpected argument '" + DocumentedLink + "'.")]
    [InlineData(new[] { "run", DocumentedLink, "--", "--code-link" }, "katlang: unexpected argument '--code-link'.")]
    [InlineData(new[] { "check", DocumentedLink, "--random-seed", "5" }, "katlang: option '--random-seed' is not valid for 'check': check does not evaluate.")]
    [InlineData(new[] { "check", DocumentedLink, "--max-decimal-places", "2" }, "katlang: option '--max-decimal-places' is not valid for 'check': check does not evaluate.")]
    [InlineData(new[] { "run", DocumentedLink, "--min-decimal-places", "5", "--max-decimal-places", "2" }, "katlang: option '--min-decimal-places' must not exceed option '--max-decimal-places'; got 5 and 2.")]
    [InlineData(new[] { "run" }, "katlang: 'run' requires a <file|link> argument.")]
    [InlineData(new[] { "check", "--" }, "katlang: 'check' requires a <file|link> argument.")]
    public async Task TheCommandLineRules_AreUnchangedForALink(string[] args, string expected)
    {
        var (result, downloads) = await InvokeAsync(args);

        Assert.Equal((Failure, ""), (result.ExitCode, result.Output));
        Assert.Equal(expected + "\n" + HelpText.UsageHint, result.TrimmedError);
        Assert.Empty(downloads);
    }

    [Fact]
    public async Task TheOptions_ApplyToALinksProgram_ExactlyAsToAFile()
    {
        const string source = "1 / 3\nMath.RandomInt(1, 1000000)\n";
        var link = Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(source)).Url;
        using var file = new ExactProgramFile(source);
        string[] options = ["--random-seed", "42", "--max-decimal-places", "4", "--min-decimal-places", "2", "--code-link"];

        var (fromLink, _) = await InvokeAsync(["run", link, .. options]);
        var (fromFile, _) = await InvokeAsync(["run", file.Path, .. options]);

        Assert.Equal(Success, fromLink.ExitCode);
        Assert.StartsWith("0.3333\n", fromLink.TrimmedOutput);
        AssertSameRun(fromFile, fromLink, "run");
    }

    [Theory]
    [InlineData("Run", "https://katlang.org/#1/ML4", "CodeLink")]
    [InlineData("Check", "HTTP://example.com/#1/ML4", "CodeLink")]
    [InlineData("Run", "https://example.com/p.kat#", "CodeLink")]
    [InlineData("Run", "https://example.com/p.kat", "ProgramUrl")]
    [InlineData("Check", "HtTpS://example.com/p.kat", "ProgramUrl")]
    [InlineData("Run", "http://example.com/p.kat", "ProgramUrl")]
    [InlineData("Run", "https://", "ProgramUrl")]
    [InlineData("Source", "https://example.com/p.kat", "ProgramUrl")]
    // Everything else is a file path for run and check, whatever it looks like.
    [InlineData("Run", "program.kat", "File")]
    [InlineData("Run", "./https://example.com/p.kat", "File")]
    [InlineData("Run", "https:/example.com/p.kat", "File")]
    [InlineData("Run", "https:example.com", "File")]
    [InlineData("Check", " https://example.com/p.kat", "File")]
    [InlineData("Run", "ftp://example.com/p.kat", "File")]
    [InlineData("Run", "file:///C:/p.kat", "File")]
    [InlineData("Run", "#1/ML4", "File")]
    [InlineData("Run", "katlang.org/#1/ML4", "File")]
    [InlineData("Check", "", "File")]
    // source reads every operand as a link: one with no web address is a code link to refuse.
    [InlineData("Source", "#1/ML4", "CodeLink")]
    [InlineData("Source", "program.kat", "CodeLink")]
    [InlineData("Source", "", "CodeLink")]
    public void TheOperandKind_IsDecidedFromTheOperandAlone(string command, string operand, string expected)
        => Assert.Equal(
            Enum.Parse<ProgramOperandKind>(expected),
            ProgramOperand.Classify(Enum.Parse<CliCommandKind>(command), operand));

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task AnOperandThatIsNoLink_StaysAFilePath_AlsoAfterTheTerminator(string command)
    {
        // A code-link fragment with no web address before it is a link for source only.
        foreach (var operand in new[] { "#1/4MWjDBlNE4PH", "katlang.org/#1/4MWjDBlNE4PH", "ftp://katlang.org/#1/4MWjDBlNE4PH" })
        {
            var (plain, downloads) = await InvokeAsync(command, operand);
            var (afterTerminator, _) = await InvokeAsync(command, "--", operand);

            Assert.Equal((Failure, ""), (plain.ExitCode, plain.Output));
            Assert.StartsWith("katlang: ", plain.Error);
            Assert.DoesNotContain("invalid code link", plain.Error);
            Assert.Contains("file", plain.Error);
            Assert.Equal(plain.Error, afterTerminator.Error);
            Assert.Empty(downloads);
        }
    }

    [Fact]
    public async Task OnPosix_AFileWhosePathStartsLikeALink_StillRunsAsAFile()
    {
        // A directory named "https:" can exist only where ':' is a file-name character. The
        // operand https://<name>/program.kat is a link, by the rule; the same file is still
        // reachable as ./https://<name>/program.kat, which is no link.
        if (OperatingSystem.IsWindows())
            return;

        var name = $"katlang-cli-{Guid.NewGuid():N}";
        var schemeDirectory = Path.Combine(Environment.CurrentDirectory, "https:");
        var createdSchemeDirectory = !Directory.Exists(schemeDirectory);
        var directory = Path.Combine(schemeDirectory, name);
        Directory.CreateDirectory(directory);
        try
        {
            File.WriteAllText(Path.Combine(directory, "program.kat"), "6 * 7\n");

            var (asFile, fileDownloads) = await InvokeAsync("run", $"./https://{name}/program.kat");
            var (asLink, linkDownloads) = await InvokeAsync("run", $"https://{name}/program.kat");

            Assert.Equal((Success, "42", ""), (asFile.ExitCode, asFile.TrimmedOutput, asFile.Error));
            Assert.Empty(fileDownloads);

            // The link form asked the downloader, which serves nothing in this test.
            Assert.Equal($"https://{name}/program.kat", Assert.Single(linkDownloads));
            Assert.Equal((Failure, ""), (asLink.ExitCode, asLink.Output));
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
            if (createdSchemeDirectory && !Directory.EnumerateFileSystemEntries(schemeDirectory).Any())
                Directory.Delete(schemeDirectory);
        }
    }
}

/// <summary>
/// A file that holds exactly <paramref name="program"/> as the CLI reads files: UTF-8, with
/// every line break and character as given. The CLI drops ONE leading byte order mark, so a
/// program that itself starts with U+FEFF is written with one more in front. The program must
/// be well-formed UTF-16: a file cannot hold an unpaired surrogate.
/// </summary>
internal sealed class ExactProgramFile : IDisposable
{
    public ExactProgramFile(string program)
    {
        Path = System.IO.Path.Combine(System.IO.Path.GetTempPath(), $"katlang-cli-{Guid.NewGuid():N}.kat");

        var strict = new UTF8Encoding(encoderShouldEmitUTF8Identifier: false, throwOnInvalidBytes: true);
        using var stream = File.Create(Path);
        if (program.StartsWith('\uFEFF'))
            stream.Write(Encoding.UTF8.GetPreamble());
        stream.Write(strict.GetBytes(program));
    }

    public string Path { get; }

    public void Dispose()
    {
        try
        {
            File.Delete(Path);
        }
        catch (IOException)
        {
            // A leftover temp file is not worth failing a test over.
        }
    }
}
