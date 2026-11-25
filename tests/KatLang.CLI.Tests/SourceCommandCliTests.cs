using System.Text;
using System.Text.RegularExpressions;
using KatLang.Tests.CodeLinks;

namespace KatLang.CLI.Tests;

/// <summary>
/// <c>katlang source &lt;link&gt;</c> through the CLI boundary: the program a code link carries,
/// written to stdout exactly — no newline added, control characters raw — and nothing run. A
/// link that carries no program is one fixed line on stderr and exit status 1, with stdout
/// empty and no usage hint; the command takes one operand and no option. (A link with no
/// <c>#</c> is a program URL, which <c>source</c> downloads: <see cref="ProgramUrlCliTests"/>.)
/// </summary>
public sealed class SourceCommandCliTests
{
    private const int Success = 0;
    private const int Failure = 1;
    private const string LinkPrefix = "https://katlang.org/#1/";

    /// <summary>The documented link: it opens <c>100 - 3 * 5 ^ 2</c>.</summary>
    private const string DocumentedLink = LinkPrefix + "4MWjDBlNE4PH";

    private const string DocumentedSource = "100 - 3 * 5 ^ 2";

    private const string NotValidForSource = "is not valid for 'source': source reads a link and runs nothing.";

    private static string LinkOf(string fixtureCase) => LinkPrefix + CodeLinkFixtures.Generated(fixtureCase).Payload;

    // ── The program, exactly ────────────────────────────────────────────────

    [Fact]
    public async Task Source_OfTheDocumentedLink_IsTheDocumentedProgram()
    {
        var result = await Cli.InvokeAsync("source", DocumentedLink);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal(DocumentedSource, result.Output);
        Assert.Equal("", result.Error);
    }

    [Theory]
    [InlineData("lines-lf")]
    [InlineData("lines-lf-final")]
    [InlineData("lines-crlf")]
    [InlineData("lines-crlf-final")]
    [InlineData("lines-cr")]
    [InlineData("lines-mixed")]
    [InlineData("lines-double-final")]
    [InlineData("lines-leading-blank")]
    [InlineData("lines-tabs")]
    [InlineData("lines-trailing-spaces")]
    [InlineData("lines-unicode-separators")]
    [InlineData("whitespace-space")]
    [InlineData("whitespace-lf")]
    [InlineData("whitespace-crlf")]
    [InlineData("latvian-comment")]
    [InlineData("emoji-in-string")]
    [InlineData("boundary-in-program")]
    [InlineData("program-parse-error")]
    [InlineData("program-error")]
    public async Task Source_WritesTheProgramExactly_WithNoNewlineAdded(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        var result = await Cli.InvokeAsync("source", LinkPrefix + @case.Payload);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal(@case.Source, result.Output);
        Assert.Equal("", result.Error);
    }

    [Theory]
    [InlineData("controls-all")]
    [InlineData("controls-in-program")]
    [InlineData("single-nul")]
    [InlineData("bidi-controls")]
    [InlineData("zero-width")]
    [InlineData("lines-bom-inside")]
    public async Task Source_WritesControlCharactersRaw(string name)
    {
        // stdout carries the program itself, like program output, outside the stderr policy
        // that escapes control characters: what the link carries is what is written.
        var @case = CodeLinkFixtures.Generated(name);
        Assert.Contains(@case.Source, character => char.IsControl(character) || character is '‮' or '​' or '﻿');

        var result = await Cli.InvokeAsync("source", LinkPrefix + @case.Payload);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal(@case.Source, result.Output);
        Assert.Equal("", result.Error);
    }

    [Fact]
    public async Task Source_OfEveryFixtureLink_IsItsProgram_OrTheSurrogateRefusal()
    {
        var printed = 0;
        var refused = 0;
        foreach (var @case in CodeLinkFixtures.GeneratedCases.Where(@case => @case.Status == "ok"))
        {
            var result = await Cli.InvokeAsync("source", LinkPrefix + @case.Payload);
            if (IsWellFormed(@case.Source))
            {
                Assert.Equal((Success, @case.Source, ""), (result.ExitCode, result.Output, result.Error));
                printed++;
            }
            else
            {
                Assert.Equal((Failure, "", UnpairedSurrogateLine + Environment.NewLine), (result.ExitCode, result.Output, result.Error));
                refused++;
            }
        }

        Assert.True(printed >= 690, $"{printed} programs were printed");
        Assert.True(refused >= 8, $"{refused} programs have an unpaired surrogate");
    }

    [Theory]
    [InlineData("tutorial-001")]
    [InlineData("lines-crlf-final")]
    [InlineData("lines-mixed")]
    [InlineData("lines-tabs")]
    [InlineData("latvian-crlf")]
    [InlineData("emoji-crlf")]
    [InlineData("chinese")]
    [InlineData("controls-in-program")]
    [InlineData("boundary-every-latin1")]
    [InlineData("supplementary-max")]
    [InlineData("comment-20000")]
    [InlineData("comment-payload-1970")]
    public async Task Source_RedirectedToAFile_IsTheProgramByteForByteAsUtf8_AndLinksBackToItself(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);
        var link = LinkPrefix + @case.Payload;
        var path = Path.Combine(Path.GetTempPath(), $"katlang-cli-{Guid.NewGuid():N}.kat");
        try
        {
            // What the shell's redirection gives the CLI: a UTF-8 stream with no byte order mark
            // (Program.cs sets the console's output encoding to UTF-8).
            int exitCode;
            await using (var stdout = new StreamWriter(File.Create(path), new UTF8Encoding(encoderShouldEmitUTF8Identifier: false)))
                exitCode = await CliApplication.RunAsync(["source", link], stdout, new StringWriter());

            Assert.Equal(Success, exitCode);
            Assert.Equal(Encoding.UTF8.GetBytes(@case.Source), await File.ReadAllBytesAsync(path));

            // And the file is the same program to the CLI: its link is the link it came from.
            var check = await Cli.InvokeAsync("check", path, "--code-link");
            Assert.Equal("katlang-link: " + link, check.TrimmedError.Split('\n')[^1]);
        }
        finally
        {
            File.Delete(path);
        }
    }

    [Fact]
    public async Task Source_WritesOnce_WithNoLineAndNoFlushOfItsOwn_AndNothingToStderr()
    {
        var log = new List<string>();

        var exitCode = await CliApplication.RunAsync(
            ["source", DocumentedLink], new LoggingWriter(log, "stdout"), new LoggingWriter(log, "stderr"));

        Assert.Equal(Success, exitCode);
        Assert.Equal(["stdout write: " + DocumentedSource], log);
    }

    [Fact]
    public async Task Source_RunsNothing_AndLoadsNothing()
    {
        // A program that would fail, one that would never end, and one that would load a
        // module: each is only text here.
        var downloader = new RecordingDownloader();
        string[] programs =
        [
            "1 / 0",
            "A = (1, 2\nB = ]",
            "Loop(n) = n + 1, true\nLoop(0).while",
            "Lib = load('https://katlang.org/lib.kat')\nLib.Value",
            "\"not KatLang\" {{{",
        ];

        foreach (var program in programs)
        {
            var link = Assert.IsType<CodeLinkEncoding.Link>(CodeLink.Encode(program)).Url;

            var result = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "source", link);

            Assert.Equal((Success, program, ""), (result.ExitCode, result.Output, result.Error));
        }

        Assert.Empty(downloader.RequestedUrls);
    }

    [Fact]
    public async Task Source_ReadsOnlyTheFragment_WhateverTheOriginPathAndQuery()
    {
        var payload = DocumentedLink[LinkPrefix.Length..];
        string[] links =
        [
            "http://localhost:5218/#1/" + payload,
            "https://katlang.org/examples#1/" + payload,
            "https://katlang.org/?utm_source=chat#1/" + payload,
            "#1/" + payload,
        ];

        foreach (var link in links)
        {
            var result = await Cli.InvokeAsync("source", link);
            Assert.Equal((Success, DocumentedSource, ""), (result.ExitCode, result.Output, result.Error));
        }
    }

    [Fact]
    public async Task Source_TakesTheLinkExactlyAsGiven_WithNothingTrimmedOrDecoded()
    {
        // A space after the payload is part of it, not trimmed away, and no payload character
        // ever needs percent-encoding, so an escape is a character code links do not use.
        var payload = DocumentedLink[LinkPrefix.Length..];
        string[] links = [DocumentedLink + " ", DocumentedLink + "\t", LinkPrefix + payload[..3] + "%" + ((int)payload[3]).ToString("X2", System.Globalization.CultureInfo.InvariantCulture) + payload[4..]];

        foreach (var link in links)
        {
            var result = await Cli.InvokeAsync("source", link);
            Assert.Equal(Failure, result.ExitCode);
            Assert.Equal("", result.Output);
            Assert.Equal(InvalidLinkLine(CodeLinkRefusal.InvalidCharacter) + Environment.NewLine, result.Error);
        }
    }

    // ── A program UTF-8 cannot represent ────────────────────────────────────

    [Theory]
    [InlineData("lone-high")]
    [InlineData("lone-low")]
    [InlineData("lone-reversed-pair")]
    [InlineData("lone-high-at-end")]
    [InlineData("lone-low-at-start")]
    [InlineData("lone-in-program")]
    [InlineData("lone-repeated")]
    [InlineData("lone-mixed-with-pairs")]
    public async Task Source_OfAProgramWithAnUnpairedSurrogate_IsRefused(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);
        Assert.False(IsWellFormed(@case.Source));

        var result = await Cli.InvokeAsync("source", LinkPrefix + @case.Payload);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(
            "katlang: cannot print the program: it contains an unpaired surrogate, which UTF-8 cannot represent."
            + Environment.NewLine,
            result.Error);
    }

    [Theory]
    [InlineData("emoji-single")]
    [InlineData("emoji-zwj-family")]
    [InlineData("supplementary-run")]
    [InlineData("supplementary-max")]
    [InlineData("boundary-high-bmp")]
    public async Task Source_PrintsWellFormedTextAtUnicodeBoundaries(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);

        var result = await Cli.InvokeAsync("source", LinkPrefix + @case.Payload);

        Assert.Equal((Success, @case.Source, ""), (result.ExitCode, result.Output, result.Error));
    }

    // ── A link that carries no program ──────────────────────────────────────

    public static TheoryData<string, string> InvalidLinks => new()
    {
        // A web link with a # is read as a code link, never downloaded, whatever follows the #.
        { "https://katlang.org/#", "katlang: invalid code link: it has no #<format>/<payload> fragment." },
        { "https://katlang.org/a/019ead4b-d41d-7564-ba11-c177f917a0fe#top", "katlang: invalid code link: it has no #<format>/<payload> fragment." },
        { "https://example.com/program.kat#L10", "katlang: invalid code link: it has no #<format>/<payload> fragment." },
        // An operand that is no web link at all is no program URL either.
        { "4MWjDBlNE4PH", "katlang: invalid code link: it has no #<format>/<payload> fragment." },
        { "katlang.org/api/a/019ead4b-d41d-7564-ba11-c177f917a0fe", "katlang: invalid code link: it has no #<format>/<payload> fragment." },
        { "ftp://katlang.org/program.kat", "katlang: invalid code link: it has no #<format>/<payload> fragment." },
        { "program.kat", "katlang: invalid code link: it has no #<format>/<payload> fragment." },
        { "https://katlang.org/#01/4MWjDBlNE4PH", "katlang: invalid code link: it has no #<format>/<payload> fragment." },
        { "", "katlang: invalid code link: it has no #<format>/<payload> fragment." },
        { "https://katlang.org/#code/IwBhAIFpwZnAqcBWcA9cAmIA", "katlang: invalid code link: it has no #<format>/<payload> fragment." },
        { "https://katlang.org/#c1/4MWjDBlNE4PH", "katlang: invalid code link: it has no #<format>/<payload> fragment." },
        { "https://katlang.org/#1/", "katlang: invalid code link: its payload is empty." },
        { DocumentedLink + "%", "katlang: invalid code link: its payload has a character that code links do not use." },
        { "https://katlang.org/#1/4MWjDBl#NE4PH", "katlang: invalid code link: its payload has a character that code links do not use." },
        { DocumentedLink + "?x=1", "katlang: invalid code link: its payload has a character that code links do not use." },
        { DocumentedLink + "\n", "katlang: invalid code link: its payload has a character that code links do not use." },
        { "https://katlang.org/#2/4MWjDBlNE4PH", "katlang: invalid code link: its format is not one this KatLang reads; a newer KatLang may read it." },
        { "https://katlang.org/#1/4MWjDBlNE4P", "katlang: invalid code link: its payload is damaged or cut short." },
        { "https://katlang.org/#1/A", "katlang: invalid code link: its payload is damaged or cut short." },
        { DocumentedLink + "A", "katlang: invalid code link: its payload does not re-encode to itself, so it was changed." },
    };

    [Theory]
    [MemberData(nameof(InvalidLinks))]
    public async Task Source_OfAnInvalidLink_IsOneLineOnStderr_AndNothingOnStdout(string link, string expected)
    {
        // None of these is downloaded: the downloader is never asked.
        var downloader = new RecordingDownloader();

        var result = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "source", "--", link);

        // The command line was valid: no usage hint follows.
        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(expected + Environment.NewLine, result.Error);
        Assert.Empty(downloader.RequestedUrls);
    }

    [Fact]
    public async Task Source_OfALinkOverALimit_SaysWhichLimit()
    {
        var payloadTooLong = await Cli.InvokeAsync("source", LinkPrefix + CodeLinkFixtures.Generated("payload-1971").Payload);
        // No encoder makes a link for a program over the source limit; this payload of 20,001
        // "a" was made with the format's reference implementation (the decoder oracle's
        // crafted-20001-a).
        var sourceTooLong = await Cli.InvokeAsync("source", LinkPrefix + "__2O8I9GolghMVOv6xtq6e");
        var atPayloadLimit = await Cli.InvokeAsync("source", LinkOf("payload-1970"));

        Assert.Equal((Failure, ""), (payloadTooLong.ExitCode, payloadTooLong.Output));
        Assert.Equal("katlang: invalid code link: its payload is longer than 1,970 characters." + Environment.NewLine, payloadTooLong.Error);

        Assert.Equal((Failure, ""), (sourceTooLong.ExitCode, sourceTooLong.Output));
        Assert.Equal("katlang: invalid code link: its program is longer than 20,000 UTF-16 code units." + Environment.NewLine, sourceTooLong.Error);

        Assert.Equal((Success, CodeLinkFixtures.Generated("payload-1970").Source, ""), (atPayloadLimit.ExitCode, atPayloadLimit.Output, atPayloadLimit.Error));
        var atSourceLimit = await Cli.InvokeAsync("source", LinkOf("source-20000"));
        Assert.Equal((Success, CodeLinkFixtures.Generated("source-20000").Source, ""), (atSourceLimit.ExitCode, atSourceLimit.Output, atSourceLimit.Error));
    }

    [Fact]
    public async Task Source_HasOneLineForEveryRefusal_AndNeverEchoesTheLink()
    {
        // The reasons are fixed text: nothing of the link, which may hold anything, reaches
        // the terminal.
        var hostile = "\u001b[31m‮#1/\u001b]0;title\u0007\r\nkatlang: forged line";

        var result = await Cli.InvokeAsync("source", hostile);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(InvalidLinkLine(CodeLinkRefusal.InvalidCharacter) + Environment.NewLine, result.Error);

        foreach (var reason in Enum.GetValues<CodeLinkRefusal>())
            Assert.All(InvalidLinkLine(reason), character => Assert.InRange(character, ' ', '~'));
    }

    [Fact]
    public async Task Source_WhenStdoutFails_ReportsTheError()
    {
        var error = new StringWriter();

        var exitCode = await CliApplication.RunAsync(
            ["source", DocumentedLink], new FailingWriter(new IOException("the pipe is closed")), error);

        Assert.Equal(Failure, exitCode);
        Assert.Equal("katlang: unexpected error: the pipe is closed" + Environment.NewLine, error.ToString());
    }

    // ── The command line ────────────────────────────────────────────────────

    [Theory]
    [InlineData(new[] { "source" }, "katlang: 'source' requires a <link> argument.")]
    [InlineData(new[] { "source", "--" }, "katlang: 'source' requires a <link> argument.")]
    [InlineData(new[] { "source", DocumentedLink, "extra" }, "katlang: unexpected argument 'extra'.")]
    [InlineData(new[] { "source", DocumentedLink, DocumentedLink }, "katlang: unexpected argument '" + DocumentedLink + "'.")]
    [InlineData(new[] { "source", DocumentedLink, "--raw" }, "katlang: unknown option '--raw'.")]
    [InlineData(new[] { "--help", "source", DocumentedLink }, "katlang: option '--help' cannot be combined with other arguments.")]
    [InlineData(new[] { "source", "--version" }, "katlang: option '--version' cannot be combined with other arguments.")]
    [InlineData(new[] { "sources", DocumentedLink }, "katlang: unknown command 'sources'.")]
    [InlineData(new[] { "Source", DocumentedLink }, "katlang: unknown command 'Source'.")]
    public async Task UsageErrors_AreReportedWithTheUsageHint(string[] args, string expected)
    {
        var result = await Cli.InvokeAsync(args);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(expected + "\n" + HelpText.UsageHint, result.TrimmedError);
    }

    public static TheoryData<string[], string> RefusedOptions => new()
    {
        // Every command option, in every position an option may be written.
        { new[] { "source", DocumentedLink, "--allow-loading" }, "--allow-loading" },
        { new[] { "--allow-loading", "source", DocumentedLink }, "--allow-loading" },
        { new[] { "source", "--random-seed", "5", DocumentedLink }, "--random-seed" },
        { new[] { "source", DocumentedLink, "--random-seed", "-5" }, "--random-seed" },
        { new[] { "source", DocumentedLink, "--min-decimal-places", "2" }, "--min-decimal-places" },
        { new[] { "--min-decimal-places", "0", "source", DocumentedLink }, "--min-decimal-places" },
        { new[] { "source", DocumentedLink, "--max-decimal-places", "2" }, "--max-decimal-places" },
        { new[] { "source", "--max-decimal-places", "99", "--", DocumentedLink }, "--max-decimal-places" },
        { new[] { "source", DocumentedLink, "--code-link" }, "--code-link" },
        { new[] { "--code-link", "source", DocumentedLink }, "--code-link" },
        { new[] { "source", "--code-link", "--", DocumentedLink }, "--code-link" },
        // Several: the first in the order allow-loading, random-seed, min, max, code-link,
        // whatever order they were written in.
        { new[] { "source", DocumentedLink, "--code-link", "--max-decimal-places", "2", "--min-decimal-places", "1", "--random-seed", "5", "--allow-loading" }, "--allow-loading" },
        { new[] { "source", DocumentedLink, "--code-link", "--max-decimal-places", "2", "--min-decimal-places", "1", "--random-seed", "5" }, "--random-seed" },
        { new[] { "source", DocumentedLink, "--code-link", "--max-decimal-places", "2", "--min-decimal-places", "1" }, "--min-decimal-places" },
        { new[] { "source", DocumentedLink, "--code-link", "--max-decimal-places", "2" }, "--max-decimal-places" },
        // A minimum above the maximum is not reached: the options are refused first.
        { new[] { "source", DocumentedLink, "--min-decimal-places", "5", "--max-decimal-places", "2" }, "--min-decimal-places" },
    };

    [Theory]
    [MemberData(nameof(RefusedOptions))]
    public async Task EveryCommandOption_IsRefusedForSource(string[] args, string option)
    {
        var result = await Cli.InvokeAsync(args);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal($"katlang: option '{option}' {NotValidForSource}\n{HelpText.UsageHint}", result.TrimmedError);
    }

    [Fact]
    public async Task TheRefusal_IsTheEstablishedWording()
    {
        var result = await Cli.InvokeAsync("source", DocumentedLink, "--code-link");

        Assert.Equal(
            "katlang: option '--code-link' is not valid for 'source': source reads a link and runs nothing.\n"
            + "Run 'katlang --help' for usage.",
            result.TrimmedError);
    }

    [Theory]
    [InlineData(new[] { "source", DocumentedLink, "--random-seed", "x" }, "katlang: option '--random-seed' requires an integer between -9223372036854775808 and 9223372036854775807; got 'x'.")]
    [InlineData(new[] { "source", DocumentedLink, "--random-seed" }, "katlang: option '--random-seed' requires a value.")]
    [InlineData(new[] { "source", DocumentedLink, "--max-decimal-places", "100" }, "katlang: option '--max-decimal-places' requires an integer between 0 and 99; got '100'.")]
    [InlineData(new[] { "source", DocumentedLink, "--code-link", "--code-link" }, "katlang: option '--code-link' was specified more than once.")]
    public async Task TheExistingOptionRules_ApplyBeforeTheRefusal(string[] args, string expected)
    {
        // A value is validated where it appears, before the command it applies to is known,
        // and a repeated option is reported where it repeats.
        var result = await Cli.InvokeAsync(args);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(expected + "\n" + HelpText.UsageHint, result.TrimmedError);
    }

    [Fact]
    public async Task TheTerminator_MakesEveryLaterArgumentTheLink()
    {
        var afterTerminator = await Cli.InvokeAsync("source", "--", DocumentedLink);
        Assert.Equal((Success, DocumentedSource, ""), (afterTerminator.ExitCode, afterTerminator.Output, afterTerminator.Error));

        // An option spelling after the terminator is the link, and no link at all.
        var optionAsLink = await Cli.InvokeAsync("source", "--", "--code-link");
        Assert.Equal(Failure, optionAsLink.ExitCode);
        Assert.Equal("", optionAsLink.Output);
        Assert.Equal(InvalidLinkLine(CodeLinkRefusal.NotACodeLink) + Environment.NewLine, optionAsLink.Error);
    }

    [Fact]
    public void TheOtherCommands_AcceptTheLiteralOperandSource()
    {
        // Use the exact operand for both a filename and an expression without changing the
        // test process's working directory to supply a file named "source".
        foreach (var (command, kind) in new[] { ("run", CliCommandKind.Run), ("check", CliCommandKind.Check), ("eval", CliCommandKind.Eval) })
        {
            var parsed = CommandLine.Parse([command, "source"]);
            Assert.Null(parsed.Error);
            Assert.Equal(new CliInvocation(kind, "source", default), parsed.Invocation);
        }
    }

    // ── Help and documentation ──────────────────────────────────────────────

    [Fact]
    public async Task Help_DocumentsTheSourceCommand()
    {
        var result = await Cli.InvokeAsync("--help");
        var help = result.TrimmedOutput;
        var prose = Regex.Replace(help, @"\s+", " ");

        Assert.Equal(Success, result.ExitCode);

        // Its usage line, after the three commands that take a program, with no option.
        Assert.Contains("  katlang check <file|link> [--allow-loading] [--code-link]\n  katlang source <link>\n\nOptions:\n", help);

        // What it writes and where, exactly; what it refuses and how.
        Assert.Contains("\n  source <link>      Write the program of a link of either kind to\n", help);
        Assert.Contains("Write the program of a link of either kind to stdout, and run nothing.", prose);
        Assert.Contains("exactly as it was read: no line break is added and control characters are written raw", prose);
        Assert.Contains("redirecting stdout reproduces the program byte for byte as UTF-8 (katlang source \"<link>\" > program.kat).", prose);
        Assert.Contains("fails with exit status 1 and one line on stderr:", prose);
        Assert.Contains("\n                       katlang: invalid code link: <reason>\n", help);
        Assert.Contains("If the program contains an unpaired surrogate, source reports that UTF-8 cannot represent it and exits with status 1.", prose);
        Assert.Contains("source takes no options.", prose);

        // The terminator's entry names the link too.
        Assert.Contains("End of options: every later argument is a file, source or link, even one that begins with two dashes", prose);

        Assert.All(help.Split('\n'), line => Assert.True(line.Length <= 80, $"help line exceeds 80 columns: '{line}'"));
    }

    [Fact]
    public void CliGuide_DocumentsTheSourceCommandAndItsExactLines()
    {
        var guide = File.ReadAllText(RepositoryFile("docs/cli.md"));

        Assert.Contains("katlang source \"<link>\" > program.kat", guide, StringComparison.Ordinal);
        Assert.Contains("katlang: invalid code link: <reason>", guide, StringComparison.Ordinal);
        Assert.Contains(UnpairedSurrogateLine, guide, StringComparison.Ordinal);
        foreach (var reason in Enum.GetValues<CodeLinkRefusal>())
            Assert.Contains(CodeLinkText.RefusalReason(reason), guide, StringComparison.Ordinal);
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private const string UnpairedSurrogateLine =
        "katlang: cannot print the program: it contains an unpaired surrogate, which UTF-8 cannot represent.";

    private static string InvalidLinkLine(CodeLinkRefusal reason)
        => "katlang: invalid code link: " + CodeLinkText.RefusalReason(reason);

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

    private static string RepositoryFile(string relativePath)
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "KatLang.slnx")))
            directory = directory.Parent;
        Assert.NotNull(directory);

        return Path.Combine(directory.FullName, relativePath);
    }

    /// <summary>Program output that cannot be written: every write throws.</summary>
    private sealed class FailingWriter(Exception exception) : StringWriter
    {
        public override void Write(string? value) => throw exception;

        public override void WriteLine(string? value) => throw exception;
    }

    /// <summary>Records each write, line and flush, in order, across both streams.</summary>
    private sealed class LoggingWriter(List<string> log, string stream) : StringWriter
    {
        public override void Write(string? value)
        {
            log.Add($"{stream} write: {value}");
            base.Write(value);
        }

        public override void WriteLine(string? value)
        {
            log.Add($"{stream} line: {value}");
            base.WriteLine(value);
        }

        public override void Flush()
        {
            log.Add($"{stream} flush");
            base.Flush();
        }
    }
}
