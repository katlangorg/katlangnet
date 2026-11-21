using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;
using KatLang.Tests.CodeLinks;

namespace KatLang.CLI.Tests;

/// <summary>
/// <c>--code-link</c> through the CLI boundary: after the command's usual output, one last line
/// on stderr with the link to exactly the program the command read — whatever the program does,
/// once the command has its source — and nothing else changed: stdout byte for byte, the exit
/// status, and, without the option, no work at all.
/// </summary>
public sealed class CodeLinkCliTests
{
    private const int Success = 0;
    private const int Failure = 1;
    private const string CodeLinkOption = "--code-link";
    private const string LinkLinePrefix = "katlang-link: https://katlang.org/#1/";

    /// <summary>The line for "1 + 2", whose payload the reference encoder made (fixture case <c>cli-sum</c>).</summary>
    private static string SumLink => LinkLinePrefix + CodeLinkFixtures.Generated("cli-sum").Payload;

    /// <summary>One program for each way a command can end.</summary>
    private static readonly Dictionary<string, string> Programs = new()
    {
        ["rows"] = "1 + 2\n'text', [1, 2]\nSquare(x) = x * x\nSquare(12)\n",
        ["no-output"] = "A = 1\nB = A + 1\n",
        ["empty"] = "",
        ["syntax-error"] = "A = (1, 2\nB = ]\n",
        ["several-diagnostics"] = "1 +\n\"no\"\n2 *\n",
        ["evaluation-error"] = "Value = 10\nValue / 0\n",
        ["display-limit"] = CliApplicationTests.DisplayOverflowSource,
        ["latvian-crlf"] = "# Rēķins\r\nSumma = 12.50\r\nSumma * 2\r\n",
    };

    public static TheoryData<string, string> CommandsAndPrograms
    {
        get
        {
            var data = new TheoryData<string, string>();
            foreach (var command in new[] { "run", "eval", "check" })
            {
                foreach (var program in Programs.Keys)
                    data.Add(command, program);
            }

            return data;
        }
    }

    // ── One last line, and nothing else changes ─────────────────────────────

    [Theory]
    [MemberData(nameof(CommandsAndPrograms))]
    public async Task CodeLink_IsTheLastStderrLine_AfterAnyOutputAndDiagnostics_AndChangesNothingElse(string command, string program)
    {
        var source = Programs[program];
        using var file = new TempSourceFile(source);
        var operand = command == "eval" ? source : file.Path;

        var without = await Cli.InvokeAsync(command, operand);
        var with = await Cli.InvokeAsync(command, operand, CodeLinkOption);

        // stdout byte for byte, the exit status, and stderr up to one more line: the link.
        Assert.Equal(without.ExitCode, with.ExitCode);
        Assert.Equal(without.Output, with.Output);
        Assert.Equal(without.Error + CodeLinkText.Line(source) + Environment.NewLine, with.Error);
    }

    [Fact]
    public async Task CodeLink_OfTheDocumentedExample_IsTheDocumentedLink()
    {
        // The documented example: https://katlang.org/#1/4MWjDBlNE4PH opens
        // 100 - 3 * 5 ^ 2 and shows 25.
        var result = await Cli.InvokeAsync("eval", CodeLinkOption, "100 - 3 * 5 ^ 2");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("25" + Environment.NewLine, result.Output);
        Assert.Equal("katlang-link: https://katlang.org/#1/4MWjDBlNE4PH" + Environment.NewLine, result.Error);
    }

    [Theory]
    [InlineData("lines-lf")]
    [InlineData("lines-lf-final")]
    [InlineData("lines-crlf")]
    [InlineData("lines-cr")]
    [InlineData("lines-mixed")]
    [InlineData("lines-tabs")]
    [InlineData("lines-trailing-spaces")]
    [InlineData("latvian-comment")]
    [InlineData("emoji-in-string")]
    [InlineData("boundary-in-program")]
    public async Task CodeLink_EncodesTheProgramAsWritten_ForEveryCommand(string name)
    {
        var @case = CodeLinkFixtures.Generated(name);
        using var file = new TempSourceFile(@case.Source);
        var expected = LinkLinePrefix + @case.Payload;

        Assert.Equal(expected, LastErrorLine(await Cli.InvokeAsync("eval", @case.Source, CodeLinkOption)));
        Assert.Equal(expected, LastErrorLine(await Cli.InvokeAsync("run", file.Path, CodeLinkOption)));
        Assert.Equal(expected, LastErrorLine(await Cli.InvokeAsync("check", file.Path, CodeLinkOption)));
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task CodeLink_OfACrlfFile_KeepsItsLineBreaks(string command)
    {
        var vector = CodeLinkFixtures.Vector("crlf-line-endings");
        Assert.Equal("A = 1\r\nB = 2\r\nA + B\r\n", vector.Source);
        using var file = new TempSourceFile(vector.Source);

        var result = await Cli.InvokeAsync(command, file.Path, CodeLinkOption);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal(command == "run" ? "3" + Environment.NewLine : "", result.Output);
        Assert.Equal("katlang-link: https://katlang.org/#1/9Sj55xXYp6jJZ2-pb" + Environment.NewLine, result.Error);
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task CodeLink_OfAFileWithAByteOrderMark_LeavesTheMarkOut(string command)
    {
        // The CLI drops ONE leading byte order mark when it reads a file, as file metadata; the
        // link carries the text the command evaluates.
        using var file = new TempByteFile([0xEF, 0xBB, 0xBF, .. Encoding.UTF8.GetBytes("1 + 2")]);

        var result = await Cli.InvokeAsync(command, file.Path, CodeLinkOption);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal(command == "run" ? "3" + Environment.NewLine : "", result.Output);
        Assert.Equal(SumLink + Environment.NewLine, result.Error);
    }

    [Fact]
    public async Task CodeLink_OfAFileWithTwoByteOrderMarks_KeepsTheSecond()
    {
        // Only the first mark is file metadata. The second is program text, and the program the
        // command evaluates, and links, starts with it.
        using var file = new TempByteFile([0xEF, 0xBB, 0xBF, .. Encoding.UTF8.GetBytes("﻿1 + 2")]);

        var result = await Cli.InvokeAsync("run", file.Path, CodeLinkOption);

        Assert.Equal(LinkLinePrefix + CodeLinkFixtures.Generated("cli-sum-after-bom").Payload, LastErrorLine(result));
        Assert.NotEqual(SumLink, LastErrorLine(result));
    }

    // ── Programs that cannot be a code link ─────────────────────────────────

    [Theory]
    [InlineData("eval")]
    [InlineData("run")]
    [InlineData("check")]
    public async Task CodeLink_OfTheEmptyProgram_IsNone(string command)
    {
        var result = await InvokeWithCodeLinkAsync(command, "");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal("katlang-link: none: the program is empty." + Environment.NewLine, result.Error);
    }

    [Theory]
    [InlineData("eval")]
    [InlineData("run")]
    [InlineData("check")]
    public async Task CodeLink_AtTheSourceLimit(string command)
    {
        // A comment line of 20,000 code units, and the same line one code unit longer.
        var atLimit = CodeLinkFixtures.Generated("comment-20000");
        var overLimit = CodeLinkFixtures.Generated("comment-20001");

        var linked = await InvokeWithCodeLinkAsync(command, atLimit.Source);
        var refused = await InvokeWithCodeLinkAsync(command, overLimit.Source);

        Assert.Equal(Success, linked.ExitCode);
        Assert.Equal("", linked.Output);
        Assert.Equal(LinkLinePrefix + atLimit.Payload + Environment.NewLine, linked.Error);

        Assert.Equal(Success, refused.ExitCode);
        Assert.Equal("", refused.Output);
        Assert.Equal(
            "katlang-link: none: the program is 20,001 UTF-16 code units long, more than the 20,000 a code link can carry."
            + Environment.NewLine,
            refused.Error);
    }

    [Theory]
    [InlineData("eval")]
    [InlineData("run")]
    [InlineData("check")]
    public async Task CodeLink_AtThePayloadLimit(string command)
    {
        // Comment lines whose payloads are 1,970 and 1,971 characters long.
        var atLimit = CodeLinkFixtures.Generated("comment-payload-1970");
        var overLimit = CodeLinkFixtures.Generated("comment-payload-1971");

        var linked = await InvokeWithCodeLinkAsync(command, atLimit.Source);
        var refused = await InvokeWithCodeLinkAsync(command, overLimit.Source);

        Assert.Equal(Success, linked.ExitCode);
        Assert.Equal("", linked.Output);
        Assert.Equal(LinkLinePrefix + atLimit.Payload + Environment.NewLine, linked.Error);

        Assert.Equal(Success, refused.ExitCode);
        Assert.Equal("", refused.Output);
        Assert.Equal(
            "katlang-link: none: the program's link payload would be 1,971 characters long, more than the 1,970 a code link can carry."
            + Environment.NewLine,
            refused.Error);
    }

    // ── The option follows the existing option rules ────────────────────────

    public static TheoryData<string[]> OptionPositions => new()
    {
        new[] { "--code-link", "eval", "1 + 2" },
        new[] { "eval", "--code-link", "1 + 2" },
        new[] { "eval", "1 + 2", "--code-link" },
        new[] { "eval", "--code-link", "--", "1 + 2" },
        new[] { "--random-seed", "5", "eval", "1 + 2", "--code-link", "--max-decimal-places", "2" },
        new[] { "--allow-loading", "--code-link", "--min-decimal-places", "0", "eval", "1 + 2" },
    };

    [Theory]
    [MemberData(nameof(OptionPositions))]
    public async Task CodeLink_MayBeWrittenAnywhereBeforeTheTerminator(string[] args)
    {
        var result = await Cli.InvokeAsync(args);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("3" + Environment.NewLine, result.Output);
        Assert.Equal(SumLink + Environment.NewLine, result.Error);
    }

    [Fact]
    public async Task CodeLink_AfterTheTerminator_IsTheSourceText()
    {
        using var file = new TempSourceFile(CodeLinkOption);

        var afterTerminator = await Cli.InvokeAsync("eval", "--", CodeLinkOption);
        var fromFile = await Cli.InvokeAsync("run", file.Path);

        Assert.Equal(fromFile, afterTerminator);
        Assert.DoesNotContain("katlang-link:", afterTerminator.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(new[] { "eval", "1", "--code-link", "--code-link" }, "katlang: option '--code-link' was specified more than once.")]
    [InlineData(new[] { "--code-link", "run", "a.kat", "--code-link" }, "katlang: option '--code-link' was specified more than once.")]
    [InlineData(new[] { "--help", "--code-link" }, "katlang: option '--help' cannot be combined with other arguments.")]
    [InlineData(new[] { "--code-link", "--version" }, "katlang: option '--version' cannot be combined with other arguments.")]
    [InlineData(new[] { "--code-link" }, "katlang: no command specified.")]
    [InlineData(new[] { "eval", "--code-link" }, "katlang: 'eval' requires a <source> argument.")]
    [InlineData(new[] { "check", "a.kat", "extra", "--code-link" }, "katlang: unexpected argument 'extra'.")]
    [InlineData(new[] { "eval", "1", "--code-link=yes" }, "katlang: unknown option '--code-link=yes'.")]
    public async Task UsageErrors_StopTheCommandBeforeThereIsALink(string[] args, string expected)
    {
        var result = await Cli.InvokeAsync(args);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(expected + "\n" + HelpText.UsageHint, result.TrimmedError);
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task FileErrors_StopTheCommandBeforeThereIsALink(string command)
    {
        var missing = await Cli.InvokeAsync(command, TempSourceFile.MissingPath(), CodeLinkOption);
        var directory = await Cli.InvokeAsync(command, Path.TrimEndingDirectorySeparator(Path.GetTempPath()), CodeLinkOption);

        Assert.Equal(Failure, missing.ExitCode);
        Assert.Equal("", missing.Output);
        Assert.Contains("file not found", missing.TrimmedError, StringComparison.Ordinal);
        Assert.DoesNotContain("katlang-link:", missing.Error, StringComparison.Ordinal);

        Assert.Equal(Failure, directory.ExitCode);
        Assert.Equal("", directory.Output);
        Assert.Contains("cannot read file", directory.TrimmedError, StringComparison.Ordinal);
        Assert.DoesNotContain("katlang-link:", directory.Error, StringComparison.Ordinal);
    }

    // ── Whatever happens once the command has its source ────────────────────

    [Fact]
    public async Task Cancellation_AfterTheSourceIsObtained_StillEndsWithTheLink()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var output = new StringWriter();
        var error = new StringWriter();

        var exitCode = await CliApplication.RunAsync(
            ["eval", "1 + 2", CodeLinkOption], output, error, cancellationToken: cancellation.Token);

        Assert.Equal(Failure, exitCode);
        Assert.Equal("", output.ToString());
        Assert.Equal("katlang: cancelled." + Environment.NewLine + SumLink + Environment.NewLine, error.ToString());
    }

    [Fact]
    public async Task Cancellation_BeforeTheFileIsRead_LeavesNoLink()
    {
        using var file = new TempSourceFile("1 + 2");
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var error = new StringWriter();

        var exitCode = await CliApplication.RunAsync(
            ["run", file.Path, CodeLinkOption], new StringWriter(), error, cancellationToken: cancellation.Token);

        Assert.Equal(Failure, exitCode);
        Assert.Equal("katlang: cancelled." + Environment.NewLine, error.ToString());
    }

    [Fact]
    public async Task UnexpectedError_IsReported_ThenTheLink()
    {
        var error = new StringWriter();

        var exitCode = await CliApplication.RunAsync(
            ["eval", "1 + 2", CodeLinkOption], new FailingWriter(new IOException("the pipe is closed")), error);

        Assert.Equal(Failure, exitCode);
        Assert.Equal(
            "katlang: unexpected error: the pipe is closed" + Environment.NewLine + SumLink + Environment.NewLine,
            error.ToString());
    }

    [Fact]
    public async Task Stdout_IsFlushedBeforeTheLink_AndOnlyWithTheOption()
    {
        var withOption = new List<string>();
        await CliApplication.RunAsync(
            ["eval", "1 + 2", CodeLinkOption], new LoggingWriter(withOption, "stdout"), new LoggingWriter(withOption, "stderr"));

        var withoutOption = new List<string>();
        await CliApplication.RunAsync(
            ["eval", "1 + 2"], new LoggingWriter(withoutOption, "stdout"), new LoggingWriter(withoutOption, "stderr"));

        Assert.Equal(["stdout: 3", "stdout: flush", "stderr: " + SumLink], withOption);
        Assert.Equal(["stdout: 3"], withoutOption);
    }

    // ── Help ────────────────────────────────────────────────────────────────

    [Fact]
    public async Task Help_DocumentsTheCodeLinkOption()
    {
        var result = await Cli.InvokeAsync("--help");
        var help = result.TrimmedOutput;
        var prose = Regex.Replace(help, @"\s+", " ");

        Assert.Equal(Success, result.ExitCode);

        // Every command takes it.
        Assert.Contains("                     [--max-decimal-places <integer>] [--code-link]\n", help);
        Assert.Contains("                        [--max-decimal-places <integer>] [--code-link]\n", help);
        Assert.Contains("  katlang check <file> [--allow-loading] [--code-link]\n", help + "\n");
        Assert.Equal(3, help.Split("[--code-link]").Length - 1);

        // What it writes, where, when, and the limits, which are the encoder's own.
        Assert.Contains("\n  --code-link        After the command's output and diagnostics, write\n", help);
        Assert.Contains("\n                       katlang-link: https://katlang.org/#1/<payload>\n", help);
        Assert.Contains("\n                       katlang-link: none: <reason>\n", help);
        Assert.Contains(
            string.Create(
                CultureInfo.InvariantCulture,
                $"A program that is empty, longer than {CodeLink.MaxSourceLength:N0} UTF-16 code units, or whose payload would be longer than {CodeLink.MaxPayloadLength:N0} characters has no link"),
            prose);
        Assert.Contains("The line is written whatever the program does, once its source has been read; stdout and the exit status are unchanged.", prose);
        Assert.Contains("anyone who has it can read the program.", prose);

        Assert.All(help.Split('\n'), line => Assert.True(line.Length <= 80, $"help line exceeds 80 columns: '{line}'"));
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static async Task<CliResult> InvokeWithCodeLinkAsync(string command, string source)
    {
        if (command == "eval")
            return await Cli.InvokeAsync("eval", source, CodeLinkOption);

        using var file = new TempSourceFile(source);
        return await Cli.InvokeAsync(command, file.Path, CodeLinkOption);
    }

    private static string LastErrorLine(CliResult result) => result.TrimmedError.Split('\n')[^1];

    /// <summary>A throwaway file with exact bytes, for byte order marks.</summary>
    private sealed class TempByteFile : IDisposable
    {
        public TempByteFile(byte[] content)
        {
            Path = System.IO.Path.Combine(System.IO.Path.GetTempPath(), $"katlang-cli-{Guid.NewGuid():N}.kat");
            File.WriteAllBytes(Path, content);
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

    /// <summary>Program output that cannot be written: every line throws.</summary>
    private sealed class FailingWriter(Exception exception) : StringWriter
    {
        public override void WriteLine(string? value) => throw exception;
    }

    /// <summary>Records each line written and each flush, in order, across both streams.</summary>
    private sealed class LoggingWriter(List<string> log, string stream) : StringWriter
    {
        public override void WriteLine(string? value)
        {
            log.Add($"{stream}: {value}");
            base.WriteLine(value);
        }

        public override void Flush()
        {
            log.Add($"{stream}: flush");
            base.Flush();
        }
    }
}
