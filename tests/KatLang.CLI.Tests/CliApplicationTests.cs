using System.Globalization;
using System.Reflection;
using System.Text;

namespace KatLang.CLI.Tests;

/// <summary>
/// Behavioral coverage for the v1 CLI contract, driven through the CLI boundary
/// (<see cref="CliApplication.RunAsync"/>): argument array in, exit code and the
/// two output streams out.
/// </summary>
public sealed class CliApplicationTests
{
    private const int Success = 0;
    private const int Failure = 1;

    // ── Help and version ────────────────────────────────────────────────────

    [Fact]
    public async Task Help_PrintsTheContractUsage_OnStdout()
    {
        var result = await Cli.InvokeAsync("--help");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Error);
        Assert.Contains("Usage:", result.TrimmedOutput);
        Assert.Contains("katlang run <file> [--allow-loading]", result.TrimmedOutput);
        Assert.Contains("katlang eval <source> [--allow-loading]", result.TrimmedOutput);
        Assert.Contains("katlang check <file> [--allow-loading]", result.TrimmedOutput);
        Assert.Contains("--allow-loading", result.TrimmedOutput);
        Assert.Contains("Disabled by default.", result.TrimmedOutput);
        // The help names the hosts KatLang's default allow-list actually admits (the CLI
        // configures none of its own).
        Assert.Contains("katlang.org and its subdomains only", result.TrimmedOutput);
        // The transport bounds the help quotes must be the ones actually enforced.
        Assert.Contains($"{HttpSourceDownloader.DownloadTimeout.TotalSeconds:0} seconds", result.TrimmedOutput);
        Assert.Contains($"1 MiB ({HttpSourceDownloader.MaxResponseBodyBytes.ToString("N0", System.Globalization.CultureInfo.InvariantCulture)} content", result.TrimmedOutput);
        Assert.Contains("bytes), excluding HTTP headers and chunk framing.", result.TrimmedOutput);
        Assert.Contains("--version", result.TrimmedOutput);
        Assert.Contains("--help", result.TrimmedOutput);
        // The options terminator the parser implements is part of the documented contract.
        Assert.Contains("--                 End of options", result.TrimmedOutput);
        Assert.Contains("katlang eval -- \"--1\"", result.TrimmedOutput);
    }

    [Fact]
    public void Readme_ReportsTheShippedTransportBounds()
    {
        var readme = File.ReadAllText(RepositoryFile("README.md"));
        Assert.Contains($"1 MiB ({HttpSourceDownloader.MaxResponseBodyBytes.ToString("N0", System.Globalization.CultureInfo.InvariantCulture)} content bytes)", readme);
        Assert.Contains($"{HttpSourceDownloader.DownloadTimeout.TotalSeconds:0}-second cancellation deadline", readme);
    }

    /// <summary>
    /// The random-seed option has ONE spelling. The pre-release <c>--seed</c> was removed without
    /// an alias, so a maintained document, generator guidance, or the release smoke naming it would
    /// teach an option the CLI rejects. The negative tests of this project name it on purpose and
    /// are not scanned.
    /// </summary>
    [Theory]
    [InlineData("README.md")]
    [InlineData("tutorial.md")]
    [InlineData("AGENTS.md")]
    [InlineData(".github/agents/katlang-generator.agent.md")]
    [InlineData("experimental/prompts/katlang-generator.txt")]
    [InlineData(".github/workflows/release.yml")]
    [InlineData("docs/design/seeded-randomness-2026-09.md")]
    [InlineData("docs/design/language-rules/evaluator-and-hosting.md")]
    [InlineData("src/KatLang/SEMANTIC-ALIGNMENT.md")]
    public void MaintainedDocs_NeverNameTheRemovedSeedSpelling(string relativePath)
    {
        var text = File.ReadAllText(RepositoryFile(relativePath));

        Assert.DoesNotContain("--seed", text, StringComparison.Ordinal);
    }

    private static string RepositoryFile(string relativePath)
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "KatLang.slnx")))
            directory = directory.Parent;
        Assert.NotNull(directory);

        return Path.Combine(directory.FullName, relativePath);
    }

    [Fact]
    public async Task Version_ReportsTheLoadedKatLangRuntime_AsASingleLine()
    {
        var result = await Cli.InvokeAsync("--version");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Error);

        // ONE line: `katlang` is the command-line distribution of KatLang, not
        // a separately versioned product.
        Assert.DoesNotContain("\n", result.TrimmedOutput);

        // The expectation is DERIVED from the loaded KatLang assembly rather
        // than restated, so this fails if the reported number ever stops
        // tracking the runtime actually executing. ProductVersionOf retains a
        // SemVer pre-release suffix while removing only SDK-added build
        // metadata. Whether that runtime is the INTENDED one is a separate,
        // independent question, checked below against test-build metadata.
        Assert.Equal($"KatLang {ProductVersionOf(typeof(KatLangEngine))}", result.TrimmedOutput);
    }

    /// <summary>
    /// The release invariant behind the single reported number: one MSBuild
    /// property (KatLangVersion, owned by KatLangVersion.props) versions both
    /// the CLI and the KatLang library, so the CLI can identify itself by the
    /// runtime it carries. If either project stops reading that property, the
    /// two assemblies desynchronize and this fails.
    /// </summary>
    [Fact]
    public void CliProductVersion_EqualsTheLoadedKatLangRuntimeVersion()
    {
        Assert.Equal(ProductVersionOf(typeof(KatLangEngine)), ProductVersionOf(typeof(CliApplication)));
    }

    /// <summary>
    /// The currently shipped version: what the build INTENDED to ship against
    /// what the CLI actually reports.
    ///
    /// <para>The expectation is injected at compile time from KatLangVersion.props
    /// - the same property that versions the KatLang library the CLI carries -
    /// so a KatLang release moves one number and lands here with nothing to
    /// restate. It is NOT read from the loaded KatLang assembly, which is what
    /// keeps the comparison meaningful: whenever the runtime the process
    /// actually loaded was built or copied from anything other than the
    /// intended number, the CLI reports that other number and this fails.</para>
    /// </summary>
    [Fact]
    public async Task Version_ReportsTheCurrentlyShippedKatLangVersion()
    {
        var result = await Cli.InvokeAsync("--version");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal($"KatLang {IntendedKatLangVersion}", result.TrimmedOutput);
    }

    [Fact]
    public async Task Help_IsAStandaloneGlobalOption()
    {
        var result = await Cli.InvokeAsync("run", "--help");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains("option '--help' cannot be combined", result.TrimmedError);
    }

    // ── eval ────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("Only")]
    [InlineData("(Only)")]
    [InlineData("Only()")]
    public async Task Eval_CollectingOnlyValueDemand_RendersTheExactEmptyList(string row)
    {
        var result = await Cli.InvokeAsync("eval", $"Only(*xs) = xs\n{row}");
        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Error);
        Assert.Equal("[]", result.TrimmedOutput);
    }

    [Fact]
    public async Task Eval_EvaluatesItsArgumentAsSource_NotAsAFileName()
    {
        var result = await Cli.InvokeAsync("eval", "sum(range(1, 100))");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("5050", result.TrimmedOutput);
        Assert.Equal("", result.Error);
    }

    [Fact]
    public async Task Eval_SourceStartingWithMinus_StaysSource()
    {
        // Only "--" introduces an option, so a leading '-' cannot be mistaken
        // for one.
        var result = await Cli.InvokeAsync("eval", "-1");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("-1", result.TrimmedOutput);
    }

    [Fact]
    public async Task Eval_DoubleDash_AllowsSourceStartingWithTwoDashes()
    {
        var result = await Cli.InvokeAsync("eval", "--", "--1");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("1", result.TrimmedOutput);
        Assert.Equal("", result.Error);
    }

    [Fact]
    public async Task Eval_EmptySource_IsASuccessfulProgramWithoutOutput()
    {
        var result = await Cli.InvokeAsync("eval", "");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal("", result.Error);
    }

    [Fact]
    public async Task Eval_ZeroRowEmission_SucceedsSilently()
    {
        var result = await Cli.InvokeAsync("eval", "[]*");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal("", result.Error);
    }

    [Fact]
    public async Task Eval_ReportsSyntaxDiagnostics_OnStderr()
    {
        var result = await Cli.InvokeAsync("eval", "1 +");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains("Unexpected end of input", result.TrimmedError);
        // KatLang's source location is preserved, not rewritten away.
        Assert.Matches(@"^\[\d+:\d+\] ", result.TrimmedError);
    }

    [Theory]
    [InlineData("(1", "[1:3] Expected ')' but found end of input.")]
    [InlineData("public = 1", "[1:1] Unexpected 'public'.")]
    // A character the lexer cannot recognize is reported by the lexer alone, in its own words.
    [InlineData("1 + @", "[1:5] Unexpected character: '@'.")]
    [InlineData("A.@ 1", "[1:5] Unexpected item after a closed expression on the same line.")]
    [InlineData("A.\npublic Good = 41", "[1:2] Expected property name after '.'")]
    [InlineData("A*\r\nB*", "[2:1] The final `*` on an earlier line continued as multiplication")]
    // SYN-07A: the same-line separator rule is reported at the second item's
    // first token, with the generic three-repair wording, exactly like every
    // other parser diagnostic.
    [InlineData("1 2", "[1:3] Unexpected item after a closed expression on the same line. Add ',' to separate slots, add an operator to continue the expression, or start a declaration on a new line.")]
    [InlineData("F(a, b) = a + b\r\nF(1 2)", "[2:5] Unexpected item after a closed expression on the same line.")]
    [InlineData("x = 3 y = 4", "[1:7] Unexpected item after a closed expression on the same line.")]
    public async Task Eval_ReportsUserFacingParserWordingAndLocations(string source, string expected)
    {
        var result = await Cli.InvokeAsync("eval", source);
        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains(expected, result.TrimmedError);
    }

    // ── run ─────────────────────────────────────────────────────────────────

    [Fact]
    public async Task Run_EvaluatesTheFileContents()
    {
        using var file = new TempSourceFile("Square(X) = X * X\nSquare(7)\n");

        var result = await Cli.InvokeAsync("run", file.Path);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("49", result.TrimmedOutput);
        Assert.Equal("", result.Error);
    }

    [Fact]
    public async Task Run_PrintsTheSameResultAsEval_ForTheSameSource()
    {
        const string source = "sum(range(1, 100))";
        using var file = new TempSourceFile(source);

        var runResult = await Cli.InvokeAsync("run", file.Path);
        var evalResult = await Cli.InvokeAsync("eval", source);

        Assert.Equal(Success, runResult.ExitCode);
        Assert.Equal(evalResult.ExitCode, runResult.ExitCode);
        Assert.Equal(evalResult.TrimmedOutput, runResult.TrimmedOutput);
    }

    [Fact]
    public async Task Run_ReportsEvaluationFailures_OnStderr()
    {
        using var file = new TempSourceFile("1 / 0\n");

        var result = await Cli.InvokeAsync("run", file.Path);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains("Division by zero", result.TrimmedError);
    }

    [Fact]
    public async Task Run_ProgramWithoutOutput_SucceedsSilently()
    {
        using var file = new TempSourceFile("Value = 42\n");

        var result = await Cli.InvokeAsync("run", file.Path);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal("", result.Error);
    }

    // ── Display limit ───────────────────────────────────────────────────────

    /// <summary>
    /// Evaluates successfully under every default limit — each list has two
    /// item slots and strings contribute no host atoms — while the rendered
    /// text doubles per level and passes KatLang's display ceiling.
    /// </summary>
    private const string DisplayOverflowSource =
        "'first output row'\nToText(x) = x.string\nValues = range(1, 1000).map(ToText)\n"
        + "L0 = [Values, Values]\nL1 = [L0, L0]\nL2 = [L1, L1]\nL3 = [L2, L2]\n"
        + "L4 = [L3, L3]\nL5 = [L4, L4]\nL6 = [L5, L5]\nL7 = [L6, L6]\nL7\n";

    /// <summary>
    /// The notice KatLang renders for its default display ceiling, taken from
    /// the package rather than restated, so the CLI contract is pinned to the
    /// package's wording without the tests coupling to it.
    /// </summary>
    private static string DisplayLimitNotice =>
        KatLangError.FromEvalError(
            new EvalError.DisplayLengthLimitExceeded(EvaluationLimits.MaxSupportedDisplayLength)).Message;

    [Fact]
    public async Task DisplayOverflowSource_ReachesRenderingAfterSuccessfulEvaluation()
    {
        var success = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(DisplayOverflowSource));
        Assert.Empty(success.Atoms); // No earlier host-atom projection refusal.
        Assert.Equal(2, success.OutputRows.Count);
        Assert.Equal("first output row", Assert.IsType<Result.Str>(success.OutputRows[0]).Value);

        var rendering = success.RenderDisplay();
        Assert.True(rendering.LimitExceeded);
        Assert.Equal(KatLangErrorCode.DisplayLengthLimitExceeded, rendering.LimitError!.Code);
        Assert.Equal(DisplayLimitNotice, rendering.Text);
    }

    [Fact]
    public async Task Run_OutputExceedingTheDisplayLimit_IsACommandFailure()
    {
        using var file = new TempSourceFile(DisplayOverflowSource);

        var result = await Cli.InvokeAsync("run", file.Path);

        // The notice is a diagnostic, not program output: stderr carries it,
        // stdout stays empty, and the exit code says the command failed.
        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(DisplayLimitNotice + Environment.NewLine, result.Error);
    }

    [Fact]
    public async Task Eval_OutputExceedingTheDisplayLimit_IsACommandFailure()
    {
        var result = await Cli.InvokeAsync("eval", DisplayOverflowSource);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(DisplayLimitNotice + Environment.NewLine, result.Error);
    }

    [Theory]
    [InlineData("run")]
    [InlineData("eval")]
    public async Task OutputEqualToTheDisplayLimitNotice_IsOrdinaryOutput(string command)
    {
        // The discriminator: a program whose genuine output IS the notice text
        // renders byte-identically to an overflow. The CLI must tell the two
        // apart structurally, never by looking at the text.
        using var file = new TempSourceFile($"'{DisplayLimitNotice}'\n");

        var result = await Cli.InvokeAsync(command, command == "run" ? file.Path : $"'{DisplayLimitNotice}'\n");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal(DisplayLimitNotice + Environment.NewLine, result.Output);
        Assert.Equal("", result.Error);
    }

    [Fact]
    public async Task Check_DoesNotEvaluate_SoADisplayOverflowIsNotItsConcern()
    {
        using var file = new TempSourceFile(DisplayOverflowSource);

        var result = await Cli.InvokeAsync("check", file.Path);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal("", result.Error);
    }

    // ── check ───────────────────────────────────────────────────────────────

    [Fact]
    public async Task Check_ValidFile_SucceedsSilently()
    {
        using var file = new TempSourceFile("Square(X) = X * X\nSquare(7)\n");

        var result = await Cli.InvokeAsync("check", file.Path);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal("", result.Error);
    }

    [Theory]
    // Both sources parse and elaborate cleanly but CANNOT be evaluated. If
    // `check` ever executed the program it would surface the very diagnostic the
    // companion `run` assertion below expects, and these cases would fail.
    [InlineData("1 / 0\n", "Division by zero")]
    [InlineData("Undefined\n", "implicit parameter")]
    public async Task Check_ValidatesWithoutEvaluating(string source, string evaluationOnlyDiagnostic)
    {
        using var file = new TempSourceFile(source);

        var checkResult = await Cli.InvokeAsync("check", file.Path);

        Assert.Equal(Success, checkResult.ExitCode);
        Assert.Equal("", checkResult.Output);
        Assert.Equal("", checkResult.Error);

        // The discriminator: evaluating the same file DOES fail.
        var runResult = await Cli.InvokeAsync("run", file.Path);

        Assert.Equal(Failure, runResult.ExitCode);
        Assert.Contains(evaluationOnlyDiagnostic, runResult.TrimmedError);
    }

    [Fact]
    public async Task Check_InvalidSource_ReportsDiagnosticsAndFails()
    {
        using var file = new TempSourceFile("A = \n");

        var result = await Cli.InvokeAsync("check", file.Path);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains("Unexpected end of input", result.TrimmedError);
        Assert.Matches(@"^\[\d+:\d+\] ", result.TrimmedError);
    }

    [Theory]
    [InlineData("check")]
    [InlineData("run")]
    public async Task StrayRootCloser_FailsTheCommand_AndNeverEvaluatesTheRecoveredRemainder(string command)
    {
        // The parser keeps `After = 2` / `After` after the stray ')' for
        // diagnostics and editor analysis, but the document is invalid: the
        // recovered remainder would print `2`, and neither command may.
        using var file = new TempSourceFile("Before = 1\n)\nAfter = 2\nAfter\n");

        var result = await Cli.InvokeAsync(command, file.Path);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(
            "[2:1] Unexpected ')' at the top level. There is no open '(' for it to close.",
            result.TrimmedError);
    }

    [Theory]
    [InlineData("check")]
    [InlineData("run")]
    public async Task DiagnosticFlood_PrintsOneBoundedList(string command)
    {
        // Five thousand stray closers are five thousand diagnostics; the one list keeps the
        // first MaxSupportedDiagnosticCount and ends with the limit marker, so neither command
        // prints more than that however much of the file is malformed.
        using var file = new TempSourceFile(new string(')', 5000));

        var result = await Cli.InvokeAsync(command, file.Path);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        var lines = result.TrimmedError.Split('\n');
        Assert.Equal(SourceProcessingLimits.MaxSupportedDiagnosticCount + 1, lines.Length);
        Assert.Equal("[1:1] Unexpected ')' at the top level. There is no open '(' for it to close.", lines[0]);
        Assert.Equal(
            $"Diagnostic limit of {SourceProcessingLimits.MaxSupportedDiagnosticCount} diagnostics reached: later diagnostics were omitted.",
            lines[^1]);
    }

    // ── File handling ───────────────────────────────────────────────────────

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task MissingFile_IsReportedCleanly(string command)
    {
        var result = await Cli.InvokeAsync(command, TempSourceFile.MissingPath());

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains("file not found", result.TrimmedError);
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task EmptyFilePath_IsReportedInCliWords(string command)
    {
        // The file API rejects an empty path with a message addressed to .NET callers
        // ("... (Parameter 'path')"); the CLI reports it in its own words instead.
        var result = await Cli.InvokeAsync(command, "");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal("katlang: cannot read file '': the path is empty.", result.TrimmedError);
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task WhitespaceFilePath_NeverLeaksAFrameworkParameterName(string command)
    {
        // Windows treats a whitespace-only path as empty; elsewhere it is an ordinary missing
        // file. Either way the report is the CLI's own.
        var result = await Cli.InvokeAsync(command, "   ");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.StartsWith("katlang: ", result.TrimmedError);
        Assert.DoesNotContain("(Parameter", result.TrimmedError);
    }

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task UnreadableFile_IsReportedCleanly(string command)
    {
        // A directory exists as a path but cannot be read as a file. The path is
        // used without a trailing separator so it resolves to the directory
        // itself rather than to a nameless file inside it.
        var directory = Path.TrimEndingDirectorySeparator(Path.GetTempPath());

        var result = await Cli.InvokeAsync(command, directory);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains("cannot read file", result.TrimmedError);
    }

    // ── Malformed invocations ───────────────────────────────────────────────

    [Theory]
    [InlineData(new string[0], "no command specified")]
    [InlineData(new[] { "run" }, "'run' requires a <file> argument")]
    [InlineData(new[] { "eval" }, "'eval' requires a <source> argument")]
    [InlineData(new[] { "check" }, "'check' requires a <file> argument")]
    [InlineData(new[] { "unknown" }, "unknown command 'unknown'")]
    [InlineData(new[] { "run", "a.kat", "unexpected" }, "unexpected argument 'unexpected'")]
    [InlineData(new[] { "run", "a.kat", "--nope" }, "unknown option '--nope'")]
    [InlineData(new[] { "--nope" }, "unknown option '--nope'")]
    [InlineData(new[] { "eval", "1", "--allow-loading", "--allow-loading" }, "specified more than once")]
    [InlineData(new[] { "--help", "--version" }, "cannot be combined")]
    [InlineData(new[] { "--version", "eval", "1" }, "option '--version' cannot be combined")]
    [InlineData(new[] { "--help", "--nope" }, "unknown option '--nope'")]
    public async Task MalformedInvocation_ReportsUsageErrorWithoutCrashing(string[] args, string expected)
    {
        var result = await Cli.InvokeAsync(args);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains(expected, result.TrimmedError);
        Assert.Contains("Run 'katlang --help' for usage.", result.TrimmedError);
    }

    // ── Loading ─────────────────────────────────────────────────────────────

    private const string ModuleUrl = "https://katlang.org/demo/cli-test-lib.kat";
    private const string LoadingSource = $"open '{ModuleUrl}'\nVal\n";

    private static Dictionary<string, string> Modules() => new()
    {
        [ModuleUrl] = "public Val = 41",
    };

    [Theory]
    [InlineData("run")]
    [InlineData("check")]
    public async Task Loading_IsDisabledByDefault(string command)
    {
        var downloader = new RecordingDownloader(Modules());
        using var file = new TempSourceFile(LoadingSource);

        var result = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, command, file.Path);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        // Nothing was fetched: KatLang was never given a downloader.
        Assert.Empty(downloader.RequestedUrls);
        Assert.Contains("module elaboration is unavailable", result.TrimmedError);
    }

    [Fact]
    public async Task Eval_Loading_IsDisabledByDefault()
    {
        var downloader = new RecordingDownloader(Modules());

        var result = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "eval", LoadingSource);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Empty(downloader.RequestedUrls);
        Assert.Contains("module elaboration is unavailable", result.TrimmedError);
    }

    [Fact]
    public async Task AllowLoading_EnablesKatLangModuleLoading_ForRun()
    {
        var downloader = new RecordingDownloader(Modules());
        using var file = new TempSourceFile(LoadingSource);

        var result = await Cli.InvokeWithDownloaderAsync(
            downloader.DownloadAsync, "run", file.Path, "--allow-loading");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("41", result.TrimmedOutput);
        Assert.Equal(ModuleUrl, Assert.Single(downloader.RequestedUrls));
    }

    [Fact]
    public async Task AllowLoading_EnablesKatLangModuleLoading_ForEval()
    {
        var downloader = new RecordingDownloader(Modules());

        var result = await Cli.InvokeWithDownloaderAsync(
            downloader.DownloadAsync, "eval", LoadingSource, "--allow-loading");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("41", result.TrimmedOutput);
        Assert.Equal(ModuleUrl, Assert.Single(downloader.RequestedUrls));
    }

    [Fact]
    public async Task AllowLoading_MayAppearBeforeTheCommand()
    {
        var downloader = new RecordingDownloader(Modules());

        var result = await Cli.InvokeWithDownloaderAsync(
            downloader.DownloadAsync, "--allow-loading", "eval", LoadingSource);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("41", result.TrimmedOutput);
        Assert.Equal(ModuleUrl, Assert.Single(downloader.RequestedUrls));
    }

    [Fact]
    public async Task AllowLoading_ResolvesModulesForCheck_WithoutEvaluating()
    {
        var downloader = new RecordingDownloader(Modules());
        using var file = new TempSourceFile(LoadingSource);

        var result = await Cli.InvokeWithDownloaderAsync(
            downloader.DownloadAsync, "check", file.Path, "--allow-loading");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal("", result.Error);
        // Validation still had to resolve the loaded algorithm.
        Assert.Equal(ModuleUrl, Assert.Single(downloader.RequestedUrls));
    }

    [Fact]
    public async Task AllowLoading_ReportsLoadingFailures()
    {
        // Serves nothing: every fetch faults.
        var downloader = new RecordingDownloader();

        var result = await Cli.InvokeWithDownloaderAsync(
            downloader.DownloadAsync, "eval", LoadingSource, "--allow-loading");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal(ModuleUrl, Assert.Single(downloader.RequestedUrls));
        Assert.Contains("failed to fetch", result.TrimmedError);
    }

    [Fact]
    public async Task AllowLoading_KeepsKatLangsHostPolicy()
    {
        // Host allow-listing belongs to KatLang, not to the CLI: a downloader is
        // configured, yet a disallowed origin is still refused — untouched.
        var downloader = new RecordingDownloader();

        var result = await Cli.InvokeWithDownloaderAsync(
            downloader.DownloadAsync, "eval", "open 'https://example.com/x.kat'\n1", "--allow-loading");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Empty(downloader.RequestedUrls);
        Assert.Contains("domain not allowed", result.TrimmedError);
    }

    [Theory]
    [InlineData("http://katlang.org/x.kat", "only HTTPS URLs are allowed")]
    [InlineData("https://127.0.0.1/x.kat", "domain not allowed")]
    [InlineData("https://katlang.org.example.net/x.kat", "domain not allowed")]
    [InlineData("https://katlang.org:8443@example.net/x.kat", "must not contain user information")]
    [InlineData("https://alice:s3cret@katlang.org/x.kat", "must not contain user information")]
    [InlineData("https://example.net\uFF0F.katlang.org/x.kat", "its host is not a valid DNS name or IP address")]
    public async Task AllowLoading_RefusesForbiddenSchemesAndHosts_BeforeAnyRequest(string url, string expected)
    {
        // KatLang's scheme and allowed-host checks run before the CLI transport is ever
        // consulted, with or without the flag's transport bounds.
        var downloader = new RecordingDownloader();

        var result = await Cli.InvokeWithDownloaderAsync(
            downloader.DownloadAsync, "eval", $"open '{url}'\n1", "--allow-loading");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Empty(downloader.RequestedUrls);
        Assert.Contains(expected, result.TrimmedError);
    }

    [Fact]
    public async Task HttpDownloader_RefusesRedirectsBeforeFetchingTheirDestination()
    {
        await using var destination = new LoopbackHttpServer(
            () => LoopbackHttpServer.Ok("public Value = 42"));
        await using var origin = new LoopbackHttpServer(
            () => LoopbackHttpServer.Redirect(destination.Url("localhost")));

        var exception = await Assert.ThrowsAsync<HttpRequestException>(async () =>
            await HttpSourceDownloader.Shared.DownloadAsync(origin.Url("127.0.0.1"), CancellationToken.None));

        Assert.Contains("redirects are not allowed", exception.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(1, origin.RequestCount);
        Assert.Equal(0, destination.RequestCount);
    }

    // ── Seeding ─────────────────────────────────────────────────────────────

    /// <summary>Every random operation in both spellings, plus the cache law, so a
    /// seed that failed to reach any part of evaluation would show.</summary>
    private const string RandomSource =
        "P = Math.RandomInt(0, 1e30)\nMath.Random(0, 1), random(2, 6), P, P, P(), randomInt(-5, 5)";

    /// <summary>
    /// The CLI adds no randomness semantics of its own: <c>--random-seed</c> is exactly
    /// <see cref="RunOptions.RandomSeed"/>, so the package's own seeded display is the
    /// expectation, never a captured literal.
    /// </summary>
    private static string SeededEngineDisplay(string source, long seed)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, new RunOptions { RandomSeed = seed }))
            .ToDisplayString()
            .ReplaceLineEndings("\n");

    [Theory]
    [InlineData("0", 0L)]
    [InlineData("-0", 0L)]
    [InlineData("+0", 0L)]
    [InlineData("1", 1L)]
    [InlineData("-1", -1L)]
    [InlineData("+1", 1L)]
    [InlineData("42", 42L)]
    [InlineData("-42", -42L)]
    [InlineData("+42", 42L)]
    [InlineData("00042", 42L)]
    [InlineData("-5", -5L)]
    [InlineData("+5", 5L)]
    [InlineData("-9223372036854775808", long.MinValue)]
    [InlineData("9223372036854775807", long.MaxValue)]
    public async Task Eval_RandomSeed_AcceptsEverySignedLongSpelling_AndIsReproducible(string token, long seed)
    {
        var first = await Cli.InvokeAsync("eval", RandomSource, "--random-seed", token);
        var second = await Cli.InvokeAsync("eval", RandomSource, "--random-seed", token);

        Assert.Equal(Success, first.ExitCode);
        Assert.Equal("", first.Error);
        Assert.Equal(first.TrimmedOutput, second.TrimmedOutput);
        Assert.Equal(SeededEngineDisplay(RandomSource, seed), first.TrimmedOutput);
    }

    [Fact]
    public async Task RandomSeed_PlusAndMinusFive_AreDifferentStreams_AndUnseededRunsDiffer()
    {
        var plus = await Cli.InvokeAsync("eval", RandomSource, "--random-seed", "+5");
        var minus = await Cli.InvokeAsync("eval", RandomSource, "--random-seed", "-5");
        Assert.Equal(Success, plus.ExitCode);
        Assert.Equal(Success, minus.ExitCode);
        Assert.NotEqual(plus.TrimmedOutput, minus.TrimmedOutput);

        // Unseeded: four invocations over a 1e30-wide draw agree only by an accident
        // of probability ~1e-29.
        var unseeded = new HashSet<string>(StringComparer.Ordinal);
        for (var i = 0; i < 4; i++)
        {
            var result = await Cli.InvokeAsync("eval", "Math.RandomInt(0, 1e30)");
            Assert.Equal(Success, result.ExitCode);
            unseeded.Add(result.TrimmedOutput);
        }

        Assert.True(unseeded.Count > 1, "unseeded eval produced one constant value");
    }

    [Fact]
    public async Task Run_RandomSeed_ReproducesTheSameOutput_AndAgreesWithEval()
    {
        using var file = new TempSourceFile(RandomSource);

        var first = await Cli.InvokeAsync("run", file.Path, "--random-seed", "42");
        var second = await Cli.InvokeAsync("run", file.Path, "--random-seed", "42");
        var eval = await Cli.InvokeAsync("eval", RandomSource, "--random-seed", "42");

        Assert.Equal(Success, first.ExitCode);
        Assert.Equal("", first.Error);
        Assert.Equal(first.TrimmedOutput, second.TrimmedOutput);
        Assert.Equal(first.TrimmedOutput, eval.TrimmedOutput);
        Assert.Equal(SeededEngineDisplay(RandomSource, 42), first.TrimmedOutput);
    }

    [Fact]
    public async Task RandomSeed_MayAppearAnywhereAmongTheArguments()
    {
        using var file = new TempSourceFile(RandomSource);
        var expected = SeededEngineDisplay(RandomSource, 7);

        foreach (var args in new[]
                 {
                     new[] { "--random-seed", "7", "run", file.Path },
                     new[] { "run", "--random-seed", "7", file.Path },
                     new[] { "run", file.Path, "--random-seed", "7" },
                     new[] { "--random-seed", "7", "run", "--", file.Path },
                     new[] { "--random-seed", "7", "eval", RandomSource },
                     new[] { "eval", "--random-seed", "7", RandomSource },
                     new[] { "eval", RandomSource, "--random-seed", "7" },
                     new[] { "eval", "--random-seed", "7", "--", RandomSource },
                 })
        {
            var result = await Cli.InvokeAsync(args);

            Assert.Equal(Success, result.ExitCode);
            Assert.Equal("", result.Error);
            Assert.Equal(expected, result.TrimmedOutput);
        }
    }

    [Fact]
    public async Task RandomSeed_AndAllowLoading_AreOrthogonal_OnALoadedRandomModule()
    {
        const string url = "https://katlang.org/demo/cli-seed-lib.kat";
        const string module = "public Val = Math.RandomInt(0, 1e30)";
        const string source = $"open '{url}'\nVal, Math.Random(0, 1)";
        var modules = new Dictionary<string, string> { [url] = module };

        var first = await Cli.InvokeWithDownloaderAsync(new RecordingDownloader(modules).DownloadAsync, "eval", source, "--allow-loading", "--random-seed", "9");
        var second = await Cli.InvokeWithDownloaderAsync(new RecordingDownloader(modules).DownloadAsync, "--random-seed", "9", "eval", source, "--allow-loading");

        Assert.Equal(Success, first.ExitCode);
        Assert.Equal("", first.Error);
        Assert.Equal(first.TrimmedOutput, second.TrimmedOutput);

        var engine = await KatLangEngine.RunAsync(
            source,
            new RunOptions { DownloadCode = new RecordingDownloader(modules).DownloadAsync, RandomSeed = 9 });
        Assert.Equal(
            Assert.IsType<RunResult.Success>(engine).ToDisplayString().ReplaceLineEndings("\n"),
            first.TrimmedOutput);

        // Loading stays disabled without its flag, seed or no seed.
        var unloaded = await Cli.InvokeWithDownloaderAsync(new RecordingDownloader(modules).DownloadAsync, "eval", source, "--random-seed", "9");
        Assert.Equal(Failure, unloaded.ExitCode);
        Assert.Contains("module elaboration is unavailable", unloaded.TrimmedError);
    }

    [Theory]
    [InlineData(new[] { "eval", "1", "--random-seed", "1", "--random-seed", "2" }, "option '--random-seed' was specified more than once.")]
    [InlineData(new[] { "eval", "1", "--random-seed", "1", "--random-seed", "1" }, "option '--random-seed' was specified more than once.")]
    [InlineData(new[] { "eval", "1", "--random-seed" }, "option '--random-seed' requires a value.")]
    [InlineData(new[] { "eval", "1", "--random-seed", "--allow-loading" }, "option '--random-seed' requires a value.")]
    [InlineData(new[] { "eval", "1", "--random-seed", "--display-decimals", "2" }, "option '--random-seed' requires a value.")]
    [InlineData(new[] { "eval", "1", "--random-seed", "--" }, "option '--random-seed' requires a value.")]
    // A following non-option token is always TRIED as the value (single dashes and
    // words alike): the command name is not skipped over to find a number.
    [InlineData(new[] { "--random-seed", "eval", "1" }, "option '--random-seed' requires an integer between -9223372036854775808 and 9223372036854775807; got 'eval'.")]
    // The value is the next token only: a joined value is an unknown option.
    [InlineData(new[] { "eval", "1", "--random-seed=42" }, "unknown option '--random-seed=42'.")]
    // After the terminator the spelling is a positional, here the command.
    [InlineData(new[] { "--", "--random-seed", "42" }, "unknown command '--random-seed'.")]
    [InlineData(new[] { "--help", "--random-seed", "42" }, "option '--help' cannot be combined with other arguments.")]
    [InlineData(new[] { "--random-seed", "42", "--help" }, "option '--help' cannot be combined with other arguments.")]
    [InlineData(new[] { "--version", "--random-seed", "42" }, "option '--version' cannot be combined with other arguments.")]
    [InlineData(new[] { "--random-seed", "42", "--version" }, "option '--version' cannot be combined with other arguments.")]
    public async Task RandomSeed_MalformedInvocations_ReportUsageErrors(string[] args, string expected)
    {
        var result = await Cli.InvokeAsync(args);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains(expected, result.TrimmedError);
        Assert.Contains("Run 'katlang --help' for usage.", result.TrimmedError);
    }

    /// <summary>
    /// The pre-release <c>--seed</c> spelling was removed, not aliased: it is an unknown option
    /// in every form and position, never a seed, never a deprecation warning, and never a second
    /// spelling of <c>--random-seed</c> (so it is not reported as a repeat of it either).
    /// </summary>
    [Theory]
    [InlineData(new[] { "eval", "1", "--seed", "42" }, "--seed")]
    [InlineData(new[] { "eval", "1", "--seed" }, "--seed")]
    [InlineData(new[] { "eval", "1", "--seed=42" }, "--seed=42")]
    [InlineData(new[] { "--seed", "42", "eval", "1" }, "--seed")]
    [InlineData(new[] { "run", "missing-seed-audit.kat", "--seed", "42" }, "--seed")]
    [InlineData(new[] { "check", "missing-seed-audit.kat", "--seed", "42" }, "--seed")]
    [InlineData(new[] { "eval", "1", "--random-seed", "42", "--seed", "42" }, "--seed")]
    [InlineData(new[] { "--seed", "42", "--help" }, "--seed")]
    public async Task RemovedSeedSpelling_IsAnUnknownOption(string[] args, string option)
    {
        var result = await Cli.InvokeAsync(args);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal($"katlang: unknown option '{option}'.\nRun 'katlang --help' for usage.", result.TrimmedError);
    }

    [Theory]
    [InlineData("abc")]
    [InlineData("")]
    [InlineData("+")]
    [InlineData("-")]
    [InlineData("1.5")]
    [InlineData("1e3")]
    [InlineData("0x10")]
    [InlineData("1,000")]
    [InlineData(" 5")]
    [InlineData("5 ")]
    [InlineData("-x")]
    [InlineData("9223372036854775808")]  // long.MaxValue + 1
    [InlineData("-9223372036854775809")] // long.MinValue - 1
    [InlineData("18446744073709551615")] // ulong.MaxValue
    public async Task RandomSeed_InvalidValues_AreRejectedWithTheIntegerRangeMessage(string value)
    {
        var result = await Cli.InvokeAsync("eval", "1", "--random-seed", value);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(
            $"katlang: option '--random-seed' requires an integer between -9223372036854775808 and 9223372036854775807; got '{value}'.\n"
            + "Run 'katlang --help' for usage.",
            result.TrimmedError);
    }

    [Fact]
    public async Task Check_RefusesTheRandomSeed_BecauseCheckDoesNotEvaluate()
    {
        using var file = new TempSourceFile(RandomSource);
        const string refusal = "katlang: option '--random-seed' is not valid for 'check': check does not evaluate.\n"
            + "Run 'katlang --help' for usage.";

        foreach (var args in new[]
                 {
                     new[] { "check", file.Path, "--random-seed", "5" },
                     new[] { "--random-seed", "0", "check", file.Path },
                     new[] { "check", "--random-seed", "-1", file.Path, "--allow-loading" },
                 })
        {
            var result = await Cli.InvokeAsync(args);

            Assert.Equal(Failure, result.ExitCode);
            Assert.Equal("", result.Output);
            Assert.Equal(refusal, result.TrimmedError);
        }

        // The same file still checks cleanly without the option.
        var plain = await Cli.InvokeAsync("check", file.Path);
        Assert.Equal(Success, plain.ExitCode);
    }

    [Fact]
    public async Task Check_MalformedRandomSeed_IsReportedBeforeTheApplicabilityRefusal()
    {
        using var file = new TempSourceFile(RandomSource);

        var result = await Cli.InvokeAsync("check", file.Path, "--random-seed", "abc");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Contains("requires an integer between", result.TrimmedError);
        Assert.DoesNotContain("not valid for 'check'", result.TrimmedError);
    }

    [Fact]
    public async Task DoubleDash_KeepsRandomSeedTokensPositional()
    {
        using var file = new TempSourceFile("1\n");

        // After the terminator `--random-seed` is a positional: a third positional for run.
        var run = await Cli.InvokeAsync("run", file.Path, "--", "--random-seed", "5");
        Assert.Equal(Failure, run.ExitCode);
        Assert.Contains("unexpected argument '--random-seed'.", run.TrimmedError);

        // For eval a post-terminator `--random-seed` is SOURCE, never an option and never a
        // missing value: the CLI reports exactly what KatLang reports for that text.
        var eval = await Cli.InvokeAsync("eval", "--", "--random-seed");
        Assert.Equal(Failure, eval.ExitCode);
        Assert.Equal("", eval.Output);
        Assert.Equal(KatLangEngine.Run("--random-seed").ToDisplayString().ReplaceLineEndings("\n"), eval.TrimmedError);
        Assert.DoesNotContain("requires a value", eval.TrimmedError);
        Assert.DoesNotContain("unknown option", eval.TrimmedError);

        // And a seed BEFORE the terminator still applies to source after it.
        var seededSource = await Cli.InvokeAsync("--random-seed", "3", "eval", "--", "--1 + Math.RandomInt(0, 1e30)");
        Assert.Equal(Success, seededSource.ExitCode);
        Assert.Equal(SeededEngineDisplay("--1 + Math.RandomInt(0, 1e30)", 3), seededSource.TrimmedOutput);
    }

    /// <summary>
    /// Seeding is host configuration only. Unlike <c>DisplayDecimals</c>, KatLang has no seeding
    /// property: a program's own <c>RandomSeed</c> is an ordinary declaration that
    /// <c>--random-seed</c> neither reads nor yields to, and that seeds nothing on its own.
    /// </summary>
    [Fact]
    public async Task ProgramsOwnRandomSeedProperty_IsOrdinary_OnlyTheOptionSeeds()
    {
        const string declared = "RandomSeed = 7\nRandomSeed, Math.RandomInt(0, 1e30)";

        // The property is an ordinary value, and the draw is the option's seed exactly as if
        // the declaration were absent.
        var seeded = await Cli.InvokeAsync("eval", declared, "--random-seed", "42");
        Assert.Equal(Success, seeded.ExitCode);
        Assert.Equal("", seeded.Error);
        Assert.Equal(SeededEngineDisplay("7, Math.RandomInt(0, 1e30)", 42), seeded.TrimmedOutput);

        // Without the option the declaration seeds nothing: four draws over 1e30 values agree
        // only by an accident of probability ~1e-29.
        var unseeded = new HashSet<string>(StringComparer.Ordinal);
        for (var i = 0; i < 4; i++)
        {
            var result = await Cli.InvokeAsync("eval", declared);
            Assert.Equal(Success, result.ExitCode);
            unseeded.Add(result.TrimmedOutput);
        }

        Assert.True(unseeded.Count > 1, "a declared RandomSeed property seeded an unseeded eval");
    }

    [Fact]
    public async Task Help_DocumentsTheRandomSeedOption()
    {
        var result = await Cli.InvokeAsync("--help");
        var help = result.TrimmedOutput;

        Assert.Equal(Success, result.ExitCode);
        Assert.Contains("katlang run <file> [--allow-loading] [--random-seed <integer>]", help);
        Assert.Contains("katlang eval <source> [--allow-loading] [--random-seed <integer>]", help);
        Assert.Contains("katlang check <file> [--allow-loading]\n", help + "\n");
        Assert.DoesNotContain("check <file> [--allow-loading] [--random-seed", help);
        Assert.Contains("\n  --random-seed <integer>\n                     Seed KatLang's random operations (Math.Random,\n", help);
        Assert.Contains("Not valid for check", help);
        Assert.Contains("random values may differ", help);

        // One spelling: the removed `--seed` and a joined `=value` form are never taught.
        Assert.DoesNotContain("--seed", help);
        Assert.DoesNotContain("--random-seed=", help);
    }

    // ── Display decimals ────────────────────────────────────────────────────

    /// <summary>Fractions, a midpoint, a list, and a sequence, so the count shows everywhere.</summary>
    private const string FractionSource = "1 / 7, 2 / 3, (2.5, [-2.5])";

    /// <summary>
    /// The CLI adds no display semantics of its own: <c>--display-decimals</c> is exactly
    /// <see cref="RunOptions.DefaultDisplayDecimals"/>, so the package's own display under that
    /// default is the expectation, never a re-implemented rounding.
    /// </summary>
    private static string EngineDisplay(string source, RunOptions options)
        => KatLangEngine.Run(source, options).ToDisplayString().ReplaceLineEndings("\n");

    [Theory]
    [InlineData("0")]
    [InlineData("3")]
    [InlineData("99")]
    public async Task Eval_DisplayDecimals_IsKatLangsHostDefault(string token)
    {
        var decimals = int.Parse(token, CultureInfo.InvariantCulture);

        var result = await Cli.InvokeAsync("eval", FractionSource, "--display-decimals", token);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Error);
        Assert.Equal(EngineDisplay(FractionSource, new RunOptions { DefaultDisplayDecimals = decimals }), result.TrimmedOutput);
    }

    [Fact]
    public async Task Eval_DisplayDecimals_RendersThroughThePackagesRules()
    {
        Assert.Equal("0.143", (await Cli.InvokeAsync("eval", "--display-decimals", "3", "1 / 7")).TrimmedOutput);

        // 0 is a real setting: midpoints round away from zero, like Math.Round.
        Assert.Equal("3\n-3", (await Cli.InvokeAsync("eval", "2.5, -2.5", "--display-decimals", "0")).TrimmedOutput);

        // Special values keep their spelling; -0 stays -0 while -0.0 takes the places.
        Assert.Equal(
            "NaN\nInfinity\n-Infinity\n-0\n-0.00000",
            (await Cli.InvokeAsync("eval", "Math.Sqrt(-1), 9e6144 * 10, Math.Ln(0), -0, -0.0", "--display-decimals", "5")).TrimmedOutput);
    }

    [Fact]
    public async Task OmittedDisplayDecimals_KeepsCanonicalOutput()
    {
        var result = await Cli.InvokeAsync("eval", FractionSource);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal(KatLangEngine.Run(FractionSource).ToDisplayString().ReplaceLineEndings("\n"), result.TrimmedOutput);
        Assert.Equal(EngineDisplay(FractionSource, new RunOptions()), result.TrimmedOutput);
    }

    [Theory]
    [InlineData("0")]
    [InlineData("3")]
    [InlineData("99")]
    public async Task ProgramsOwnDisplayDecimals_OverridesTheOption(string token)
    {
        using var file = new TempSourceFile("DisplayDecimals = 6\n1 / 7\n");

        var eval = await Cli.InvokeAsync("eval", "DisplayDecimals = 6\n1 / 7", "--display-decimals", token);
        var run = await Cli.InvokeAsync("run", file.Path, "--display-decimals", token);

        Assert.Equal(Success, eval.ExitCode);
        Assert.Equal("0.142857", eval.TrimmedOutput);
        Assert.Equal(Success, run.ExitCode);
        Assert.Equal("0.142857", run.TrimmedOutput);
    }

    [Fact]
    public async Task InvalidDisplayDecimalsProperty_StillFails_TheOptionIsNoRecovery()
    {
        const string source = "DisplayDecimals = -1\n1 / 7";

        var withOption = await Cli.InvokeAsync("eval", source, "--display-decimals", "3");
        var without = await Cli.InvokeAsync("eval", source);

        Assert.Equal(Failure, withOption.ExitCode);
        Assert.Equal("", withOption.Output);
        Assert.Contains("DisplayDecimals must be a non-negative integer.", withOption.TrimmedError);
        Assert.Equal(without.ExitCode, withOption.ExitCode);
        Assert.Equal(without.TrimmedError, withOption.TrimmedError);
    }

    [Fact]
    public async Task Run_DisplayDecimals_ReadsAUtf8FileByRelativePathWithSpaces()
    {
        // A path RELATIVE to the process's current directory (never changed here), through a
        // directory and a file name with spaces, holding non-ASCII UTF-8 text.
        var directory = Path.Combine(Environment.CurrentDirectory, $"katlang cli display {Guid.NewGuid():N}");
        Directory.CreateDirectory(directory);
        try
        {
            var path = Path.Combine(directory, "display program.kat");
            File.WriteAllText(path, "'π ≈ 3.14159'\nMath.Pi, 1 / 7\n", new UTF8Encoding(encoderShouldEmitUTF8Identifier: false));
            var relative = Path.GetRelativePath(Environment.CurrentDirectory, path);
            Assert.False(Path.IsPathRooted(relative));

            var result = await Cli.InvokeAsync("run", "--display-decimals", "4", relative);

            Assert.Equal(Success, result.ExitCode);
            Assert.Equal("", result.Error);
            // Strings are never touched; every number takes the four places.
            Assert.Equal("π ≈ 3.14159\n3.1416\n0.1429", result.TrimmedOutput);
        }
        finally
        {
            Directory.Delete(directory, recursive: true);
        }
    }

    [Theory]
    [InlineData("-1")]
    [InlineData("100")]
    [InlineData("1.5")]
    [InlineData("abc")]
    [InlineData("")]
    [InlineData(" 5")]
    [InlineData("5 ")]
    [InlineData("0x10")]
    [InlineData("1e1")]
    [InlineData("1,0")]
    [InlineData("+")]
    [InlineData("-")]
    [InlineData("2147483648")]           // int.MaxValue + 1
    [InlineData("99999999999999999999")] // beyond long
    public async Task DisplayDecimals_InvalidValues_AreUsageErrors_BeforeAnyEvaluation(string value)
    {
        // `Missing` would be an evaluation diagnostic if the program ran; it never does.
        var result = await Cli.InvokeAsync("eval", "Missing", "--display-decimals", value);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal(
            $"katlang: option '--display-decimals' requires an integer between 0 and {RunOptions.MaxDisplayDecimals}; got '{value}'.\n"
            + "Run 'katlang --help' for usage.",
            result.TrimmedError);
    }

    [Theory]
    [InlineData("+2", 2)]
    [InlineData("02", 2)]
    [InlineData("-0", 0)]
    [InlineData("+0", 0)]
    public async Task DisplayDecimals_AcceptsTheSameIntegerSpellingsAsSeed(string token, int decimals)
    {
        var result = await Cli.InvokeAsync("eval", FractionSource, "--display-decimals", token);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal(EngineDisplay(FractionSource, new RunOptions { DefaultDisplayDecimals = decimals }), result.TrimmedOutput);
    }

    [Theory]
    [InlineData(new[] { "eval", "1", "--display-decimals" }, "option '--display-decimals' requires a value.")]
    [InlineData(new[] { "eval", "1", "--display-decimals", "--random-seed", "5" }, "option '--display-decimals' requires a value.")]
    [InlineData(new[] { "eval", "--display-decimals", "--", "1" }, "option '--display-decimals' requires a value.")]
    [InlineData(new[] { "eval", "1", "--display-decimals", "2", "--display-decimals", "2" }, "option '--display-decimals' was specified more than once.")]
    [InlineData(new[] { "eval", "1", "--display-decimals=2" }, "unknown option '--display-decimals=2'.")]
    [InlineData(new[] { "--help", "--display-decimals", "2" }, "option '--help' cannot be combined with other arguments.")]
    [InlineData(new[] { "--display-decimals", "2", "--version" }, "option '--version' cannot be combined with other arguments.")]
    [InlineData(new[] { "eval", "--display-decimals", "2" }, "'eval' requires a <source> argument.")]
    [InlineData(new[] { "run", "--display-decimals", "2" }, "'run' requires a <file> argument.")]
    public async Task DisplayDecimals_MalformedInvocations_ReportUsageErrors(string[] args, string expected)
    {
        var result = await Cli.InvokeAsync(args);

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Equal($"katlang: {expected}\nRun 'katlang --help' for usage.", result.TrimmedError);
    }

    [Fact]
    public async Task DisplayDecimals_TriesTheNextToken_NeverSkipsTheCommandToFindOne()
    {
        var result = await Cli.InvokeAsync("--display-decimals", "eval", "1");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Contains(
            $"option '--display-decimals' requires an integer between 0 and {RunOptions.MaxDisplayDecimals}; got 'eval'.",
            result.TrimmedError);
    }

    [Fact]
    public async Task Check_RefusesDisplayDecimals_BecauseCheckDoesNotEvaluate()
    {
        using var file = new TempSourceFile("1 / 7\n");
        const string refusal = "katlang: option '--display-decimals' is not valid for 'check': check does not evaluate.\n"
            + "Run 'katlang --help' for usage.";

        foreach (var args in new[]
                 {
                     new[] { "check", file.Path, "--display-decimals", "2" },
                     new[] { "--display-decimals", "0", "check", file.Path },
                     new[] { "check", "--display-decimals", "99", file.Path, "--allow-loading" },
                 })
        {
            var result = await Cli.InvokeAsync(args);

            Assert.Equal(Failure, result.ExitCode);
            Assert.Equal("", result.Output);
            Assert.Equal(refusal, result.TrimmedError);
        }

        // Without the option, check is exactly as before: silent success.
        var plain = await Cli.InvokeAsync("check", file.Path);
        Assert.Equal(Success, plain.ExitCode);
        Assert.Equal("", plain.Output);
        Assert.Equal("", plain.Error);
    }

    [Fact]
    public async Task Check_MalformedDisplayDecimals_IsReportedBeforeTheApplicabilityRefusal()
    {
        using var file = new TempSourceFile("1 / 7\n");

        var result = await Cli.InvokeAsync("check", file.Path, "--display-decimals", "abc");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Contains("requires an integer between", result.TrimmedError);
        Assert.DoesNotContain("not valid for 'check'", result.TrimmedError);
    }

    [Fact]
    public async Task Check_WithRandomSeedAndDisplayDecimals_RefusesTheSeedFirst()
    {
        using var file = new TempSourceFile("1 / 7\n");

        var result = await Cli.InvokeAsync("check", file.Path, "--display-decimals", "2", "--random-seed", "5");

        Assert.Equal(Failure, result.ExitCode);
        Assert.Contains("option '--random-seed' is not valid for 'check'", result.TrimmedError);
    }

    [Fact]
    public async Task DisplayDecimals_MayAppearAnywhere_AndComposesWithRandomSeedAndLoading()
    {
        using var file = new TempSourceFile(RandomSource);
        var expected = EngineDisplay(RandomSource, new RunOptions { RandomSeed = 42, DefaultDisplayDecimals = 3 });

        foreach (var args in new[]
                 {
                     new[] { "--display-decimals", "3", "--random-seed", "42", "run", file.Path },
                     new[] { "run", "--random-seed", "42", "--display-decimals", "3", file.Path },
                     new[] { "run", file.Path, "--display-decimals", "3", "--random-seed", "42" },
                     new[] { "--random-seed", "42", "run", file.Path, "--display-decimals", "3", "--allow-loading" },
                     new[] { "--allow-loading", "--display-decimals", "3", "run", "--random-seed", "42", "--", file.Path },
                     new[] { "eval", RandomSource, "--random-seed", "42", "--display-decimals", "3" },
                     new[] { "eval", RandomSource, "--display-decimals", "3", "--random-seed", "42" },
                 })
        {
            var result = await Cli.InvokeAsync(args);

            Assert.Equal(Success, result.ExitCode);
            Assert.Equal("", result.Error);
            Assert.Equal(expected, result.TrimmedOutput);
        }
    }

    [Fact]
    public async Task DisplayDecimals_ChangesNoSeededValue()
    {
        // The same seed draws the same values whatever is displayed: the package's own atoms
        // are identical, and only the rendered digits differ.
        var plain = Assert.IsType<RunResult.Success>(KatLangEngine.Run(RandomSource, new RunOptions { RandomSeed = 42 }));
        var shown = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run(RandomSource, new RunOptions { RandomSeed = 42, DefaultDisplayDecimals = 3 }));
        Assert.Equal(plain.Atoms, shown.Atoms);

        var seeded = await Cli.InvokeAsync("eval", RandomSource, "--random-seed", "42");
        var seededAndShown = await Cli.InvokeAsync("eval", RandomSource, "--random-seed", "42", "--display-decimals", "3");

        Assert.Equal(SeededEngineDisplay(RandomSource, 42), seeded.TrimmedOutput);
        Assert.Equal(shown.ToDisplayString().ReplaceLineEndings("\n"), seededAndShown.TrimmedOutput);
        Assert.NotEqual(seeded.TrimmedOutput, seededAndShown.TrimmedOutput);
    }

    [Fact]
    public async Task DisplayDecimals_AndAllowLoading_AreOrthogonal()
    {
        const string url = "https://katlang.org/demo/cli-display-lib.kat";
        const string source = $"open '{url}'\nThird, Val / 7";
        var modules = new Dictionary<string, string> { [url] = "public Third = 1 / 3\npublic Val = 1" };

        var loader = new RecordingDownloader(modules);
        var loaded = await Cli.InvokeWithDownloaderAsync(loader.DownloadAsync, "eval", source, "--allow-loading", "--display-decimals", "2");

        Assert.Equal(Success, loaded.ExitCode);
        Assert.Equal("0.33\n0.14", loaded.TrimmedOutput);
        Assert.Equal(url, Assert.Single(loader.RequestedUrls));

        // Loading stays disabled without its flag, display option or no display option.
        var gated = new RecordingDownloader(modules);
        var unloaded = await Cli.InvokeWithDownloaderAsync(gated.DownloadAsync, "eval", source, "--display-decimals", "2");

        Assert.Equal(Failure, unloaded.ExitCode);
        Assert.Equal("", unloaded.Output);
        Assert.Empty(gated.RequestedUrls);
        Assert.Contains("module elaboration is unavailable", unloaded.TrimmedError);
    }

    [Fact]
    public async Task DoubleDash_KeepsDisplayDecimalsTokensPositional()
    {
        using var file = new TempSourceFile("1 / 7\n");

        // An option BEFORE the terminator applies to source after it that begins with two dashes.
        var dashed = await Cli.InvokeAsync("eval", "--display-decimals", "2", "--", "--1 / 3");
        Assert.Equal(Success, dashed.ExitCode);
        Assert.Equal("0.33", dashed.TrimmedOutput);

        // After the terminator the spelling is a positional: a third positional for run ...
        var run = await Cli.InvokeAsync("run", file.Path, "--", "--display-decimals", "2");
        Assert.Equal(Failure, run.ExitCode);
        Assert.Contains("unexpected argument '--display-decimals'.", run.TrimmedError);

        // ... and SOURCE for eval: never an option, never a missing value.
        var eval = await Cli.InvokeAsync("eval", "--", "--display-decimals");
        Assert.Equal(Failure, eval.ExitCode);
        Assert.DoesNotContain("requires a value", eval.TrimmedError);
        Assert.DoesNotContain("unknown option", eval.TrimmedError);
        Assert.Contains("implicit parameter", eval.TrimmedError);
    }

    [Fact]
    public async Task Help_DocumentsTheDisplayDecimalsOption()
    {
        var result = await Cli.InvokeAsync("--help");
        var help = result.TrimmedOutput;

        Assert.Equal(Success, result.ExitCode);
        Assert.Contains("katlang run <file> [--allow-loading] [--random-seed <integer>]\n                     [--display-decimals <integer>]\n", help);
        Assert.Contains("katlang eval <source> [--allow-loading] [--random-seed <integer>]\n                        [--display-decimals <integer>]\n", help);
        Assert.Contains("katlang check <file> [--allow-loading]\n", help + "\n");
        Assert.DoesNotContain("check <file> [--allow-loading] [--display-decimals", help);

        // The quoted range is KatLang's own, and the text says what the option is — a
        // display default the program may override — never "significant digits".
        Assert.Contains($"from 0 through {RunOptions.MaxDisplayDecimals}.", help);
        Assert.Contains("DisplayDecimals property overrides", help);
        Assert.Contains("Display only", help);
        Assert.DoesNotContain("significant", help, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(2, help.Split("Not valid for check").Length - 1);

        // The layout stays within an 80-column terminal.
        Assert.All(help.Split('\n'), line => Assert.True(line.Length <= 80, $"help line exceeds 80 columns: '{line}'"));
    }

    // ── Process boundary behavior ───────────────────────────────────────────

    [Fact]
    public async Task UnexpectedException_IsSummarizedWithoutAStackTrace()
    {
        var error = new StringWriter();
        var exception = new InvalidOperationException("simulated\r\ninternal failure");

        var exitCode = await CliApplication.RunAsync(
            ["--help"],
            new ThrowingTextWriter(exception),
            error);

        Assert.Equal(Failure, exitCode);
        Assert.Equal("katlang: unexpected error: simulated internal failure", error.ToString().Trim());
        Assert.DoesNotContain(nameof(InvalidOperationException), error.ToString());
        Assert.DoesNotContain(" at ", error.ToString());
    }

    [Fact]
    public async Task RequestedCancellation_IsReportedCleanly()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var output = new StringWriter();
        var error = new StringWriter();

        var exitCode = await CliApplication.RunAsync(
            ["eval", "42"],
            output,
            error,
            cancellationToken: cancellation.Token);

        Assert.Equal(Failure, exitCode);
        Assert.Equal("", output.ToString());
        Assert.Equal("katlang: cancelled.", error.ToString().Trim());
    }

    /// <summary>
    /// The package/product version of the assembly that defines
    /// <paramref name="type"/>. The SDK may append source-revision build
    /// metadata, which is deliberately not part of the package version.
    /// </summary>
    private static string ProductVersionOf(Type type)
    {
        var informational = type.Assembly
            .GetCustomAttribute<AssemblyInformationalVersionAttribute>()
            ?.InformationalVersion;
        if (!string.IsNullOrWhiteSpace(informational))
        {
            var metadata = informational.IndexOf('+');
            return metadata >= 0 ? informational[..metadata] : informational;
        }

        return type.Assembly.GetName().Version!.ToString(3);
    }

    private const string IntendedVersionKey = "IntendedKatLangVersion";

    /// <summary>
    /// The KatLang version this build intends to ship, compiled into THIS
    /// assembly from $(KatLangVersion). Reading it off the test assembly - not
    /// off KatLang.dll - is what makes it an oracle rather than an echo.
    /// </summary>
    private static string IntendedKatLangVersion => ReadIntendedKatLangVersion();

    private static string ReadIntendedKatLangVersion()
    {
        var version = typeof(CliApplicationTests).Assembly
            .GetCustomAttributes<AssemblyMetadataAttribute>()
            .SingleOrDefault(metadata => metadata.Key == IntendedVersionKey)
            ?.Value;

        // Deliberately no literal fallback. An absent or empty value means the
        // build metadata stopped flowing - a dropped KatLangVersion.props
        // import, a renamed property - and substituting a hard-coded number
        // here would silently restore the hand-synchronized version drift this
        // metadata exists to remove.
        if (string.IsNullOrWhiteSpace(version))
        {
            throw new InvalidOperationException(
                $"This test assembly carries no '{IntendedVersionKey}' assembly metadata, so the " +
                "CLI version contract has no build-time expectation to check against. " +
                "KatLang.CLI.Tests.csproj must import KatLangVersion.props and emit " +
                "$(KatLangVersion) as AssemblyMetadata.");
        }

        return version;
    }

    private sealed class ThrowingTextWriter(Exception exception) : StringWriter
    {
        public override void WriteLine(string? value) => throw exception;
    }
}
