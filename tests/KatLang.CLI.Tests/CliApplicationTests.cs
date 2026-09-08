using System.Reflection;

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
        // The transport bounds the help quotes must be the ones actually enforced.
        Assert.Contains($"{HttpSourceDownloader.DownloadTimeout.TotalSeconds:0} seconds", result.TrimmedOutput);
        Assert.Contains($"1 MiB ({HttpSourceDownloader.MaxResponseBodyBytes.ToString("N0", System.Globalization.CultureInfo.InvariantCulture)} content", result.TrimmedOutput);
        Assert.Contains("bytes), excluding HTTP headers and chunk framing.", result.TrimmedOutput);
        Assert.Contains("--version", result.TrimmedOutput);
        Assert.Contains("--help", result.TrimmedOutput);
    }

    [Fact]
    public void Readme_ReportsTheShippedTransportBounds()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "KatLang.slnx")))
            directory = directory.Parent;
        Assert.NotNull(directory);

        var readme = File.ReadAllText(Path.Combine(directory.FullName, "README.md"));
        Assert.Contains($"1 MiB ({HttpSourceDownloader.MaxResponseBodyBytes.ToString("N0", System.Globalization.CultureInfo.InvariantCulture)} content bytes)", readme);
        Assert.Contains($"{HttpSourceDownloader.DownloadTimeout.TotalSeconds:0}-second cancellation deadline", readme);
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
        Assert.Contains("Unexpected token", result.TrimmedError);
        // KatLang's source location is preserved, not rewritten away.
        Assert.Matches(@"^\[\d+:\d+\] ", result.TrimmedError);
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
        Assert.Contains("Unexpected token", result.TrimmedError);
        Assert.Matches(@"^\[\d+:\d+\] ", result.TrimmedError);
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
