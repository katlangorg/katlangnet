using System.Net;
using System.Net.Sockets;
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
        Assert.Contains("--version", result.TrimmedOutput);
        Assert.Contains("--help", result.TrimmedOutput);
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
        // tracking the runtime actually executing. VersionOf reads the assembly
        // identity - a different metadata source than the informational version
        // the CLI renders - so it is an independent oracle, not a copy of the
        // implementation. Whether that runtime is the INTENDED one is a
        // separate question, checked below against build metadata.
        Assert.Equal($"KatLang {VersionOf(typeof(KatLangEngine))}", result.TrimmedOutput);
    }

    /// <summary>
    /// The release invariant behind the single reported number: one MSBuild
    /// property (KatLangVersion, owned by KatLangVersion.props) versions both
    /// the CLI and the KatLang library, so the CLI can identify itself by the
    /// runtime it carries. If either project stops reading that property, the
    /// two assemblies desynchronize and this fails.
    /// </summary>
    [Fact]
    public void CliAssemblyVersion_EqualsTheLoadedKatLangRuntimeVersion()
    {
        Assert.Equal(VersionOf(typeof(KatLangEngine)), VersionOf(typeof(CliApplication)));
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

    [Fact]
    public async Task HttpDownloader_RefusesRedirectsBeforeFetchingTheirDestination()
    {
        await using var destination = new SingleResponseHttpServer(
            () => SingleResponseHttpServer.Ok("public Value = 42"));
        await using var origin = new SingleResponseHttpServer(
            () => SingleResponseHttpServer.Redirect(destination.Url("localhost")));

        var exception = await Assert.ThrowsAsync<HttpRequestException>(async () =>
            await HttpSourceDownloader.DownloadAsync(origin.Url("127.0.0.1"), CancellationToken.None));

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
    /// The three-part version of the assembly that defines <paramref name="type"/>,
    /// taken from its assembly identity.
    /// </summary>
    private static string VersionOf(Type type)
        => type.Assembly.GetName().Version!.ToString(3);

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

    /// <summary>
    /// One-request loopback HTTP endpoint. It keeps the redirect test entirely
    /// offline while exercising the downloader's real process-wide HttpClient.
    /// </summary>
    private sealed class SingleResponseHttpServer : IAsyncDisposable
    {
        private readonly TcpListener _listener = new(IPAddress.Loopback, 0);
        private readonly CancellationTokenSource _cancellation = new();
        private readonly Func<string> _response;
        private readonly Task _serverTask;
        private int _requestCount;

        public SingleResponseHttpServer(Func<string> response)
        {
            _response = response;
            _listener.Start();
            _serverTask = ServeOneAsync();
        }

        public int RequestCount => Volatile.Read(ref _requestCount);

        public string Url(string host)
        {
            var endpoint = (IPEndPoint)_listener.LocalEndpoint;
            return $"http://{host}:{endpoint.Port}/module.kat";
        }

        public static string Ok(string content)
        {
            var length = Encoding.UTF8.GetByteCount(content);
            return $"HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: {length}\r\nConnection: close\r\n\r\n{content}";
        }

        public static string Redirect(string location)
            => $"HTTP/1.1 302 Found\r\nLocation: {location}\r\nContent-Length: 0\r\nConnection: close\r\n\r\n";

        public async ValueTask DisposeAsync()
        {
            await _cancellation.CancelAsync();
            _listener.Stop();

            try
            {
                await _serverTask;
            }
            catch (Exception ex) when (ex is OperationCanceledException or SocketException or ObjectDisposedException)
            {
                // A destination that was correctly never requested is still
                // blocked in AcceptTcpClientAsync when the fixture is disposed.
            }

            _cancellation.Dispose();
        }

        private async Task ServeOneAsync()
        {
            using var client = await _listener.AcceptTcpClientAsync(_cancellation.Token);
            Interlocked.Increment(ref _requestCount);

            await using var stream = client.GetStream();
            var buffer = new byte[1024];
            var request = new StringBuilder();

            while (!request.ToString().Contains("\r\n\r\n", StringComparison.Ordinal))
            {
                var read = await stream.ReadAsync(buffer, _cancellation.Token);
                if (read == 0)
                    break;

                request.Append(Encoding.ASCII.GetString(buffer, 0, read));
                if (request.Length > 16 * 1024)
                    throw new InvalidOperationException("Loopback test request headers were unexpectedly large.");
            }

            var response = Encoding.UTF8.GetBytes(_response());
            await stream.WriteAsync(response, _cancellation.Token);
        }
    }
}
