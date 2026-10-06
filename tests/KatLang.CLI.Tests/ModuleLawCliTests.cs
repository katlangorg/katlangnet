namespace KatLang.CLI.Tests;

/// <summary>
/// The open/module law system (Q-19 D-I, Q-29 A-U, Q-31 H-P, Q-32 I-U) at the CLI boundary: <c>check</c> reports the
/// static <c>AmbiguousOpen</c>, <c>eval</c> and <c>run</c> surface the very same error, and loading through
/// <c>--allow-loading</c> observes module hygiene and module identity exactly as the engine does. Only the transport is
/// substituted (<see cref="RecordingDownloader"/>); everything from argument parsing to rendering is the CLI's own.
/// </summary>
public sealed class ModuleLawCliTests
{
    private const int Success = 0;
    private const int Failure = 1;

    private const string AmbiguousSource = "open A, B\nA = { public X = 1 }\nB = { public X = 2 }\nX\n";

    private static RunOptions LoadingOptions(RecordingDownloader downloader)
        => new() { DownloadCode = downloader.DownloadAsync };

    // ── Q-29 A-U: a written ambiguous name is a front-end error ─────────────────────────────

    [Fact]
    public async Task WrittenAmbiguousName_IsReportedByCheck_AndSurfacedIdenticallyByEvalAndRun()
    {
        using var file = new TempSourceFile(AmbiguousSource);

        var check = await Cli.InvokeAsync("check", file.Path);
        var run = await Cli.InvokeAsync("run", file.Path);
        var eval = await Cli.InvokeAsync("eval", AmbiguousSource);

        Assert.Equal(Failure, check.ExitCode);
        Assert.Equal(Failure, run.ExitCode);
        Assert.Equal(Failure, eval.ExitCode);
        Assert.Equal("", check.Output);
        Assert.Equal("", run.Output);
        Assert.Equal("", eval.Output);
        Assert.Equal(
            "[4:1] 'X' is ambiguous: 2 different opened algorithms provide it at the same open level (A, B), so it "
            + "names no single declaration. Qualify it with the algorithm you mean, or open only one of them.",
            check.TrimmedError);
        Assert.Equal(check.TrimmedError, run.TrimmedError);
        Assert.Equal(check.TrimmedError, eval.TrimmedError);

        // The one public code behind that text: the engine's parse failure for the same source.
        var engine = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(AmbiguousSource, new RunOptions()));
        Assert.Equal(KatLangErrorCode.AmbiguousOpen, Assert.Single(engine.Errors).Code);
    }

    [Fact]
    public async Task AnOverlapNobodyWrites_IsValidSource()
    {
        const string source = "open A, B\nA = { public X = 1 }\nB = { public X = 2 }\nA.X + B.X\n";
        using var file = new TempSourceFile(source);

        var check = await Cli.InvokeAsync("check", file.Path);
        var eval = await Cli.InvokeAsync("eval", source);

        Assert.Equal(Success, check.ExitCode);
        Assert.Equal("", check.Error);
        Assert.Equal(Success, eval.ExitCode);
        Assert.Equal("3", eval.TrimmedOutput);
    }

    // ── Q-19 D-I: providers count once per identity ─────────────────────────────────────────

    [Fact]
    public async Task OneDeclarationReachedByTwoSpellings_IsOneProvider()
    {
        const string source =
            "Lib = {\n    public Sub = { public X = 1 }\n    public R = {\n        open Sub, Lib.Sub\n        X\n    }\n}\nLib.R\n";

        var result = await Cli.InvokeAsync("eval", source);

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Error);
        Assert.Equal("1", result.TrimmedOutput);
    }

    // ── Q-31 H-P: a loaded module is rooted at the prelude ──────────────────────────────────

    [Theory]
    [InlineData("open 'https://katlang.org/demo/cli-hygiene.kat'\nsum(xs) = 999\nV\n")]
    [InlineData("open M\nsum(xs) = 999\nM = load('https://katlang.org/demo/cli-hygiene.kat')\nV\n")]
    [InlineData("sum(xs) = 999\nM = load('https://katlang.org/demo/cli-hygiene.kat')\nM.V\n")]
    public async Task ALoadSitesShadowOfABuiltin_NeverReachesTheModule(string source)
    {
        const string url = "https://katlang.org/demo/cli-hygiene.kat";
        var downloader = new RecordingDownloader(new Dictionary<string, string> { [url] = "public V = sum((1, 2))" });

        var result = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "eval", source, "--allow-loading");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Error);
        Assert.Equal("3", result.TrimmedOutput);
        Assert.Equal(url, Assert.Single(downloader.RequestedUrls));
    }

    [Fact]
    public async Task AModulesFreeName_IsItsMembersOwnParameter_NeverTheLoadSitesProperty()
    {
        const string url = "https://katlang.org/demo/cli-free-name.kat";
        var downloader = new RecordingDownloader(new Dictionary<string, string> { [url] = "public G = y + 1" });
        const string source = "y = 100\nM = load('https://katlang.org/demo/cli-free-name.kat')\nM.G(4)\n";
        using var file = new TempSourceFile(source);

        var check = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "check", file.Path, "--allow-loading");
        var run = await Cli.InvokeWithDownloaderAsync(downloader.DownloadAsync, "run", file.Path, "--allow-loading");

        Assert.Equal(Success, check.ExitCode);
        Assert.Equal("", check.Error);
        Assert.Equal(Success, run.ExitCode);
        Assert.Equal("5", run.TrimmedOutput);
    }

    // ── Q-32 I-U: one canonical URL is one module declaration ───────────────────────────────

    [Fact]
    public async Task OneUrlLoadedUnderTwoHolders_IsOneMemberBinding()
    {
        const string url = "https://katlang.org/demo/cli-identity.kat";
        // One draw: the member is one binding with one zero-argument cache entry, whichever holder reaches it.
        var downloader = new RecordingDownloader(new Dictionary<string, string> { [url] = "public V = random(1, 1000000)" });
        const string source =
            "A = { public L = load('https://katlang.org/demo/cli-identity.kat') }\n"
            + "B = { public L = load('https://katlang.org/demo/cli-identity.kat') }\n"
            + "A.L.V == B.L.V\n";

        var result = await Cli.InvokeWithDownloaderAsync(
            downloader.DownloadAsync, "eval", source, "--allow-loading", "--random-seed", "7");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Error);
        Assert.Equal("true", result.TrimmedOutput);
        Assert.Equal(url, Assert.Single(downloader.RequestedUrls));
    }

    [Fact]
    public async Task OneUrlOpenedTwice_IsOneProvider()
    {
        const string url = "https://katlang.org/demo/cli-twice.kat";
        var downloader = new RecordingDownloader(new Dictionary<string, string> { [url] = "public X = 5" });

        var result = await Cli.InvokeWithDownloaderAsync(
            downloader.DownloadAsync, "eval", $"open '{url}', '{url}'\nX\n", "--allow-loading");

        Assert.Equal(Success, result.ExitCode);
        Assert.Equal("", result.Error);
        Assert.Equal("5", result.TrimmedOutput);
    }

    [Fact]
    public async Task TwoModulesProvidingOneWrittenName_AreTheStaticAmbiguity_InCheckAndEval()
    {
        const string first = "https://katlang.org/demo/cli-first.kat";
        const string second = "https://katlang.org/demo/cli-second.kat";
        var modules = new Dictionary<string, string> { [first] = "public X = 1", [second] = "public X = 2" };
        var source = $"open '{first}', '{second}'\nX\n";
        using var file = new TempSourceFile(source);

        var check = await Cli.InvokeWithDownloaderAsync(
            new RecordingDownloader(modules).DownloadAsync, "check", file.Path, "--allow-loading");
        var eval = await Cli.InvokeWithDownloaderAsync(
            new RecordingDownloader(modules).DownloadAsync, "eval", source, "--allow-loading");

        Assert.Equal(Failure, check.ExitCode);
        Assert.Equal(Failure, eval.ExitCode);
        Assert.Equal("", eval.Output);
        // A module's import view is locationless and carries no URL, so its provider renders as the block it is.
        Assert.Equal(
            "[2:1] 'X' is ambiguous: 2 different opened algorithms provide it at the same open level ({...}, {...}), so "
            + "it names no single declaration. Qualify it with the algorithm you mean, or open only one of them.",
            check.TrimmedError);
        Assert.Equal(check.TrimmedError, eval.TrimmedError);

        var engine = Assert.IsType<RunResult.ParseFailure>(
            await KatLangEngine.RunAsync(source, LoadingOptions(new RecordingDownloader(modules))));
        Assert.Equal(KatLangErrorCode.AmbiguousOpen, Assert.Single(engine.Errors).Code);
    }
}
