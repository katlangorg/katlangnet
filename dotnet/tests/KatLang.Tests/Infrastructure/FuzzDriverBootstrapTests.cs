using System.Diagnostics;
using System.Text.RegularExpressions;
using Xunit.Abstractions;

namespace KatLang.Tests.Infrastructure;

/// <summary>
/// SEC-05: the native libFuzzer driver is built only from the reviewed upstream commit pinned in
/// <c>fuzz/libfuzzer-driver.sh</c>, after its source matches the pinned SHA-256, and a cached
/// driver is reused only after its identity and integrity are re-checked.
///
/// <para>The source checks run everywhere. The behavioral check runs the offline Bash suite
/// <c>fuzz/tests/libfuzzer-driver.tests.sh</c> (fake curl/clang, no network, no real cache):
/// directly under Bash on Linux or through WSL on Windows. Missing execution support fails
/// the check explicitly so an unexecuted security suite cannot be reported as passed.</para>
/// </summary>
public class FuzzDriverBootstrapTests
{
    private const string BootstrapPath = "fuzz/libfuzzer-driver.sh";
    private const string RunnerPath = "fuzz/run-campaign.sh";
    private const string ReadmePath = "fuzz/README.md";
    private const string SuitePath = "fuzz/tests/libfuzzer-driver.tests.sh";
    private readonly ITestOutputHelper _output;

    public FuzzDriverBootstrapTests(ITestOutputHelper output) => _output = output;

    [Fact]
    public void Bootstrap_PinsOneFullCommitAndSourceDigest()
    {
        var (commit, digest) = Pin();
        Assert.Matches("^[0-9a-f]{40}$", commit);
        Assert.Matches("^[0-9a-f]{64}$", digest);
        var bootstrap = Text(BootstrapPath);
        Assert.Contains("https://raw.githubusercontent.com/Metalnem/libfuzzer-dotnet/${LIBFUZZER_DOTNET_COMMIT}/${SOURCE_NAME}",
            bootstrap, StringComparison.Ordinal);
    }

    [Fact]
    public void Readme_DocumentsTheSamePin()
    {
        var (commit, digest) = Pin();
        var readme = Text(ReadmePath);
        Assert.Contains($"| Commit | `{commit}` |", readme, StringComparison.Ordinal);
        Assert.Contains($"| SHA-256 | `{digest}` |", readme, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(BootstrapPath)]
    [InlineData(RunnerPath)]
    [InlineData(ReadmePath)]
    public void NoMutableUpstreamReferenceOrUnverifiedBuild(string path)
    {
        var text = Text(path);
        Assert.DoesNotContain("libfuzzer-dotnet/master", text, StringComparison.Ordinal);
        Assert.DoesNotContain("libfuzzer-dotnet/main", text, StringComparison.Ordinal);
        if (path == BootstrapPath)
            return;
        // Only the bootstrap downloads or compiles the driver: no runner code line and no documented
        // command line does either (README prose may still name the tools).
        Assert.DoesNotMatch(path == RunnerPath ? @"(?m)^[^#\r\n]*\b(curl|clang)\b" : @"(?m)^\s*(curl|clang)\s", text);
    }

    [Fact]
    public void Runner_TakesTheDriverOnlyFromTheBootstrap()
    {
        var runner = Text(RunnerPath);
        Assert.Contains("if ! DRIVER=$(bash \"$SCRIPT_DIR/libfuzzer-driver.sh\" \"$DRIVER_DIR\"); then", runner, StringComparison.Ordinal);
        Assert.DoesNotContain("[ ! -x \"$DRIVER\" ]", runner, StringComparison.Ordinal);
        Assert.Single(Regex.Matches(runner, @"(?m)^DRIVER=|DRIVER=\$\("));
    }

    [Fact]
    public void OfflineSecuritySuitePasses()
    {
        var suite = Absolute(SuitePath);
        ProcessStartInfo start;
        if (OperatingSystem.IsLinux())
        {
            start = new ProcessStartInfo("bash");
            start.ArgumentList.Add(suite);
        }
        else if (OperatingSystem.IsWindows())
        {
            var wslSuite = WslPath(suite);
            Assert.True(wslSuite is not null,
                "SEC-05 security suite was not executed: install/enable a WSL distro with Bash, or run these tests on Linux.");
            start = new ProcessStartInfo("wsl");
            start.ArgumentList.Add("-e");
            start.ArgumentList.Add("bash");
            start.ArgumentList.Add(wslSuite);
        }
        else
        {
            Assert.Fail("SEC-05 security suite was not executed: it requires Linux Bash or WSL on Windows.");
            return;
        }

        var (exit, output) = Run(start, TimeSpan.FromMinutes(3));
        _output.WriteLine(output);
        Assert.True(exit == 0, $"exit {exit}\n{output}");
        Assert.Matches(@"(?m)^ALL \d+ CHECKS PASSED\s*$", output);
    }

    private static (string Commit, string Digest) Pin()
    {
        var bootstrap = Text(BootstrapPath);
        var commit = Assert.Single(Regex.Matches(bootstrap, @"(?m)^LIBFUZZER_DOTNET_COMMIT=(\S*)$"));
        var digest = Assert.Single(Regex.Matches(bootstrap, @"(?m)^LIBFUZZER_DOTNET_SHA256=(\S*)$"));
        return (commit.Groups[1].Value, digest.Groups[1].Value);
    }

    private static string? WslPath(string windowsPath)
    {
        try
        {
            var start = new ProcessStartInfo("wsl");
            foreach (var argument in new[] { "-e", "wslpath", "-a", "-u", windowsPath })
                start.ArgumentList.Add(argument);
            var (exit, output) = Run(start, TimeSpan.FromSeconds(60));
            var path = output.Trim();
            return exit == 0 && path.StartsWith('/') ? path.Split('\n')[0].Trim() : null;
        }
        catch (System.ComponentModel.Win32Exception)
        {
            return null;
        }
    }

    private static (int Exit, string Output) Run(ProcessStartInfo start, TimeSpan limit)
    {
        start.UseShellExecute = false;
        start.CreateNoWindow = true;
        start.RedirectStandardOutput = true;
        start.RedirectStandardError = true;
        using var process = Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        if (!process.WaitForExit(limit))
        {
            process.Kill(entireProcessTree: true);
            throw new TimeoutException($"{start.FileName} did not finish within {limit}.");
        }

        return (process.ExitCode, stdout.GetAwaiter().GetResult() + stderr.GetAwaiter().GetResult());
    }

    private static string Text(string relativePath) => File.ReadAllText(Absolute(relativePath));

    private static string Absolute(string relativePath)
        => Path.Combine(KatLang.TestInfrastructure.RepoRoot.Find(), relativePath.Replace('/', Path.DirectorySeparatorChar));
}
