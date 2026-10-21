using System.Diagnostics;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace KatLang.Tests.Infrastructure;

/// <summary>
/// SEC-06: the fuzz launcher obtains its SharpFuzz instrumenter ONLY as the repository-local
/// tool pinned in <c>dotnet-tools.json</c>. It never installs a global tool, never resolves a
/// <c>sharpfuzz</c> executable through <c>PATH</c>, and never falls back to one when restore or
/// instrumentation fails.
///
/// <para>The source checks run everywhere. The process checks run the real
/// <c>scripts/fuzz-parser.ps1</c> under Windows PowerShell 5.1 (its supported host) inside a
/// sandbox whose path contains spaces, with <c>PATH</c> reduced to fake <c>dotnet</c>,
/// <c>wsl</c>, and global <c>sharpfuzz</c> commands that only log their invocation. They are
/// Windows-only because the launcher is; elsewhere they return without running.</para>
/// </summary>
public class FuzzToolingPolicyTests
{
    private const string ManifestPath = "dotnet-tools.json";
    private const string LauncherPath = "scripts/fuzz-parser.ps1";
    private const string ReadmePath = "fuzz/README.md";
    private const string HarnessProjectPath = "fuzz/KatLang.ParserFuzz/KatLang.ParserFuzz.csproj";
    private const string PinnedSharpFuzzVersion = "2.3.0";
    private const string GlobalMarker = "GLOBAL-SHARPFUZZ";

    // ---- T1/T2: manifest ----------------------------------------------------------------

    [Fact]
    public void Manifest_PinsSharpFuzzCommandLineExactly()
    {
        using var manifest = JsonDocument.Parse(Text(ManifestPath));
        var root = manifest.RootElement;
        Assert.Equal(1, root.GetProperty("version").GetInt32());
        Assert.True(root.GetProperty("isRoot").GetBoolean());

        var tool = root.GetProperty("tools").GetProperty("sharpfuzz.commandline");
        var version = tool.GetProperty("version").GetString();
        Assert.Equal(PinnedSharpFuzzVersion, version);
        Assert.Matches(@"^\d+\.\d+\.\d+$", version!);
        Assert.Equal(new[] { "sharpfuzz" }, tool.GetProperty("commands").EnumerateArray().Select(c => c.GetString()!).ToArray());
        Assert.False(tool.GetProperty("rollForward").GetBoolean());
    }

    [Fact]
    public void Manifest_PreservesStrykerEntry()
    {
        using var manifest = JsonDocument.Parse(Text(ManifestPath));
        var tool = manifest.RootElement.GetProperty("tools").GetProperty("dotnet-stryker");
        Assert.Equal("4.16.0", tool.GetProperty("version").GetString());
        Assert.Equal(new[] { "dotnet-stryker" }, tool.GetProperty("commands").EnumerateArray().Select(c => c.GetString()!).ToArray());
        Assert.False(tool.GetProperty("rollForward").GetBoolean());
    }

    [Fact]
    public void Manifest_IsTheOnlyRepositoryRootManifest()
    {
        // `dotnet tool run` prefers <dir>/.config/dotnet-tools.json over <dir>/dotnet-tools.json,
        // so a second manifest at the root would silently change which pin the launcher uses.
        Assert.False(File.Exists(Absolute(".config/dotnet-tools.json")));
    }

    [Fact]
    public void Manifest_CommandLinePinMatchesHarnessLibraryVersion()
    {
        var project = XDocument.Parse(Text(HarnessProjectPath));
        var reference = Assert.Single(project.Descendants("PackageReference"),
            e => (string?)e.Attribute("Include") == "SharpFuzz");
        Assert.Equal(PinnedSharpFuzzVersion, (string?)reference.Attribute("Version"));
    }

    // ---- T3/T4/T5: launcher source --------------------------------------------------------

    [Fact]
    public void Launcher_NeverInstallsGloballyOrEditsPath()
    {
        var code = LauncherCode();
        Assert.DoesNotMatch(@"(?i)\btool\s+install\b", code);
        Assert.DoesNotMatch(@"(?i)--global\b", code);
        Assert.DoesNotMatch(@"(?i)\.dotnet[\\/]tools", code);
        Assert.DoesNotMatch(@"(?i)\$env:PATH\s*=", code);
        Assert.DoesNotMatch(@"(?i)SetEnvironmentVariable\(\s*'PATH'", code);
    }

    [Fact]
    public void Launcher_NeverDiscoversSharpFuzzThroughPath()
    {
        var code = LauncherCode();
        Assert.DoesNotMatch(@"(?i)Get-Command\s+sharpfuzz", code);
        Assert.DoesNotMatch(@"(?i)Get-Command\b[^\r\n]*sharpfuzz", code);
        // The only invocation of sharpfuzz is through `dotnet tool run`.
        var invocations = Regex.Matches(code, @"(?i)sharpfuzz\s+\$targetDll");
        var invocation = Assert.Single(invocations.Cast<Match>());
        Assert.Matches(@"(?i)&\s*dotnet\s+tool\s+run\s+$", code[..invocation.Index]);
        Assert.DoesNotMatch(@"(?im)^\s*&\s*sharpfuzz\b", code);
    }

    [Fact]
    public void Launcher_RestoresFromTheRepositoryManifest()
    {
        var code = LauncherCode();
        Assert.Contains("$toolManifest = Join-Path $repoRoot 'dotnet-tools.json'", code, StringComparison.Ordinal);
        Assert.Contains("& dotnet tool restore --tool-manifest $toolManifest", code, StringComparison.Ordinal);
        Assert.Contains("& dotnet tool run sharpfuzz $targetDll", code, StringComparison.Ordinal);
    }

    // ---- T12: documentation ---------------------------------------------------------------

    [Fact]
    public void Readme_DescribesOnlyTheLocalTool()
    {
        var readme = Text(ReadmePath);
        Assert.DoesNotMatch(@"(?i)tool\s+install\s+(--global|-g)\b", readme);
        Assert.DoesNotMatch(@"(?im)^\s*sharpfuzz\s", readme);
        Assert.DoesNotContain("global tool (installs", readme, StringComparison.Ordinal);
        Assert.Contains("dotnet tool restore", readme, StringComparison.Ordinal);
        Assert.Contains("dotnet tool run sharpfuzz", readme, StringComparison.Ordinal);
        Assert.Contains("`2.3.0`", readme, StringComparison.Ordinal);
    }

    // ---- T5/T8/T9/T10: successful instrumentation ------------------------------------------

    [Fact]
    public void Process_InstrumentsThroughTheLocalToolFromTheRepositoryRoot()
    {
        if (!OperatingSystem.IsWindows())
            return;

        using var sandbox = new LauncherSandbox();
        var run = sandbox.Run(skipBuild: false);

        Assert.True(run.ExitCode == 0, run.Describe());
        Assert.DoesNotContain("THROWN:", run.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(GlobalMarker, run.Log, StringComparison.Ordinal);

        var dotnet = run.LogLines.Where(l => l.StartsWith("dotnet ", StringComparison.Ordinal)).ToList();
        var restore = $"dotnet [{sandbox.RepoRoot}] tool restore --tool-manifest \"{sandbox.ManifestPath}\"";
        var publish = dotnet.FindIndex(l => l.Contains(" publish ", StringComparison.Ordinal));
        var instrument = $"dotnet [{sandbox.RepoRoot}] tool run sharpfuzz \"{sandbox.TargetDll}\"";

        // Restore, publish, instrument, in that order, each exactly once; both tool steps run
        // from the repository root although the caller started elsewhere, and the path with
        // spaces reaches the tool as one quoted argument, unchanged.
        Assert.Equal(3, dotnet.Count);
        Assert.Equal(restore, dotnet[0]);
        Assert.Equal(1, publish);
        Assert.Equal(instrument, dotnet[2]);

        var campaign = run.LogLines.FindIndex(l => l.StartsWith("wsl ", StringComparison.Ordinal) && l.Contains(" bash ", StringComparison.Ordinal));
        Assert.True(campaign > run.LogLines.IndexOf(instrument), run.Describe());

        // The caller's location is restored after the script's Push-Location/Pop-Location.
        Assert.Contains($"LOCATION={sandbox.CallerDirectory}", run.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void Process_SecondRunRestoresAgainWithoutGlobalInstall()
    {
        if (!OperatingSystem.IsWindows())
            return;

        using var sandbox = new LauncherSandbox();
        var first = sandbox.Run(skipBuild: false);
        var second = sandbox.Run(skipBuild: false);

        Assert.True(first.ExitCode == 0, first.Describe());
        Assert.True(second.ExitCode == 0, second.Describe());
        Assert.DoesNotContain(GlobalMarker, second.Log, StringComparison.Ordinal);
        Assert.DoesNotContain(" install", second.Log, StringComparison.Ordinal);
        Assert.Single(second.LogLines, l => l.Contains(" tool restore --tool-manifest ", StringComparison.Ordinal));
        Assert.Single(second.LogLines, l => l.Contains(" tool run sharpfuzz ", StringComparison.Ordinal));
    }

    // ---- T6: restore failure --------------------------------------------------------------

    [Fact]
    public void Process_RestoreFailureStopsBeforePublishInstrumentationAndCampaign()
    {
        if (!OperatingSystem.IsWindows())
            return;

        using var sandbox = new LauncherSandbox();
        var run = sandbox.Run(skipBuild: false, restoreExit: 3);

        Assert.True(run.ExitCode != 0, run.Describe());
        Assert.Contains("Local tool restore failed (exit 3)", run.Output, StringComparison.Ordinal);
        Assert.Single(run.LogLines, l => l.Contains(" tool restore ", StringComparison.Ordinal));
        Assert.DoesNotContain(" publish ", run.Log, StringComparison.Ordinal);
        Assert.DoesNotContain("sharpfuzz \"", run.Log, StringComparison.Ordinal);
        Assert.DoesNotContain(" bash ", run.Log, StringComparison.Ordinal);
        Assert.DoesNotContain(GlobalMarker, run.Log, StringComparison.Ordinal);
        Assert.Contains($"LOCATION={sandbox.CallerDirectory}", run.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void Process_RestoreFailureExitsNonZeroWhenRunAsAFile()
    {
        if (!OperatingSystem.IsWindows())
            return;

        using var sandbox = new LauncherSandbox();
        var run = sandbox.RunFile(restoreExit: 1);

        Assert.True(run.ExitCode != 0, run.Describe());
        Assert.Contains("Local tool restore failed", run.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(" bash ", run.Log, StringComparison.Ordinal);
        Assert.DoesNotContain(GlobalMarker, run.Log, StringComparison.Ordinal);
    }

    // ---- T7: instrumentation failure --------------------------------------------------------

    [Fact]
    public void Process_InstrumentationFailureStopsBeforeCampaignWithoutFallback()
    {
        if (!OperatingSystem.IsWindows())
            return;

        using var sandbox = new LauncherSandbox();
        var run = sandbox.Run(skipBuild: false, sharpFuzzExit: 7);

        Assert.True(run.ExitCode != 0, run.Describe());
        Assert.Contains("sharpfuzz instrumentation failed (exit 7)", run.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("Local tool restore failed", run.Output, StringComparison.Ordinal);
        Assert.Single(run.LogLines, l => l.Contains(" tool run sharpfuzz ", StringComparison.Ordinal));
        Assert.DoesNotContain(" bash ", run.Log, StringComparison.Ordinal);
        Assert.DoesNotContain(GlobalMarker, run.Log, StringComparison.Ordinal);
        Assert.Contains($"LOCATION={sandbox.CallerDirectory}", run.Output, StringComparison.Ordinal);
    }

    // ---- T11: -SkipBuild --------------------------------------------------------------------

    [Fact]
    public void Process_SkipBuildNeitherRestoresNorInstruments()
    {
        if (!OperatingSystem.IsWindows())
            return;

        using var sandbox = new LauncherSandbox();
        sandbox.CreatePublishedTarget();
        // A restore that would fail proves -SkipBuild does not attempt one.
        var run = sandbox.Run(skipBuild: true, restoreExit: 9, sharpFuzzExit: 9);

        Assert.True(run.ExitCode == 0, run.Describe());
        Assert.DoesNotContain("dotnet ", run.Log, StringComparison.Ordinal);
        Assert.DoesNotContain(GlobalMarker, run.Log, StringComparison.Ordinal);
        Assert.Single(run.LogLines, l => l.StartsWith("wsl ", StringComparison.Ordinal) && l.Contains(" bash ", StringComparison.Ordinal));
    }

    [Fact]
    public void Process_SkipBuildStillRequiresAnExistingPublish()
    {
        if (!OperatingSystem.IsWindows())
            return;

        using var sandbox = new LauncherSandbox();
        var run = sandbox.Run(skipBuild: true);

        Assert.True(run.ExitCode != 0, run.Describe());
        Assert.Contains("-SkipBuild set but no publish found", run.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet ", run.Log, StringComparison.Ordinal);
        Assert.DoesNotContain(" bash ", run.Log, StringComparison.Ordinal);
    }

    // ---- helpers ----------------------------------------------------------------------------

    /// <summary>The launcher without its comments, so prose about the old behavior cannot hide or fake code.</summary>
    private static string LauncherCode()
    {
        var source = Text(LauncherPath);
        source = Regex.Replace(source, @"<#.*?#>", "", RegexOptions.Singleline);
        return string.Join('\n', source.Split('\n').Select(line => Regex.Replace(line, @"^\s*#.*$", "")));
    }

    private static string Text(string relativePath)
        => File.ReadAllText(Absolute(relativePath)).ReplaceLineEndings("\n");

    private static string Absolute(string relativePath)
        => Path.Combine(RepoRoot.Find(), relativePath.Replace('/', Path.DirectorySeparatorChar));

    private sealed record LauncherRun(int ExitCode, string Output, string Log)
    {
        public List<string> LogLines { get; } =
            Log.ReplaceLineEndings("\n").Split('\n', StringSplitOptions.RemoveEmptyEntries).Select(l => l.TrimEnd()).ToList();

        public string Describe() => $"exit {ExitCode}\n--- output ---\n{Output}\n--- command log ---\n{Log}";
    }

    /// <summary>
    /// A copy of the launcher and manifest in a directory with spaces, plus fake commands. The
    /// fake <c>dotnet</c> and <c>wsl</c> log "name [working directory] arguments" and return the
    /// configured exit codes; the fake <c>sharpfuzz</c> sits both first on PATH and in the
    /// sandboxed user's <c>.dotnet\tools</c> and logs a marker that must never appear.
    /// </summary>
    private sealed class LauncherSandbox : IDisposable
    {
        private readonly string _root;
        private readonly string _bin;
        private readonly string _profile;
        private readonly string _log;

        public LauncherSandbox()
        {
            _root = Path.Combine(Path.GetTempPath(), $"katlang sec06 {Guid.NewGuid():N}");
            RepoRoot = Path.Combine(_root, "repo with spaces");
            CallerDirectory = Path.Combine(_root, "caller dir");
            _bin = Path.Combine(_root, "fake bin");
            _profile = Path.Combine(_root, "profile");
            _log = Path.Combine(_root, "commands.log");

            var source = FuzzToolingPolicyTests.RepoRootPath();
            Directory.CreateDirectory(Path.Combine(RepoRoot, "scripts"));
            Directory.CreateDirectory(Path.Combine(RepoRoot, "fuzz", "KatLang.ParserFuzz", "Testcases"));
            Directory.CreateDirectory(CallerDirectory);
            Directory.CreateDirectory(_bin);
            Directory.CreateDirectory(Path.Combine(_profile, ".dotnet", "tools"));
            File.Copy(Path.Combine(source, "scripts", "fuzz-parser.ps1"), LauncherScript);
            File.Copy(Path.Combine(source, "dotnet-tools.json"), ManifestPath);
            File.WriteAllText(Path.Combine(RepoRoot, "fuzz", "katlang.dict"), "");
            File.WriteAllText(Path.Combine(RepoRoot, "fuzz", "run-campaign.sh"), "");

            WriteCmd(Path.Combine(_bin, "dotnet.cmd"),
                "@echo off",
                ">>\"%SEC06_LOG%\" echo dotnet [%CD%] %*",
                "if /i \"%~1 %~2\"==\"tool restore\" exit /b %SEC06_RESTORE_EXIT%",
                "if /i \"%~1 %~2 %~3\"==\"tool run sharpfuzz\" exit /b %SEC06_SHARPFUZZ_EXIT%",
                "exit /b 0");
            WriteCmd(Path.Combine(_bin, "wsl.cmd"),
                "@echo off",
                ">>\"%SEC06_LOG%\" echo wsl [%CD%] %*",
                "if /i \"%~2\"==\"wslpath\" echo /mnt/fake",
                "exit /b 0");
            var global = new[] { "@echo off", $">>\"%SEC06_LOG%\" echo {GlobalMarker} %*", "exit /b 0" };
            WriteCmd(Path.Combine(_bin, "sharpfuzz.cmd"), global);
            WriteCmd(Path.Combine(_profile, ".dotnet", "tools", "sharpfuzz.cmd"), global);
        }

        public string RepoRoot { get; }
        public string CallerDirectory { get; }
        public string LauncherScript => Path.Combine(RepoRoot, "scripts", "fuzz-parser.ps1");
        public string ManifestPath => Path.Combine(RepoRoot, "dotnet-tools.json");
        public string TargetDll => Path.Combine(RepoRoot, "fuzz", "artifacts", "publish-linux", "KatLang.dll");

        public void CreatePublishedTarget()
        {
            Directory.CreateDirectory(Path.GetDirectoryName(TargetDll)!);
            File.WriteAllText(TargetDll, "");
        }

        /// <summary>Runs the launcher from <see cref="CallerDirectory"/> and reports the location afterwards.</summary>
        public LauncherRun Run(bool skipBuild, int restoreExit = 0, int sharpFuzzExit = 0)
        {
            var command = string.Join("\n",
                "$ErrorActionPreference = 'Stop'",
                $"Set-Location -LiteralPath {Quote(CallerDirectory)}",
                "$params = @{ MaxTotalTime = 1 }",
                skipBuild ? "$params.SkipBuild = $true" : "",
                "$code = 0",
                $"try {{ & {Quote(LauncherScript)} @params; $code = $LASTEXITCODE }}",
                "catch { Write-Output ('THROWN: ' + $_.Exception.Message); $code = 1 }",
                "Write-Output ('LOCATION=' + (Get-Location).Path)",
                "exit $code");
            var encoded = Convert.ToBase64String(Encoding.Unicode.GetBytes(command));
            return Start(["-NoProfile", "-NonInteractive", "-ExecutionPolicy", "Bypass", "-EncodedCommand", encoded],
                restoreExit, sharpFuzzExit);
        }

        /// <summary>Runs the launcher the documented way, as a file, to observe the real process exit code.</summary>
        public LauncherRun RunFile(int restoreExit = 0, int sharpFuzzExit = 0)
            => Start(["-NoProfile", "-NonInteractive", "-ExecutionPolicy", "Bypass", "-File", LauncherScript, "-MaxTotalTime", "1"],
                restoreExit, sharpFuzzExit);

        private LauncherRun Start(string[] arguments, int restoreExit, int sharpFuzzExit)
        {
            if (File.Exists(_log))
                File.Delete(_log);

            var system = Environment.SystemDirectory;
            var powershell = Path.Combine(system, "WindowsPowerShell", "v1.0", "powershell.exe");
            var start = new ProcessStartInfo(powershell)
            {
                UseShellExecute = false,
                CreateNoWindow = true,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                WorkingDirectory = CallerDirectory,
            };
            foreach (var argument in arguments)
                start.ArgumentList.Add(argument);

            // Only the fakes and the OS are reachable: a real dotnet, wsl, or sharpfuzz cannot run.
            start.Environment["PATH"] = string.Join(';', _bin, system, Path.Combine(system, "WindowsPowerShell", "v1.0"));
            start.Environment["USERPROFILE"] = _profile;
            start.Environment["SEC06_LOG"] = _log;
            start.Environment["SEC06_RESTORE_EXIT"] = restoreExit.ToString(System.Globalization.CultureInfo.InvariantCulture);
            start.Environment["SEC06_SHARPFUZZ_EXIT"] = sharpFuzzExit.ToString(System.Globalization.CultureInfo.InvariantCulture);
            // A PowerShell 7 module path breaks Windows PowerShell 5.1's own module loading.
            start.Environment.Remove("PSModulePath");
            start.Environment.Remove("WSLENV");
            start.Environment.Remove("KATLANG_FUZZ_MODE");
            start.Environment.Remove("KATLANG_FUZZ_SEED");

            using var process = Process.Start(start)!;
            var stderr = process.StandardError.ReadToEndAsync();
            var stdout = process.StandardOutput.ReadToEndAsync();
            if (!process.WaitForExit(TimeSpan.FromSeconds(120)))
            {
                process.Kill(entireProcessTree: true);
                throw new TimeoutException("fuzz-parser.ps1 did not finish within 120 s.");
            }

            var log = File.Exists(_log) ? File.ReadAllText(_log) : "";
            return new LauncherRun(process.ExitCode,
                stdout.GetAwaiter().GetResult() + "\n" + stderr.GetAwaiter().GetResult(), log);
        }

        private static string Quote(string path) => "'" + path.Replace("'", "''") + "'";

        private static void WriteCmd(string path, params string[] lines)
            => File.WriteAllText(path, string.Join("\r\n", lines) + "\r\n", Encoding.ASCII);

        public void Dispose()
        {
            try
            {
                Directory.Delete(_root, recursive: true);
            }
            catch (IOException)
            {
            }
            catch (UnauthorizedAccessException)
            {
            }
        }
    }

    private static string RepoRootPath() => KatLang.TestInfrastructure.RepoRoot.Find();
}
