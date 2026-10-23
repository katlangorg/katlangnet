using System.Diagnostics;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using Xunit;

namespace KatLang.TestInfrastructure;

/// <summary>
/// Strict allocation measurements (exactly zero bytes, an exact byte count, or an equality of two
/// counts) run in ONE child test host per test assembly, started with background GC disabled.
/// <para>
/// <see cref="GC.GetAllocatedBytesForCurrentThread"/> is exact for a quiet thread, but while a
/// background (concurrent) gen2 collection runs, the unused remainder of the measured thread's
/// allocation context can be counted as allocated (dotnet/runtime#134724; proposed fix
/// dotnet/runtime#134855). Other test classes in the same host trigger such collections, so an
/// allocation-free window intermittently read up to one allocation quantum (CI run 39916338803:
/// 7,096 bytes for warmed safe escaping). Measured on .NET 11.0.0-rc.2 linux-x64 and win-x64
/// (CI-REL-1): 63/256 and 69/256 allocation-free windows read 40–7,912 bytes under background
/// collections, and 0/256 did with <c>DOTNET_gcConcurrent=0</c> under ~290–390 blocking gen2
/// collections. Remove this isolation once the pinned runtime contains the upstream fix.
/// </para>
/// <para>
/// A measuring test is a <c>[Fact]</c> whose name ends in <see cref="ChildSuffix"/>. It starts with
/// <c>if (!GcIsolatedAllocation.EnterChild()) return;</c> — in an ordinary run it does nothing —
/// and ends with <see cref="Complete"/>. <see cref="RunChildrenAsync"/> runs every such test of an
/// assembly in the child and requires each one to have completed there, so a measurement can
/// neither skip silently nor pass without executing. Ordinary tests keep the normal GC settings.
/// </para>
/// </summary>
internal static class GcIsolatedAllocation
{
    public const string ChildSuffix = "_GcIsolatedChild";

    /// <summary>Optional directory where <see cref="RunChildrenAsync"/> leaves its diagnostics (set by validate-all.ps1).</summary>
    public const string DiagnosticsDirectoryEnvironment = "KATLANG_TEST_DIAGNOSTICS_DIR";

    private const string ChildEnvironment = "KATLANG_GC_ISOLATED_ALLOCATION_CHILD";
    private const string MarkerFileEnvironment = "KATLANG_GC_ISOLATED_ALLOCATION_MARKER_FILE";
    private static readonly TimeSpan ChildTimeout = TimeSpan.FromSeconds(240);
    private static readonly TimeSpan CleanupTimeout = TimeSpan.FromSeconds(5);
    private static readonly object MarkerGate = new();

    /// <summary>
    /// False in an ordinary run. In the child it verifies that background GC is really off and that
    /// the counter observes a known heap allocation exactly, then returns true.
    /// </summary>
    public static bool EnterChild([CallerMemberName] string test = "")
    {
        if (Environment.GetEnvironmentVariable(ChildEnvironment) != "1")
            return false;

        AppendMarker($"# {test}: {RuntimeInformation.FrameworkDescription} {RuntimeInformation.RuntimeIdentifier}, "
            + $"process {Environment.ProcessId}, thread {Environment.CurrentManagedThreadId}; {GcConfiguration()}");
        Assert.False(
            ConcurrentGcEnabled(),
            "The GC-isolated child must run without background GC; GC configuration: " + GcConfiguration());
        var known = MeasureKnownAllocation();
        // byte[37] is a 24-byte array header plus 37 bytes, rounded to 64 on a 64-bit runtime.
        if (Environment.Is64BitProcess)
            Assert.Equal(64, known);
        else
            Assert.True(known > 0, $"the allocation counter missed a heap allocation ({known} bytes)");
        return true;
    }

    /// <summary>Records that a measuring test ran to completion in the child.</summary>
    public static void Complete([CallerMemberName] string test = "") => AppendMarker(test);

    private static void AppendMarker(string line)
    {
        var marker = Environment.GetEnvironmentVariable(MarkerFileEnvironment);
        Assert.False(string.IsNullOrWhiteSpace(marker), "GC-isolated child has no marker file");
        lock (MarkerGate)
            File.AppendAllText(marker!, line + Environment.NewLine);
    }

    /// <summary>The <see cref="ChildSuffix"/> tests of <paramref name="assembly"/>, as <c>Type.Method</c> full names.</summary>
    public static IReadOnlyList<string> ChildTests(Assembly assembly)
        => assembly.GetTypes()
            .SelectMany(type => type.GetMethods(BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static | BindingFlags.DeclaredOnly)
                .Where(method => method.Name.EndsWith(ChildSuffix, StringComparison.Ordinal)
                    && method.GetCustomAttribute<FactAttribute>() is not null)
                .Select(method => type.FullName + "." + method.Name))
            .Order(StringComparer.Ordinal)
            .ToList();

    /// <summary>
    /// Runs every <see cref="ChildSuffix"/> test of <paramref name="assembly"/> in one child test host
    /// with <c>DOTNET_gcConcurrent=0</c> and requires each to complete. The child's output (and this
    /// host's GC configuration) is kept in <see cref="DiagnosticsDirectoryEnvironment"/> when set.
    /// </summary>
    public static async Task RunChildrenAsync(Assembly assembly)
    {
        var expected = ChildTests(assembly);
        Assert.NotEmpty(expected);
        var markerFile = Path.Combine(Path.GetTempPath(), $"katlang-gc-isolated-{Guid.NewGuid():N}.txt");
        File.WriteAllText(markerFile, "");

        var startInfo = new ProcessStartInfo("dotnet")
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            CreateNoWindow = true,
        };
        startInfo.ArgumentList.Add("vstest");
        startInfo.ArgumentList.Add(assembly.Location);
        startInfo.ArgumentList.Add("--Tests:" + string.Join(",", expected));
        startInfo.Environment[ChildEnvironment] = "1";
        startInfo.Environment[MarkerFileEnvironment] = markerFile;
        startInfo.Environment["DOTNET_gcConcurrent"] = "0";
        startInfo.Environment["DOTNET_NOLOGO"] = "1";

        var watch = Stopwatch.StartNew();
        string stdout, stderr;
        string? cleanupFailure = null;
        int? exitCode = null;
        try
        {
            using (var process = new Process { StartInfo = startInfo })
            {
                process.Start();
                var stdoutTask = process.StandardOutput.ReadToEndAsync();
                var stderrTask = process.StandardError.ReadToEndAsync();
                try
                {
                    // Include pipe draining in the deadline: a descendant can keep a redirected
                    // handle open even after vstest itself has exited.
                    await Task.WhenAll(process.WaitForExitAsync(), stdoutTask, stderrTask).WaitAsync(ChildTimeout);
                    exitCode = process.ExitCode;
                }
                catch (TimeoutException)
                {
                    try { process.Kill(entireProcessTree: true); }
                    catch (InvalidOperationException) { /* already exited */ }
                    catch (System.ComponentModel.Win32Exception exception) { cleanupFailure = exception.Message; }
                    try
                    {
                        await Task.WhenAll(process.WaitForExitAsync(), stdoutTask, stderrTask).WaitAsync(CleanupTimeout);
                    }
                    catch (TimeoutException)
                    {
                        cleanupFailure = (cleanupFailure is null ? "" : cleanupFailure + "; ")
                            + "process exit or output drain did not complete within the cleanup deadline";
                    }
                }

                stdout = stdoutTask.IsCompletedSuccessfully ? await stdoutTask : "(stdout did not close before cleanup deadline)";
                stderr = stderrTask.IsCompletedSuccessfully ? await stderrTask : "(stderr did not close before cleanup deadline)";
            }

            var markers = File.ReadAllLines(markerFile).Where(line => line.Length > 0).ToList();
            var completed = markers.Where(line => !line.StartsWith('#')).ToList();
            var report = string.Join(
                Environment.NewLine,
                $"assembly: {assembly.GetName().Name}",
                $"parent test host: {RuntimeInformation.FrameworkDescription} {RuntimeInformation.RuntimeIdentifier}; {GcConfiguration()}",
                $"child: dotnet vstest with DOTNET_gcConcurrent=0; exit code {exitCode?.ToString() ?? "none (killed after timeout)"}; {watch.Elapsed.TotalSeconds:F1} s",
                $"cleanup: {cleanupFailure ?? "completed"}",
                $"expected ({expected.Count}): {string.Join(", ", expected)}",
                $"completed ({completed.Count}): {string.Join(", ", completed)}",
                "---- child hosts ----",
                string.Join(Environment.NewLine, markers.Where(line => line.StartsWith('#'))),
                "---- child stdout ----",
                stdout.TrimEnd(),
                "---- child stderr ----",
                stderr.TrimEnd());
            KeepDiagnostics(assembly, report);

            Assert.True(exitCode is not null, $"The GC-isolated child did not exit within {ChildTimeout.TotalSeconds:F0} s.{Environment.NewLine}{report}");
            Assert.True(exitCode == 0, $"The GC-isolated child exited with {exitCode}.{Environment.NewLine}{report}");
            var expectedMethods = expected.Select(name => name[(name.LastIndexOf('.') + 1)..]).Order(StringComparer.Ordinal);
            Assert.True(
                expectedMethods.SequenceEqual(completed.Order(StringComparer.Ordinal)),
                $"Not every GC-isolated measurement completed in the child.{Environment.NewLine}{report}");
        }
        finally
        {
            try { File.Delete(markerFile); }
            catch (IOException) { /* best-effort cleanup */ }
        }
    }

    /// <summary>The runtime's own view of the GC mode, which is what the counter depends on.</summary>
    public static bool ConcurrentGcEnabled()
        => GC.GetConfigurationVariables().TryGetValue("ConcurrentGC", out var value) && value is true;

    public static string GcConfiguration()
    {
        var variables = GC.GetConfigurationVariables();
        string Read(string name) => variables.TryGetValue(name, out var value) ? value?.ToString() ?? "null" : "absent";
        return $"ServerGC={Read("ServerGC")}, ConcurrentGC={Read("ConcurrentGC")}, "
            + $"DOTNET_gcConcurrent={Environment.GetEnvironmentVariable("DOTNET_gcConcurrent") ?? "unset"}, "
            + $"DOTNET_gcServer={Environment.GetEnvironmentVariable("DOTNET_gcServer") ?? "unset"}";
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static long MeasureKnownAllocation()
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        var value = AllocateKnown();
        var after = GC.GetAllocatedBytesForCurrentThread();
        GC.KeepAlive(value);
        return after - before;
    }

    // Returned to the caller, so the allocation escapes and cannot be stack-allocated or removed.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static object AllocateKnown() => new byte[37];

    private static void KeepDiagnostics(Assembly assembly, string report)
    {
        var directory = Environment.GetEnvironmentVariable(DiagnosticsDirectoryEnvironment);
        if (string.IsNullOrWhiteSpace(directory))
            return;
        Directory.CreateDirectory(directory);
        File.WriteAllText(Path.Combine(directory, $"gc-isolated-allocation-{assembly.GetName().Name}.log"), report + Environment.NewLine);
    }
}
