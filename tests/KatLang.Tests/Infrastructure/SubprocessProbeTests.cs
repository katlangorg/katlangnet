using System.Diagnostics;
using Xunit.Abstractions;

namespace KatLang.Tests.Infrastructure;

public class SubprocessProbeTests
{
    [Fact]
    public async Task ExplicitProbes_RunOnceInAFreshProcess_WithEnvironmentOutputAndAsyncCompletion()
    {
        var marker = Path.Combine(Path.GetTempPath(), $"katlang-probe-host-{Guid.NewGuid():N}.txt");
        var start = SubprocessProbe.StartInfo(typeof(Fixture).Assembly,
            [typeof(Fixture).FullName + ".WriteEnvironment", typeof(Fixture).FullName + ".AppendAfterAwait"]);
        start.Environment[Fixture.Marker] = marker;
        start.Environment[Fixture.Value] = "inherited-value";
        try
        {
            var (exit, text) = await Run(start);
            Assert.True(exit == 0, text);
            var lines = await File.ReadAllLinesAsync(marker);
            Assert.Equal(2, lines.Length);
            Assert.NotEqual(Environment.ProcessId.ToString(), lines[0]);
            Assert.Equal("inherited-value", lines[1]);
            Assert.Contains("probe-output", text, StringComparison.Ordinal);
            Assert.Equal(2, text.Split('\n').Count(line => line.StartsWith("PROBE PASS ", StringComparison.Ordinal)));
        }
        finally { File.Delete(marker); }
    }

    [Theory]
    [InlineData("Missing", "MissingMethodException")]
    [InlineData(nameof(Fixture.Fail), "probe assertion failed")]
    [InlineData(nameof(Fixture.WithArgument), "parameterless")]
    public async Task MissingInvalidAndFailingProbes_ReturnFailure(string method, string expected)
    {
        var (exit, text) = await Run(SubprocessProbe.StartInfo(typeof(Fixture), method));
        Assert.NotEqual(0, exit);
        Assert.Contains(expected, text, StringComparison.Ordinal);
        Assert.DoesNotContain("PROBE PASS ", text, StringComparison.Ordinal);
    }

    [Fact]
    public async Task DuplicateNames_AreRejectedBeforeAnyProbeExecutes()
    {
        var name = typeof(Fixture).FullName + "." + nameof(Fixture.Fail);
        var (exit, text) = await Run(SubprocessProbe.StartInfo(typeof(Fixture).Assembly, [name, name]));
        Assert.NotEqual(0, exit);
        Assert.Contains("unique", text, StringComparison.Ordinal);
        Assert.DoesNotContain("PROBE START ", text, StringComparison.Ordinal);
    }

    private static async Task<(int Exit, string Output)> Run(ProcessStartInfo start)
    {
        using var process = Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        await process.WaitForExitAsync();
        return (process.ExitCode, await stdout + Environment.NewLine + await stderr);
    }

    // These are explicitly named probes, not independently discovered tests.
    public sealed class Fixture(ITestOutputHelper output)
    {
        public const string Marker = "KATLANG_PROBE_HOST_FIXTURE_MARKER";
        public const string Value = "KATLANG_PROBE_HOST_FIXTURE_VALUE";

        public void WriteEnvironment()
        {
            output.WriteLine("probe-output");
            File.WriteAllText(Environment.GetEnvironmentVariable(Marker)!, Environment.ProcessId + Environment.NewLine);
        }

        public async Task AppendAfterAwait()
        {
            await Task.Yield();
            await File.AppendAllTextAsync(Environment.GetEnvironmentVariable(Marker)!, Environment.GetEnvironmentVariable(Value) + Environment.NewLine);
        }

        public void Fail() => Assert.Fail("probe assertion failed");
        public void WithArgument(int value) => throw new InvalidOperationException($"Must not execute: {value}");
    }
}
