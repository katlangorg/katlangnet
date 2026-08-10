using System.Diagnostics;

namespace KatLang.Tests;

/// <summary>
/// Process-isolated regression proving that builtin-argument recursion is bounded by
/// the budget chokepoints: before the depth-charged argument-evaluation chokepoint
/// (<c>EvaluationBudget.TryEnterArgumentEvaluation</c>), a zero-parameter property
/// reaching itself through a builtin argument (<c>A = count(A)</c>,
/// <c>A = range(1, A)</c>, <c>A = if(1, A, 0)</c>, a loop's initial state or count)
/// terminated the whole process with an uncatchable
/// <see cref="StackOverflowException"/>. An in-process test cannot observe that
/// failure mode safely, so a child process runs the worst spellings, asserts the
/// structured resource error, writes a success marker, and exits normally.
/// Follows the subprocess convention of <see cref="AstStructuralDepthProcessTests"/>.
/// </summary>
public class EvaluationLimitsProcessTests
{
    private const string ProbeChildEnvironment = "KATLANG_EVALUATION_LIMITS_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_EVALUATION_LIMITS_PROBE_MARKER_FILE";
    private const string ProbeSuccessMarker = "katlang-evaluation-limits-recursion-ok";

    [Fact]
    public async Task BuiltinArgumentRecursion_IsStructurallyBounded_InSubprocess()
        => await RunProbeChild("BuiltinArgumentRecursion_ProbeChild");

    [Fact]
    public void BuiltinArgumentRecursion_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // The spellings that previously killed the process, through the public
        // engine path under DEFAULT limits — exactly the configuration an
        // embedding host runs with.
        foreach (var source in new[]
        {
            "A = count(A)\nA",
            "A = range(1, A)\nA.count",
            "A = if(1, A, 0)\nA",
            "A = take([1, 2, 3], A)\nA",
            "A = [1, 2].take(A)\nA",
            "Add(a, b) = a + b\nA = [1, 2].reduce(Add, A)\nA",
            "Step = x, 0\nA = Step.while(A)\nA",
            "Inc = x + 1\nA = Inc.repeat(A, 0)\nA",
        })
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
            Assert.Single(failure.Errors);

            var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
            Assert.True(
                result.Error is EvalError.EvaluationDepthExceeded or EvalError.EvaluationStackExhausted,
                $"expected a structured resource error for `{source.Replace("\n", " ; ")}`, got {result.Error}");
        }

        WriteProbeMarker();
    }

    private static async Task RunProbeChild(string childTestName)
    {
        var assemblyPath = typeof(EvaluationLimitsProcessTests).Assembly.Location;
        var testName = typeof(EvaluationLimitsProcessTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(
            Path.GetTempPath(),
            $"katlang-eval-limits-probe-{Guid.NewGuid():N}.txt");

        var startInfo = new ProcessStartInfo("dotnet")
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            CreateNoWindow = true,
        };
        startInfo.ArgumentList.Add("vstest");
        startInfo.ArgumentList.Add(assemblyPath);
        startInfo.ArgumentList.Add("--Tests:" + testName);
        startInfo.Environment[ProbeChildEnvironment] = "1";
        startInfo.Environment[ProbeMarkerFileEnvironment] = markerFile;
        startInfo.Environment["DOTNET_NOLOGO"] = "1";

        try
        {
            using var process = new Process { StartInfo = startInfo };
            process.Start();
            var stdoutTask = process.StandardOutput.ReadToEndAsync();
            var stderrTask = process.StandardError.ReadToEndAsync();

            var exited = true;
            using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(90));
            try
            {
                await process.WaitForExitAsync(timeout.Token);
            }
            catch (OperationCanceledException)
            {
                exited = false;
                try { process.Kill(entireProcessTree: true); }
                catch { /* process already exited */ }
                await process.WaitForExitAsync();
            }

            var stdout = await stdoutTask;
            var stderr = await stderrTask;
            var combined = stdout + Environment.NewLine + stderr;

            Assert.True(exited, $"Probe subprocess '{childTestName}' did not exit within 90 seconds."
                + Environment.NewLine + combined);
            Assert.DoesNotContain("Stack overflow", combined, StringComparison.OrdinalIgnoreCase);
            Assert.DoesNotContain("StackOverflowException", combined, StringComparison.OrdinalIgnoreCase);
            Assert.True(
                process.ExitCode == 0,
                $"Probe subprocess '{childTestName}' exited with {process.ExitCode}.{Environment.NewLine}{combined}");
            Assert.True(
                File.Exists(markerFile),
                $"Probe child '{childTestName}' did not write its success marker.{Environment.NewLine}{combined}");
            Assert.Equal(ProbeSuccessMarker, (await File.ReadAllTextAsync(markerFile)).Trim());
        }
        finally
        {
            try { File.Delete(markerFile); }
            catch { /* best-effort cleanup */ }
        }
    }

    private static void WriteProbeMarker()
    {
        var markerFile = Environment.GetEnvironmentVariable(ProbeMarkerFileEnvironment);
        Assert.False(string.IsNullOrWhiteSpace(markerFile));
        File.WriteAllText(markerFile!, ProbeSuccessMarker);
    }
}
