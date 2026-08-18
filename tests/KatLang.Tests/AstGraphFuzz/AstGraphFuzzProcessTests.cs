using System.Diagnostics;
using KatLang.Tests.AstGraphFuzz;

namespace KatLang.Tests;

/// <summary>
/// Process-isolated small-stack half of the structural AST-graph fuzz campaign.
///
/// <para>The primary safety invariant — a preflight-accepted host AST must never kill the
/// process, overflow the native stack, hang, or escape with a raw CLR exception — cannot be
/// demonstrated in-process: a violation would take xUnit down with it. So a child process
/// (following the <see cref="AstStructuralDepthProcessTests"/> probe convention) executes the
/// ENTIRE deterministic corpus plus the maximum ACCEPTED member of every boundary family on a
/// dedicated thread with a deliberately small 1 MiB stack — the documented minimum supported
/// environment. The child prints each case id BEFORE executing it, so a crashed batch
/// identifies the failing case from the captured output alone, and any single case can be
/// replayed with <c>KATLANG_AST_FUZZ_ONLY</c>.</para>
///
/// <para>Exit classification in the parent: normal success (exit 0 + marker + no overflow
/// text), structured failures happen INSIDE the child and still exit 0, timeout (killed after
/// the deadline), abnormal exit (non-zero / stack-overflow text / missing marker). Timeouts
/// are a last-resort process-safety guard only, never the correctness oracle.</para>
/// </summary>
public class AstGraphFuzzProcessTests
{
    private const string ProbeChildEnvironment = "KATLANG_AST_FUZZ_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_AST_FUZZ_PROBE_MARKER_FILE";
    private const string ProbeSuccessMarker = "katlang-ast-graph-fuzz-ok";
    private const int SmallStackBytes = 1 * 1024 * 1024;

    private static async Task RunProbeChild(string childTestName)
    {
        var assemblyPath = typeof(AstGraphFuzzProcessTests).Assembly.Location;
        var testName = typeof(AstGraphFuzzProcessTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(
            Path.GetTempPath(),
            $"katlang-ast-fuzz-probe-{Guid.NewGuid():N}.txt");

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
            using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(120));
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

            Assert.True(
                exited,
                $"Fuzz probe '{childTestName}' did not exit within 120 seconds (last case line "
                + $"identifies the hang).{Environment.NewLine}{combined}");
            Assert.DoesNotContain("Stack overflow", combined, StringComparison.OrdinalIgnoreCase);
            Assert.DoesNotContain("StackOverflowException", combined, StringComparison.OrdinalIgnoreCase);
            Assert.True(
                process.ExitCode == 0,
                $"Fuzz probe '{childTestName}' exited with {process.ExitCode} (last case line "
                + $"identifies the crash).{Environment.NewLine}{combined}");
            Assert.True(
                File.Exists(markerFile),
                $"Fuzz probe '{childTestName}' did not write its success marker."
                + Environment.NewLine + combined);
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

    [Fact]
    public async Task Campaign_EveryAcceptedCaseAndBoundaryFamily_SurvivesAOneMiBStack()
        => await RunProbeChild(nameof(Campaign_ProbeChild));

    [Fact]
    public void Campaign_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        AstStructuralDepthProcessTests.RunOnThreadWithStack(
            SmallStackBytes,
            () =>
            {
                var seed = AstGraphFuzzTests.CampaignSeed;
                var caseCount = AstGraphFuzzTests.CampaignCaseCount;
                var only = AstGraphFuzzTests.CampaignOnlyCase;

                // 1) The whole deterministic corpus. The case id is printed BEFORE execution
                //    so a crash names its case; every outcome must be structured (success or
                //    EvalError) — the harness classifies anything else as a defect.
                for (var index = 0; index < caseCount; index++)
                {
                    if (only is { } o && o != index)
                        continue;

                    Console.WriteLine($"fuzz-case {seed:X}:{index}");
                    var graphCase = AstGraphFuzzer.Generate(seed, index);
                    var program = AstGraphFuzzer.WrapInProgram(AstGraphFuzzer.MaterializeShared(graphCase));
                    _ = Evaluator.RunCounted(program);
                    _ = Evaluator.Run(program);
                }

                // 2) The maximum ACCEPTED member of every dangerous boundary family, executed
                //    physically at the documented minimum stack. If a future cost-model edit
                //    re-admits a dangerous class, the max accepted size grows and this child
                //    dies here — a controlled, attributable failure in the parent.
                Console.WriteLine("fuzz-boundary spine-reentry");
                var spineMax = BoundaryFamilies.MaxAccepted(BoundaryFamilies.SpineReentryChain, hi: 60);
                AssertOk(Evaluator.Run(BoundaryFamilies.SpineReentryChain(spineMax)));

                Console.WriteLine("fuzz-boundary join-alternation");
                var alternationMax = BoundaryFamilies.MaxAccepted(BoundaryFamilies.JoinAlternationChain, hi: 80);
                AssertOk(Evaluator.Run(BoundaryFamilies.JoinAlternationChain(alternationMax)));

                Console.WriteLine("fuzz-boundary join-handoff");
                var handoffMax = BoundaryFamilies.MaxAccepted(
                    static n => AstGraphFuzzer.WrapInProgram(BoundaryFamilies.JoinHandoffChain(n)),
                    hi: 80);
                AssertOk(Evaluator.Run(
                    AstGraphFuzzer.WrapInProgram(BoundaryFamilies.JoinHandoffChain(handoffMax))));

                Console.WriteLine("fuzz-boundary unary-exact-limit");
                AssertOk(Evaluator.Run(
                    BoundaryFamilies.UnaryChain(EvaluationLimits.MaxSupportedAstDepth - 1)));

                Console.WriteLine("fuzz-boundary pure-join-spine");
                AssertOk(Evaluator.Run(BoundaryFamilies.PureJoinSpine(4_000)));

                Console.WriteLine("fuzz-boundary shared-wide-root");
                AssertOk(Evaluator.Run(BoundaryFamilies.SharedWideRoot(64)));

                Console.WriteLine("fuzz-boundary shared-deep-route");
                AssertOk(Evaluator.Run(
                    BoundaryFamilies.SharedDeepRouteDiamond(sharedHeight: 150, longRoute: 100)));

                // 3) The accepted-but-semantically-exponential diamond stays governed by the
                //    structured step budget on the small stack too (depth 20 against a
                //    100-step budget: bulk work charges per ~4096-operation checkpoint, so it
                //    trips after ~410k of the ~1M semantic operations — milliseconds).
                Console.WriteLine("fuzz-boundary doubling-diamond");
                var diamond = Evaluator.Run(
                    BoundaryFamilies.DoublingDiamond(20),
                    new EvaluationLimits { MaxSteps = 100 });
                if (!diamond.IsError)
                    throw new InvalidOperationException("doubling diamond must hit the step budget");
            });

        WriteProbeMarker();

        static void AssertOk<T>(EvalResult<T> result)
        {
            if (result.IsError)
                throw new InvalidOperationException($"expected success, got {result.Error}");
        }
    }
}
