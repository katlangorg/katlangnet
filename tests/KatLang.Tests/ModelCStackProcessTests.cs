using System.Diagnostics;
using KatLang.Evaluation;

namespace KatLang.Tests;

public class ModelCStackProcessTests
{
    private const string Child = "KATLANG_MODEL_C_STACK_CHILD";
    private const string Marker = "KATLANG_MODEL_C_STACK_MARKER";

    [Fact]
    public async Task TransportForwardingFamiliesCallbacksAndCycles_AreSafeInAConstrainedChild()
    {
        var marker = Path.Combine(Path.GetTempPath(), $"katlang-model-c-stack-{Guid.NewGuid():N}.txt");
        var start = new ProcessStartInfo("dotnet") { UseShellExecute = false, CreateNoWindow = true,
            RedirectStandardOutput = true, RedirectStandardError = true };
        start.ArgumentList.Add("vstest");
        start.ArgumentList.Add(typeof(ModelCStackProcessTests).Assembly.Location);
        start.ArgumentList.Add("--Tests:" + typeof(ModelCStackProcessTests).FullName + ".ConstrainedChild");
        start.Environment[Child] = "1"; start.Environment[Marker] = marker;
        try
        {
            using var process = Process.Start(start)!;
            var output = process.StandardOutput.ReadToEndAsync();
            var error = process.StandardError.ReadToEndAsync();
            using var deadline = new CancellationTokenSource(TimeSpan.FromSeconds(90));
            try { await process.WaitForExitAsync(deadline.Token); }
            catch (OperationCanceledException) { process.Kill(entireProcessTree: true); await process.WaitForExitAsync(); Assert.Fail("Model-C constrained child timed out"); }
            var text = await output + await error;
            Assert.True(process.ExitCode == 0, text);
            Assert.DoesNotContain("Stack overflow", text, StringComparison.OrdinalIgnoreCase);
            Assert.True(File.Exists(marker), text);
            Assert.Equal("model-c-stack-ok", await File.ReadAllTextAsync(marker));
        }
        finally { File.Delete(marker); }
    }

    [Fact]
    public void ConstrainedChild()
    {
        if (Environment.GetEnvironmentVariable(Child) != "1") return;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(1024 * 1024, () =>
        {
            new NeedCellTests().OneHundredThousandProductionParameterTransports_ShareOneAddressOnAConstrainedStack();
            var aliases = string.Join("\n", Enumerable.Range(0, 2_000).Select(i => $"A{i}=A{i+1}")) + "\nA2000=Inc\nInc(x)=x+1\nA0(6)";
            var forwarding = string.Join("\n", Enumerable.Range(0, 16).Select(i => $"F{i}(x)=F{i+1}")) + "\nF16(x)=x+x\nF0(4)";
            Success(aliases, "7"); Success(forwarding, "8");
            Success("Down(0)=0\nDown(n)=Down(n-1)\nDown(16)", "0");
            Success("F(n)=if(n==0,0,first(map([n-1],F)))\nF(8)", "0");
            foreach (var source in new[] { "F(n)=F(n+1)\nF(0)", "F(n)=first(map([n+1],F))\nF(0)", "F(n)=repeat(F,1,n)\nF(0)" })
            {
                var result = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = new EvaluationLimits { MaxDepth = 32 } });
                var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
                Assert.True(error.Code is KatLangErrorCode.EvaluationDepthExceeded or KatLangErrorCode.EvaluationStackExhausted, error.Message);
            }
            NeedCell? cycle = null;
            cycle = new NeedCell(() => cycle!.Demand(), () => cycle!.DemandAsync());
            Assert.Equal(KatLangErrorCode.DemandCycle, cycle.Demand().Error.Code);
            Assert.Equal(KatLangErrorCode.DemandCycle, cycle.DemandAsync().GetAwaiter().GetResult().Error.Code);
            File.WriteAllText(Environment.GetEnvironmentVariable(Marker)!, "model-c-stack-ok");
        }, TimeSpan.FromSeconds(60));
    }

    private static void Success(string source, string expected)
        => Assert.Equal(expected, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
}
