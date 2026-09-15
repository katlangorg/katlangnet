using System.Diagnostics;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// Process-isolated regressions proving that evaluator re-entry recursion is bounded by
/// the budget chokepoints. Before the depth-charged argument-evaluation chokepoint
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
    public async Task ResolvedValueDemandRecursion_IsStructurallyBounded_InSubprocess()
        => await RunProbeChild("ResolvedValueDemandRecursion_ProbeChild");

    [Fact]
    public async Task PlannedLoopUnderRecursion_IsStructurallyBounded_InSubprocess()
        => await RunProbeChild("PlannedLoopUnderRecursion_ProbeChild");

    /// <summary>
    /// Final audit (September 2026): the loop planner (<c>LoopOptimizer.TryBuildLoopExprPlan</c>)
    /// and the planned expression evaluator recurse once per AST level of the step body between
    /// two budget chokepoints, and a plan is built at loop-INVOCATION time — after the dynamic
    /// recursion has already consumed most of the host stack. A parser- and preflight-accepted
    /// step (an 80-operator chain, or 126 nested <c>if</c>s) invoked at a modest recursion depth
    /// therefore terminated the whole process with an uncatchable stack overflow inside the
    /// planner, where the generic strategy completes or reports the structured stack error.
    /// Both walks now probe the host stack per level: an unplannable step falls back to the
    /// generic strategy, and a planned spine that runs out of headroom degrades to the
    /// structured <see cref="EvalError.EvaluationStackExhausted"/>. The generic strategy is the
    /// oracle for the value where the run completes.
    /// </summary>
    [Fact]
    public void PlannedLoopUnderRecursion_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        var chain80 = "Step(x) = x" + string.Concat(Enumerable.Repeat(" + 1", 80));
        var chain200 = "Step(x) = x" + string.Concat(Enumerable.Repeat(" + 1", 200));
        var nestedIfs = "Step(x) = " + string.Concat(Enumerable.Repeat("if(x + 1, ", 126)) + "x + 1"
            + string.Concat(Enumerable.Repeat(", 0)", 126));

        // A guard that simply refuses every plan must not satisfy the safety test.
        // At shallow depth, these accepted spines must execute planned operations,
        // produce the hand-computed result, and preserve the generic budget relations.
        foreach (var (step, expected) in new[] { (chain80, 160), (chain200, 400) })
        {
            var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(step + "\nStep.repeat(2, 0)").Root);
            var diagnostics = new LoopOptimizationDiagnostics();
            var planned = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics);
            var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false);
            Assert.False(planned.Result.IsError);
            Assert.False(generic.Result.IsError);
            Assert.Equal(new Result.Atom(expected), planned.Result.Value.Value);
            Assert.Equal(generic.Result.Value, planned.Result.Value);
            Assert.True(diagnostics.PlannedBuiltinOperations > 0);
            Assert.Equal(0, diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
            // Unconfigured step accounting can omit optimized iterations; configuring
            // MaxSteps pins the generic strategy in CreateRootCtx. Depth and persistent
            // materialization, in contrast, must agree even on this wholly planned path.
            Assert.InRange(planned.Budget.ConsumedSteps, 0, generic.Budget.ConsumedSteps);
            Assert.Equal(generic.Budget.PeakDepth, planned.Budget.PeakDepth);
            Assert.Equal(generic.Budget.MaterializedItems, planned.Budget.MaterializedItems);
            Assert.Equal(generic.Budget.MaterializedStringChars, planned.Budget.MaterializedStringChars);
            Assert.Equal(0, planned.Budget.CurrentDepth);
            Assert.Equal(0, generic.Budget.CurrentDepth);
        }

        foreach (var (recursion, step) in new[] { (55, chain80), (60, chain80), (40, chain200), (50, nestedIfs), (30, nestedIfs) })
        {
            var source = $"Rec(n) = if(n == 0, Step.repeat(2, 0), Rec(n - 1))\n{step}\nRec({recursion})";
            var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

            // Public engine path under DEFAULT limits — the configuration an embedding host runs with.
            var result = KatLangEngine.Run(source);
            switch (result)
            {
                case RunResult.Success:
                    // The optimized run completed (planned, or generic after the planner's
                    // fallback): its value is the generic strategy's value.
                    var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false).Result;
                    Assert.False(generic.IsError, "generic strategy failed for recursion " + recursion + (generic.IsError ? ": " + generic.Error : ""));
                    Assert.Equal(generic.Value.Value, Assert.IsType<RunResult.Success>(result).Value);
                    break;
                case RunResult.EvalFailure failure:
                    var error = Assert.Single(failure.Errors);
                    Assert.True(
                        error.Source is EvalError.EvaluationStackExhausted or EvalError.EvaluationDepthExceeded,
                        $"expected success or a structured resource error for recursion {recursion}, got: {error.Message}");
                    break;
                default:
                    Assert.Fail($"unexpected outcome {result.GetType().Name} for recursion {recursion}");
                    break;
            }
        }

        WriteProbeMarker();
    }

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

    [Fact]
    public void ResolvedValueDemandRecursion_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // These are the original AlgEnv reproducer, its ordinary-dot `string`
        // counterpart, and the lexical `string` receiver that formerly reached
        // an uncatchable CLR stack overflow. A small explicit limit pins the
        // deterministic error; the default public path separately proves that
        // the process returns normally under the production ceiling.
        foreach (var source in new[]
        {
            "F(v) = v\nx = F(x)\nx",
            "F(v) = v.string\nx = F(x)\nx",
            "A = A.string\nA",
        })
        {
            var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
            var bounded = Evaluator.Run(expr, new EvaluationLimits { MaxDepth = 24 });
            Assert.True(bounded.IsError);
            Assert.Equal(
                24,
                Assert.IsType<EvalError.EvaluationDepthExceeded>(bounded.Error).Limit);

            var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
            Assert.Single(failure.Errors);
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
