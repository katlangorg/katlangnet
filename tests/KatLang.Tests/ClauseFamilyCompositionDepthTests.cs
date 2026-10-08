using System.Diagnostics;

namespace KatLang.Tests;

/// <summary>
/// Composed-depth guards for clause-family elaboration. The parser elaborates clause
/// families (ordinary-vs-conditional decision, head-pattern checks, branch arity checks)
/// while the body is still being built — BEFORE the finished root reaches the iterative
/// <see cref="AstStructuralPreflight"/> gate — so nothing in that phase may walk a branch
/// body recursively: a composed tree (in-budget operator chains stacked inside in-budget
/// container levels) is far deeper than any CLR-safe recursion depth. These tests pin that
/// a composed multi-clause family below the limit parses and elaborates normally and that
/// the audit's composed reproducer is rejected with the structured structural-depth
/// diagnostic. The process-terminating depths run in
/// <see cref="ClauseFamilyCompositionDepthProcessTests"/>.
/// <para>History: these guards were written for the parser's former branch-body Grace scan
/// (<c>Parser.FindGraceSpan</c>), the one such pre-preflight walk, which recursed until it was
/// made iterative. Q-16 G-O (2026-10-07) deleted the scan — Grace eligibility is the parameter
/// detector's per-owner decision — and its first-match-order tests went with it; the depth
/// guards stay so that no future pre-preflight walk of a clause body can return.</para>
/// </summary>
public class ClauseFamilyCompositionDepthTests
{
    /// <summary>
    /// The composed-depth multi-clause generator from the Track 3 audit: the first
    /// clause body stacks <paramref name="levels"/> parenthesized sequence levels,
    /// each carrying its own flat <c>+1</c> chain of <paramref name="chainOps"/>
    /// operators. Every parser mechanism stays inside its own budget (group nesting
    /// charges 4 of the 384 cumulative units per level; each chain is parsed
    /// iteratively and stays below <see cref="Parser.MaxExpressionChainDepth"/>),
    /// while the composed tree is roughly <c>levels * (chainOps + 2)</c> nodes deep.
    /// The second clause makes the family conditional, so the first clause's deep body
    /// goes through clause-family elaboration as a branch body.
    /// </summary>
    internal static string ComposedClauseFamilySource(int levels, int chainOps)
    {
        var chain = string.Concat(Enumerable.Repeat("+1", chainOps));
        var body =
            string.Concat(Enumerable.Repeat("(0, ", levels))
            + "1"
            + string.Concat(Enumerable.Repeat(chain + ")", levels));
        return $"F(0) = {body}\nF(x) = 1\nF(0)";
    }

    [Fact]
    public void BelowLimitComposedClauseFamily_ParsesNormally()
    {
        // The composed multi-clause shape at a structurally acceptable size
        // (~250 nodes deep: inside the raw 640 gate AND the front-end 300 gate) must
        // keep parsing and elaborating cleanly — the depth rejection is about depth,
        // not about the clause-family shape itself.
        var source = ComposedClauseFamilySource(levels: 3, chainOps: 80);

        var raw = Parser.ParseSyntax(source);
        Assert.False(raw.HasErrors);
        var property = Assert.Single(raw.Root.Properties);
        Assert.Equal("F", property.Name);
        var conditional = Assert.IsType<Algorithm.Conditional>(property.Value);
        Assert.Equal(2, conditional.Branches.Count);
        Assert.Single(raw.Root.Output);

        Assert.False(Parser.Parse(source).HasErrors);
    }

    [Fact]
    public void ComposedAuditShape_IsRejectedWithTheStructuralDiagnostic()
    {
        // The audit's exact reproducer (19 levels x 200-op chains, ~3.8k nodes deep):
        // parsing must complete far enough for the raw-syntax structural preflight to
        // reject the composed tree with its established diagnostic — in THIS process,
        // on an ordinary test-host thread. Extreme depths run process-isolated in
        // ClauseFamilyCompositionDepthProcessTests.
        var source = ComposedClauseFamilySource(levels: 19, chainOps: 200);

        var raw = Parser.ParseSyntax(source);
        Assert.True(raw.HasErrors);
        Assert.Contains(
            raw.Diagnostics,
            d => d.Message.Contains(
                $"structural AST depth limit of {AstStructuralPreflight.RawSyntaxMaxAstDepth}",
                StringComparison.Ordinal));
        // The placeholder root: downstream consumers never see the unsafe tree.
        Assert.Empty(raw.Root.Properties);
        Assert.Empty(raw.Root.Output);

        // The full front-end path surfaces the same structured rejection.
        var elaborated = Parser.Parse(source);
        Assert.True(elaborated.HasErrors);
        Assert.Contains(
            elaborated.Diagnostics,
            d => d.Message.Contains(
                $"structural AST depth limit of {AstStructuralPreflight.RawSyntaxMaxAstDepth}",
                StringComparison.Ordinal));
    }
}

/// <summary>
/// Process-isolated regression proving clause-family elaboration cannot terminate the host
/// process on composed-depth families: when the parser's former branch-body Grace scan
/// recursively walked the completed clause body BEFORE the structural preflight ran, a source
/// whose every parser mechanism stayed in budget still overflowed the CLR stack. An in-process
/// test cannot demonstrate that safely, so a child process parses the composed shapes on a
/// dedicated thread with the DOCUMENTED minimum supported stack (1 MiB), observes the
/// structured structural-depth diagnostic, writes a success marker, and exits normally.
/// Follows the subprocess convention of <see cref="AstStructuralDepthProcessTests"/>.
/// </summary>
public class ClauseFamilyCompositionDepthProcessTests
{
    private const string ProbeChildEnvironment = "KATLANG_CLAUSE_FAMILY_DEPTH_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_CLAUSE_FAMILY_DEPTH_PROBE_MARKER_FILE";
    private const string ProbeSuccessMarker = "katlang-clause-family-depth-preflight-ok";

    private static async Task RunProbeChild(string childTestName)
    {
        var assemblyPath = typeof(ClauseFamilyCompositionDepthProcessTests).Assembly.Location;
        var testName = typeof(ClauseFamilyCompositionDepthProcessTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(
            Path.GetTempPath(),
            $"katlang-clause-family-depth-probe-{Guid.NewGuid():N}.txt");

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

    [Fact]
    public async Task ComposedDepthClauseFamilies_AreRejectedInSubprocess_WithoutProcessTermination()
        => await RunProbeChild("ComposedDepthClauseFamilies_ProbeChild");

    [Fact]
    public void ComposedDepthClauseFamilies_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // The DOCUMENTED minimum supported environment: a dedicated 1 MiB thread.
        // Every parser budget is calibrated for it and the preflight is iterative, so both
        // composed shapes must come back as ONE structured structural-depth diagnostic —
        // never a stack overflow, on any stack.
        AstStructuralDepthProcessTests.RunOnThreadWithStack(1_048_576, () =>
        {
            // Far beyond any plausible CLR-safe recursion depth (~16k nodes on the
            // deep path), yet comfortably inside the 2 MiB source-length ceiling.
            AssertComposedShapeRejectedStructurally(levels: 80, chainOps: 200);

            // The audit's exact reproducer shape.
            AssertComposedShapeRejectedStructurally(levels: 19, chainOps: 200);
        });

        WriteProbeMarker();
    }

    private static void AssertComposedShapeRejectedStructurally(int levels, int chainOps)
    {
        var source = ClauseFamilyCompositionDepthTests.ComposedClauseFamilySource(levels, chainOps);
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains(
                $"structural AST depth limit of {AstStructuralPreflight.RawSyntaxMaxAstDepth}",
                StringComparison.Ordinal));
        Assert.Empty(result.Root.Properties);
        Assert.Empty(result.Root.Output);
    }
}
