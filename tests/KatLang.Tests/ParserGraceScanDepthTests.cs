using System.Diagnostics;

namespace KatLang.Tests;

/// <summary>
/// Regression coverage for the parser's conditional-branch grace scan
/// (<c>Parser.FindGraceSpan</c>). The scan runs while clause families are still
/// being elaborated — BEFORE the finished root reaches the iterative
/// <see cref="AstStructuralPreflight"/> gate — so it must walk composed trees
/// (in-budget operator chains stacked inside in-budget container levels) that are
/// far deeper than any CLR-safe recursion depth. These tests pin the scan's exact
/// first-match order for every expression form it inspects, the unchanged ordinary
/// grace diagnostic, the below-limit composed control, and the structured
/// structural-depth rejection of the audit's composed reproducer. The
/// process-terminating depths run in <see cref="ParserGraceScanDepthProcessTests"/>.
/// </summary>
public class ParserGraceScanDepthTests
{
    private const string GraceBodyMessage = "Grace is not allowed in conditional branch bodies";

    /// <summary>
    /// The composed-depth multi-clause generator from the Track 3 audit: the first
    /// clause body stacks <paramref name="levels"/> parenthesized sequence levels,
    /// each carrying its own flat <c>+1</c> chain of <paramref name="chainOps"/>
    /// operators. Every parser mechanism stays inside its own budget (group nesting
    /// charges 4 of the 384 cumulative units per level; each chain is parsed
    /// iteratively and stays below <see cref="Parser.MaxExpressionChainDepth"/>),
    /// while the composed tree is roughly <c>levels * (chainOps + 2)</c> nodes deep.
    /// The second clause makes the family conditional, which is what routes the
    /// first clause's deep body through the grace scan.
    /// </summary>
    internal static string ComposedGraceScanClauseFamilySource(int levels, int chainOps)
    {
        var chain = string.Concat(Enumerable.Repeat("+1", chainOps));
        var body =
            string.Concat(Enumerable.Repeat("(0, ", levels))
            + "1"
            + string.Concat(Enumerable.Repeat(chain + ")", levels));
        return $"F(0) = {body}\nF(x) = 1\nF(0)";
    }

    private static Diagnostic AssertSingleGraceDiagnostic(string source)
    {
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        return Assert.Single(
            result.Diagnostics,
            d => d.Message.Contains(GraceBodyMessage, StringComparison.Ordinal));
    }

    // ── First-match order: the reported span is the leftmost grace in source order ──
    //
    // Each case places TWO grace nodes (or one grace after a non-grace sibling) in
    // distinct child positions of one expression form; the reported span must be the
    // first one in depth-first source order. Expected spans were captured from the
    // established scan behavior and pin the visitation order per node kind:
    // Binary/Index/SequenceConstruct left-then-right, Unary/SequenceSpread operand,
    // ListLiteral items in written order, Call function-then-argument-outputs,
    // DotCall target-then-argument-outputs (arguments optional), Block output rows
    // in written order. (The internal SequenceConstruct join node has no parser
    // origin site, so its left-then-right order is not reachable from source.)

    [Theory]
    // Binary: the whole left subtree is scanned before the right operand.
    [InlineData("F(0) = ~a + ~b", 1, 8, 1, 9)]
    [InlineData("F(0) = 1 + ~b", 1, 12, 1, 13)]
    // List literal: items in written order.
    [InlineData("F(0) = [~a, ~b]", 1, 9, 1, 10)]
    // Call: argument output slots in written order.
    [InlineData("F(0) = G(~a, ~b)", 1, 10, 1, 11)]
    // Call: the function expression is scanned before the argument outputs.
    [InlineData("F(0) = (~a)(~b)", 1, 9, 1, 10)]
    // Dot-call: the receiver target is scanned before the argument outputs.
    [InlineData("F(0) = (~a).G(~b)", 1, 9, 1, 10)]
    // Dot-call without arguments: target-only descent.
    [InlineData("F(0) = (~a).count", 1, 9, 1, 10)]
    // Block: output rows in written order.
    [InlineData("F(0) = (~a, ~b)", 1, 9, 1, 10)]
    [InlineData("F(0) = (1, ~b)", 1, 12, 1, 13)]
    // Unary: operand descent.
    [InlineData("F(0) = -~a", 1, 9, 1, 10)]
    // Index: the target is scanned before the selector.
    [InlineData("F(0) = (~a):(~b)", 1, 9, 1, 10)]
    [InlineData("F(0) = x:(~b)", 1, 11, 1, 12)]
    // Spread: operand descent.
    [InlineData("F(0) = (~a)*", 1, 9, 1, 10)]
    // Nested combination across list, binary, call, and block forms.
    [InlineData("F(0) = [1 + 2, G(3, (4, ~c + ~d))]", 1, 25, 1, 26)]
    // Postfix grace spelling participates in the same source order.
    [InlineData("F(0) = a~ + b~", 1, 8, 1, 9)]
    public void GraceScan_FirstMatchSpan_IsTheLeftmostGraceInSourceOrder(
        string source, int startLine, int startColumn, int endLine, int endColumn)
    {
        var diagnostic = AssertSingleGraceDiagnostic(source);
        Assert.Equal(startLine, diagnostic.Span.StartLineNumber);
        Assert.Equal(startColumn, diagnostic.Span.StartColumn);
        Assert.Equal(endLine, diagnostic.Span.EndLineNumber);
        Assert.Equal(endColumn, diagnostic.Span.EndColumn);
    }

    [Fact]
    public void GraceScan_MultiClauseFamily_ReportsPerBranchFirstMatch_InBranchOrder()
    {
        var result = Parser.ParseSyntax("F(0) = ~a + ~b\nF(x) = x~ * 2");
        Assert.True(result.HasErrors);
        var graceDiagnostics = result.Diagnostics
            .Where(d => d.Message.Contains(GraceBodyMessage, StringComparison.Ordinal))
            .ToList();

        // One diagnostic per offending branch, in branch order, each anchored on
        // that branch's OWN first grace (never the family-wide first).
        Assert.Equal(2, graceDiagnostics.Count);
        Assert.Equal(1, graceDiagnostics[0].Span.StartLineNumber);
        Assert.Equal(8, graceDiagnostics[0].Span.StartColumn);
        Assert.Equal(2, graceDiagnostics[1].Span.StartLineNumber);
        Assert.Equal(8, graceDiagnostics[1].Span.StartColumn);
    }

    [Fact]
    public void GraceScan_OrdinaryPrefixGraceBody_DiagnosticKindMessageAndSpanUnchanged()
    {
        var diagnostic = AssertSingleGraceDiagnostic("F(0) = ~a");
        Assert.Equal("Grace is not allowed in conditional branch bodies for 'F'.", diagnostic.Message);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(1, diagnostic.Span.StartLineNumber);
        Assert.Equal(8, diagnostic.Span.StartColumn);
        Assert.Equal(1, diagnostic.Span.EndLineNumber);
        Assert.Equal(9, diagnostic.Span.EndColumn);
    }

    [Fact]
    public void GraceScan_BelowLimitComposedClauseFamily_ParsesNormally()
    {
        // The same composed multi-clause shape at a structurally acceptable size
        // (~250 nodes deep: inside the raw 640 gate AND the front-end 300 gate) must
        // keep parsing and elaborating cleanly — the depth rejection is about depth,
        // not about the clause-family shape itself.
        var source = ComposedGraceScanClauseFamilySource(levels: 3, chainOps: 80);

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
    public void GraceScanDepth_ComposedAuditShape_IsRejectedWithTheStructuralDiagnostic()
    {
        // The audit's exact reproducer (19 levels x 200-op chains, ~3.8k nodes deep):
        // parsing must complete far enough for the raw-syntax structural preflight to
        // reject the composed tree with its established diagnostic — in THIS process,
        // on an ordinary test-host thread. Extreme depths run process-isolated in
        // ParserGraceScanDepthProcessTests.
        var source = ComposedGraceScanClauseFamilySource(levels: 19, chainOps: 200);

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
/// Process-isolated regression proving the conditional-branch grace scan cannot
/// terminate the host process on composed-depth clause families: before the scan
/// became iterative, <c>Parser.FindGraceSpan</c> recursively walked the completed
/// clause body BEFORE the structural preflight ran, so a source whose every parser
/// mechanism stayed in budget still overflowed the CLR stack. An in-process test
/// cannot demonstrate that safely, so a child process parses the composed shapes on
/// a dedicated thread with the DOCUMENTED minimum supported stack (1 MiB), observes
/// the structured structural-depth diagnostic, writes a success marker, and exits
/// normally. Follows the subprocess convention of
/// <see cref="AstStructuralDepthProcessTests"/>.
/// </summary>
public class ParserGraceScanDepthProcessTests
{
    private const string ProbeChildEnvironment = "KATLANG_GRACE_SCAN_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_GRACE_SCAN_PROBE_MARKER_FILE";
    private const string ProbeSuccessMarker = "katlang-grace-scan-preflight-ok";

    private static async Task RunProbeChild(string childTestName)
    {
        var assemblyPath = typeof(ParserGraceScanDepthProcessTests).Assembly.Location;
        var testName = typeof(ParserGraceScanDepthProcessTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(
            Path.GetTempPath(),
            $"katlang-grace-scan-probe-{Guid.NewGuid():N}.txt");

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
        // Every parser budget is calibrated for it, the preflight and the grace scan
        // are iterative, so both composed shapes must come back as ONE structured
        // structural-depth diagnostic — never a stack overflow, on any stack.
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
        var source = ParserGraceScanDepthTests.ComposedGraceScanClauseFamilySource(levels, chainOps);
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
