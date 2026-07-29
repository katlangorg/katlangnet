using System.Diagnostics;

namespace KatLang.Tests;

/// <summary>
/// Regression coverage for the parser-owned limit on flat binary and postfix chains.
/// The raw parser builds these chains iteratively, but their left-deep AST shape is
/// consumed by recursive frontend visitors, so over-limit probes must be process-isolated.
/// </summary>
public class ParserExpressionChainDepthTests
{
    private const string ChainMessage = "Expression operator or postfix chain is too deep";
    private const string ProbeChildEnvironment = "KATLANG_EXPRESSION_CHAIN_PROBE_CHILD";

    private static string BinaryChain(string op, int operatorCount)
        => "Output = " + string.Join(
            $" {op} ",
            Enumerable.Repeat("1", operatorCount + 1));

    private static string MultilineTrailingOperatorChain(string op, int operatorCount)
        => "Output = " + string.Join(
            $" {op}{Environment.NewLine}",
            Enumerable.Repeat("1", operatorCount + 1));

    private static string DotCallChain(int operatorCount, bool leadingNewlines = false)
    {
        var separator = leadingNewlines ? Environment.NewLine : string.Empty;
        return "Output = Root" + string.Concat(
            Enumerable.Repeat($"{separator}.Member()", operatorCount));
    }

    private const string SpreadContinuation = "*";

    /// <summary>
    /// `1` followed by <paramref name="spreadCount"/> directly attached postfix `*`
    /// spread markers (each star adds one spread layer). The base primary contributes
    /// NO expression-chain level (only guarded operator/postfix nodes are recorded),
    /// so the chain depth equals the number of written spread markers exactly — there
    /// is no root-node off-by-one to account for. Written both as an explicit
    /// `Output = ...` body and as a bare root-output row, which reach the same guard.
    /// </summary>
    private static string SpreadChain(int spreadCount, bool explicitOutput = true)
        => (explicitOutput ? "Output = 1" : "1")
            + string.Concat(Enumerable.Repeat(SpreadContinuation, spreadCount));

    private static string DotThenSpreadChain(int dotCount, int spreadCount)
        => "Output = Root"
            + string.Concat(Enumerable.Repeat(".Member", dotCount))
            + string.Concat(Enumerable.Repeat(SpreadContinuation, spreadCount));

    private static Diagnostic AssertControlledChainFailure(string source)
    {
        var result = Parser.Parse(source);
        Assert.True(result.HasErrors);
        var diagnostic = Assert.Single(
            result.Diagnostics,
            diagnostic => diagnostic.Message.Contains(ChainMessage, StringComparison.Ordinal));
        Assert.True(diagnostic.Span.StartLineNumber >= 1);
        Assert.True(diagnostic.Span.StartColumn >= 1);
        Assert.True(diagnostic.Span.EndLineNumber >= diagnostic.Span.StartLineNumber);
        return diagnostic;
    }

    [Fact]
    public void ArithmeticChain_BelowLimit_Succeeds()
        => Assert.False(Parser.Parse(
            BinaryChain("+", Parser.MaxExpressionChainDepth - 1)).HasErrors);

    [Fact]
    public void ArithmeticChain_AtLimit_Succeeds()
        => Assert.False(Parser.Parse(
            BinaryChain("+", Parser.MaxExpressionChainDepth)).HasErrors);

    [Fact]
    public void ArithmeticChain_AboveLimit_ReturnsStructuredError()
        => AssertControlledChainFailure(
            BinaryChain("+", Parser.MaxExpressionChainDepth + 1));

    [Theory]
    [InlineData("<")]
    [InlineData("==")]
    [InlineData("and")]
    [InlineData("or")]
    public void ComparisonEqualityAndLogicalChains_AboveLimit_ReturnStructuredError(string op)
        => AssertControlledChainFailure(
            BinaryChain(op, Parser.MaxExpressionChainDepth + 1));

    [Fact]
    public void DotCallChain_AboveLimit_ReturnsStructuredError()
        => AssertControlledChainFailure(
            DotCallChain(Parser.MaxExpressionChainDepth + 1));

    [Fact]
    public void MultilineTrailingOperatorChain_AboveLimit_ReturnsStructuredError()
        => AssertControlledChainFailure(
            MultilineTrailingOperatorChain("+", Parser.MaxExpressionChainDepth + 1));

    [Fact]
    public void MultilineLeadingDotChain_AboveLimit_ReturnsStructuredError()
        => AssertControlledChainFailure(
            DotCallChain(Parser.MaxExpressionChainDepth + 1, leadingNewlines: true));

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void SpreadChain_AtLimit_ParsesWithoutDiagnostics(bool explicitOutput)
    {
        var result = Parser.Parse(SpreadChain(Parser.MaxExpressionChainDepth, explicitOutput));
        Assert.False(result.HasErrors);
        Assert.Empty(result.Diagnostics);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void SpreadChain_AboveLimit_ReturnsStructuredError(bool explicitOutput)
        => AssertControlledChainFailure(
            SpreadChain(Parser.MaxExpressionChainDepth + 1, explicitOutput));

    [Fact]
    public void SpreadChain_BoundaryIsExactlyMaxExpressionChainDepth()
    {
        // The greatest accepted and smallest rejected chains are ADJACENT, which pins the
        // depth accounting itself: a base primary costs 0 levels and each attached `*`
        // spread marker costs exactly 1, so the deepest accepted spread chain is
        // MaxExpressionChainDepth.
        Assert.False(Parser.Parse(SpreadChain(Parser.MaxExpressionChainDepth)).HasErrors);
        Assert.True(Parser.Parse(SpreadChain(Parser.MaxExpressionChainDepth + 1)).HasErrors);
    }

    [Fact]
    public void SpreadChain_JustAboveLimit_ReportsOneDeterministicDiagnosticOnTheOffendingOperator()
    {
        // Smallest over-limit chain. The diagnostic must point at the `*` spread
        // marker that crossed the limit — the (MaxExpressionChainDepth + 1)-th —
        // rather than at the whole expression (matching the dot-call chain guard,
        // which anchors on the dot token).
        var source = SpreadChain(Parser.MaxExpressionChainDepth + 1, explicitOutput: false);
        var offendingColumn = "1".Length + (Parser.MaxExpressionChainDepth * SpreadContinuation.Length) + 1;

        var first = AssertControlledChainFailure(source);
        Assert.Equal(1, first.Span.StartLineNumber);
        Assert.Equal(offendingColumn, first.Span.StartColumn);
        Assert.Equal(1, first.Span.EndLineNumber);
        Assert.Equal(offendingColumn, first.Span.EndColumn);

        // Parsing terminates normally and repeats identically: same severity, message, span.
        for (var repeat = 0; repeat < 3; repeat++)
        {
            var again = AssertControlledChainFailure(source);
            Assert.Equal(first.Severity, again.Severity);
            Assert.Equal(first.Message, again.Message);
            Assert.Equal(first.Span.StartLineNumber, again.Span.StartLineNumber);
            Assert.Equal(first.Span.StartColumn, again.Span.StartColumn);
            Assert.Equal(first.Span.EndLineNumber, again.Span.EndLineNumber);
            Assert.Equal(first.Span.EndColumn, again.Span.EndColumn);
        }
    }

    [Fact]
    public void DotThenSpreadChain_UsesOneCombinedExpressionChainBudget()
    {
        // A member chain may precede the attached `*` spread markers; both
        // continuation kinds charge the same flat budget, with no reset at the
        // marker boundary. (A dot AFTER a spread is the fluent
        // `operand*.Target(...)` lowering, charged to the same budget through
        // its call node.)
        var dotCount = Parser.MaxExpressionChainDepth / 2;
        var spreadCount = Parser.MaxExpressionChainDepth - dotCount;

        Assert.False(Parser.Parse(DotThenSpreadChain(dotCount, spreadCount)).HasErrors);
        AssertControlledChainFailure(DotThenSpreadChain(dotCount, spreadCount + 1));
    }

    [Fact]
    public void NestedCallArguments_OverBudget_EmitNestingDiagnostic()
    {
        // Call arguments nest structurally (`F(F(...))`) and are bounded by the
        // parser recursion budget rather than the flat-chain guard: deep nesting
        // reports the structured nesting diagnostic, never a crash. (The spread
        // marker itself has no call form — chained spread is the flat `value**`
        // postfix chain covered above.)
        var source = Rep("F(", 5000) + "1" + Rep(")", 5000);
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(
            result.Diagnostics,
            d => d.Message.Contains("Nesting is too deep", StringComparison.Ordinal));
    }

    private static string Rep(string s, int n) => string.Concat(Enumerable.Repeat(s, n));

    [Fact]
    public void ThousandsOfIndependentShortExpressions_RemainAccepted()
    {
        var source = string.Join(Environment.NewLine, Enumerable.Repeat("1", 5_000));
        Assert.False(Parser.Parse(source).HasErrors);
    }

    [Fact]
    public void CommaListAndSequenceHeavySources_AreNotTreatedAsOperatorChains()
    {
        var items = string.Join(", ", Enumerable.Repeat("1", 2_000));
        Assert.False(Parser.Parse("Output = " + items).HasErrors);
        Assert.False(Parser.Parse("Output = [" + items + "]").HasErrors);
        Assert.False(Parser.Parse("Output = (" + items + ")").HasErrors);
    }

    [Fact]
    public async Task ExtremeOperatorChains_AreControlledInSubprocess()
    {
        var assemblyPath = typeof(ParserExpressionChainDepthTests).Assembly.Location;
        var testName = typeof(ParserExpressionChainDepthTests).FullName
            + ".ExtremeOperatorChains_ProbeChild";
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
        startInfo.Environment["DOTNET_NOLOGO"] = "1";

        using var process = new Process { StartInfo = startInfo };
        process.Start();
        var stdoutTask = process.StandardOutput.ReadToEndAsync();
        var stderrTask = process.StandardError.ReadToEndAsync();

        var exited = true;
        using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(30));
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

        Assert.True(exited, "Expression-chain probe subprocess did not exit within 30 seconds.");
        Assert.DoesNotContain("Stack overflow", combined, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("StackOverflowException", combined, StringComparison.OrdinalIgnoreCase);
        Assert.True(
            process.ExitCode == 0,
            $"Expression-chain probe subprocess exited with {process.ExitCode}.{Environment.NewLine}{combined}");
    }

    [Fact]
    public void ExtremeOperatorChains_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        var sources = new[]
        {
            BinaryChain("+", 5_000),
            BinaryChain("<", 5_000),
            BinaryChain("==", 5_000),
            BinaryChain("and", 5_000),
            MultilineTrailingOperatorChain("+", 5_000),
            DotCallChain(5_000),
            DotCallChain(5_000, leadingNewlines: true),
            SpreadChain(5_000),
        };

        Assert.All(sources, source => AssertControlledChainFailure(source));

        static void AssertControlledNestingFailure(string source)
        {
            var result = Parser.ParseSyntax(source);
            Assert.True(result.HasErrors);
            Assert.Contains(
                result.Diagnostics,
                diagnostic => diagnostic.Message.Contains(
                    "Nesting is too deep",
                    StringComparison.Ordinal));
        }

        // Run the recursive forms in this fresh process as well. The parent
        // test executes this child from whichever Debug/Release assembly is
        // under test, proving the configured diagnostic boundary is reached
        // without terminating the host.
        AssertControlledNestingFailure(Rep("(", 5_000) + "1" + Rep(")", 5_000));
        AssertControlledNestingFailure(Rep("F(", 5_000) + "1" + Rep(")", 5_000));
        AssertControlledNestingFailure(
            Rep("G(F(", 5_000) + "1" + Rep("))", 5_000));
        AssertControlledNestingFailure(Rep("F(", 5_000) + "1");
    }
}
