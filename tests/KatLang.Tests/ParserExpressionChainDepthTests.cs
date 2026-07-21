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
        };

        Assert.All(sources, source => AssertControlledChainFailure(source));
    }
}
