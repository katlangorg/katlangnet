namespace KatLang.CLI.Tests;

/// <summary>
/// STR-02 through the real CLI boundary: a double-quoted string reaches KatLang exactly as the
/// argument array carries it (no shell is involved here), interpolates on both the <c>eval</c> and
/// the <c>run</c> path, prints raw at the root, and a front-end diagnostic in a hole is an ordinary
/// parse failure. Shells that strip embedded double quotes before the process sees them (Windows
/// PowerShell 5.1's native-argument passing) are a wrapper concern, documented in the STR-03 handoff.
/// </summary>
public class InterpolationCliTests
{
    [Fact]
    public async Task Eval_InterpolatesADoubleQuotedArgument()
    {
        var result = await Cli.InvokeAsync("eval", "n = 3\n\"n = {n}, list = {[n, 'x']}\"");
        Assert.Equal(0, result.ExitCode);
        Assert.Equal("n = 3, list = [3, x]", result.TrimmedOutput);
    }

    [Fact]
    public async Task Run_InterpolatesASourceFile()
    {
        using var file = new TempSourceFile("Greet(name) = \"Hello, {name}!\"\nGreet('KatLang')\n");
        var result = await Cli.InvokeAsync("run", file.Path);
        Assert.Equal(0, result.ExitCode);
        Assert.Equal("Hello, KatLang!", result.TrimmedOutput);
    }

    [Fact]
    public async Task Eval_DisplayDecimalsNeverReachTheTextOfAHole()
    {
        var result = await Cli.InvokeAsync("eval", "--display-decimals", "2", "\"{1.5}\", 1.5");
        Assert.Equal(0, result.ExitCode);
        Assert.Equal("1.5\n1.50", result.TrimmedOutput);
    }

    [Fact]
    public async Task Eval_AMalformedHoleIsAParseFailure()
    {
        var result = await Cli.InvokeAsync("eval", "\"{1, 2}\"");
        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("interpolation hole", result.TrimmedError, StringComparison.Ordinal);
    }
}
