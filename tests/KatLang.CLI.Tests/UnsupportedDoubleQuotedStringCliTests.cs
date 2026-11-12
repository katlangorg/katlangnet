namespace KatLang.CLI.Tests;

/// <summary>
/// STR-03 through the real CLI boundary: a double quote reaches KatLang exactly as the argument
/// array carries it (no shell is involved here) and is the one targeted parse failure on both the
/// <c>eval</c> and the <c>run</c> path. Nothing is evaluated and nothing is downloaded, and a
/// single-quoted string that contains double quotes or braces is ordinary text.
/// </summary>
public class UnsupportedDoubleQuotedStringCliTests
{
    [Fact]
    public async Task Eval_RejectsADoubleQuotedString_WithTheTargetedDiagnostic()
    {
        var result = await Cli.InvokeAsync("eval", "\"Hello\"");

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal("", result.TrimmedOutput);
        Assert.Contains("Double-quoted strings are not supported. Write text in single quotes: 'text'.", result.TrimmedError, StringComparison.Ordinal);
    }

    [Fact]
    public async Task Eval_RejectsInterpolation_WithoutPrintingAnyResult()
    {
        var result = await Cli.InvokeAsync("eval", "n = 3\n\"n = {n}\"\nn + 1");

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal("", result.TrimmedOutput);
        Assert.Contains("string interpolation are not supported", result.TrimmedError, StringComparison.Ordinal);
        Assert.DoesNotContain("interpolation hole", result.TrimmedError, StringComparison.Ordinal);
    }

    [Fact]
    public async Task Run_RejectsADoubleQuotedStringInASourceFile()
    {
        using var file = new TempSourceFile("Greet(name) = \"Hello, {name}!\"\nGreet('KatLang')\n");

        var result = await Cli.InvokeAsync("run", file.Path);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal("", result.TrimmedOutput);
        Assert.Contains("string interpolation are not supported", result.TrimmedError, StringComparison.Ordinal);
    }

    [Fact]
    public async Task Eval_WithLoadingAllowed_NeverDownloadsARejectedTarget()
    {
        var downloader = new RecordingDownloader(new Dictionary<string, string>
        {
            ["https://katlang.org/lib.kat"] = "public V = 1",
        });

        var result = await Cli.InvokeWithDownloaderAsync(
            downloader.DownloadAsync, "eval", "--allow-loading", "open \"https://katlang.org/lib.kat\"\nV");

        Assert.NotEqual(0, result.ExitCode);
        Assert.Empty(downloader.RequestedUrls);
        Assert.Contains("Double-quoted strings are not supported", result.TrimmedError, StringComparison.Ordinal);
    }

    [Fact]
    public async Task Eval_SingleQuotedText_KeepsDoubleQuotesBracesAndBackslashes()
    {
        var result = await Cli.InvokeAsync("eval", "'say \"hi\"', '{x}', 'C:\\temp'");

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("say \"hi\"\n{x}\nC:\\temp", result.TrimmedOutput);
    }

    [Fact]
    public async Task Eval_ANumberBesideText_StillTakesDisplayDecimals()
    {
        var result = await Cli.InvokeAsync("eval", "--display-decimals", "2", "'Total', 1.5");

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("Total\n1.50", result.TrimmedOutput);
    }
}
