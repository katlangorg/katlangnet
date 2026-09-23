using System.Globalization;

namespace KatLang.CLI.Tests;

public class DisplayDecimalsCliReviewTests
{
    [Theory]
    [InlineData("de-DE")]
    [InlineData("ar-EG")]
    public async Task NumericOptions_UseTheSameInvariantAsciiGrammar(string cultureName)
    {
        var previous = CultureInfo.CurrentCulture;
        CultureInfo.CurrentCulture = CultureInfo.GetCultureInfo(cultureName);
        try
        {
            foreach (var (token, expected) in new[] { ("0", "0"), ("1", "0.1"), ("98", "0." + new string('1', 34) + new string('0', 64)), ("99", "0." + new string('1', 34) + new string('0', 65)), ("+2", "0.11"), ("02", "0.11"), ("-0", "0") })
            {
                var result = await Cli.InvokeAsync("eval", "--display-decimals", token, "--seed", token, "1 / 9");
                Assert.Equal(0, result.ExitCode);
                Assert.Equal("", result.Error);
                Assert.Equal(expected, result.TrimmedOutput);
            }
            foreach (var token in new[] { "٢", "２", "−2", " 2", "2\t", "1e2", "0x10", "1.5", "+", "999999999999999999999999", "-999999999999999999999999" })
            foreach (var option in new[] { "--seed", "--display-decimals" })
            {
                var result = await Cli.InvokeAsync("eval", "1", option, token);
                Assert.Equal(1, result.ExitCode);
                Assert.Equal("", result.Output);
                Assert.Contains($"option '{option}' requires an integer between", result.Error);
            }
            foreach (var token in new[] { "-1", "100", "-2147483648", "2147483647" })
                Assert.Equal(1, (await Cli.InvokeAsync("eval", "1", "--display-decimals", token)).ExitCode);
        }
        finally
        {
            CultureInfo.CurrentCulture = previous;
        }
    }

    [Theory]
    [InlineData("--help")]
    [InlineData("--version")]
    public async Task GlobalOptions_RejectEveryCurrentOptionInEitherOrder_ButAllowAnEmptyTerminator(string global)
    {
        foreach (var option in new[] { new[] { "--allow-loading" }, ["--seed", "0"], ["--display-decimals", "0"] })
        foreach (var args in new[] { option.Prepend(global).ToArray(), option.Append(global).ToArray() })
        {
            var result = await Cli.InvokeAsync(args);
            Assert.Equal(1, result.ExitCode);
            Assert.Equal("", result.Output);
            Assert.Contains("cannot be combined with other arguments", result.Error);
        }
        Assert.Equal(0, (await Cli.InvokeAsync(global, "--")).ExitCode);
        Assert.Equal(1, (await Cli.InvokeAsync("--", global)).ExitCode);
    }

    [Theory]
    [InlineData("--display-decimal")]
    [InlineData("--display-digits")]
    [InlineData("--display-decimals=2")]
    public async Task UndocumentedSpellings_RemainUnknownOptions(string option)
    {
        var result = await Cli.InvokeAsync("eval", "1", option);
        Assert.Equal(1, result.ExitCode);
        Assert.Contains($"unknown option '{option}'", result.Error);
    }

    [Theory]
    [InlineData("abc")]
    [InlineData("100")]
    [InlineData("--seed")]
    [InlineData("--allow-loading")]
    public async Task BadDisplayOption_PrecedesFileIoAndModuleAcquisition(string token)
    {
        var calls = 0;
        ValueTask<string> Download(string _, CancellationToken __)
        {
            calls++;
            throw new InvalidOperationException("CLI parsing must happen first");
        }
        foreach (var command in new[] { "run", "check", "eval" })
        {
            var source = command == "eval" ? "open 'https://katlang.org/display-audit.kat'\n1" : "missing-display-audit.kat";
            var result = await Cli.InvokeWithDownloaderAsync(Download,
                command, source, "--allow-loading", "--display-decimals", token);
            Assert.Equal(1, result.ExitCode);
            Assert.Equal("", result.Output);
            Assert.Contains("option '--display-decimals' requires", result.Error);
            Assert.DoesNotContain("file not found", result.Error);
            Assert.Equal(0, calls);
        }
    }

    [Fact]
    public async Task AllOptionsAndTerminator_ComposeWithLoadingAndSourceOverride()
    {
        const string url = "https://katlang.org/display-audit.kat";
        const string source = "open 'https://katlang.org/display-audit.kat'\nDisplayDecimals = 0\nThird, randomInt(2, 3)";
        var groups = new[] { new[] { "--display-decimals", "99" }, ["--seed", "123"], ["--allow-loading"] };
        for (var a = 0; a < 3; a++)
        for (var b = 0; b < 3; b++)
        {
            if (a == b) continue;
            var c = 3 - a - b;
            var loader = new RecordingDownloader(new Dictionary<string, string> { [url] = "public Third = 1 / 3" });
            string[] args = [.. groups[a], "eval", .. groups[b], .. groups[c], "--", source];
            var result = await Cli.InvokeWithDownloaderAsync(loader.DownloadAsync, args);
            Assert.Equal(0, result.ExitCode);
            Assert.Equal("", result.Error);
            Assert.Equal("0\n2", result.TrimmedOutput);
            Assert.Equal(url, Assert.Single(loader.RequestedUrls));
        }
    }
}
