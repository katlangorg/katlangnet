using System.Globalization;

namespace KatLang.CLI.Tests;

public class DecimalPlacesCliReviewTests
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
            // 1 / 9 carries 34 fractional digits. A maximum rounds and never pads, so 98 and 99
            // show the stored 34 digits; a minimum pads and never rounds, so they add zeros.
            var ninth = "0." + new string('1', 34);
            foreach (var (token, expected) in new[] { ("0", "0"), ("1", "0.1"), ("98", ninth), ("99", ninth), ("+2", "0.11"), ("02", "0.11"), ("-0", "0") })
            {
                var result = await Cli.InvokeAsync("eval", "--max-decimal-places", token, "--random-seed", token, "1 / 9");
                Assert.Equal(0, result.ExitCode);
                Assert.Equal("", result.Error);
                Assert.Equal(expected, result.TrimmedOutput);
            }
            foreach (var (token, expected) in new[] { ("0", ninth), ("1", ninth), ("98", ninth + new string('0', 64)), ("99", ninth + new string('0', 65)), ("+2", ninth), ("02", ninth), ("-0", ninth) })
            {
                var result = await Cli.InvokeAsync("eval", "--min-decimal-places", token, "--random-seed", token, "1 / 9");
                Assert.Equal(0, result.ExitCode);
                Assert.Equal("", result.Error);
                Assert.Equal(expected, result.TrimmedOutput);
            }
            foreach (var token in new[] { "٢", "２", "−2", " 2", "2\t", "1e2", "0x10", "1.5", "+", "999999999999999999999999", "-999999999999999999999999" })
            foreach (var option in new[] { "--random-seed", "--min-decimal-places", "--max-decimal-places" })
            {
                var result = await Cli.InvokeAsync("eval", "1", option, token);
                Assert.Equal(1, result.ExitCode);
                Assert.Equal("", result.Output);
                Assert.Contains($"option '{option}' requires an integer between", result.Error);
            }
            foreach (var token in new[] { "-1", "100", "-2147483648", "2147483647" })
            foreach (var option in new[] { "--min-decimal-places", "--max-decimal-places" })
                Assert.Equal(1, (await Cli.InvokeAsync("eval", "1", option, token)).ExitCode);
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
        foreach (var option in new[] { new[] { "--allow-loading" }, ["--random-seed", "0"], ["--min-decimal-places", "0"], ["--max-decimal-places", "0"] })
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
    [InlineData("--display-decimals")]
    [InlineData("--display-decimal")]
    [InlineData("--display-digits")]
    [InlineData("--decimal-places")]
    [InlineData("--max-decimal-place")]
    [InlineData("--max-decimal-places=2")]
    [InlineData("--min-decimal-places=2")]
    public async Task UndocumentedSpellings_RemainUnknownOptions(string option)
    {
        var result = await Cli.InvokeAsync("eval", "1", option);
        Assert.Equal(1, result.ExitCode);
        Assert.Contains($"unknown option '{option}'", result.Error);
    }

    [Theory]
    [InlineData("abc")]
    [InlineData("100")]
    [InlineData("--random-seed")]
    [InlineData("--allow-loading")]
    public async Task BadDisplayOption_PrecedesFileIoAndModuleAcquisition(string token)
    {
        var calls = 0;
        ValueTask<string> Download(string _, CancellationToken __)
        {
            calls++;
            throw new InvalidOperationException("CLI parsing must happen first");
        }
        foreach (var option in new[] { "--min-decimal-places", "--max-decimal-places" })
        foreach (var command in new[] { "run", "check", "eval" })
        {
            var source = command == "eval" ? "open 'https://katlang.org/display-audit.kat'\n1" : "missing-display-audit.kat";
            var result = await Cli.InvokeWithDownloaderAsync(Download,
                command, source, "--allow-loading", option, token);
            Assert.Equal(1, result.ExitCode);
            Assert.Equal("", result.Output);
            Assert.Contains($"option '{option}' requires", result.Error);
            Assert.DoesNotContain("file not found", result.Error);
            Assert.Equal(0, calls);
        }
    }

    [Fact]
    public async Task AllOptionsAndTerminator_ComposeWithLoadingAndTheSourceFilter()
    {
        // The source maximum 0 is the smaller of the two maximums (Q-10 D-F: the minimum),
        // so the output is shown with no decimal places whatever the option order.
        const string url = "https://katlang.org/display-audit.kat";
        const string source = "open 'https://katlang.org/display-audit.kat'\nMaxDecimalPlaces = 0\nThird, randomInt(2, 3)";
        var groups = new[] { new[] { "--max-decimal-places", "99" }, ["--random-seed", "123"], ["--allow-loading"] };
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
