using System.Globalization;
using KatLang.Formatting;
using KatLang.Tests.Randomness;

namespace KatLang.Tests.Hosting;

public class DisplayDecimalsHostileReviewTests
{
    private static readonly TimeSpan Timeout = TimeSpan.FromSeconds(30);
    private static readonly OutputFormatter[] Formatters =
        [OutputFormatters.Exact, OutputFormatters.Readable, OutputFormatters.Concise];

    [Theory]
    [InlineData(null)]
    [InlineData(0)]
    [InlineData(99)]
    public async Task SuspendedSourceSetting_PreservesDrawOrderAndHostCalls_BeforeBoundedRendering(int? hostDefault)
    {
        const long seed = 20260923;
        const string source = "Mark(random(0, 1))\nDisplayDecimals = Digits(randomInt(6, 9))";
        var words = SeededRun.Words(seed);
        var fraction = ReferenceRandomOracle.Random(words, 0, 1);
        var digits = ReferenceRandomOracle.RandomInt(words, 6, 9);
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = new List<string>();
        var operations = HostOperations.Create(
            HostOperation.Create("Mark", (args, _) =>
            {
                calls.Add("output");
                Assert.Equal(fraction, Assert.IsType<Result.Atom>(Assert.Single(args)).Value);
                return args[0];
            }, "value"),
            HostOperation.CreateAsync("Digits", async (args, _) =>
            {
                calls.Add("display");
                Assert.Equal(digits, Assert.IsType<Result.Atom>(Assert.Single(args)).Value);
                reached.SetResult();
                await release.Task;
                return args[0];
            }, "value"));

        var pending = KatLangEngine.RunAsync(source, new RunOptions
        {
            HostOperations = operations,
            RandomSeed = seed,
            DefaultDisplayDecimals = hostDefault,
            EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 5 },
        });
        try
        {
            await reached.Task.WaitAsync(Timeout);
            Assert.False(pending.IsCompleted);
            Assert.Equal(["output", "display"], calls);
        }
        finally
        {
            release.TrySetResult();
        }

        var result = Assert.IsType<RunResult.Success>(await pending.WaitAsync(Timeout));
        Assert.Equal(fraction, Assert.Single(result.Atoms));
        Assert.Equal(1, result.EmittedCount);
        Assert.Equal((int)digits, result.DisplayOptions.Decimals);
        Assert.Equal(["output", "display"], calls);
        Assert.True(result.RenderDisplay().LimitExceeded);
        foreach (var formatter in Formatters)
        {
            var rendering = formatter.RenderDisplay(result);
            Assert.True(rendering.LimitExceeded);
            Assert.Equal(KatLangErrorCode.DisplayLengthLimitExceeded, rendering.LimitError!.Code);
            Assert.InRange(rendering.Text.Length, 0, 5);
        }
    }

    [Theory]
    [InlineData(null)]
    [InlineData(0)]
    [InlineData(99)]
    public async Task CancellationDuringSourceSetting_IsNotRescuedByTheDefault(int? hostDefault)
    {
        using var cancellation = new CancellationTokenSource();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = new List<string>();
        var operations = HostOperations.Create(
            HostOperation.Create("Output", (_, _) => { calls.Add("output"); return new Result.Atom(1); }),
            HostOperation.CreateAsync("Digits", async (_, token) =>
            {
                calls.Add("display");
                Assert.Equal(cancellation.Token, token);
                reached.SetResult();
                await release.Task.WaitAsync(token);
                return new Result.Atom(2);
            }));
        var pending = KatLangEngine.RunAsync("Output\nDisplayDecimals = Digits", new RunOptions
        {
            HostOperations = operations,
            DefaultDisplayDecimals = hostDefault,
            EvaluationCancellationToken = cancellation.Token,
        });
        try
        {
            await reached.Task.WaitAsync(Timeout);
            Assert.False(pending.IsCompleted);
            Assert.Equal(["output", "display"], calls);
            cancellation.Cancel();
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await pending.WaitAsync(Timeout));
            Assert.Equal(cancellation.Token, error.CancellationToken);
            Assert.Equal(["output", "display"], calls);
        }
        finally
        {
            release.TrySetResult();
        }
    }

    [Theory]
    [InlineData("open 'https://katlang.org/display-audit.kat'\nThird", 4)]
    [InlineData("M = load('https://katlang.org/display-audit.kat')\nM.Third", 4)]
    [InlineData("M = load('https://katlang.org/display-audit.kat')\nDisplayDecimals = M.DisplayDecimals\nM.Third", 2)]
    public async Task LoadedDisplayProperty_OnlyDecidesWhenTheCallerDeclaresIt(string source, int expectedDecimals)
    {
        var downloads = 0;
        var run = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, new RunOptions
        {
            DefaultDisplayDecimals = 4,
            DownloadCode = (_, _) =>
            {
                downloads++;
                return ValueTask.FromResult("public DisplayDecimals = 2\npublic Third = 1 / 3");
            },
        }));
        Assert.Equal(1, downloads);
        Assert.Equal(expectedDecimals, run.DisplayOptions.Decimals);
        Assert.Equal(expectedDecimals == 2 ? "0.33" : "0.3333", run.ToDisplayString());
    }

    [Fact]
    public async Task InvalidLoadedSource_BlocksOutputAndDisplayHostOperations_WithIdenticalDiagnostics()
    {
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.Create("Tick", (_, _) =>
        {
            calls++;
            return new Result.Atom(2);
        }));
        string[]? baseline = null;
        foreach (var decimals in new int?[] { null, 0, 99 })
        {
            var downloads = 0;
            var result = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(
                "open 'https://katlang.org/display-audit.kat'\nTick\nDisplayDecimals = Tick", new RunOptions
                {
                    DefaultDisplayDecimals = decimals,
                    HostOperations = operations,
                    DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult("public Broken = 1 +"); },
                }));
            Assert.Equal(1, downloads);
            Assert.Equal(0, calls);
            var diagnostics = result.Errors.Select(error => $"{error.Code}|{error.Span}|{error.Message}").ToArray();
            baseline ??= diagnostics;
            Assert.Equal(baseline, diagnostics);
        }
    }

    [Theory]
    [InlineData("if(0.125, 1, 0)", KatLangErrorCode.TypeMismatch)]
    [InlineData("(0.125, 0.375):2", KatLangErrorCode.BadIndex)]
    [InlineData("DisplayDecimals(1) = 2\nDisplayDecimals(2) = 3\n1 / 7", KatLangErrorCode.NoMatchingBranch)]
    public async Task NumericAndConditionalDiagnostics_KeepCanonicalTextAndSpans(string source, KatLangErrorCode code)
    {
        SourceProvenance.ParseValid(source);
        var baseline = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        Assert.Equal(code, Assert.Single(baseline.Errors).Code);
        foreach (var decimals in new[] { 0, 99 })
        {
            var run = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source,
                new RunOptions { DefaultDisplayDecimals = decimals }));
            Assert.Equal(
                baseline.Errors.Select(error => (error.Code, error.Message, error.Span)),
                run.Errors.Select(error => (error.Code, error.Message, error.Span)));
            Assert.Equal(baseline.ToDisplayString(), run.ToDisplayString());
            foreach (var formatter in Formatters)
                Assert.Equal(baseline.ToDisplayString(), formatter.Format(run));
        }
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(34)]
    [InlineData(99)]
    public void ExtremeAndQuantumValues_HostAndSourceUseIdenticalFormatting(int decimals)
    {
        const string source = "9e6144, 1e-6176, -1e-6176, 1, 1.0, 1.00, 0.5 + 0.5, -0, -0.0, 0.125, -0.125";
        var hosted = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source,
            new RunOptions { DefaultDisplayDecimals = decimals }));
        var declared = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            $"DisplayDecimals = {decimals.ToString(CultureInfo.InvariantCulture)}\n{source}"));
        Assert.Equal(declared.ToDisplayString(), hosted.ToDisplayString());
        foreach (var formatter in Formatters)
            Assert.Equal(formatter.Format(declared), formatter.Format(hosted));
        Assert.Equal(declared.Atoms, hosted.Atoms);
    }

    [Fact]
    public void RetainedResults_AndTheirCopies_FormatConcurrentlyAfterOtherRuns()
    {
        var options = new RunOptions { DefaultDisplayDecimals = 2 };
        var first = Assert.IsType<RunResult.Success>(KatLangEngine.Run("1 / 7", options));
        var second = Assert.IsType<RunResult.Success>(KatLangEngine.Run("DisplayDecimals = 8\n1 / 7", options));
        _ = KatLangEngine.Run("DisplayDecimals = 0\n1 / 7", options);
        var firstCopy = first with { };
        Assert.Equal(first, firstCopy);
        Assert.Equal(first.GetHashCode(), firstCopy.GetHashCode());
        // Display configuration was already part of record equality before this feature.
        Assert.NotEqual(first, first with { DisplayOptions = second.DisplayOptions });
        Parallel.For(0, 96, i =>
        {
            var run = i % 2 == 0 ? firstCopy : second;
            var expected = i % 2 == 0 ? "0.14" : "0.14285714";
            Assert.Equal(expected, run.ToDisplayString());
            foreach (var formatter in Formatters)
                Assert.Equal(expected, formatter.Format(run));
        });
        Assert.Equal(2, options.DefaultDisplayDecimals);
    }

    [Fact]
    public void OutputlessPrograms_DoNotEvaluateTheSourceSettingOrCreateOutput()
    {
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.Create("Digits", (_, _) =>
        {
            calls++;
            return new Result.Atom(2);
        }));
        foreach (var decimals in new int?[] { null, 0, 99 })
        {
            var run = KatLangEngine.Run("DisplayDecimals = Digits", new RunOptions
            {
                DefaultDisplayDecimals = decimals,
                HostOperations = operations,
            });
            Assert.IsType<RunResult.NoProgramOutput>(run);
            Assert.Equal(0, calls);
        }
    }
}
