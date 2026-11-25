using System.Globalization;
using KatLang.Formatting;
using KatLang.Tests.Randomness;

namespace KatLang.Tests.Hosting;

public class DecimalPlacesHostileReviewTests
{
    private static readonly TimeSpan Timeout = TimeSpan.FromSeconds(30);
    private static readonly OutputFormatter[] Formatters =
        [OutputFormatters.Exact, OutputFormatters.Readable, OutputFormatters.Concise];

    /// <summary>Options carrying only the named host setting; the other stays absent.</summary>
    private static RunOptions Host(string setting, int? places, RunOptions template) => new()
    {
        MinDecimalPlaces = setting == "MinDecimalPlaces" ? places : null,
        MaxDecimalPlaces = setting == "MaxDecimalPlaces" ? places : null,
        HostOperations = template.HostOperations,
        RandomSeed = template.RandomSeed,
        EvaluationLimits = template.EvaluationLimits,
        EvaluationCancellationToken = template.EvaluationCancellationToken,
        DownloadCode = template.DownloadCode,
    };

    private static int? Effective(string setting, RunResult run)
        => setting == "MinDecimalPlaces" ? run.DisplayOptions.MinDecimalPlaces : run.DisplayOptions.MaxDecimalPlaces;

    // A host setting of 5 is smaller than every possible drawn source setting (6..9), so it
    // decides the display (Q-10 D-F) while the source setting is still evaluated, suspended
    // and all; 99 is larger, so the drawn source setting decides. The same holds for either
    // property.
    [Theory]
    [InlineData("MaxDecimalPlaces", null)]
    [InlineData("MaxDecimalPlaces", 5)]
    [InlineData("MaxDecimalPlaces", 99)]
    [InlineData("MinDecimalPlaces", null)]
    [InlineData("MinDecimalPlaces", 5)]
    [InlineData("MinDecimalPlaces", 99)]
    public async Task SuspendedSourceSetting_PreservesDrawOrderAndHostCalls_BeforeBoundedRendering(string setting, int? hostDefault)
    {
        const long seed = 20260923;
        var source = $"Mark(random(0, 1))\n{setting} = Digits(randomInt(6, 9))";
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

        // A drawn fraction shows at least "0.d" — three characters — under either setting, so a
        // two-character bound is exceeded whatever digits the seed produced.
        var pending = KatLangEngine.RunAsync(source, Host(setting, hostDefault, new RunOptions
        {
            HostOperations = operations,
            RandomSeed = seed,
            EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 2 },
        }));
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
        Assert.Equal(hostDefault is { } host ? Math.Min(host, (int)digits) : (int)digits, Effective(setting, result));
        Assert.Equal(["output", "display"], calls);
        Assert.True(result.RenderDisplay().LimitExceeded);
        foreach (var formatter in Formatters)
        {
            var rendering = formatter.RenderDisplay(result);
            Assert.True(rendering.LimitExceeded);
            Assert.Equal(KatLangErrorCode.DisplayLengthLimitExceeded, rendering.LimitError!.Code);
            Assert.InRange(rendering.Text.Length, 0, 2);
        }
    }

    [Theory]
    [InlineData("MaxDecimalPlaces", null)]
    [InlineData("MaxDecimalPlaces", 0)]
    [InlineData("MaxDecimalPlaces", 99)]
    [InlineData("MinDecimalPlaces", null)]
    [InlineData("MinDecimalPlaces", 0)]
    [InlineData("MinDecimalPlaces", 99)]
    public async Task CancellationDuringSourceSetting_IsNotRescuedByTheDefault(string setting, int? hostDefault)
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
        var pending = KatLangEngine.RunAsync($"Output\n{setting} = Digits", Host(setting, hostDefault, new RunOptions
        {
            HostOperations = operations,
            EvaluationCancellationToken = cancellation.Token,
        }));
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
    [InlineData("M = load('https://katlang.org/display-audit.kat')\nMaxDecimalPlaces = M.MaxDecimalPlaces\nM.Third", 2)]
    public async Task LoadedDisplayProperty_OnlyDecidesWhenTheCallerDeclaresIt(string source, int expectedDecimals)
    {
        var downloads = 0;
        var run = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, new RunOptions
        {
            MaxDecimalPlaces = 4,
            DownloadCode = (_, _) =>
            {
                downloads++;
                return ValueTask.FromResult("public MaxDecimalPlaces = 2\npublic Third = 1 / 3");
            },
        }));
        Assert.Equal(1, downloads);
        Assert.Equal(expectedDecimals, run.DisplayOptions.MaxDecimalPlaces);
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
                "open 'https://katlang.org/display-audit.kat'\nTick\nMaxDecimalPlaces = Tick", new RunOptions
                {
                    MaxDecimalPlaces = decimals,
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
    [InlineData("(0.125, 0.375)[2]", KatLangErrorCode.BadIndex)]
    [InlineData("MaxDecimalPlaces(1) = 2\nMaxDecimalPlaces(2) = 3\n1 / 7", KatLangErrorCode.NoMatchingBranch)]
    public async Task NumericAndConditionalDiagnostics_KeepCanonicalTextAndSpans(string source, KatLangErrorCode code)
    {
        SourceProvenance.ParseValid(source);
        var baseline = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        Assert.Equal(code, Assert.Single(baseline.Errors).Code);
        foreach (var decimals in new[] { 0, 99 })
        {
            var run = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source,
                new RunOptions { MaxDecimalPlaces = decimals }));
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
        foreach (var setting in new[] { "MinDecimalPlaces", "MaxDecimalPlaces" })
        {
            var hosted = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, Host(setting, decimals, new RunOptions())));
            var declared = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
                $"{setting} = {decimals.ToString(CultureInfo.InvariantCulture)}\n{source}"));
            Assert.Equal(declared.ToDisplayString(), hosted.ToDisplayString());
            foreach (var formatter in Formatters)
                Assert.Equal(formatter.Format(declared), formatter.Format(hosted));
            Assert.Equal(declared.Atoms, hosted.Atoms);
        }

        // Once any setting is present, the three spellings of one (1, 1.0, 1.00, 0.5 + 0.5) and
        // the two of negative zero display alike: the text depends on the value, not the quantum.
        var rows = KatLangEngine.Run(source, new RunOptions { MaxDecimalPlaces = decimals })
            .ToDisplayString().ReplaceLineEndings("\n").Split('\n');
        Assert.Equal(["1", "1", "1", "1"], rows[3..7]);
        Assert.Equal(["-0", "-0"], rows[7..9]);
    }

    [Fact]
    public void RetainedResults_AndTheirCopies_FormatConcurrentlyAfterOtherRuns()
    {
        var options = new RunOptions { MaxDecimalPlaces = 2 };
        var first = Assert.IsType<RunResult.Success>(KatLangEngine.Run("1 / 7", options));
        // The program's own stricter filter decides its run (Q-10 D-F: the minimum of the two).
        var second = Assert.IsType<RunResult.Success>(KatLangEngine.Run("MaxDecimalPlaces = 1\n1 / 7", options));
        _ = KatLangEngine.Run("MaxDecimalPlaces = 0\n1 / 7", options);
        var firstCopy = first with { };
        Assert.Equal(first, firstCopy);
        Assert.Equal(first.GetHashCode(), firstCopy.GetHashCode());
        // Display configuration was already part of record equality before this feature.
        Assert.NotEqual(first, first with { DisplayOptions = second.DisplayOptions });
        Parallel.For(0, 96, i =>
        {
            var run = i % 2 == 0 ? firstCopy : second;
            var expected = i % 2 == 0 ? "0.14" : "0.1";
            Assert.Equal(expected, run.ToDisplayString());
            foreach (var formatter in Formatters)
                Assert.Equal(expected, formatter.Format(run));
        });
        Assert.Equal(2, options.MaxDecimalPlaces);
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
            var run = KatLangEngine.Run("MinDecimalPlaces = Digits\nMaxDecimalPlaces = Digits", new RunOptions
            {
                MinDecimalPlaces = decimals,
                MaxDecimalPlaces = decimals,
                HostOperations = operations,
            });
            Assert.IsType<RunResult.NoProgramOutput>(run);
            Assert.Equal(0, calls);
        }
    }
}
