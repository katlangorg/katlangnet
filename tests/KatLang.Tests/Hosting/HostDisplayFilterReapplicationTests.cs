using KatLang.Formatting;

namespace KatLang.Tests.Hosting;

/// <summary>
/// <see cref="RunResult.WithHostDisplayDecimals"/>: re-applying the HOST display filter to a
/// completed result (Q-10 D-F; RUN-06). The contract under test, as documented on the method:
/// <list type="bullet">
///   <item>EQUIVALENCE — the returned result renders, on every surface, exactly like the same run
///   made with <see cref="RunOptions.DefaultDisplayDecimals"/> set to the new filter;</item>
///   <item>REPLACEMENT — the new host filter replaces the previous one (chained calls keep only
///   the last; <c>null</c> removes it), while the program root's own <c>DisplayDecimals</c> source
///   filter is kept and still composes by minimum;</item>
///   <item>PER VARIANT — a <see cref="RunResult.Success"/> becomes a new result sharing the run's
///   root, value and atoms; every other variant, the failure of an invalid root
///   <c>DisplayDecimals</c> included, is returned as the same instance;</item>
///   <item>VALIDATION — a filter outside 0..<see cref="RunOptions.MaxDisplayDecimals"/> is rejected
///   for every variant, never clamped;</item>
///   <item>PURITY — nothing is evaluated: no host operation runs, and the original result is
///   unchanged.</item>
/// </list>
/// Added by the final Constitution-wide audit (2026-10-10), which found the public method
/// (commit <c>3fe6fd7e</c>) pinned only by the public API baseline.
/// </summary>
public class HostDisplayFilterReapplicationTests
{
    private static readonly OutputFormattingOptions LayoutOptions = new() { NewLine = "\n" };

    private static (string Canonical, string Rendered, string Exact, string Readable, string Concise) Renderings(RunResult run)
        => (
            run.ToDisplayString().ReplaceLineEndings("\n"),
            run.RenderDisplay().Text.ReplaceLineEndings("\n"),
            OutputFormatters.Exact.Format(run).ReplaceLineEndings("\n"),
            OutputFormatters.Readable.Format(run, LayoutOptions),
            OutputFormatters.Concise.Format(run, LayoutOptions));

    public static TheoryData<string> Sources => new()
    {
        "1 / 3",
        "1 / 3, 2 / 3, 10",
        "[1 / 3, (2 / 7, 0.5)], 'text', true",
        "DisplayDecimals = 3\n1 / 7, 22 / 7",
        "DisplayDecimals = 0\n2.5, 3.5, -0.5",
        "-0, 0.000, 1.10",
    };

    public static TheoryData<string, int?> SourcesByFilter()
    {
        var data = new TheoryData<string, int?>();
        foreach (var source in Sources)
            foreach (var filter in new int?[] { null, 0, 1, 2, 5, RunOptions.MaxDisplayDecimals })
                data.Add(source, filter);
        return data;
    }

    [Theory]
    [MemberData(nameof(SourcesByFilter))]
    public void ReappliedFilter_RendersLikeTheSameRunMadeWithThatDefault(string source, int? filter)
    {
        var reapplied = KatLangEngine.Run(source).WithHostDisplayDecimals(filter);
        var direct = KatLangEngine.Run(source, new RunOptions { DefaultDisplayDecimals = filter });

        Assert.IsType<RunResult.Success>(reapplied);
        Assert.Equal(Renderings(direct), Renderings(reapplied));
    }

    [Theory]
    [MemberData(nameof(SourcesByFilter))]
    public async Task ReappliedFilter_RendersLikeTheSameAsyncRunMadeWithThatDefault(string source, int? filter)
    {
        var reapplied = (await KatLangEngine.RunAsync(source)).WithHostDisplayDecimals(filter);
        var direct = await KatLangEngine.RunAsync(source, new RunOptions { DefaultDisplayDecimals = filter });

        Assert.Equal(Renderings(direct), Renderings(reapplied));
    }

    [Fact]
    public void NewFilter_ReplacesThePreviousHostFilter_AndNullRemovesIt()
    {
        const string source = "1 / 3, 2 / 3";
        var withTwo = KatLangEngine.Run(source, new RunOptions { DefaultDisplayDecimals = 2 });

        Assert.Equal("0.33\n0.67", Renderings(withTwo).Canonical);
        Assert.Equal(
            Renderings(KatLangEngine.Run(source, new RunOptions { DefaultDisplayDecimals = 5 })),
            Renderings(withTwo.WithHostDisplayDecimals(1).WithHostDisplayDecimals(5)));
        Assert.Equal(Renderings(KatLangEngine.Run(source)), Renderings(withTwo.WithHostDisplayDecimals(null)));
        Assert.Equal(Renderings(withTwo), Renderings(withTwo.WithHostDisplayDecimals(2)));
    }

    [Fact]
    public void SourceFilter_IsKept_AndStillComposesByMinimum()
    {
        var run = KatLangEngine.Run("DisplayDecimals = 3\n1 / 7");

        Assert.Equal("0.143", Renderings(run).Canonical);
        Assert.Equal("0.143", Renderings(run.WithHostDisplayDecimals(5)).Canonical);
        Assert.Equal("0.1", Renderings(run.WithHostDisplayDecimals(1)).Canonical);
        Assert.Equal("0.143", Renderings(run.WithHostDisplayDecimals(1).WithHostDisplayDecimals(null)).Canonical);
    }

    [Fact]
    public void Success_BecomesANewResult_SharingTheRunsPayload_AndTheOriginalIsUnchanged()
    {
        var original = Assert.IsType<RunResult.Success>(KatLangEngine.Run("1 / 3, [2 / 3]"));
        var before = Renderings(original);

        var reapplied = Assert.IsType<RunResult.Success>(original.WithHostDisplayDecimals(1));

        Assert.NotSame(original, reapplied);
        Assert.Same(original.Root, reapplied.Root);
        Assert.Same(original.Value, reapplied.Value);
        Assert.Same(original.Atoms, reapplied.Atoms);
        Assert.Same(original.OutputRows, reapplied.OutputRows);
        Assert.Equal(original.EmittedCount, reapplied.EmittedCount);
        Assert.Equal(before, Renderings(original));
        Assert.NotEqual(before.Canonical, Renderings(reapplied).Canonical);
    }

    public static TheoryData<string> NonSuccessSources => new()
    {
        "1 +",
        "1 / 0",
        "DisplayDecimals = 200\n1 / 3",
        "DisplayDecimals = 1 / 0\n1 / 3",
        "# no output rows",
    };

    [Theory]
    [MemberData(nameof(NonSuccessSources))]
    public void EveryOtherVariant_IsReturnedAsTheSameInstance(string source)
    {
        var run = KatLangEngine.Run(source);
        Assert.IsNotType<RunResult.Success>(run);

        foreach (var filter in new int?[] { null, 0, 2, RunOptions.MaxDisplayDecimals })
            Assert.Same(run, run.WithHostDisplayDecimals(filter));
    }

    [Theory]
    [InlineData("1 / 3", -1)]
    [InlineData("1 / 3", RunOptions.MaxDisplayDecimals + 1)]
    [InlineData("1 / 0", -1)]
    [InlineData("1 +", RunOptions.MaxDisplayDecimals + 1)]
    [InlineData("# no output rows", -1)]
    public void FilterOutsideTheRange_IsRejectedForEveryVariant_NeverClamped(string source, int filter)
    {
        var run = KatLangEngine.Run(source);
        var error = Assert.Throws<ArgumentOutOfRangeException>(() => run.WithHostDisplayDecimals(filter));
        Assert.Equal("hostDisplayDecimals", error.ParamName);
    }

    [Fact]
    public void Reapplication_EvaluatesNothing()
    {
        var calls = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Tick", (_, _) =>
            {
                calls++;
                return new Result.Atom((System.Numerics.Decimal128)calls / 3);
            })),
        };
        var run = KatLangEngine.Run("Tick(), Tick()", options);
        Assert.Equal(2, calls);

        var reapplied = run.WithHostDisplayDecimals(2).WithHostDisplayDecimals(null).WithHostDisplayDecimals(4);
        _ = Renderings(reapplied);

        Assert.Equal(2, calls);
        Assert.Equal("0.3333\n0.6667", Renderings(reapplied).Canonical);
    }

    [Fact]
    public void Reapplication_PreservesTheDisplayBound_WhenTheNewFilterOverflows()
    {
        var limits = new EvaluationLimits { MaxDisplayLength = 40 };
        var original = Assert.IsType<RunResult.Success>(KatLangEngine.Run("1 / 3", new RunOptions
        {
            EvaluationLimits = limits,
        }));
        Assert.False(original.RenderDisplay().LimitExceeded);

        var reapplied = original.WithHostDisplayDecimals(RunOptions.MaxDisplayDecimals);
        var direct = KatLangEngine.Run("1 / 3", new RunOptions
        {
            EvaluationLimits = limits,
            DefaultDisplayDecimals = RunOptions.MaxDisplayDecimals,
        });
        foreach (var formatter in new[] { OutputFormatters.Exact, OutputFormatters.Readable, OutputFormatters.Concise })
        {
            var expected = formatter.RenderDisplay(direct);
            var actual = formatter.RenderDisplay(reapplied);
            Assert.True(actual.LimitExceeded);
            Assert.Equal(expected.Text, actual.Text);
            Assert.Equal(expected.LimitError!.Code, actual.LimitError!.Code);
            Assert.InRange(actual.Text.Length, 0, 40);
        }
        Assert.Equal(direct.RenderDisplay().Text, reapplied.RenderDisplay().Text);
        Assert.Equal(direct.RenderDisplay().LimitExceeded, reapplied.RenderDisplay().LimitExceeded);
        Assert.Equal(direct.RenderDisplay().LimitError!.Code, reapplied.RenderDisplay().LimitError!.Code);
        Assert.False(original.RenderDisplay().LimitExceeded);
    }

    [Fact]
    public async Task Reapplication_AfterSuspendedHostCallsAndSeededDraws_IsPureAndConcurrent()
    {
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.CreateAsync("Observe", async (args, _) =>
        {
            await Task.Yield();
            Interlocked.Increment(ref calls);
            return args[0];
        }, "value"));
        const string source = "Observe(random(0, 1)), Observe(random(0, 1))";
        var original = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, new RunOptions
        {
            RandomSeed = 20261010,
            HostOperations = operations,
        }));
        Assert.Equal(2, calls);
        var before = Renderings(original);
        var control = KatLangEngine.Run(source, new RunOptions
        {
            RandomSeed = 20261010,
            HostOperations = HostOperations.Create(HostOperation.Create("Observe", (args, _) => args[0], "value")),
            DefaultDisplayDecimals = 4,
        });

        var copies = await Task.WhenAll(Enumerable.Range(0, 16).Select(_ => Task.Run(() =>
            Assert.IsType<RunResult.Success>(original.WithHostDisplayDecimals(4)))));
        foreach (var copy in copies)
        {
            Assert.Same(original.Value, copy.Value);
            Assert.Same(original.OutputRows, copy.OutputRows);
            Assert.Equal(Renderings(control), Renderings(copy));
        }
        Assert.Equal(2, calls);
        Assert.Equal(before, Renderings(original));
    }
}
