using KatLang.Formatting;

namespace KatLang.Tests.Hosting;

/// <summary>
/// <see cref="RunResult.WithHostDecimalPlaces"/>: re-applying the HOST decimal-places settings to
/// a completed result (Q-10 D-F, extended to both settings on 2026-11-12; RUN-06). The contract
/// under test, as documented on the method:
/// <list type="bullet">
///   <item>EQUIVALENCE — the returned result is what the same run would have returned with
///   <see cref="RunOptions.MinDecimalPlaces"/> and <see cref="RunOptions.MaxDecimalPlaces"/> set
///   to the new pair: it renders identically on every surface, and a pair whose effective
///   minimum exceeds its effective maximum is that run's <see cref="RunResult.EvalFailure"/>;</item>
///   <item>REPLACEMENT — BOTH host settings are replaced (chained calls keep only the last pair;
///   <c>null</c> removes a setting), while the program root's own <c>MinDecimalPlaces</c> and
///   <c>MaxDecimalPlaces</c> source settings are kept and still compose by minimum;</item>
///   <item>PER VARIANT — a <see cref="RunResult.Success"/> becomes a new result sharing the run's
///   root, value and atoms, or the conflict failure; every other variant, the failure of an
///   invalid root setting included, is returned as the same instance;</item>
///   <item>VALIDATION — a value outside 0..<see cref="RunOptions.DecimalPlacesLimit"/>, and a host
///   minimum above the host maximum, are rejected for every variant, never clamped;</item>
///   <item>PURITY — nothing is evaluated: no host operation runs, and the original result is
///   unchanged.</item>
/// </list>
/// Added by the final Constitution-wide audit (2026-10-10), which found the public method
/// (commit <c>3fe6fd7e</c>) pinned only by the public API baseline; ported from the one-setting
/// <c>WithHostDisplayDecimals</c> when the two settings replaced it.
/// </summary>
public class HostDecimalPlacesReapplicationTests
{
    private static readonly OutputFormattingOptions LayoutOptions = new() { NewLine = "\n" };

    private static (string Canonical, string Rendered, string Exact, string Readable, string Concise) Renderings(RunResult run)
        => (
            run.ToDisplayString().ReplaceLineEndings("\n"),
            run.RenderDisplay().Text.ReplaceLineEndings("\n"),
            OutputFormatters.Exact.Format(run).ReplaceLineEndings("\n"),
            OutputFormatters.Readable.Format(run, LayoutOptions),
            OutputFormatters.Concise.Format(run, LayoutOptions));

    private static RunOptions Host(int? min, int? max) => new() { MinDecimalPlaces = min, MaxDecimalPlaces = max };

    /// <summary>
    /// Everything two results of the same run must share to be "what a run made with those host
    /// settings would have returned": the variant, every rendering, the display configuration,
    /// and each structured error.
    /// </summary>
    private static void AssertEquivalent(RunResult direct, RunResult reapplied)
    {
        Assert.Equal(direct.GetType(), reapplied.GetType());
        Assert.Equal(Renderings(direct), Renderings(reapplied));
        Assert.Equal(direct.DisplayOptions, reapplied.DisplayOptions);
        if (direct is RunResult.EvalFailure failure)
        {
            Assert.Equal(
                failure.Errors.Select(static e => (e.Code, e.Message, e.Span)),
                ((RunResult.EvalFailure)reapplied).Errors.Select(static e => (e.Code, e.Message, e.Span)));
        }
    }

    public static TheoryData<string> Sources => new()
    {
        "1 / 3",
        "1 / 3, 2 / 3, 10",
        "[1 / 3, (2 / 7, 0.5)], 'text', true",
        "MaxDecimalPlaces = 3\n1 / 7, 22 / 7",
        "MaxDecimalPlaces = 0\n2.5, 3.5, -0.5",
        "MinDecimalPlaces = 3\n1 / 8, 10",
        "MinDecimalPlaces = 1\nMaxDecimalPlaces = 4\n1 / 7, 10, 2.5",
        "-0, 0.000, 1.10",
    };

    private static readonly (int? Min, int? Max)[] HostPairs =
    [
        (null, null), (null, 0), (null, 1), (null, 2), (null, 5), (null, RunOptions.DecimalPlacesLimit),
        (0, null), (2, null), (5, null), (RunOptions.DecimalPlacesLimit, null),
        (0, 0), (2, 2), (1, 4), (0, RunOptions.DecimalPlacesLimit),
        (RunOptions.DecimalPlacesLimit, RunOptions.DecimalPlacesLimit),
    ];

    public static TheoryData<string, int?, int?> SourcesByHostPair()
    {
        var data = new TheoryData<string, int?, int?>();
        foreach (var source in Sources)
            foreach (var (min, max) in HostPairs)
                data.Add(source, min, max);
        return data;
    }

    /// <summary>
    /// The equivalence, conflicts included: a program declaring a minimum of 3 re-applied with a
    /// host maximum of 2 is the failure the fresh run returns, with the same message and span.
    /// </summary>
    [Theory]
    [MemberData(nameof(SourcesByHostPair))]
    public void ReappliedPair_IsWhatTheSameRunMadeWithThatPairReturns(string source, int? min, int? max)
    {
        SourceProvenance.ParseValid(source);
        var original = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));

        var reapplied = original.WithHostDecimalPlaces(min, max);
        var direct = KatLangEngine.Run(source, Host(min, max));

        AssertEquivalent(direct, reapplied);
    }

    [Theory]
    [MemberData(nameof(SourcesByHostPair))]
    public async Task ReappliedPair_IsWhatTheSameAsyncRunMadeWithThatPairReturns(string source, int? min, int? max)
    {
        var original = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source));

        var reapplied = original.WithHostDecimalPlaces(min, max);
        var direct = await KatLangEngine.RunAsync(source, Host(min, max));

        AssertEquivalent(direct, reapplied);
    }

    /// <summary>The same equivalence starting from a run that already carried a host pair.</summary>
    [Theory]
    [MemberData(nameof(SourcesByHostPair))]
    public void ReappliedPair_ReplacesTheRunsOwnHostPair(string source, int? min, int? max)
    {
        var configured = KatLangEngine.Run(source, Host(0, 1));
        if (configured is not RunResult.Success)
            return; // the first pair already conflicts with this program's own settings

        AssertEquivalent(KatLangEngine.Run(source, Host(min, max)), configured.WithHostDecimalPlaces(min, max));
    }

    [Fact]
    public void NewPair_ReplacesBothPreviousHostSettings_AndNullRemovesOne()
    {
        const string source = "1 / 3, 2 / 3, 10";
        var withTwo = KatLangEngine.Run(source, Host(2, 2));

        Assert.Equal("0.33\n0.67\n10.00", Renderings(withTwo).Canonical);

        // Chained calls keep only the last pair.
        AssertEquivalent(
            KatLangEngine.Run(source, Host(null, 5)),
            withTwo.WithHostDecimalPlaces(1, 1).WithHostDecimalPlaces(null, 5));
        Assert.Equal("0.33333\n0.66667\n10", Renderings(withTwo.WithHostDecimalPlaces(null, 5)).Canonical);

        // A null removes that host setting and leaves the other as given: the minimum of the
        // run's own pair is NOT kept when only a maximum is re-applied, and vice versa.
        Assert.Equal("0.33\n0.67\n10", Renderings(withTwo.WithHostDecimalPlaces(null, 2)).Canonical);
        Assert.Equal(
            "0.3333333333333333333333333333333333\n0.6666666666666666666666666666666667\n10.00",
            Renderings(withTwo.WithHostDecimalPlaces(2, null)).Canonical);

        // Both null: no host setting, canonical display again.
        AssertEquivalent(KatLangEngine.Run(source), withTwo.WithHostDecimalPlaces(null, null));

        // Re-applying the pair the result was produced with changes nothing.
        AssertEquivalent(withTwo, withTwo.WithHostDecimalPlaces(2, 2));
    }

    [Fact]
    public void SourceSettings_AreKept_AndStillComposeByMinimum()
    {
        var maximum = KatLangEngine.Run("MaxDecimalPlaces = 3\n1 / 7");

        Assert.Equal("0.143", Renderings(maximum).Canonical);
        Assert.Equal("0.143", Renderings(maximum.WithHostDecimalPlaces(null, 5)).Canonical);
        Assert.Equal("0.1", Renderings(maximum.WithHostDecimalPlaces(null, 1)).Canonical);
        Assert.Equal("0.143", Renderings(maximum.WithHostDecimalPlaces(null, 1).WithHostDecimalPlaces(null, null)).Canonical);

        var minimum = KatLangEngine.Run("MinDecimalPlaces = 3\n2.5");

        Assert.Equal("2.500", Renderings(minimum).Canonical);
        Assert.Equal("2.500", Renderings(minimum.WithHostDecimalPlaces(5, null)).Canonical);
        Assert.Equal("2.5", Renderings(minimum.WithHostDecimalPlaces(1, null)).Canonical);
        Assert.Equal("2.500", Renderings(minimum.WithHostDecimalPlaces(1, null).WithHostDecimalPlaces(null, null)).Canonical);
    }

    [Fact]
    public void Success_BecomesANewResult_SharingTheRunsPayload_AndTheOriginalIsUnchanged()
    {
        var original = Assert.IsType<RunResult.Success>(KatLangEngine.Run("1 / 3, [2 / 3]"));
        var before = Renderings(original);

        foreach (var (min, max) in new (int?, int?)[] { (null, 1), (40, null), (1, 1) })
        {
            var reapplied = Assert.IsType<RunResult.Success>(original.WithHostDecimalPlaces(min, max));

            Assert.NotSame(original, reapplied);
            Assert.Same(original.Root, reapplied.Root);
            Assert.Same(original.Value, reapplied.Value);
            Assert.Same(original.Atoms, reapplied.Atoms);
            Assert.Same(original.OutputRows, reapplied.OutputRows);
            Assert.Equal(original.EmittedCount, reapplied.EmittedCount);
            Assert.Equal(before, Renderings(original));
            Assert.NotEqual(before.Canonical, Renderings(reapplied).Canonical);
        }
    }

    /// <summary>
    /// A new effective pair that conflicts is the EvalFailure a fresh run returns — never a
    /// clamped, swapped, or dropped setting — positioned at the program's own declaration. The
    /// failure carries the run's root, and re-applying from the ORIGINAL success still works.
    /// </summary>
    [Fact]
    public void ConflictingEffectivePair_IsTheFreshRunsEvalFailure_AndTheOriginalStaysUsable()
    {
        const string source = "MinDecimalPlaces = 4\n1 / 7";
        var original = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal("0.1428571428571428571428571428571429", Renderings(original).Canonical);

        var conflict = Assert.IsType<RunResult.EvalFailure>(original.WithHostDecimalPlaces(null, 2));
        var error = Assert.Single(conflict.Errors);
        Assert.Equal(KatLangErrorCode.IllegalInEval, error.Code);
        Assert.Equal(
            "Illegal in eval: MinDecimalPlaces must not exceed MaxDecimalPlaces: the minimum is 4 (from the program) and the maximum is 2 (from the host).",
            error.Message);
        Assert.Equal(new SourceSpan(1, 1, 1, 17), error.Span);
        Assert.Same(original.Root, conflict.Root);
        AssertEquivalent(KatLangEngine.Run(source, Host(null, 2)), conflict);

        // A failure renders independently of every display setting: later calls return it as is.
        Assert.Same(conflict, conflict.WithHostDecimalPlaces(null, 9));
        Assert.Same(conflict, conflict.WithHostDecimalPlaces(null, null));

        // Hosts re-apply from the original success, which is unchanged and still usable.
        Assert.Equal("0.1429", Renderings(original.WithHostDecimalPlaces(null, 4)).Canonical);
        Assert.Equal("0.14286", Renderings(original.WithHostDecimalPlaces(null, 5)).Canonical);
        Assert.Equal("0.1428571428571428571428571428571429", Renderings(original).Canonical);
    }

    [Fact]
    public void ConflictingEffectivePair_IsPositionedAtTheProgramsMaximum_WhenTheMinimumIsTheHosts()
    {
        const string source = "X = 1 / 7\nMaxDecimalPlaces = 2\nX";
        var original = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));

        var conflict = Assert.IsType<RunResult.EvalFailure>(original.WithHostDecimalPlaces(4, null));
        var error = Assert.Single(conflict.Errors);
        Assert.Equal(KatLangErrorCode.IllegalInEval, error.Code);
        Assert.Equal(
            "Illegal in eval: MinDecimalPlaces must not exceed MaxDecimalPlaces: the minimum is 4 (from the host) and the maximum is 2 (from the program).",
            error.Message);
        Assert.Equal(new SourceSpan(2, 1, 2, 17), error.Span);
        AssertEquivalent(KatLangEngine.Run(source, Host(4, null)), conflict);
    }

    [Fact]
    public void ConflictFailure_CarriesTheRunsPropertyObservations()
    {
        const string source = "X = 1 / 7\nMinDecimalPlaces = 4\nX";
        var original = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run(source, new RunOptions { ObservePropertyValues = true }));
        Assert.NotNull(original.PropertyObservations);

        var conflict = Assert.IsType<RunResult.EvalFailure>(original.WithHostDecimalPlaces(null, 2));

        Assert.Same(original.PropertyObservations, conflict.PropertyObservations);
        var direct = KatLangEngine.Run(source, new RunOptions { ObservePropertyValues = true, MaxDecimalPlaces = 2 });
        Assert.Equal(
            direct.PropertyObservations!.Select(static o => (o.Name, o.Status, o.EmittedCount)),
            conflict.PropertyObservations!.Select(static o => (o.Name, o.Status, o.EmittedCount)));
    }

    public static TheoryData<string> NonSuccessSources => new()
    {
        "1 +",
        "1 / 0",
        "MaxDecimalPlaces = 200\n1 / 3",
        "MaxDecimalPlaces = 1 / 0\n1 / 3",
        "MinDecimalPlaces = 200\n1 / 3",
        "MinDecimalPlaces = 1 / 0\n1 / 3",
        "MinDecimalPlaces = 5\nMaxDecimalPlaces = 3\n1 / 3",
        "# no output rows",
    };

    [Theory]
    [MemberData(nameof(NonSuccessSources))]
    public void EveryOtherVariant_IsReturnedAsTheSameInstance(string source)
    {
        var run = KatLangEngine.Run(source);
        Assert.IsNotType<RunResult.Success>(run);

        foreach (var (min, max) in HostPairs)
            Assert.Same(run, run.WithHostDecimalPlaces(min, max));
    }

    [Theory]
    [InlineData("1 / 3", -1)]
    [InlineData("1 / 3", RunOptions.DecimalPlacesLimit + 1)]
    [InlineData("1 / 0", -1)]
    [InlineData("1 +", RunOptions.DecimalPlacesLimit + 1)]
    [InlineData("# no output rows", -1)]
    public void ValueOutsideTheRange_IsRejectedForEveryVariant_NeverClamped(string source, int value)
    {
        var run = KatLangEngine.Run(source);

        var max = Assert.Throws<ArgumentOutOfRangeException>(() => run.WithHostDecimalPlaces(null, value));
        Assert.Equal("max", max.ParamName);
        Assert.Equal(value, max.ActualValue);

        var min = Assert.Throws<ArgumentOutOfRangeException>(() => run.WithHostDecimalPlaces(value, null));
        Assert.Equal("min", min.ParamName);
        Assert.Equal(value, min.ActualValue);
    }

    /// <summary>
    /// The host's OWN pair inconsistent: a host argument error — exactly the configuration a run
    /// rejects before parsing — for every variant, never an EvalFailure and never repaired.
    /// </summary>
    [Theory]
    [InlineData("1 / 3")]
    [InlineData("MinDecimalPlaces = 1\nMaxDecimalPlaces = 9\n1 / 3")]
    [InlineData("1 / 0")]
    [InlineData("1 +")]
    [InlineData("# no output rows")]
    public void InconsistentHostPair_IsAnArgumentError_ForEveryVariant(string source)
    {
        var run = KatLangEngine.Run(source);

        foreach (var (min, max) in new[] { (5, 3), (1, 0), (RunOptions.DecimalPlacesLimit, 0) })
        {
            var error = Assert.Throws<ArgumentException>(() => run.WithHostDecimalPlaces(min, max));
            Assert.IsNotType<ArgumentOutOfRangeException>(error);
            Assert.Contains($"({min})", error.Message, StringComparison.Ordinal);
            Assert.Contains($"({max})", error.Message, StringComparison.Ordinal);

            // The engine entry point rejects the same pair the same way, before parsing.
            Assert.Throws<ArgumentException>(() => KatLangEngine.Run(source, Host(min, max)));
        }

        // Equal values, and either one alone, are consistent.
        _ = run.WithHostDecimalPlaces(3, 3);
        _ = run.WithHostDecimalPlaces(RunOptions.DecimalPlacesLimit, null);
        _ = run.WithHostDecimalPlaces(null, 0);
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
        // Both source settings call the host operation, so a re-evaluation of either would show.
        var run = KatLangEngine.Run("MinDecimalPlaces = Tick() * 0\nMaxDecimalPlaces = Tick() * 0 + 9\nTick(), Tick()", options);
        Assert.IsType<RunResult.Success>(run);
        Assert.Equal(4, calls);

        var reapplied = run.WithHostDecimalPlaces(null, 2).WithHostDecimalPlaces(null, null).WithHostDecimalPlaces(1, 4);
        _ = Renderings(reapplied);
        _ = run.WithHostDecimalPlaces(null, 0);

        Assert.Equal(4, calls);
        Assert.Equal("0.3333\n0.6667", Renderings(reapplied).Canonical);
    }

    [Fact]
    public void Reapplication_PreservesTheDisplayBound_WhenTheNewPairOverflows()
    {
        var limits = new EvaluationLimits { MaxDisplayLength = 40 };
        var original = Assert.IsType<RunResult.Success>(KatLangEngine.Run("1 / 3", new RunOptions
        {
            EvaluationLimits = limits,
        }));
        Assert.False(original.RenderDisplay().LimitExceeded);

        // A maximum of 99 lengthens nothing (it never pads); a minimum of 99 does.
        Assert.False(original.WithHostDecimalPlaces(null, RunOptions.DecimalPlacesLimit).RenderDisplay().LimitExceeded);

        var reapplied = original.WithHostDecimalPlaces(RunOptions.DecimalPlacesLimit, null);
        var direct = KatLangEngine.Run("1 / 3", new RunOptions
        {
            EvaluationLimits = limits,
            MinDecimalPlaces = RunOptions.DecimalPlacesLimit,
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
            MinDecimalPlaces = 4,
            MaxDecimalPlaces = 4,
        });

        var copies = await Task.WhenAll(Enumerable.Range(0, 16).Select(_ => Task.Run(() =>
            Assert.IsType<RunResult.Success>(original.WithHostDecimalPlaces(4, 4)))));
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
