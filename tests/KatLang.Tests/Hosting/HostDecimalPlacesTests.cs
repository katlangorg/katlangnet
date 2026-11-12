using System.Globalization;
using KatLang.Formatting;
using KatLang.Rendering;
using KatLang.Semantics;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests.Hosting;

/// <summary>
/// <see cref="RunOptions.MinDecimalPlaces"/> and <see cref="RunOptions.MaxDecimalPlaces"/>: the
/// HOST decimal-places settings. The contract under test (Q-10 D-F, extended to both settings on
/// 2026-11-12; the composition table itself is pinned by
/// <see cref="DecimalPlacesCompositionTests"/>, the formatting rule by
/// <see cref="DecimalPlacesFormattingTests"/>, and the consistency errors by
/// <see cref="DecimalPlacesConsistencyTests"/>):
/// <list type="bullet">
///   <item>COMPOSITION — the program root's own <c>MinDecimalPlaces</c> / <c>MaxDecimalPlaces</c>
///   property is the SOURCE setting; each setting composes with its counterpart by the minimum of
///   the present ones, otherwise it stays absent; an invalid source setting is still its own
///   failure whatever the host setting (a host setting never excuses it);</item>
///   <item>DISPLAY ONLY — values, atoms, emitted counts, diagnostics, the evaluation budget,
///   the random stream, host operations, and the property cache are exactly those of the same
///   run without a host setting;</item>
///   <item>ONE effective pair per run, read identically by every rendering surface;</item>
///   <item>immutable HOST configuration, each value validated at initialization — never a KatLang
///   declaration, so parsing, name resolution, and editor tooling never see it.</item>
/// </list>
/// Most pins were written for the one former setting and are kept on the MAXIMUM, its direct
/// successor; the laws that are not about a particular text run on BOTH settings
/// (<see cref="Setting"/>).
/// </summary>
public class HostDecimalPlacesTests
{
    /// <summary>One of the two independent decimal-places settings.</summary>
    public enum Setting
    {
        Min,
        Max,
    }

    private static RunOptions Default(int? decimals) => new() { MaxDecimalPlaces = decimals };

    /// <summary>Options carrying ONLY the given host setting; the other one stays absent.</summary>
    private static RunOptions Host(Setting setting, int? places, long? seed = null) => setting == Setting.Min
        ? new RunOptions { MinDecimalPlaces = places, RandomSeed = seed }
        : new RunOptions { MaxDecimalPlaces = places, RandomSeed = seed };

    /// <summary>A program root's own declaration of the given setting, as one source line.</summary>
    private static string Declare(Setting setting, int places)
        => $"{setting}DecimalPlaces = {places.ToString(CultureInfo.InvariantCulture)}\n";

    private static int? Effective(Setting setting, DisplayOptions options)
        => setting == Setting.Min ? options.MinDecimalPlaces : options.MaxDecimalPlaces;

    private static DisplayOptions WithHost(Setting setting, DisplayOptions options, int? places) => setting == Setting.Min
        ? options with { HostMinDecimalPlaces = places }
        : options with { HostMaxDecimalPlaces = places };

    private static readonly Setting[] Settings = [Setting.Min, Setting.Max];

    private static string Display(RunResult result) => result.ToDisplayString().ReplaceLineEndings("\n");

    private static RunResult.Success Success(string source, RunOptions? options = null)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, options));

    private static readonly OutputFormattingOptions LayoutOptions = new() { NewLine = "\n" };

    /// <summary>Every rendering surface of one run, as one comparable tuple.</summary>
    private static (string Canonical, string Rendered, string Exact, string Readable, string Concise) Renderings(RunResult run)
        => (
            Display(run),
            run.RenderDisplay().Text.ReplaceLineEndings("\n"),
            OutputFormatters.Exact.Format(run).ReplaceLineEndings("\n"),
            OutputFormatters.Readable.Format(run, LayoutOptions),
            OutputFormatters.Concise.Format(run, LayoutOptions));

    /// <summary>
    /// The raw outcome of a successful run — everything a host default must leave alone —
    /// compared exactly: structural value equality, the canonical (quantum-faithful)
    /// rendering of the value under the baseline's own display options, emitted count, output
    /// rows, and the host atoms spelled by the one canonical number renderer.
    /// </summary>
    private static void AssertSameRawOutcome(RunResult.Success expected, RunResult.Success actual)
    {
        Assert.True(Result.ValueComparer.Equals(expected.Value, actual.Value), $"expected {expected.Value} but got {actual.Value}");
        Assert.Equal(
            Display(expected),
            Display(actual with { DisplayOptions = expected.DisplayOptions }));
        Assert.Equal(expected.EmittedCount, actual.EmittedCount);
        Assert.Equal(expected.OutputRows.Count, actual.OutputRows.Count);
        Assert.Equal(
            expected.Atoms.Select(ValueTextRenderer.FormatNumberInvariant),
            actual.Atoms.Select(ValueTextRenderer.FormatNumberInvariant));
    }

    private static void AssertSameFailure(RunResult expected, RunResult actual)
    {
        Assert.Equal(expected.GetType(), actual.GetType());
        var expectedErrors = Errors(expected);
        var actualErrors = Errors(actual);
        Assert.Equal(expectedErrors, actualErrors);
        Assert.Equal(Display(expected), Display(actual));

        static IReadOnlyList<(KatLangErrorCode Code, string Message, SourceSpan? Span)> Errors(RunResult run)
            => run switch
            {
                RunResult.EvalFailure e => [.. e.Errors.Select(error => (error.Code, error.Message, error.Span))],
                RunResult.ParseFailure p => [.. p.Errors.Select(error => (error.Code, error.Message, error.Span))],
                RunResult.NoProgramOutput n => [(n.Diagnostic.Code, n.Diagnostic.Message, n.Diagnostic.Span)],
                RunResult.Success => throw new InvalidOperationException("expected a failure"),
            };
    }

    // ── Configuration ────────────────────────────────────────────────────────

    [Fact]
    public void Default_IsAbsent_AndTheRangeIsTheDocumentedOne()
    {
        Assert.Null(new RunOptions().MinDecimalPlaces);
        Assert.Null(new RunOptions().MaxDecimalPlaces);
        Assert.Equal(99, RunOptions.DecimalPlacesLimit);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(34)]
    [InlineData(RunOptions.DecimalPlacesLimit)]
    public void ValidDefaults_AreKeptExactly(int decimals)
    {
        Assert.Equal(decimals, Default(decimals).MaxDecimalPlaces);
        Assert.Null(Default(decimals).MinDecimalPlaces);

        // Neither setting is derived from the other: a minimum alone leaves the maximum absent.
        var minimumOnly = new RunOptions { MinDecimalPlaces = decimals };
        Assert.Equal(decimals, minimumOnly.MinDecimalPlaces);
        Assert.Null(minimumOnly.MaxDecimalPlaces);
    }

    [Theory]
    [InlineData(-1)]
    [InlineData(RunOptions.DecimalPlacesLimit + 1)]
    [InlineData(int.MinValue)]
    [InlineData(int.MaxValue)]
    public void OutOfRangeDefaults_AreRejectedAtInitialization_NeverClamped(int decimals)
    {
        // The options object cannot exist with an invalid default, so no synchronous or
        // asynchronous entry point — and no source diagnostic or span — is ever involved.
        var exception = Assert.Throws<ArgumentOutOfRangeException>(() => Default(decimals));
        Assert.Equal(nameof(RunOptions.MaxDecimalPlaces), exception.ParamName);
        Assert.Equal(decimals, exception.ActualValue);
        Assert.Contains($"between 0 and {RunOptions.DecimalPlacesLimit}", exception.Message, StringComparison.Ordinal);

        var minimum = Assert.Throws<ArgumentOutOfRangeException>(() => new RunOptions { MinDecimalPlaces = decimals });
        Assert.Equal(nameof(RunOptions.MinDecimalPlaces), minimum.ParamName);
        Assert.Equal(decimals, minimum.ActualValue);
        Assert.Contains($"between 0 and {RunOptions.DecimalPlacesLimit}", minimum.Message, StringComparison.Ordinal);
    }

    // ── Composition ──────────────────────────────────────────────────────────

    [Fact]
    public void NoDefault_KeepsCanonicalDisplay_ByteForByte()
    {
        var canonical = Display(KatLangEngine.Run("1 / 7"));
        Assert.Equal("0.1428571428571428571428571428571429", canonical);
        Assert.Equal(canonical, Display(KatLangEngine.Run("1 / 7", new RunOptions())));
        Assert.Equal(canonical, Display(KatLangEngine.Run("1 / 7", Default(null))));
    }

    [Fact]
    public void HostDefaultOnly_ControlsTheDisplay()
    {
        var run = Success("1 / 7", Default(3));
        Assert.Equal("0.143", Display(run));
        Assert.Equal(3, run.DisplayOptions.MaxDecimalPlaces);
    }

    [Fact]
    public void SourcePropertyOnly_IsUnchanged()
        => Assert.Equal("0.142857", Display(KatLangEngine.Run("MaxDecimalPlaces = 6\n1 / 7")));

    [Theory]
    [InlineData(0, "0")]
    [InlineData(3, "0.143")]
    [InlineData(6, "0.142857")]
    [InlineData(RunOptions.DecimalPlacesLimit, "0.142857")]
    public void DeclaredProperty_ComposesWithTheHostFilter_ByMinimum(int hostFilter, string expected)
    {
        var run = Success("MaxDecimalPlaces = 6\n1 / 7", Default(hostFilter));
        Assert.Equal(expected, Display(run));
        Assert.Equal(Math.Min(6, hostFilter), run.DisplayOptions.MaxDecimalPlaces);
    }

    [Fact]
    public void Zero_IsARealSetting_NeverAbsence()
    {
        // A declared 0 is the smaller filter beside a host filter of 5; a host filter of 0
        // applies (midpoints round away from zero, so 2.5 shows 3 and -2.5 shows -3); no
        // filter keeps the digits.
        Assert.Equal("3\n-3", Display(KatLangEngine.Run("MaxDecimalPlaces = 0\n2.5, -2.5", Default(5))));
        Assert.Equal("3\n-3", Display(KatLangEngine.Run("2.5, -2.5", Default(0))));
        Assert.Equal("2.5\n-2.5", Display(KatLangEngine.Run("2.5, -2.5", Default(null))));
    }

    [Fact]
    public void OnlyTheRootsOwnDeclaration_IsTheSourceFilter()
    {
        // A nested MaxDecimalPlaces is an ordinary property of its block and an opened member is
        // not declared by the root: neither is the program's source display filter (unchanged
        // behavior), so the host filter alone applies to both.
        const string nested = "A = {\n    MaxDecimalPlaces = 2\n    1 / 7\n}\nA";
        const string opened = "open M\nM = {\n    public MaxDecimalPlaces = 2\n}\n1 / 7";

        foreach (var source in new[] { nested, opened })
        {
            Assert.Equal(Display(KatLangEngine.Run("1 / 7")), Display(Success(source)));
            Assert.Equal("0.1429", Display(Success(source, Default(4))));
        }
    }

    /// <summary>
    /// Every way a DECLARED <c>MaxDecimalPlaces</c> can fail — a wrong value kind, a
    /// multi-value or empty output, a non-integer, a count outside the range, a failing
    /// evaluation, a callable that cannot be demanded with zero arguments, and a body without
    /// output.
    /// </summary>
    public static TheoryData<string> InvalidDeclarations => new()
    {
        "MaxDecimalPlaces = -1\nMath.Pi",
        "MaxDecimalPlaces = 1.5\nMath.Pi",
        "MaxDecimalPlaces = 2.5\nMath.Pi",
        "MaxDecimalPlaces = Math.Sqrt(-1)\nMath.Pi",
        "MaxDecimalPlaces = 'x'\nMath.Pi",
        "MaxDecimalPlaces = true\nMath.Pi",
        "MaxDecimalPlaces = [2]\nMath.Pi",
        "MaxDecimalPlaces = 2, 3\nMath.Pi",
        "MaxDecimalPlaces = (2, 3)\nMath.Pi",
        "MaxDecimalPlaces = ()\nMath.Pi",
        "MaxDecimalPlaces = 100\nMath.Pi",
        "MaxDecimalPlaces = 1000000000\nMath.Pi",
        "MaxDecimalPlaces = 1 / 0\nMath.Pi",
        "MaxDecimalPlaces = Missing\nMath.Pi",
        "MaxDecimalPlaces(x) = x\nMath.Pi",
        "MaxDecimalPlaces = {}\nMath.Pi",
    };

    /// <summary>
    /// A host filter never excuses an invalid source filter — not even a stricter one (host
    /// <c>0</c>): the declared property is still evaluated and validated, and its failure is
    /// exactly the failure without any host filter.
    /// </summary>
    [Theory]
    [MemberData(nameof(InvalidDeclarations))]
    public async Task InvalidDeclaredProperty_StillFails_AsItsOwnFailure_WhateverTheHostFilter(string source)
    {
        var absent = KatLangEngine.Run(source);
        Assert.IsType<RunResult.EvalFailure>(absent);

        foreach (var hostDefault in new int?[] { 0, 2, RunOptions.DecimalPlacesLimit })
        {
            AssertSameFailure(absent, KatLangEngine.Run(source, Default(hostDefault)));
            AssertSameFailure(absent, await KatLangEngine.RunAsync(source, Default(hostDefault)));
        }
    }

    // ── Display only: evaluation is untouched ────────────────────────────────

    public static TheoryData<string> ProgramsWithoutMaxDecimalPlaces => new()
    {
        "1 / 7",
        "2.5, -2.5, 0.125",
        "(1 / 3, [2 / 3, (0.5, 'text')], true)",
        "Math.Sqrt(-1), 9e6144 * 10, Math.Ln(0), -0, -0.0, 0.0, 0",
        "F(x) = x / 3\nmap([1, 2, 3], F)",
        "1.50, 0.000000000000000000000000000",
        "([]*)",
        "()",
        "'only text'",
    };

    [Theory]
    [MemberData(nameof(ProgramsWithoutMaxDecimalPlaces))]
    public void HostDefault_ChangesOnlyTheEffectiveDecimals(string source)
    {
        var baseline = Success(source);
        foreach (var setting in Settings)
        foreach (var decimals in new int?[] { null, 0, 2, RunOptions.DecimalPlacesLimit })
        {
            var configured = Success(source, Host(setting, decimals));
            AssertSameRawOutcome(baseline, configured);
            Assert.Equal(WithHost(setting, baseline.DisplayOptions, decimals), configured.DisplayOptions);
            Assert.Equal(decimals, Effective(setting, configured.DisplayOptions));
            // The other setting stays absent: neither supplies a value for the other.
            Assert.Null(Effective(setting == Setting.Min ? Setting.Max : Setting.Min, configured.DisplayOptions));
            Assert.Equal(
                KatLangEngine.EvaluateToAtoms(source).Select(ValueTextRenderer.FormatNumberInvariant),
                KatLangEngine.EvaluateToAtoms(source, Host(setting, decimals)).Select(ValueTextRenderer.FormatNumberInvariant));
        }
    }

    /// <summary>
    /// Budget neutrality at the public façade: the host default costs no evaluation step. The
    /// program succeeds at exactly its step boundary and fails one step below it, with or
    /// without the default; the same count in a DECLARED property is evaluated and costs
    /// steps, which is what makes the boundary sensitive.
    /// </summary>
    [Fact]
    public void HostDefault_CostsNoEvaluationStep()
    {
        const string program = "F(x) = x / 3\nmap([1, 2, 3, 4], F), 1 / 7";

        static RunResult RunWithin(string source, long maxSteps, int? decimals, Setting setting = Setting.Max)
            => KatLangEngine.Run(source, new RunOptions
            {
                EvaluationLimits = new EvaluationLimits { MaxSteps = maxSteps },
                MinDecimalPlaces = setting == Setting.Min ? decimals : null,
                MaxDecimalPlaces = setting == Setting.Max ? decimals : null,
            });

        long boundary = 1;
        while (!RunWithin(program, boundary, null).IsSuccess)
        {
            Assert.True(boundary < 100_000, "the program never fit a step budget");
            boundary++;
        }

        Assert.True(boundary > 1, "the boundary must be measurable one step below it");
        // A maximum alone never pads, so 3 / 3 shows as the plain 1.
        Assert.Equal("[0.33, 0.67, 1, 1.33]\n0.14", Display(RunWithin(program, boundary, 2)));

        foreach (var setting in Settings)
        foreach (var decimals in new int?[] { null, 0, 2, RunOptions.DecimalPlacesLimit })
        {
            Assert.True(RunWithin(program, boundary, decimals, setting).IsSuccess);
            var below = Assert.IsType<RunResult.EvalFailure>(RunWithin(program, boundary - 1, decimals, setting));
            Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, Assert.Single(below.Errors).Code);
        }

        // The power anchor: a declared property IS evaluated, so the same count written as
        // either property no longer fits the program's own boundary.
        Assert.False(RunWithin($"MaxDecimalPlaces = 2\n{program}", boundary, null).IsSuccess);
        Assert.False(RunWithin($"MinDecimalPlaces = 2\n{program}", boundary, null).IsSuccess);
    }

    [Fact]
    public void HostDefault_DrawsNothing_SoTheSeededStreamIsUnchanged()
    {
        // A trailing draw after several random calls: any consumed word would shift it.
        const string source = "P = Math.RandomInt(0, 1e30)\nMath.Random(0, 1), P, P(), randomInt(-5, 5), Math.Random(0, 1)";

        var baseline = Success(source, new RunOptions { RandomSeed = 42 });
        foreach (var setting in Settings)
        foreach (var decimals in new int?[] { 0, 3, RunOptions.DecimalPlacesLimit })
        {
            var configured = Success(source, Host(setting, decimals, seed: 42));
            AssertSameRawOutcome(baseline, configured);
            Assert.Equal(decimals, Effective(setting, configured.DisplayOptions));
        }
    }

    [Fact]
    public void RandomValuedDeclaration_StillEvaluatesAfterTheOutput_AndComposes()
    {
        // The declared property keeps its stream position (after the output rows) whatever the
        // host filter is; its drawn value decides the display when it is the smaller filter, and
        // a stricter host filter decides otherwise — the draw happens either way.
        const string source = "Math.Random(0, 1)\nMaxDecimalPlaces = Math.RandomInt(2, 5)";

        var baseline = Success(source, new RunOptions { RandomSeed = 7 });
        var looser = Success(source, new RunOptions { RandomSeed = 7, MaxDecimalPlaces = 9 });
        var stricter = Success(source, new RunOptions { RandomSeed = 7, MaxDecimalPlaces = 1 });

        AssertSameRawOutcome(baseline, looser);
        AssertSameRawOutcome(baseline, stricter);
        // The result keeps the drawn source filter as evaluated beside the host filter; the
        // looser host filter changes no effective count.
        Assert.Equal(baseline.DisplayOptions with { HostMaxDecimalPlaces = 9 }, looser.DisplayOptions);
        Assert.Equal(baseline.DisplayOptions with { HostMaxDecimalPlaces = 1 }, stricter.DisplayOptions);
        Assert.Equal(baseline.DisplayOptions.MaxDecimalPlaces, looser.DisplayOptions.MaxDecimalPlaces);
        Assert.InRange(looser.DisplayOptions.MaxDecimalPlaces!.Value, 2, 4);
        Assert.Equal(Display(baseline), Display(looser));
        Assert.Equal(1, stricter.DisplayOptions.MaxDecimalPlaces);
    }

    [Fact]
    public void DeclaredMaxDecimalPlaces_KeepsItsPropertyCacheReuse()
    {
        // `MaxDecimalPlaces = A` reads the SAME cached A the output row drew, so the display
        // count equals the first output value — with or without a host default.
        const string source = "A = Math.RandomInt(2, 5)\nMaxDecimalPlaces = A\nA, Math.Random(0, 1)";

        var baseline = Success(source, new RunOptions { RandomSeed = 11 });
        var configured = Success(source, new RunOptions { RandomSeed = 11, MaxDecimalPlaces = 8 });

        AssertSameRawOutcome(baseline, configured);
        Assert.Equal(baseline.DisplayOptions with { HostMaxDecimalPlaces = 8 }, configured.DisplayOptions);
        Assert.Equal(baseline.DisplayOptions.MaxDecimalPlaces, configured.DisplayOptions.MaxDecimalPlaces);
        Assert.Equal((int)configured.Atoms[0], configured.DisplayOptions.MaxDecimalPlaces);
    }

    [Fact]
    public void HostDefault_InvokesNoHostOperation_WhileADeclaredPropertyStillMay()
    {
        var counter = new HostOperationApiTests.Counter();
        var operations = HostOperations.Create(HostOperation.Create("Digits", (_, _) =>
        {
            counter.Increment();
            return new Result.Atom(4);
        }));

        // Unused by the program: the default never invokes it.
        Assert.Equal("0.14", Display(Success("1 / 7", new RunOptions { HostOperations = operations, MaxDecimalPlaces = 2 })));
        Assert.Equal(0, counter.Count);

        // Used by the output: invoked exactly once, as without a default.
        Assert.Equal("0.57", Display(Success("Digits / 7", new RunOptions { HostOperations = operations, MaxDecimalPlaces = 2 })));
        Assert.Equal(1, counter.Count);

        // A declared property calling it is ordinary evaluation: it is still evaluated beside a
        // stricter host filter (which then decides, Q-10 D-F), and decides beside a looser one.
        Assert.Equal("0.1", Display(Success("MaxDecimalPlaces = Digits\n1 / 7", new RunOptions { HostOperations = operations, MaxDecimalPlaces = 1 })));
        Assert.Equal(2, counter.Count);
        Assert.Equal("0.1429", Display(Success("MaxDecimalPlaces = Digits\n1 / 7", new RunOptions { HostOperations = operations, MaxDecimalPlaces = 9 })));
        Assert.Equal(3, counter.Count);
    }

    [Fact]
    public void Cancellation_BehavesExactlyAsWithoutADefault()
    {
        using var source = new CancellationTokenSource();
        source.Cancel();

        foreach (var decimals in new int?[] { null, 2 })
        {
            var sourceCancelled = Assert.Throws<OperationCanceledException>(() => KatLangEngine.Run(
                "1 / 7",
                new RunOptions { SourceProcessingCancellationToken = source.Token, MaxDecimalPlaces = decimals }));
            Assert.Equal(source.Token, sourceCancelled.CancellationToken);

            var evaluationCancelled = Assert.Throws<OperationCanceledException>(() => KatLangEngine.Run(
                "1 / 7",
                new RunOptions { EvaluationCancellationToken = source.Token, MaxDecimalPlaces = decimals }));
            Assert.Equal(source.Token, evaluationCancelled.CancellationToken);
        }
    }

    // ── One effective setting, every rendering surface ────────────────────────

    public static TheoryData<string, int> RenderingPrograms => new()
    {
        { "1 / 7", 3 },
        { "(1 / 3, [2 / 3, 1.5], 'label')", 2 },
        { "2.5, -2.5, 0.125, -0.125", 0 },
        { "2.5, -2.5, 0.125, -0.125", 2 },
        { "Math.Sqrt(-1), 9e6144 * 10, Math.Ln(0), -0, -0.0, 0.0, 0", 5 },
        { "(('neto', 1473.8), ('taxes', 998.365))", 2 },
        { "1 / 3", RunOptions.DecimalPlacesLimit },
    };

    /// <summary>
    /// The rendering law, for each setting: a host setting of <c>n</c> renders exactly like the
    /// same program declaring that property as <c>n</c>, on every rendering surface. (Evaluation
    /// cost is not compared: the declared property is evaluated.)
    /// </summary>
    [Theory]
    [MemberData(nameof(RenderingPrograms))]
    public void HostDefault_RendersLikeTheSameDeclaredProperty(string program, int decimals)
    {
        foreach (var setting in Settings)
        {
            var declared = KatLangEngine.Run(Declare(setting, decimals) + program);
            var hosted = KatLangEngine.Run(program, Host(setting, decimals));

            Assert.IsType<RunResult.Success>(declared);
            Assert.Equal(Renderings(declared), Renderings(hosted));
        }
    }

    /// <summary>
    /// The composition law (Q-10 D-F), for each setting: with a declared property AND a host
    /// setting of the same name, every rendering surface renders exactly like the program
    /// declaring only the smaller count — a larger host setting changes nothing, a smaller one
    /// decides.
    /// </summary>
    [Theory]
    [MemberData(nameof(RenderingPrograms))]
    public void DeclaredProperty_RendersLikeTheSmallerFilterAlone(string program, int declaredDecimals)
    {
        foreach (var setting in Settings)
        {
            var source = Declare(setting, declaredDecimals) + program;
            var absent = Success(source);

            foreach (var hostFilter in new[] { 0, 7, RunOptions.DecimalPlacesLimit })
            {
                var effective = Math.Min(declaredDecimals, hostFilter);
                var hosted = Success(source, Host(setting, hostFilter));
                var smallerAlone = Success(Declare(setting, effective) + program);

                Assert.Equal(WithHost(setting, absent.DisplayOptions, hostFilter), hosted.DisplayOptions);
                Assert.Equal(effective, Effective(setting, hosted.DisplayOptions));
                Assert.Equal(Renderings(smallerAlone), Renderings(hosted));
                if (hostFilter >= declaredDecimals)
                    Assert.Equal(Renderings(absent), Renderings(hosted));
            }
        }
    }

    [Fact]
    public void SpecialValuesAndSignedZero_KeepTheOneRenderersSpellings()
    {
        // Non-finite values keep NaN / Infinity / -Infinity under every setting. A maximum alone
        // never pads and shows a zero by its value: -0 and -0.0 are both -0, sign kept.
        Assert.Equal(
            "NaN\nInfinity\n-Infinity\n-0\n-0\n0\n0",
            Display(KatLangEngine.Run("Math.Sqrt(-1), 9e6144 * 10, Math.Ln(0), -0, -0.0, 0.0, 0", Default(5))));
        Assert.Equal(
            "(NaN, [Infinity, -0], 1.5)",
            Display(KatLangEngine.Run("(Math.Sqrt(-1), [9e6144 * 10, -0.0], 1.5)", Default(5))));

        // A minimum pads every finite number — whole numbers and both zeros included — and
        // never a non-finite one.
        Assert.Equal(
            "NaN\nInfinity\n-Infinity\n-0.00000\n-0.00000\n0.00000\n0.00000",
            Display(KatLangEngine.Run("Math.Sqrt(-1), 9e6144 * 10, Math.Ln(0), -0, -0.0, 0.0, 0", Host(Setting.Min, 5))));
        Assert.Equal(
            "(NaN, [Infinity, -0.00000], 1.50000)",
            Display(KatLangEngine.Run("(Math.Sqrt(-1), [9e6144 * 10, -0.0], 1.5)", Host(Setting.Min, 5))));
    }

    [Fact]
    public void DisplayBound_StillApplies_WhenTheDefaultLengthensTheNumbers()
    {
        // Canonical 1/3 is 36 characters and fits a 40-unit bound; padded to a minimum of 99
        // places it cannot, and every surface reports the SAME bounded overflow instead of
        // building the long text. (A maximum of 99 lengthens nothing: it never pads.)
        var options = new RunOptions
        {
            EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 40 },
            MinDecimalPlaces = RunOptions.DecimalPlacesLimit,
        };
        Assert.False(KatLangEngine.Run("1 / 3", new RunOptions { EvaluationLimits = options.EvaluationLimits }).RenderDisplay().LimitExceeded);
        Assert.False(KatLangEngine.Run("1 / 3", new RunOptions
        {
            EvaluationLimits = options.EvaluationLimits,
            MaxDecimalPlaces = RunOptions.DecimalPlacesLimit,
        }).RenderDisplay().LimitExceeded);

        var run = Success("1 / 3", options);
        foreach (var rendering in new[]
                 {
                     run.RenderDisplay(),
                     OutputFormatters.Exact.RenderDisplay(run),
                     OutputFormatters.Readable.RenderDisplay(run),
                     OutputFormatters.Concise.RenderDisplay(run),
                 })
        {
            Assert.True(rendering.LimitExceeded);
            Assert.Equal(KatLangErrorCode.DisplayLengthLimitExceeded, rendering.LimitError!.Code);
            Assert.True(rendering.Text.Length <= 40);
        }
    }

    // ── Sync / async parity ──────────────────────────────────────────────────

    public static TheoryData<string, int?> ParityCases => new()
    {
        { "1 / 7", null },
        { "1 / 7", 3 },
        { "MaxDecimalPlaces = 6\n1 / 7", null },
        { "MaxDecimalPlaces = 6\n1 / 7", 3 },
        { "MaxDecimalPlaces = 0\n2.5, -2.5", 7 },
        { "MaxDecimalPlaces = -1\n1 / 7", 3 },
        { "(1 / 3, [2 / 3])", 0 },
    };

    [Theory]
    [MemberData(nameof(ParityCases))]
    public async Task RunAsync_ResolvesTheSameEffectiveSettingAsRun(string source, int? decimals)
    {
        var sync = KatLangEngine.Run(source, Default(decimals));
        var asynchronous = await KatLangEngine.RunAsync(source, Default(decimals));

        Assert.Equal(sync.GetType(), asynchronous.GetType());
        Assert.Equal(sync.DisplayOptions, asynchronous.DisplayOptions);
        Assert.Equal(Renderings(sync), Renderings(asynchronous));
    }

    /// <summary>Source and host pairs — partial, complete, equal, and conflicting across origins.</summary>
    public static TheoryData<string, int?, int?> PairParityCases => new()
    {
        { "10, 1 / 7", 2, null },
        { "10, 1 / 7", null, 4 },
        { "10, 1 / 7", 2, 4 },
        { "10, 1 / 7", 2, 2 },
        { "10, 1 / 7", 0, RunOptions.DecimalPlacesLimit },
        { "MinDecimalPlaces = 3\n10, 1 / 7", 1, null },
        { "MinDecimalPlaces = 3\n10, 1 / 7", 5, null },
        { "MinDecimalPlaces = 2\n10, 1 / 7", null, 4 },
        { "MinDecimalPlaces = 2\nMaxDecimalPlaces = 4\n10, 1 / 7", 1, 3 },
        { "MaxDecimalPlaces = 7\n10, 1 / 7", null, 10 },
        { "MinDecimalPlaces = -1\n10, 1 / 7", 3, 5 },
        { "MinDecimalPlaces = 4\n10, 1 / 7", null, 2 },
        { "MaxDecimalPlaces = 2\n10, 1 / 7", 4, null },
        { "MinDecimalPlaces = 4\nMaxDecimalPlaces = 2\n10, 1 / 7", null, null },
    };

    [Theory]
    [MemberData(nameof(PairParityCases))]
    public async Task RunAsync_ResolvesTheSamePairAsRun(string source, int? hostMin, int? hostMax)
    {
        SourceProvenance.ParseValid(source);
        var options = new RunOptions { MinDecimalPlaces = hostMin, MaxDecimalPlaces = hostMax };
        var sync = KatLangEngine.Run(source, options);
        var asynchronous = await KatLangEngine.RunAsync(source, options);

        Assert.Equal(sync.GetType(), asynchronous.GetType());
        Assert.Equal(sync.DisplayOptions, asynchronous.DisplayOptions);
        Assert.Equal(Renderings(sync), Renderings(asynchronous));
        if (sync is RunResult.EvalFailure failure)
        {
            var error = Assert.Single(failure.Errors);
            var twin = Assert.Single(((RunResult.EvalFailure)asynchronous).Errors);
            Assert.Equal((error.Code, error.Message, error.Span), (twin.Code, twin.Message, twin.Span));
            Assert.Equal(KatLangErrorCode.IllegalInEval, error.Code);
        }
    }

    [Fact]
    public async Task AsyncTwinPath_AgreesWithTheSynchronousRun()
    {
        // A genuinely suspending asynchronous host operation routes evaluation through the
        // async twins; a declared MaxDecimalPlaces computed from that suspended work is still
        // evaluated and composes with the host filter by their minimum, and the result matches
        // the synchronous run of the same program over a synchronous operation returning the
        // same value.
        var asyncOperations = HostOperations.Create(HostOperation.CreateAsync("Digits", async (_, _) =>
        {
            await Task.Yield();
            return new Result.Atom(4);
        }));
        var syncOperations = HostOperations.Create(HostOperation.Create("Digits", (_, _) => new Result.Atom(4)));

        foreach (var (source, decimals) in new (string, int?)[]
                 {
                     ("Digits / 7", 2),
                     ("MaxDecimalPlaces = Digits\n1 / 7", 2),
                     ("MaxDecimalPlaces = Digits - 5\n1 / 7", 2),
                     ("MinDecimalPlaces = Digits - 3\n1 / 8", 2),
                     ("MinDecimalPlaces = Digits - 3\nMaxDecimalPlaces = Digits - 2\n1 / 7, 10", 9),
                     ("MinDecimalPlaces = Digits\n1 / 8", 2),
                     ("Digits / 7", null),
                 })
        {
            var asynchronous = await KatLangEngine.RunAsync(
                source, new RunOptions { HostOperations = asyncOperations, MaxDecimalPlaces = decimals });
            var sync = KatLangEngine.Run(
                source, new RunOptions { HostOperations = syncOperations, MaxDecimalPlaces = decimals });

            Assert.Equal(sync.GetType(), asynchronous.GetType());
            Assert.Equal(sync.DisplayOptions, asynchronous.DisplayOptions);
            Assert.Equal(Renderings(sync), Renderings(asynchronous));
        }

        Assert.Equal("0.57", Display(await KatLangEngine.RunAsync(
            "Digits / 7", new RunOptions { HostOperations = asyncOperations, MaxDecimalPlaces = 2 })));
        Assert.Equal("0.14", Display(await KatLangEngine.RunAsync(
            "MaxDecimalPlaces = Digits\n1 / 7", new RunOptions { HostOperations = asyncOperations, MaxDecimalPlaces = 2 })));
        Assert.Equal("0.1429", Display(await KatLangEngine.RunAsync(
            "MaxDecimalPlaces = Digits\n1 / 7", new RunOptions { HostOperations = asyncOperations, MaxDecimalPlaces = 5 })));
    }

    // ── Immutable configuration, isolated runs ───────────────────────────────

    [Fact]
    public void OneOptionsObject_AppliesTheSameDefaultToEveryRun()
    {
        var options = Default(3);

        Assert.Equal("0.143", Display(KatLangEngine.Run("1 / 7", options)));
        Assert.Equal("0.143", Display(KatLangEngine.Run("MaxDecimalPlaces = 6\n1 / 7", options)));
        Assert.Equal("0.1", Display(KatLangEngine.Run("MaxDecimalPlaces = 1\n1 / 7", options)));
        Assert.Equal("0.143", Display(KatLangEngine.Run("1 / 7", options)));
        Assert.Equal(3, options.MaxDecimalPlaces);
    }

    [Fact]
    public void ConcurrentRunsWithDifferentDefaults_DoNotInteract()
    {
        var two = Default(2);
        var eight = Default(8);
        var displays = new string[64];

        Parallel.For(0, displays.Length, i =>
            displays[i] = Display(KatLangEngine.Run("1 / 7, 2 / 3", i % 2 == 0 ? two : eight)));

        for (var i = 0; i < displays.Length; i++)
            Assert.Equal(i % 2 == 0 ? "0.14\n0.67" : "0.14285714\n0.66666667", displays[i]);
    }

    // ── Never a declaration ──────────────────────────────────────────────────

    [Fact]
    public async Task ParsingAndEditorTooling_IgnoreTheDefault()
    {
        const string source = "A = 1 / 7\nA";
        var plain = Parser.Parse(source);
        var configured = Parser.Parse(source, Default(4));
        var configuredAsync = await Parser.ParseAsync(source, Default(4));
        var bothConfigured = Parser.Parse(source, new RunOptions { MinDecimalPlaces = 1, MaxDecimalPlaces = 4 });

        // The host pair is evaluation-display configuration: the parser ignores it entirely, so
        // even a pair no run would accept changes nothing about parsing.
        var inconsistent = Parser.Parse(source, new RunOptions { MinDecimalPlaces = 5, MaxDecimalPlaces = 3 });

        foreach (var parsed in new[] { configured, configuredAsync, bothConfigured, inconsistent })
        {
            Assert.False(parsed.HasErrors);
            Assert.Equal(
                plain.Diagnostics.Select(d => (d.Code, d.Message, d.Span)),
                parsed.Diagnostics.Select(d => (d.Code, d.Message, d.Span)));
            Assert.Equal(new[] { "A" }, parsed.Root.Properties.Select(p => p.Name));

            var model = SemanticModelBuilder.Build(parsed);
            foreach (var name in new[] { "MinDecimalPlaces", "MaxDecimalPlaces" })
            {
                Assert.Empty(model.FindDeclarations(name));
                Assert.DoesNotContain(model.GetVisibleSymbolsAt(new SourcePosition(2, 1)), symbol => symbol.Name == name);
            }
        }
    }

    [Fact]
    public void ProgramReadingTheName_StillSeesNoDeclaration()
    {
        // A host setting is not a property: reading `MinDecimalPlaces` or `MaxDecimalPlaces` stays
        // an implicit parameter of the root, failing exactly as it does without a host setting.
        foreach (var source in new[] { "MaxDecimalPlaces + 1", "MinDecimalPlaces + 1" })
        {
            AssertSameFailure(KatLangEngine.Run(source), KatLangEngine.Run(source, Default(4)));
            AssertSameFailure(
                KatLangEngine.Run(source),
                KatLangEngine.Run(source, new RunOptions { MinDecimalPlaces = 1, MaxDecimalPlaces = 4 }));
        }
    }

    // ── Corpus differential ──────────────────────────────────────────────────

    public static TheoryData<string> SpecCaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var specCase in LanguageSpecCorpus.AllCases().OrderBy(static c => c.Id, StringComparer.Ordinal))
            data.Add(specCase.Id);
        return data;
    }

    private static readonly IReadOnlyDictionary<string, SpecCase> SpecById =
        LanguageSpecCorpus.AllCases().ToDictionary(static c => c.Id, StringComparer.Ordinal);

    /// <summary>
    /// Over the whole executable specification, for each setting: an explicit <c>null</c> host
    /// setting is byte-for-byte the unconfigured run; a configured one leaves every raw outcome
    /// and every failure untouched and becomes the run's effective value composed with what a
    /// program declares — the minimum of the two (Q-10 D-F), so a larger host setting changes no
    /// rendering of a declaring program at all. A case whose own declared pair the host setting
    /// contradicts fails with the consistency error instead, never with a repaired display.
    /// </summary>
    [Theory]
    [MemberData(nameof(SpecCaseIds))]
    public void Corpus_DefaultChangesOnlyTheEffectiveDecimals(string caseId)
    {
        var source = SpecById[caseId].Source;
        var baseline = KatLangEngine.Run(source);

        var explicitNull = KatLangEngine.Run(source, new RunOptions { MinDecimalPlaces = null, MaxDecimalPlaces = null });
        Assert.Equal(baseline.GetType(), explicitNull.GetType());
        Assert.Equal(baseline.DisplayOptions, explicitNull.DisplayOptions);
        Assert.Equal(baseline.ToDisplayString(), explicitNull.ToDisplayString());

        foreach (var setting in Settings)
        {
            var configured = KatLangEngine.Run(source, Host(setting, 7));
            if (baseline is not RunResult.Success success)
            {
                Assert.Equal(baseline.GetType(), configured.GetType());
                Assert.Equal(baseline.ToDisplayString(), configured.ToDisplayString());
                continue;
            }

            var expectedOptions = WithHost(setting, success.DisplayOptions, 7);
            if (expectedOptions.MinDecimalPlaces > expectedOptions.MaxDecimalPlaces)
            {
                var conflict = Assert.Single(Assert.IsType<RunResult.EvalFailure>(configured).Errors);
                Assert.Equal(KatLangErrorCode.IllegalInEval, conflict.Code);
                Assert.Contains("MinDecimalPlaces must not exceed MaxDecimalPlaces: ", conflict.Message, StringComparison.Ordinal);
                continue;
            }

            var configuredSuccess = Assert.IsType<RunResult.Success>(configured);
            AssertSameRawOutcome(success, configuredSuccess);

            var declared = Effective(setting, success.DisplayOptions);
            Assert.Equal(expectedOptions, configuredSuccess.DisplayOptions);
            Assert.Equal(declared is { } own ? Math.Min(own, 7) : 7, Effective(setting, configuredSuccess.DisplayOptions));
            if (declared <= 7)
                Assert.Equal(Renderings(success), Renderings(configuredSuccess));
        }
    }
}
