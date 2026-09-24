using System.Globalization;
using KatLang.Formatting;
using KatLang.Rendering;
using KatLang.Semantics;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests.Hosting;

/// <summary>
/// <see cref="RunOptions.DefaultDisplayDecimals"/>: the host's display-decimals DEFAULT. The
/// contract under test:
/// <list type="bullet">
///   <item>PRECEDENCE — a top-level <c>DisplayDecimals</c> property the program declares
///   decides (an invalid one as its own failure: the default is a fallback, never error
///   recovery), otherwise the host default, otherwise canonical display;</item>
///   <item>DISPLAY ONLY — values, atoms, emitted counts, diagnostics, the evaluation budget,
///   the random stream, host operations, and the property cache are exactly those of the same
///   run without a default;</item>
///   <item>ONE effective setting per run, read identically by every rendering surface;</item>
///   <item>immutable HOST configuration, validated at initialization — never a KatLang
///   declaration, so parsing, name resolution, and editor tooling never see it.</item>
/// </list>
/// </summary>
public class DefaultDisplayDecimalsTests
{
    private static RunOptions Default(int? decimals) => new() { DefaultDisplayDecimals = decimals };

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
        Assert.Null(new RunOptions().DefaultDisplayDecimals);
        Assert.Equal(99, RunOptions.MaxDisplayDecimals);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(34)]
    [InlineData(RunOptions.MaxDisplayDecimals)]
    public void ValidDefaults_AreKeptExactly(int decimals)
        => Assert.Equal(decimals, Default(decimals).DefaultDisplayDecimals);

    [Theory]
    [InlineData(-1)]
    [InlineData(RunOptions.MaxDisplayDecimals + 1)]
    [InlineData(int.MinValue)]
    [InlineData(int.MaxValue)]
    public void OutOfRangeDefaults_AreRejectedAtInitialization_NeverClamped(int decimals)
    {
        // The options object cannot exist with an invalid default, so no synchronous or
        // asynchronous entry point — and no source diagnostic or span — is ever involved.
        var exception = Assert.Throws<ArgumentOutOfRangeException>(() => Default(decimals));
        Assert.Equal(nameof(RunOptions.DefaultDisplayDecimals), exception.ParamName);
        Assert.Equal(decimals, exception.ActualValue);
        Assert.Contains($"between 0 and {RunOptions.MaxDisplayDecimals}", exception.Message, StringComparison.Ordinal);
    }

    // ── Precedence ───────────────────────────────────────────────────────────

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
        Assert.Equal(3, run.DisplayOptions.Decimals);
    }

    [Fact]
    public void SourcePropertyOnly_IsUnchanged()
        => Assert.Equal("0.142857", Display(KatLangEngine.Run("DisplayDecimals = 6\n1 / 7")));

    [Theory]
    [InlineData(0)]
    [InlineData(3)]
    [InlineData(RunOptions.MaxDisplayDecimals)]
    public void DeclaredProperty_OverridesTheHostDefault(int hostDefault)
    {
        var run = Success("DisplayDecimals = 6\n1 / 7", Default(hostDefault));
        Assert.Equal("0.142857", Display(run));
        Assert.Equal(6, run.DisplayOptions.Decimals);
    }

    [Fact]
    public void Zero_IsARealSetting_NeverAbsence()
    {
        // A declared 0 wins over a host default of 5; a host default of 0 applies (midpoints
        // round away from zero, so 2.5 shows 3 and -2.5 shows -3); no default keeps the digits.
        Assert.Equal("3\n-3", Display(KatLangEngine.Run("DisplayDecimals = 0\n2.5, -2.5", Default(5))));
        Assert.Equal("3\n-3", Display(KatLangEngine.Run("2.5, -2.5", Default(0))));
        Assert.Equal("2.5\n-2.5", Display(KatLangEngine.Run("2.5, -2.5", Default(null))));
    }

    [Fact]
    public void OnlyTheRootsOwnDeclaration_OverridesTheDefault()
    {
        // A nested DisplayDecimals is an ordinary property of its block and an opened member is
        // not declared by the root: neither is the program's display setting (unchanged
        // behavior), so the host default applies to both.
        const string nested = "A = {\n    DisplayDecimals = 2\n    1 / 7\n}\nA";
        const string opened = "open M\nM = {\n    public DisplayDecimals = 2\n}\n1 / 7";

        foreach (var source in new[] { nested, opened })
        {
            Assert.Equal(Display(KatLangEngine.Run("1 / 7")), Display(Success(source)));
            Assert.Equal("0.1429", Display(Success(source, Default(4))));
        }
    }

    /// <summary>
    /// Every way a DECLARED <c>DisplayDecimals</c> can fail — a wrong value kind, a
    /// multi-value or empty output, a non-integer, a count outside the range, a failing
    /// evaluation, a callable that cannot be demanded with zero arguments, and a body without
    /// output.
    /// </summary>
    public static TheoryData<string> InvalidDeclarations => new()
    {
        "DisplayDecimals = -1\nMath.Pi",
        "DisplayDecimals = 1.5\nMath.Pi",
        "DisplayDecimals = 2.5\nMath.Pi",
        "DisplayDecimals = Math.Sqrt(-1)\nMath.Pi",
        "DisplayDecimals = 'x'\nMath.Pi",
        "DisplayDecimals = true\nMath.Pi",
        "DisplayDecimals = [2]\nMath.Pi",
        "DisplayDecimals = 2, 3\nMath.Pi",
        "DisplayDecimals = (2, 3)\nMath.Pi",
        "DisplayDecimals = ()\nMath.Pi",
        "DisplayDecimals = 100\nMath.Pi",
        "DisplayDecimals = 1000000000\nMath.Pi",
        "DisplayDecimals = 1 / 0\nMath.Pi",
        "DisplayDecimals = Missing\nMath.Pi",
        "DisplayDecimals(x) = x\nMath.Pi",
        "DisplayDecimals = {}\nMath.Pi",
    };

    [Theory]
    [MemberData(nameof(InvalidDeclarations))]
    public async Task InvalidDeclaredProperty_StillWins_AsItsOwnFailure(string source)
    {
        var absent = KatLangEngine.Run(source);
        Assert.IsType<RunResult.EvalFailure>(absent);

        foreach (var hostDefault in new int?[] { 0, 2, RunOptions.MaxDisplayDecimals })
        {
            AssertSameFailure(absent, KatLangEngine.Run(source, Default(hostDefault)));
            AssertSameFailure(absent, await KatLangEngine.RunAsync(source, Default(hostDefault)));
        }
    }

    // ── Display only: evaluation is untouched ────────────────────────────────

    public static TheoryData<string> ProgramsWithoutDisplayDecimals => new()
    {
        "1 / 7",
        "2.5, -2.5, 0.125",
        "(1 / 3, [2 / 3, (0.5, 'text')], true)",
        "Math.Sqrt(-1), 9e6144 * 10, Math.Ln(0), -0, -0.0, 0.0, 0",
        "F(x) = x / 3\nmap([1, 2, 3], F)",
        "1.50, 0.000000000000000000000000000",
        "[]*",
        "()",
        "'only text'",
    };

    [Theory]
    [MemberData(nameof(ProgramsWithoutDisplayDecimals))]
    public void HostDefault_ChangesOnlyTheEffectiveDecimals(string source)
    {
        var baseline = Success(source);
        foreach (var decimals in new int?[] { null, 0, 2, RunOptions.MaxDisplayDecimals })
        {
            var configured = Success(source, Default(decimals));
            AssertSameRawOutcome(baseline, configured);
            Assert.Equal(baseline.DisplayOptions with { Decimals = decimals }, configured.DisplayOptions);
            Assert.Equal(
                KatLangEngine.EvaluateToAtoms(source).Select(ValueTextRenderer.FormatNumberInvariant),
                KatLangEngine.EvaluateToAtoms(source, Default(decimals)).Select(ValueTextRenderer.FormatNumberInvariant));
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

        static RunResult RunWithin(string source, long maxSteps, int? decimals)
            => KatLangEngine.Run(source, new RunOptions
            {
                EvaluationLimits = new EvaluationLimits { MaxSteps = maxSteps },
                DefaultDisplayDecimals = decimals,
            });

        long boundary = 1;
        while (!RunWithin(program, boundary, null).IsSuccess)
        {
            Assert.True(boundary < 100_000, "the program never fit a step budget");
            boundary++;
        }

        Assert.True(boundary > 1, "the boundary must be measurable one step below it");
        // 3 / 3 is the whole number 1 (integral quantum), which stays plain at any count.
        Assert.Equal("[0.33, 0.67, 1, 1.33]\n0.14", Display(RunWithin(program, boundary, 2)));

        foreach (var decimals in new int?[] { null, 0, 2, RunOptions.MaxDisplayDecimals })
        {
            Assert.True(RunWithin(program, boundary, decimals).IsSuccess);
            var below = Assert.IsType<RunResult.EvalFailure>(RunWithin(program, boundary - 1, decimals));
            Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, Assert.Single(below.Errors).Code);
        }

        // The power anchor: a declared DisplayDecimals IS evaluated, so the same count written
        // as a property no longer fits the program's own boundary.
        Assert.False(RunWithin($"DisplayDecimals = 2\n{program}", boundary, null).IsSuccess);
    }

    [Fact]
    public void HostDefault_DrawsNothing_SoTheSeededStreamIsUnchanged()
    {
        // A trailing draw after several random calls: any consumed word would shift it.
        const string source = "P = Math.RandomInt(0, 1e30)\nMath.Random(0, 1), P, P(), randomInt(-5, 5), Math.Random(0, 1)";

        var baseline = Success(source, new RunOptions { RandomSeed = 42 });
        foreach (var decimals in new int?[] { 0, 3, RunOptions.MaxDisplayDecimals })
        {
            var configured = Success(source, new RunOptions { RandomSeed = 42, DefaultDisplayDecimals = decimals });
            AssertSameRawOutcome(baseline, configured);
            Assert.Equal(decimals, configured.DisplayOptions.Decimals);
        }
    }

    [Fact]
    public void RandomValuedDeclaration_StillEvaluatesAfterTheOutput_AndWins()
    {
        // The declared property keeps its stream position (after the output rows) and its
        // drawn value decides the display, whatever the host default says.
        const string source = "Math.Random(0, 1)\nDisplayDecimals = Math.RandomInt(2, 5)";

        var baseline = Success(source, new RunOptions { RandomSeed = 7 });
        var configured = Success(source, new RunOptions { RandomSeed = 7, DefaultDisplayDecimals = 9 });

        AssertSameRawOutcome(baseline, configured);
        Assert.Equal(baseline.DisplayOptions, configured.DisplayOptions);
        Assert.InRange(configured.DisplayOptions.Decimals!.Value, 2, 4);
        Assert.Equal(Display(baseline), Display(configured));
    }

    [Fact]
    public void DeclaredDisplayDecimals_KeepsItsPropertyCacheReuse()
    {
        // `DisplayDecimals = A` reads the SAME cached A the output row drew, so the display
        // count equals the first output value — with or without a host default.
        const string source = "A = Math.RandomInt(2, 5)\nDisplayDecimals = A\nA, Math.Random(0, 1)";

        var baseline = Success(source, new RunOptions { RandomSeed = 11 });
        var configured = Success(source, new RunOptions { RandomSeed = 11, DefaultDisplayDecimals = 8 });

        AssertSameRawOutcome(baseline, configured);
        Assert.Equal(baseline.DisplayOptions, configured.DisplayOptions);
        Assert.Equal((int)configured.Atoms[0], configured.DisplayOptions.Decimals);
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
        Assert.Equal("0.14", Display(Success("1 / 7", new RunOptions { HostOperations = operations, DefaultDisplayDecimals = 2 })));
        Assert.Equal(0, counter.Count);

        // Used by the output: invoked exactly once, as without a default.
        Assert.Equal("0.57", Display(Success("Digits / 7", new RunOptions { HostOperations = operations, DefaultDisplayDecimals = 2 })));
        Assert.Equal(1, counter.Count);

        // A declared property calling it is ordinary evaluation, and it wins.
        Assert.Equal("0.1429", Display(Success("DisplayDecimals = Digits\n1 / 7", new RunOptions { HostOperations = operations, DefaultDisplayDecimals = 1 })));
        Assert.Equal(2, counter.Count);
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
                new RunOptions { SourceProcessingCancellationToken = source.Token, DefaultDisplayDecimals = decimals }));
            Assert.Equal(source.Token, sourceCancelled.CancellationToken);

            var evaluationCancelled = Assert.Throws<OperationCanceledException>(() => KatLangEngine.Run(
                "1 / 7",
                new RunOptions { EvaluationCancellationToken = source.Token, DefaultDisplayDecimals = decimals }));
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
        { "1 / 3", RunOptions.MaxDisplayDecimals },
    };

    /// <summary>
    /// The rendering law: a host default of <c>n</c> renders exactly like the same program
    /// declaring <c>DisplayDecimals = n</c>, on every rendering surface. (Evaluation cost is not
    /// compared: the declared property is evaluated.)
    /// </summary>
    [Theory]
    [MemberData(nameof(RenderingPrograms))]
    public void HostDefault_RendersLikeTheSameDeclaredProperty(string program, int decimals)
    {
        var declared = KatLangEngine.Run($"DisplayDecimals = {decimals.ToString(CultureInfo.InvariantCulture)}\n{program}");
        var hosted = KatLangEngine.Run(program, Default(decimals));

        Assert.Equal(Renderings(declared), Renderings(hosted));
    }

    /// <summary>The override law: with a declared property, a host default changes no rendering at all.</summary>
    [Theory]
    [MemberData(nameof(RenderingPrograms))]
    public void DeclaredProperty_RendersAsIfNoDefaultWereConfigured(string program, int declaredDecimals)
    {
        var source = $"DisplayDecimals = {declaredDecimals.ToString(CultureInfo.InvariantCulture)}\n{program}";
        var absent = Success(source);

        foreach (var hostDefault in new int?[] { 0, 7, RunOptions.MaxDisplayDecimals })
        {
            var hosted = Success(source, Default(hostDefault));
            Assert.Equal(absent.DisplayOptions, hosted.DisplayOptions);
            Assert.Equal(Renderings(absent), Renderings(hosted));
        }
    }

    [Fact]
    public void SpecialValuesAndSignedZero_KeepTheOneRenderersSpellings()
    {
        // Non-finite values keep NaN / Infinity / -Infinity; -0 (integral quantum) stays -0 and
        // whole numbers stay plain, while fractional zeros take the requested places.
        Assert.Equal(
            "NaN\nInfinity\n-Infinity\n-0\n-0.00000\n0.00000\n0",
            Display(KatLangEngine.Run("Math.Sqrt(-1), 9e6144 * 10, Math.Ln(0), -0, -0.0, 0.0, 0", Default(5))));
        Assert.Equal(
            "(NaN, [Infinity, -0.00000], 1.50000)",
            Display(KatLangEngine.Run("(Math.Sqrt(-1), [9e6144 * 10, -0.0], 1.5)", Default(5))));
    }

    [Fact]
    public void DisplayBound_StillApplies_WhenTheDefaultLengthensTheNumbers()
    {
        // Canonical 1/3 is 36 characters and fits a 40-unit bound; at 99 places it cannot, and
        // every surface reports the SAME bounded overflow instead of building the long text.
        var options = new RunOptions
        {
            EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 40 },
            DefaultDisplayDecimals = RunOptions.MaxDisplayDecimals,
        };
        Assert.False(KatLangEngine.Run("1 / 3", new RunOptions { EvaluationLimits = options.EvaluationLimits }).RenderDisplay().LimitExceeded);

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
        { "DisplayDecimals = 6\n1 / 7", null },
        { "DisplayDecimals = 6\n1 / 7", 3 },
        { "DisplayDecimals = 0\n2.5, -2.5", 7 },
        { "DisplayDecimals = -1\n1 / 7", 3 },
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

    [Fact]
    public async Task AsyncTwinPath_AgreesWithTheSynchronousRun()
    {
        // A genuinely suspending asynchronous host operation routes evaluation through the
        // async twins; a declared DisplayDecimals computed from that suspended work still wins,
        // and the result matches the synchronous run of the same program over a synchronous
        // operation returning the same value.
        var asyncOperations = HostOperations.Create(HostOperation.CreateAsync("Digits", async (_, _) =>
        {
            await Task.Yield();
            return new Result.Atom(4);
        }));
        var syncOperations = HostOperations.Create(HostOperation.Create("Digits", (_, _) => new Result.Atom(4)));

        foreach (var (source, decimals) in new (string, int?)[]
                 {
                     ("Digits / 7", 2),
                     ("DisplayDecimals = Digits\n1 / 7", 2),
                     ("DisplayDecimals = Digits - 5\n1 / 7", 2),
                     ("Digits / 7", null),
                 })
        {
            var asynchronous = await KatLangEngine.RunAsync(
                source, new RunOptions { HostOperations = asyncOperations, DefaultDisplayDecimals = decimals });
            var sync = KatLangEngine.Run(
                source, new RunOptions { HostOperations = syncOperations, DefaultDisplayDecimals = decimals });

            Assert.Equal(sync.GetType(), asynchronous.GetType());
            Assert.Equal(sync.DisplayOptions, asynchronous.DisplayOptions);
            Assert.Equal(Renderings(sync), Renderings(asynchronous));
        }

        Assert.Equal("0.57", Display(await KatLangEngine.RunAsync(
            "Digits / 7", new RunOptions { HostOperations = asyncOperations, DefaultDisplayDecimals = 2 })));
        Assert.Equal("0.1429", Display(await KatLangEngine.RunAsync(
            "DisplayDecimals = Digits\n1 / 7", new RunOptions { HostOperations = asyncOperations, DefaultDisplayDecimals = 2 })));
    }

    // ── Immutable configuration, isolated runs ───────────────────────────────

    [Fact]
    public void OneOptionsObject_AppliesTheSameDefaultToEveryRun()
    {
        var options = Default(3);

        Assert.Equal("0.143", Display(KatLangEngine.Run("1 / 7", options)));
        Assert.Equal("0.142857", Display(KatLangEngine.Run("DisplayDecimals = 6\n1 / 7", options)));
        Assert.Equal("0.143", Display(KatLangEngine.Run("1 / 7", options)));
        Assert.Equal(3, options.DefaultDisplayDecimals);
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

        foreach (var parsed in new[] { configured, configuredAsync })
        {
            Assert.False(parsed.HasErrors);
            Assert.Equal(
                plain.Diagnostics.Select(d => (d.Code, d.Message, d.Span)),
                parsed.Diagnostics.Select(d => (d.Code, d.Message, d.Span)));
            Assert.Equal(new[] { "A" }, parsed.Root.Properties.Select(p => p.Name));

            var model = SemanticModelBuilder.Build(parsed);
            Assert.Empty(model.FindDeclarations("DisplayDecimals"));
            Assert.DoesNotContain(model.GetVisibleSymbolsAt(new SourcePosition(2, 1)), symbol => symbol.Name == "DisplayDecimals");
        }
    }

    [Fact]
    public void ProgramReadingTheName_StillSeesNoDeclaration()
    {
        // The default is not a property: reading `DisplayDecimals` stays an implicit parameter
        // of the root, failing exactly as it does without a default.
        const string source = "DisplayDecimals + 1";
        AssertSameFailure(KatLangEngine.Run(source), KatLangEngine.Run(source, Default(4)));
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
    /// Over the whole executable specification: an explicit <c>null</c> default is byte-for-byte
    /// the unconfigured run; a configured default leaves every raw outcome and every failure
    /// untouched, overrides nothing a program declares, and otherwise becomes exactly the
    /// run's effective decimals.
    /// </summary>
    [Theory]
    [MemberData(nameof(SpecCaseIds))]
    public void Corpus_DefaultChangesOnlyTheEffectiveDecimals(string caseId)
    {
        var source = SpecById[caseId].Source;
        var baseline = KatLangEngine.Run(source);

        var explicitNull = KatLangEngine.Run(source, Default(null));
        Assert.Equal(baseline.GetType(), explicitNull.GetType());
        Assert.Equal(baseline.DisplayOptions, explicitNull.DisplayOptions);
        Assert.Equal(baseline.ToDisplayString(), explicitNull.ToDisplayString());

        var configured = KatLangEngine.Run(source, Default(7));
        Assert.Equal(baseline.GetType(), configured.GetType());
        if (baseline is not RunResult.Success success)
        {
            Assert.Equal(baseline.ToDisplayString(), configured.ToDisplayString());
            return;
        }

        var configuredSuccess = (RunResult.Success)configured;
        AssertSameRawOutcome(success, configuredSuccess);

        var declares = success.Root.Properties.Any(static p => p.Name == "DisplayDecimals");
        Assert.Equal(
            declares ? success.DisplayOptions : success.DisplayOptions with { Decimals = 7 },
            configuredSuccess.DisplayOptions);
        if (declares)
            Assert.Equal(Renderings(success), Renderings(configuredSuccess));
    }
}
