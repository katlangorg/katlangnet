using System.Globalization;
using System.Numerics;
using KatLang.Formatting;
using KatLang.Tests.Randomness;

namespace KatLang.Tests.Hosting;

/// <summary>
/// Q-10, decided D-F (2026-10-07) and extended to two settings by the owner decision of
/// 2026-11-12: a run has two independent PRESENTATION settings, <c>MinDecimalPlaces</c> (the
/// fewest digits shown after the decimal point) and <c>MaxDecimalPlaces</c> (the most), and each
/// can come from two origins — the SOURCE setting, the program root's OWN declared property of
/// that name, and the HOST setting, <see cref="RunOptions.MinDecimalPlaces"/> /
/// <see cref="RunOptions.MaxDecimalPlaces"/> (the CLI's <c>--min-decimal-places</c> /
/// <c>--max-decimal-places</c>, a host UI setting). Each setting composes with its counterpart of
/// the same name: an absent one imposes nothing; one present is effective; both present give their
/// MINIMUM; neither leaves that setting absent. Neither setting supplies a value for the other.
/// The contract pinned here, for BOTH settings (<see cref="Setting"/>):
/// <list type="bullet">
///   <item>the composition table, exactly, on the three engine routes (sync, async, async twin);</item>
///   <item>"off" (<c>null</c>) is no host setting — never zero places, never a suppressed source
///   setting — and an explicit <c>0</c> is a real setting from either origin;</item>
///   <item>a declared source setting is evaluated and validated after successful output WHATEVER
///   the host setting is — a smaller host setting never skips the read, never excuses an invalid
///   or failing value, and never changes its effects, draws, step charges, cancellation or cache
///   reuse (the ordinary cached zero-argument VALUE read of the same run; an explicit
///   <c>MaxDecimalPlaces()</c> stays a fresh call that does not satisfy it);</item>
///   <item>evaluation order: output, then the <c>MinDecimalPlaces</c> read, then the
///   <c>MaxDecimalPlaces</c> read, then validation, composition and rendering — an output failure
///   is never masked, and a failing first read stops the run before the second is attempted;</item>
///   <item>only the root's own declaration is a setting (no nested, opened, inline-opened, member,
///   module, module-root or parameter declaration);</item>
///   <item>the raw <see cref="Evaluator"/> never reads either (the intentional engine/evaluator
///   boundary, X-35);</item>
///   <item>rendering is inert: no setting changes a value, its Decimal128 representation,
///   <c>.string</c>, comparisons, atoms, or anything already evaluated.</item>
/// </list>
/// The formatting rule itself is pinned by <see cref="DecimalPlacesFormattingTests"/> and the
/// consistency errors by <see cref="DecimalPlacesConsistencyTests"/>.
/// </summary>
public sealed class DecimalPlacesCompositionTests
{
    /// <summary>One of the two independent decimal-places settings.</summary>
    public enum Setting
    {
        Min,
        Max,
    }

    public enum EngineRoute
    {
        /// <summary><see cref="KatLangEngine.Run"/>.</summary>
        Sync,

        /// <summary><see cref="KatLangEngine.RunAsync"/> with synchronous host operations.</summary>
        Async,

        /// <summary><see cref="KatLangEngine.RunAsync"/> with suspending host operations: the async twin.</summary>
        AsyncTwin,
    }

    private static readonly EngineRoute[] EngineRoutes = Enum.GetValues<EngineRoute>();

    /// <summary>The property name of a setting: <c>MinDecimalPlaces</c> or <c>MaxDecimalPlaces</c>.</summary>
    private static string Name(Setting setting) => setting + "DecimalPlaces";

    /// <summary>
    /// One engine run, comparably: the outcome kind, the effective pair the result carries, its
    /// display text, its value rendered representation-exactly, every error, and the exact
    /// host-call log.
    /// </summary>
    private sealed record Outcome(
        string Kind,
        int? Min,
        int? Max,
        string Display,
        string? Value,
        IReadOnlyList<string> Errors,
        IReadOnlyList<string> HostCalls)
    {
        public int? Effective(Setting setting) => setting == Setting.Min ? Min : Max;

        public bool AgreesWith(Outcome other)
            => Kind == other.Kind
                && Min == other.Min
                && Max == other.Max
                && Display == other.Display
                && Value == other.Value
                && Errors.SequenceEqual(other.Errors)
                && HostCalls.SequenceEqual(other.HostCalls);

        public override string ToString()
            => $"{Kind} min={Text(Min)} max={Text(Max)} value={Value} " +
               $"display=[{Display}] errors=[{string.Join(" | ", Errors)}] host=[{string.Join(",", HostCalls)}]";

        private static string Text(int? places) => places?.ToString(CultureInfo.InvariantCulture) ?? "absent";
    }

    private sealed class HostLog
    {
        private int _ticks;

        public List<string> Calls { get; } = [];

        public CancellationTokenSource? Cancellation { get; init; }

        public Result Tick()
        {
            var tock = Interlocked.Increment(ref _ticks);
            lock (Calls)
                Calls.Add($"tock#{tock}");
            return new Result.Atom((Decimal128)tock);
        }

        public Result Trace(Result value)
        {
            lock (Calls)
                Calls.Add($"trace({NumericRepresentativeSelectionTests.Exact(value)})");
            return value;
        }

        public Result Cancel()
        {
            lock (Calls)
                Calls.Add("cancel");
            Cancellation!.Cancel();
            return new Result.Atom(0);
        }
    }

    private static HostOperations OperationsFor(HostLog log, bool suspending)
        => suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync("tock", async (_, _) => { await Task.Yield(); return log.Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x"),
                HostOperation.CreateAsync("cancel", async (_, _) => { await Task.Yield(); return log.Cancel(); }))
            : HostOperations.Create(
                HostOperation.Create("tock", (_, _) => log.Tick()),
                HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x"),
                HostOperation.Create("cancel", (_, _) => log.Cancel()));

    private static async Task<(RunResult Result, HostLog Log)> RunAsync(
        EngineRoute route,
        string source,
        int? hostMin,
        int? hostMax,
        long? seed = null,
        EvaluationLimits? limits = null,
        CancellationTokenSource? cancellation = null,
        Func<string, CancellationToken, ValueTask<string>>? download = null)
    {
        var log = new HostLog { Cancellation = cancellation };
        var options = new RunOptions
        {
            HostOperations = OperationsFor(log, route == EngineRoute.AsyncTwin),
            MinDecimalPlaces = hostMin,
            MaxDecimalPlaces = hostMax,
            RandomSeed = seed,
            EvaluationLimits = limits,
            EvaluationCancellationToken = cancellation?.Token ?? default,
            DownloadCode = download,
        };

        var result = route == EngineRoute.Sync
            ? KatLangEngine.Run(source, options)
            : await KatLangEngine.RunAsync(source, options);
        return (result, log);
    }

    private static Outcome Describe(RunResult result, HostLog log)
    {
        var options = result.DisplayOptions;
        return result switch
        {
            RunResult.Success success => new(
                "ok",
                options.MinDecimalPlaces,
                options.MaxDecimalPlaces,
                success.ToDisplayString().ReplaceLineEndings("\n"),
                NumericRepresentativeSelectionTests.Exact(success.Value),
                [],
                [.. log.Calls]),
            RunResult.EvalFailure failure => new("err", options.MinDecimalPlaces, options.MaxDecimalPlaces, "", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
            RunResult.ParseFailure failure => new("parse", options.MinDecimalPlaces, options.MaxDecimalPlaces, "", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
            RunResult.NoProgramOutput none => new("none", options.MinDecimalPlaces, options.MaxDecimalPlaces, "", null, [Describe(none.Diagnostic)], [.. log.Calls]),
        };
    }

    private static string Describe(KatLangError error) => $"{error.Code}: {error.Message} @ {error.Span}";

    /// <summary>
    /// Runs <paramref name="source"/> on the three engine routes with the given host pair and
    /// requires them to agree on everything — kind, effective pair, display, exact value, errors
    /// with spans, and the host-call log. Returns the synchronous oracle.
    /// </summary>
    private static async Task<Outcome> OnEveryEngineRouteAsync(
        string source,
        int? hostMin,
        int? hostMax,
        long? seed = null,
        EvaluationLimits? limits = null,
        Func<string, CancellationToken, ValueTask<string>>? download = null)
    {
        // The synchronous engine refuses a downloader-configured options object by contract
        // (source loading is async-only), so module programs run on the two async routes.
        var routes = download is null ? EngineRoutes : [EngineRoute.Async, EngineRoute.AsyncTwin];
        Outcome? oracle = null;
        foreach (var route in routes)
        {
            var (result, log) = await RunAsync(route, source, hostMin, hostMax, seed, limits, download: download);
            var outcome = Describe(result, log);
            oracle ??= outcome;
            Assert.True(
                oracle.AgreesWith(outcome),
                $"{route}: expected {oracle}, got {outcome}\nhost min: {hostMin}, host max: {hostMax}\nsource:\n{source}");
        }

        return oracle!;
    }

    /// <summary>The same, with ONLY the named host setting present (the other stays absent).</summary>
    private static Task<Outcome> OnEveryEngineRouteAsync(
        Setting setting,
        string source,
        int? host,
        long? seed = null,
        EvaluationLimits? limits = null,
        Func<string, CancellationToken, ValueTask<string>>? download = null)
        => setting == Setting.Min
            ? OnEveryEngineRouteAsync(source, host, null, seed, limits, download)
            : OnEveryEngineRouteAsync(source, null, host, seed, limits, download);

    private static readonly int?[] HostSettings = [null, 0, 1, 5, 7, 10, RunOptions.DecimalPlacesLimit];

    private const string OneSeventh = "0.1428571428571428571428571428571429";

    /// <summary>A fraction, a positive and a negative midpoint, and a value storing a trailing zero.</summary>
    private const string Rows = "1 / 7, 2.5, -2.5, 1.50";

    private static string Zeros(int count) => new('0', count);

    /// <summary>
    /// The expected display of <see cref="Rows"/> at an effective value of ONE setting (the other
    /// absent), hand-written. A maximum rounds and never pads; a minimum pads and never rounds;
    /// either one, once present, removes the stored trailing zero of <c>1.50</c>.
    /// </summary>
    private static string ExpectedDisplay(Setting setting, int? effective) => (setting, effective) switch
    {
        (_, null) => $"{OneSeventh}\n2.5\n-2.5\n1.50",
        (Setting.Max, 0) => "0\n3\n-3\n2",
        (Setting.Max, 5) => "0.14286\n2.5\n-2.5\n1.5",
        (Setting.Max, 7) => "0.1428571\n2.5\n-2.5\n1.5",
        (Setting.Max, RunOptions.DecimalPlacesLimit) => $"{OneSeventh}\n2.5\n-2.5\n1.5",
        (Setting.Min, 0) => $"{OneSeventh}\n2.5\n-2.5\n1.5",
        (Setting.Min, 5) => $"{OneSeventh}\n2.50000\n-2.50000\n1.50000",
        (Setting.Min, 7) => $"{OneSeventh}\n2.5000000\n-2.5000000\n1.5000000",
        (Setting.Min, RunOptions.DecimalPlacesLimit) =>
            $"{OneSeventh}{Zeros(99 - 34)}\n2.5{Zeros(98)}\n-2.5{Zeros(98)}\n1.5{Zeros(98)}",
        _ => throw new ArgumentOutOfRangeException(nameof(effective), effective, null),
    };

    private static string WithSource(Setting setting, int? sourceSetting, string program)
        => sourceSetting is { } places
            ? $"{Name(setting)} = {places.ToString(CultureInfo.InvariantCulture)}\n{program}"
            : program;

    private static string Fill(string template, Setting setting) => template.Replace("{0}", Name(setting), StringComparison.Ordinal);

    public static TheoryData<Setting> BothSettings => new() { Setting.Min, Setting.Max };

    // ── The composition law ─────────────────────────────────────────────────────

    /// <summary>The ONE composition helper against an independent oracle, over the whole domain.</summary>
    [Fact]
    public void CombineDecimalPlaces_IsTheMinimumOfThePresentSettings_OverTheWholeDomain()
    {
        var domain = Enumerable.Range(0, RunOptions.DecimalPlacesLimit + 1).Select(static n => (int?)n).Prepend(null).ToArray();
        foreach (var source in domain)
        {
            foreach (var host in domain)
            {
                int? expected = (source, host) switch
                {
                    (null, null) => null,
                    (null, _) => host,
                    (_, null) => source,
                    _ => source < host ? source : host,
                };
                Assert.Equal(expected, KatLangEngine.CombineDecimalPlaces(source, host));

                // The same helper serves both settings: a result carries each composed alike.
                var options = new DisplayOptions(source, source, host, host, int.MaxValue);
                Assert.Equal(expected, options.MinDecimalPlaces);
                Assert.Equal(expected, options.MaxDecimalPlaces);
            }
        }
    }

    public static TheoryData<Setting, int?, int?, int?> CompositionTable()
    {
        var data = new TheoryData<Setting, int?, int?, int?>();
        foreach (var setting in new[] { Setting.Min, Setting.Max })
        {
            data.Add(setting, null, null, null);
            data.Add(setting, 7, null, 7);
            data.Add(setting, null, 5, 5);
            data.Add(setting, 7, 5, 5);
            data.Add(setting, 5, 7, 5);
            data.Add(setting, 0, 7, 0);
            data.Add(setting, 7, 0, 0);
            data.Add(setting, 99, 99, 99);
            data.Add(setting, 5, 5, 5);
            data.Add(setting, 0, null, 0);
            data.Add(setting, null, 0, 0);
            data.Add(setting, 99, 0, 0);
            data.Add(setting, 0, 99, 0);
        }

        return data;
    }

    /// <summary>
    /// The composition table — source-only, host-only, both, neither — with the exact display, on
    /// every engine route, for each setting. The OTHER setting stays absent throughout: a minimum
    /// alone never rounds and a maximum alone never pads.
    /// </summary>
    [Theory]
    [MemberData(nameof(CompositionTable))]
    public async Task CompositionTable_EffectiveIsTheMinimumOfThePresentSettings(
        Setting setting, int? sourceSetting, int? hostSetting, int? effective)
    {
        var source = WithSource(setting, sourceSetting, Rows);
        SourceProvenance.ParseValid(source);

        var outcome = await OnEveryEngineRouteAsync(setting, source, hostSetting);

        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(effective, outcome.Effective(setting));
        Assert.Null(outcome.Effective(setting == Setting.Min ? Setting.Max : Setting.Min));
        Assert.Equal(ExpectedDisplay(setting, effective), outcome.Display);
        Assert.Equal($"S[{OneSeventh}, 2.5, -2.5, 1.50]", outcome.Value);
    }

    /// <summary>
    /// Each setting composes independently, and only with its counterpart of the same name: the
    /// brief's three examples, with the printed text.
    /// </summary>
    [Fact]
    public async Task EachSetting_ComposesIndependently_WithItsOwnCounterpart()
    {
        const string rows = "10, 1.234567, 2.5";

        // Source min 2, max 4; host min 1, max 3 → effective min 1, max 3.
        var both = await OnEveryEngineRouteAsync($"MinDecimalPlaces = 2\nMaxDecimalPlaces = 4\n{rows}", 1, 3);
        Assert.Equal(((int?)1, (int?)3), (both.Min, both.Max));
        Assert.Equal("10.0\n1.235\n2.5", both.Display);

        // Source min 2 only; host max 4 only → effective min 2, max 4.
        var partial = await OnEveryEngineRouteAsync($"MinDecimalPlaces = 2\n{rows}", null, 4);
        Assert.Equal(((int?)2, (int?)4), (partial.Min, partial.Max));
        Assert.Equal("10.00\n1.2346\n2.50", partial.Display);

        // Source max 7; host max 10 → effective max 7, and still no minimum.
        var maximum = await OnEveryEngineRouteAsync($"MaxDecimalPlaces = 7\n{rows}, 1 / 7", null, 10);
        Assert.Equal(((int?)null, (int?)7), (maximum.Min, maximum.Max));
        Assert.Equal("10\n1.234567\n2.5\n0.1428571", maximum.Display);
    }

    /// <summary>
    /// Neither setting supplies a value for the other, from any origin: with only a minimum set
    /// nothing is rounded, with only a maximum set nothing is padded, and a fixed number of places
    /// is written by setting both to the same value.
    /// </summary>
    [Fact]
    public async Task NeitherSetting_SuppliesAValueForTheOther()
    {
        const string rows = "1.234567, 10";

        foreach (var (source, hostMin, hostMax) in new (string, int?, int?)[]
                 {
                     ($"MinDecimalPlaces = 2\n{rows}", null, null),
                     (rows, 2, null),
                 })
        {
            var minimumOnly = await OnEveryEngineRouteAsync(source, hostMin, hostMax);
            Assert.Equal(((int?)2, (int?)null), (minimumOnly.Min, minimumOnly.Max));
            Assert.Equal("1.234567\n10.00", minimumOnly.Display);
        }

        foreach (var (source, hostMin, hostMax) in new (string, int?, int?)[]
                 {
                     ($"MaxDecimalPlaces = 4\n{rows}", null, null),
                     (rows, null, 4),
                 })
        {
            var maximumOnly = await OnEveryEngineRouteAsync(source, hostMin, hostMax);
            Assert.Equal(((int?)null, (int?)4), (maximumOnly.Min, maximumOnly.Max));
            Assert.Equal("1.2346\n10", maximumOnly.Display);
        }

        foreach (var (source, hostMin, hostMax) in new (string, int?, int?)[]
                 {
                     ($"MinDecimalPlaces = 2\nMaxDecimalPlaces = 2\n{rows}", null, null),
                     (rows, 2, 2),
                     ($"MinDecimalPlaces = 2\n{rows}", null, 2),
                     ($"MaxDecimalPlaces = 2\n{rows}", 2, null),
                 })
        {
            var fixedPlaces = await OnEveryEngineRouteAsync(source, hostMin, hostMax);
            Assert.Equal(((int?)2, (int?)2), (fixedPlaces.Min, fixedPlaces.Max));
            Assert.Equal("1.23\n10.00", fixedPlaces.Display);
        }
    }

    /// <summary>
    /// The portability property: one shared program carrying a setting shows it to a recipient
    /// without a host setting, a smaller host setting decides, and a larger one changes nothing.
    /// </summary>
    [Fact]
    public async Task SharedSourceSetting_CarriesItsIntent_AndASmallerHostSettingStillWins()
    {
        const string sharedMax = "MaxDecimalPlaces = 7\n1 / 3";
        Assert.Equal("0.3333333", (await OnEveryEngineRouteAsync(sharedMax, null, null)).Display);
        Assert.Equal("0.33333", (await OnEveryEngineRouteAsync(sharedMax, null, 5)).Display);
        Assert.Equal("0.3333333", (await OnEveryEngineRouteAsync(sharedMax, null, 10)).Display);

        const string sharedMin = "MinDecimalPlaces = 7\n2.5";
        Assert.Equal("2.5000000", (await OnEveryEngineRouteAsync(sharedMin, null, null)).Display);
        Assert.Equal("2.50000", (await OnEveryEngineRouteAsync(sharedMin, 5, null)).Display);
        Assert.Equal("2.5000000", (await OnEveryEngineRouteAsync(sharedMin, 10, null)).Display);
    }

    /// <summary>
    /// "Off" is no host setting: never zero places, never a suppressed source setting. And an
    /// explicit 0 — from the program or from the host, for either setting — is a real setting,
    /// never absence: it selects the value-based display, which removes stored trailing zeros.
    /// </summary>
    [Fact]
    public async Task HostSettingOff_IsNoSetting_AndAnExplicitZeroIsARealOne()
    {
        var off = await OnEveryEngineRouteAsync("MaxDecimalPlaces = 7\n1 / 3", null, null);
        var zero = await OnEveryEngineRouteAsync("MaxDecimalPlaces = 7\n2.5", null, 0);
        Assert.Equal(((int?)null, (int?)7, "0.3333333"), (off.Min, off.Max, off.Display));
        Assert.Equal(((int?)null, (int?)0, "3"), (zero.Min, zero.Max, zero.Display));

        // No setting at all: the stored digits, trailing zeros included.
        var canonical = await OnEveryEngineRouteAsync("2.5000, 10.00", null, null);
        Assert.Equal(((int?)null, (int?)null, "2.5000\n10.00"), (canonical.Min, canonical.Max, canonical.Display));

        // An explicit 0, each setting and each origin: present, and not the canonical display.
        var hostMinZero = await OnEveryEngineRouteAsync("2.5000, 10.00", 0, null);
        var sourceMinZero = await OnEveryEngineRouteAsync("MinDecimalPlaces = 0\n2.5000, 10.00", null, null);
        Assert.Equal(((int?)0, (int?)null, "2.5\n10"), (hostMinZero.Min, hostMinZero.Max, hostMinZero.Display));
        Assert.Equal(((int?)0, (int?)null, "2.5\n10"), (sourceMinZero.Min, sourceMinZero.Max, sourceMinZero.Display));

        var hostMaxZero = await OnEveryEngineRouteAsync("2.5000, 10.00", null, 0);
        var sourceMaxZero = await OnEveryEngineRouteAsync("MaxDecimalPlaces = 0\n2.5000, 10.00", null, null);
        Assert.Equal(((int?)null, (int?)0, "3\n10"), (hostMaxZero.Min, hostMaxZero.Max, hostMaxZero.Display));
        Assert.Equal(((int?)null, (int?)0, "3\n10"), (sourceMaxZero.Min, sourceMaxZero.Max, sourceMaxZero.Display));

        // A declared 0 is the smaller setting beside a host 7; MaxDecimalPlaces = 99 is not "no
        // maximum" either — it rounds nothing here, yet the stored zeros are gone.
        var declaredZero = await OnEveryEngineRouteAsync("MaxDecimalPlaces = 0\n2.5", null, 7);
        Assert.Equal(((int?)0, "3"), (declaredZero.Max, declaredZero.Display));
        var ninetyNine = await OnEveryEngineRouteAsync("2.5000, 10.00", null, RunOptions.DecimalPlacesLimit);
        Assert.Equal(((int?)99, "2.5\n10"), (ninetyNine.Max, ninetyNine.Display));
    }

    // ── Source-setting validation, with and without a host setting ─────────────

    private static readonly (string Declaration, int Value)[] ValidDeclarations =
    [
        ("{0} = 2", 2),
        ("{0} = 0", 0),
        ("{0} = 99", 99),
        ("{0} = 2.0", 2),
        ("{0} = -0", 0),
        ("{0} = 1 + 1", 2),
        ("Two = 2\n{0} = Two", 2),
        ("{0}(*xs) = 2 + xs.count", 2),
        ("public {0} = 3", 3),
        ("{0} = { 4 }", 4),
    ];

    public static TheoryData<Setting, string, int> ValidSourceSettings()
    {
        var data = new TheoryData<Setting, string, int>();
        foreach (var setting in new[] { Setting.Min, Setting.Max })
            foreach (var (declaration, value) in ValidDeclarations)
                data.Add(setting, declaration, value);
        return data;
    }

    [Theory]
    [MemberData(nameof(ValidSourceSettings))]
    public async Task ValidSourceSetting_ComposesWithEveryHostSetting(Setting setting, string declaration, int value)
    {
        var source = Fill(declaration, setting) + "\n" + Rows;
        SourceProvenance.ParseValid(source);

        foreach (var host in HostSettings)
        {
            var outcome = await OnEveryEngineRouteAsync(setting, source, host);
            Assert.Equal("ok", outcome.Kind);
            Assert.Equal(host is { } h ? Math.Min(value, h) : value, outcome.Effective(setting));
        }
    }

    private static readonly (string Declaration, KatLangErrorCode Code, string? Message)[] InvalidDeclarations =
    [
        ("{0} = -1", KatLangErrorCode.IllegalInEval, "{0} must be a non-negative integer."),
        ("{0} = 1.5", KatLangErrorCode.IllegalInEval, "{0} must be an integer."),
        ("{0} = 100", KatLangErrorCode.IllegalInEval, "{0} must be between 0 and 99."),
        ("{0} = Math.Sqrt(-1)", KatLangErrorCode.IllegalInEval, "{0} must be an integer."),
        ("{0} = 9e6144 * 10", KatLangErrorCode.IllegalInEval, "{0} must be an integer."),
        ("{0} = -9e6144 * 10", KatLangErrorCode.IllegalInEval, "{0} must be a non-negative integer."),
        ("{0} = 'x'", KatLangErrorCode.IllegalInEval, "{0} must be a single numeric value."),
        ("{0} = true", KatLangErrorCode.IllegalInEval, "{0} must be a single numeric value."),
        ("{0} = 2, 3", KatLangErrorCode.IllegalInEval, "{0} must be a single numeric value."),
        ("{0} = (2, 3)", KatLangErrorCode.IllegalInEval, "{0} must be a single numeric value."),
        ("{0} = [2]", KatLangErrorCode.IllegalInEval, "{0} must be a single numeric value."),
        ("{0} = ()", KatLangErrorCode.IllegalInEval, "{0} must be a single numeric value."),
        ("{0} = 1 / 0", KatLangErrorCode.DivisionByZero, null),
        ("{0}(x) = x", KatLangErrorCode.ArityMismatch, null),
        ("{0} = n + 1", KatLangErrorCode.ArityMismatch, null),
        ("{0}(0) = 1\n{0}(n) = 2", KatLangErrorCode.NoMatchingBranch, null),
    ];

    public static TheoryData<Setting, string, KatLangErrorCode, string?> InvalidSourceSettings()
    {
        var data = new TheoryData<Setting, string, KatLangErrorCode, string?>();
        foreach (var setting in new[] { Setting.Min, Setting.Max })
            foreach (var (declaration, code, message) in InvalidDeclarations)
                data.Add(setting, declaration, code, message);
        return data;
    }

    /// <summary>
    /// Every invalid source value — negative, fractional, above 99, non-numeric, multi-value — is
    /// rejected, never clamped, with <c>IllegalInEval</c> at the property's declaration, and a host
    /// setting never hides it — not even a smaller one, and not a host setting of the OTHER name:
    /// the failure is exactly the failure without any host setting (code, message, span), on every
    /// route.
    /// </summary>
    [Theory]
    [MemberData(nameof(InvalidSourceSettings))]
    public async Task InvalidSourceSetting_FailsTheEngineRun_WhateverTheHostSettings(
        Setting setting, string declaration, KatLangErrorCode code, string? message)
    {
        var source = Fill(declaration, setting) + "\n1 / 7";
        SourceProvenance.ParseValid(source);

        var baseline = await OnEveryEngineRouteAsync(source, null, null);
        Assert.Equal("err", baseline.Kind);
        var error = Assert.Single(baseline.Errors);
        Assert.StartsWith(code + ": ", error, StringComparison.Ordinal);
        if (message is not null)
        {
            // Positioned at the property's own declaration: the name on the first line.
            Assert.Equal($"{code}: Illegal in eval: {Fill(message, setting)} @ [1:1, 1:17)", error);
        }

        foreach (var host in HostSettings)
        {
            foreach (var (hostMin, hostMax) in new[] { (host, (int?)null), (null, host), (host, host) })
            {
                var outcome = await OnEveryEngineRouteAsync(source, hostMin, hostMax);
                Assert.Equal(baseline.Kind, outcome.Kind);
                Assert.Equal(baseline.Errors, outcome.Errors);
                Assert.Equal(baseline.HostCalls, outcome.HostCalls);
            }
        }
    }

    // ── Effects, draws, steps, cancellation, cache ─────────────────────────────

    public static TheoryData<Setting, int?, int> EffectfulCases()
    {
        var data = new TheoryData<Setting, int?, int>();
        foreach (var setting in new[] { Setting.Min, Setting.Max })
        {
            data.Add(setting, null, 7);
            data.Add(setting, 5, 5);
            data.Add(setting, 10, 7);
            data.Add(setting, 0, 0);
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(EffectfulCases))]
    public async Task EffectfulSourceSetting_RunsExactlyOnce_WhateverTheHostSetting(Setting setting, int? hostSetting, int effective)
    {
        var outcome = await OnEveryEngineRouteAsync(setting, Fill("{0} = trace(7)\n1 / 7", setting), hostSetting);

        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(effective, outcome.Effective(setting));
        Assert.Equal(["trace(7)"], outcome.HostCalls);
    }

    public static TheoryData<Setting, int?> SettingsByHost(params int?[] hosts)
    {
        var data = new TheoryData<Setting, int?>();
        foreach (var setting in new[] { Setting.Min, Setting.Max })
            foreach (var host in hosts)
                data.Add(setting, host);
        return data;
    }

    public static TheoryData<Setting, int?> NullFiveZero => SettingsByHost(null, 5, 0);

    public static TheoryData<Setting, int?> NullFiveNinetyNine => SettingsByHost(null, 5, 99);

    public static TheoryData<Setting, int?> NullZeroFiveNinetyNine => SettingsByHost(null, 0, 5, 99);

    public static TheoryData<Setting, int?> NullFive => SettingsByHost(null, 5);

    /// <summary>The engine's read is the ordinary cached VALUE read: an output that already read the property is reused.</summary>
    [Theory]
    [MemberData(nameof(NullFiveZero))]
    public async Task ProgramThatReadsTheSourceSetting_SharesTheOneCachedEvaluation(Setting setting, int? hostSetting)
    {
        var outcome = await OnEveryEngineRouteAsync(setting, Fill("{0} = trace(7)\n{0}, 1 / 7", setting), hostSetting);

        Assert.Equal(["trace(7)"], outcome.HostCalls);
        Assert.StartsWith("S[7, ", outcome.Value, StringComparison.Ordinal);
        Assert.Equal(hostSetting is { } h ? Math.Min(7, h) : 7, outcome.Effective(setting));
    }

    /// <summary>
    /// An explicit <c>MaxDecimalPlaces()</c> (or <c>MinDecimalPlaces()</c>) is a fresh call that
    /// never READS the cached entry. Since CACHE-PUB-1 (owner decision October 22 2026) an explicit
    /// call that finds the entry EMPTY establishes it, so the engine's later cached read reuses the
    /// explicit call's value as the source setting instead of evaluating the property again
    /// (formerly two ticks and the second value, 6). A cached read first is still reused, and a
    /// later explicit call stays fresh.
    /// </summary>
    [Theory]
    [MemberData(nameof(NullFiveNinetyNine))]
    public async Task ExplicitCall_IsFresh_AndNeverSatisfiesTheCachedEngineRead(Setting setting, int? hostSetting)
    {
        var explicitOnly = await OnEveryEngineRouteAsync(setting, Fill("{0} = tock() + 4\n{0}(), 1 / 7", setting), hostSetting);
        Assert.Equal(["tock#1"], explicitOnly.HostCalls);
        Assert.StartsWith("S[5, ", explicitOnly.Value, StringComparison.Ordinal);
        Assert.Equal(hostSetting is { } h ? Math.Min(5, h) : 5, explicitOnly.Effective(setting));

        // A cached read in the output, then an explicit call: the engine reuses the cached 5.
        var cachedFirst = await OnEveryEngineRouteAsync(setting, Fill("{0} = tock() + 4\n{0}, {0}(), 1 / 7", setting), hostSetting);
        Assert.Equal(["tock#1", "tock#2"], cachedFirst.HostCalls);
        Assert.StartsWith("S[5, 6, ", cachedFirst.Value, StringComparison.Ordinal);
        Assert.Equal(hostSetting is { } h2 ? Math.Min(5, h2) : 5, cachedFirst.Effective(setting));
    }

    [Theory]
    [MemberData(nameof(NullZeroFiveNinetyNine))]
    public async Task SeededRandomSourceSetting_DrawsAfterTheOutput_WhateverTheHostSetting(Setting setting, int? hostSetting)
    {
        const long seed = 20261007;
        var words = SeededRun.Words(seed);
        var fraction = ReferenceRandomOracle.Random(words, 0, 1);
        var digits = (int)ReferenceRandomOracle.RandomInt(words, 6, 9);

        var outcome = await OnEveryEngineRouteAsync(
            setting, Fill("Math.Random(0, 1)\n{0} = Math.RandomInt(6, 9)", setting), hostSetting, seed);

        Assert.Equal(NumericRepresentativeSelectionTests.Number(fraction), outcome.Value);
        Assert.Equal(hostSetting is { } h ? Math.Min(digits, h) : digits, outcome.Effective(setting));
    }

    /// <summary>
    /// The source read is charged to the run's budget whatever the host setting is: a step-heavy
    /// source setting exceeds a tight step budget the program alone fits — with a smaller host
    /// setting too — while the raw evaluator, which never reads it, completes.
    /// </summary>
    [Theory]
    [MemberData(nameof(BothSettings))]
    public async Task StepHeavySourceSetting_IsChargedToTheRun_WhateverTheHostSetting(Setting setting)
    {
        var source = Fill("S(x) = x + 1\n{0} = repeat(S(0), 500) * 0 + 2\n1 / 3", setting);
        var limits = new EvaluationLimits { MaxSteps = 200 };

        foreach (var host in new int?[] { null, 0, 1, 5 })
        {
            var outcome = await OnEveryEngineRouteAsync(setting, source, host, limits: limits);
            Assert.Equal("err", outcome.Kind);
            Assert.StartsWith(nameof(KatLangErrorCode.EvaluationStepLimitExceeded) + ": ", Assert.Single(outcome.Errors), StringComparison.Ordinal);
        }

        var raw = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), limits: limits);
        Assert.False(raw.Result.IsError);
    }

    [Theory]
    [InlineData(Setting.Max, EngineRoute.Sync, null)]
    [InlineData(Setting.Max, EngineRoute.Sync, 0)]
    [InlineData(Setting.Max, EngineRoute.Sync, 5)]
    [InlineData(Setting.Max, EngineRoute.Async, 0)]
    [InlineData(Setting.Max, EngineRoute.AsyncTwin, null)]
    [InlineData(Setting.Max, EngineRoute.AsyncTwin, 5)]
    [InlineData(Setting.Min, EngineRoute.Sync, null)]
    [InlineData(Setting.Min, EngineRoute.Sync, 0)]
    [InlineData(Setting.Min, EngineRoute.Sync, 5)]
    [InlineData(Setting.Min, EngineRoute.Async, 0)]
    [InlineData(Setting.Min, EngineRoute.AsyncTwin, null)]
    [InlineData(Setting.Min, EngineRoute.AsyncTwin, 5)]
    public async Task CancellationDuringTheSourceSetting_CancelsTheRun_WhateverTheHostSetting(
        Setting setting, EngineRoute route, int? hostSetting)
    {
        using var cancellation = new CancellationTokenSource();
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await RunAsync(
                route,
                Fill("{0} = cancel() + 2\n1 / 3", setting),
                setting == Setting.Min ? hostSetting : null,
                setting == Setting.Max ? hostSetting : null,
                cancellation: cancellation));
        Assert.Equal(cancellation.Token, error.CancellationToken);
    }

    // ── Evaluation order ────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(NullFiveZero))]
    public async Task OutputFailure_IsNeverMasked_AndTheSourceSettingIsNotRead(Setting setting, int? hostSetting)
    {
        var divide = await OnEveryEngineRouteAsync(setting, Fill("{0} = trace(2)\n1 / 0", setting), hostSetting);
        Assert.StartsWith(nameof(KatLangErrorCode.DivisionByZero) + ": ", Assert.Single(divide.Errors), StringComparison.Ordinal);
        Assert.Empty(divide.HostCalls);

        var index = await OnEveryEngineRouteAsync(setting, Fill("{0} = 1 / 0\n[1][5]", setting), hostSetting);
        Assert.StartsWith(nameof(KatLangErrorCode.BadIndex) + ": ", Assert.Single(index.Errors), StringComparison.Ordinal);

        var none = await OnEveryEngineRouteAsync(setting, Fill("{0} = trace(2)", setting), hostSetting);
        Assert.Equal("none", none.Kind);
        Assert.Empty(none.HostCalls);
    }

    /// <summary>With BOTH declared, a failed output reads neither.</summary>
    [Fact]
    public async Task OutputFailure_ReadsNeitherSourceSetting()
    {
        const string declarations = "MinDecimalPlaces = trace(1)\nMaxDecimalPlaces = trace(2)\n";

        var divide = await OnEveryEngineRouteAsync(declarations + "trace(10) / 0", null, null);
        Assert.StartsWith(nameof(KatLangErrorCode.DivisionByZero) + ": ", Assert.Single(divide.Errors), StringComparison.Ordinal);
        Assert.Equal(["trace(10)"], divide.HostCalls);

        var none = await OnEveryEngineRouteAsync(declarations.TrimEnd('\n'), 1, 4);
        Assert.Equal("none", none.Kind);
        Assert.Empty(none.HostCalls);
    }

    [Theory]
    [MemberData(nameof(NullFive))]
    public async Task SourceSettingFailure_FollowsTheOutputsEffects(Setting setting, int? hostSetting)
    {
        var outcome = await OnEveryEngineRouteAsync(setting, Fill("{0} = trace(1) / 0\ntrace(10), 1 / 3", setting), hostSetting);

        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith(nameof(KatLangErrorCode.DivisionByZero) + ": ", Assert.Single(outcome.Errors), StringComparison.Ordinal);
        Assert.Equal(["trace(10)", "trace(1)"], outcome.HostCalls);
    }

    /// <summary>
    /// The engine's read order: the output, then <c>MinDecimalPlaces</c>, then
    /// <c>MaxDecimalPlaces</c> — whatever order the program declares them in and whatever the host
    /// settings are — on the synchronous route, the asynchronous route, and the forced async twin.
    /// </summary>
    [Theory]
    [InlineData("MinDecimalPlaces = trace(2)\nMaxDecimalPlaces = trace(4)\ntrace(10), 1 / 3")]
    [InlineData("MaxDecimalPlaces = trace(4)\nMinDecimalPlaces = trace(2)\ntrace(10), 1 / 3")]
    [InlineData("trace(10), 1 / 3\nMaxDecimalPlaces = trace(4)\nMinDecimalPlaces = trace(2)")]
    public async Task ReadOrder_IsOutput_ThenTheMinimum_ThenTheMaximum(string source)
    {
        SourceProvenance.ParseValid(source);

        foreach (var (hostMin, hostMax) in new (int?, int?)[] { (null, null), (0, 0), (1, 3), (9, 9) })
        {
            var outcome = await OnEveryEngineRouteAsync(source, hostMin, hostMax);

            Assert.Equal("ok", outcome.Kind);
            Assert.Equal(["trace(10)", "trace(2)", "trace(4)"], outcome.HostCalls);
            Assert.Equal(KatLangEngine.CombineDecimalPlaces(2, hostMin), outcome.Min);
            Assert.Equal(KatLangEngine.CombineDecimalPlaces(4, hostMax), outcome.Max);
        }

        Assert.Equal("10.00\n0.3333", (await OnEveryEngineRouteAsync(source, null, null)).Display);
    }

    /// <summary>
    /// Failure precedence of the two reads, on every engine route. A failing FIRST read is the
    /// run's failure and the second is not attempted; a failing SECOND read follows the first's
    /// effects; and both reads are evaluation, so they come before any validation — a failing
    /// maximum wins over an invalid minimum VALUE.
    /// </summary>
    [Fact]
    public async Task FailurePrecedence_FirstFailingReadStopsTheRun_AndEvaluationPrecedesValidation()
    {
        // The minimum's read fails: the maximum is never read, whichever is declared first.
        foreach (var source in new[]
                 {
                     "MinDecimalPlaces = trace(1) / 0\nMaxDecimalPlaces = trace(4)\ntrace(10)",
                     "MaxDecimalPlaces = trace(4)\nMinDecimalPlaces = trace(1) / 0\ntrace(10)",
                 })
        {
            SourceProvenance.ParseValid(source);
            foreach (var (hostMin, hostMax) in new (int?, int?)[] { (null, null), (0, 9) })
            {
                var first = await OnEveryEngineRouteAsync(source, hostMin, hostMax);
                Assert.Equal("err", first.Kind);
                Assert.StartsWith(nameof(KatLangErrorCode.DivisionByZero) + ": ", Assert.Single(first.Errors), StringComparison.Ordinal);
                Assert.Equal(["trace(10)", "trace(1)"], first.HostCalls);
            }
        }

        // The maximum's read fails: after the output and the minimum's read.
        var second = await OnEveryEngineRouteAsync(
            "MinDecimalPlaces = trace(2)\nMaxDecimalPlaces = trace(1) / 0\ntrace(10)", null, null);
        Assert.StartsWith(nameof(KatLangErrorCode.DivisionByZero) + ": ", Assert.Single(second.Errors), StringComparison.Ordinal);
        Assert.Equal(["trace(10)", "trace(2)", "trace(1)"], second.HostCalls);

        // Both are READ before either value is validated: an invalid minimum value does not
        // stop the maximum's read, whose evaluation failure is then the run's failure.
        var readsFirst = await OnEveryEngineRouteAsync(
            "MinDecimalPlaces = trace(1.5)\nMaxDecimalPlaces = trace(1) / 0\ntrace(10)", null, null);
        Assert.StartsWith(nameof(KatLangErrorCode.DivisionByZero) + ": ", Assert.Single(readsFirst.Errors), StringComparison.Ordinal);
        Assert.Equal(["trace(10)", "trace(1.5)", "trace(1)"], readsFirst.HostCalls);

        // Validation order: the minimum's value, then the maximum's, then the pair.
        var bothInvalid = await OnEveryEngineRouteAsync("MinDecimalPlaces = 1.5\nMaxDecimalPlaces = -1\n1", null, null);
        Assert.Equal(
            "IllegalInEval: Illegal in eval: MinDecimalPlaces must be an integer. @ [1:1, 1:17)",
            Assert.Single(bothInvalid.Errors));

        var invalidMaximum = await OnEveryEngineRouteAsync("MinDecimalPlaces = 5\nMaxDecimalPlaces = 100\n1", null, null);
        Assert.Equal(
            "IllegalInEval: Illegal in eval: MaxDecimalPlaces must be between 0 and 99. @ [2:1, 2:17)",
            Assert.Single(invalidMaximum.Errors));
    }

    // ── Only the program root's own declaration is a source setting ─────────────

    private const string ModuleUrl = "https://katlang.org/display-filter-audit.kat";
    private const string ModuleRootUrl = "https://katlang.org/display-filter-root.kat";

    private static Func<string, CancellationToken, ValueTask<string>> DownloadFor(Setting setting)
        => (url, _) => ValueTask.FromResult(Fill(
            url == ModuleRootUrl
                ? "{0} = 2\n1 / 7"
                : "public {0} = 2\npublic Third = 1 / 7",
            setting));

    private static readonly (string Source, bool Loads)[] NonRootSources =
    [
        ("A = {\n    {0} = 2\n    1 / 7\n}\nA", false),
        ("open M\nM = {\n    public {0} = 2\n}\n1 / 7, {0}", false),
        ("open { public {0} = 2 }\n1 / 7, {0}", false),
        ("Obj = {\n    public {0} = 2\n    public V = 1 / 7\n}\nObj.V, Obj.{0}", false),
        ("F({0}) = {0} / 7\nF(1)", false),
        ($"open '{ModuleUrl}'\nThird, {{0}}", true),
        ($"M = load('{ModuleUrl}')\nM.Third, M.{{0}}", true),
        ($"M = load('{ModuleRootUrl}')\nM", true),
    ];

    public static TheoryData<Setting, string, bool> NonRootDeclarations()
    {
        var data = new TheoryData<Setting, string, bool>();
        foreach (var setting in new[] { Setting.Min, Setting.Max })
            foreach (var (source, loads) in NonRootSources)
                data.Add(setting, source, loads);
        return data;
    }

    [Theory]
    [MemberData(nameof(NonRootDeclarations))]
    public async Task NonRootDeclaration_IsAnOrdinaryBinding_NeverASetting(Setting setting, string template, bool loads)
    {
        var source = Fill(template, setting);
        var download = loads ? DownloadFor(setting) : null;

        var unconfigured = await OnEveryEngineRouteAsync(source, null, null, download: download);
        Assert.Equal("ok", unconfigured.Kind);
        Assert.Null(unconfigured.Min);
        Assert.Null(unconfigured.Max);
        Assert.StartsWith(OneSeventh, unconfigured.Display, StringComparison.Ordinal);

        // The host setting alone applies: 4, not the nested declaration's 2.
        var hosted = await OnEveryEngineRouteAsync(setting, source, 4, download: download);
        Assert.Equal(4, hosted.Effective(setting));
        Assert.StartsWith(setting == Setting.Max ? "0.1429" : OneSeventh, hosted.Display, StringComparison.Ordinal);
        Assert.Equal(unconfigured.Value, hosted.Value);
    }

    [Theory]
    [MemberData(nameof(BothSettings))]
    public async Task RootDeclaration_IsTheSetting_EvenWhenAnOpenAlsoProvidesTheName(Setting setting)
    {
        // The owner walk selects the root's own declaration before any open; the opened member
        // stays an ordinary binding the program can read.
        var outcome = await OnEveryEngineRouteAsync(
            Fill("open M\nM = {\n    public {0} = 5\n}\n{0} = 2\n1 / 7, M.{0}", setting), null, null);

        Assert.Equal(2, outcome.Effective(setting));
        Assert.Equal(setting == Setting.Max ? "0.14\n5" : $"{OneSeventh}\n5.00", outcome.Display);
    }

    // ── The intentional engine / raw-evaluator boundary ─────────────────────────

    private static readonly (string Source, string EngineOutcome, string EngineHostCall)[] RawBoundarySources =
    [
        ("{0} = trace(2)\n1 / 3", "ok", "trace(2)"),
        ("{0} = 1 / 0\n1 / 3", nameof(KatLangErrorCode.DivisionByZero), ""),
        ("{0} = 100\n1 / 3", nameof(KatLangErrorCode.IllegalInEval), ""),
        ("{0} = trace(1.5)\n1 / 3", nameof(KatLangErrorCode.IllegalInEval), "trace(1.5)"),
    ];

    public static TheoryData<Setting, string, string, string> RawBoundaryCases()
    {
        var data = new TheoryData<Setting, string, string, string>();
        foreach (var setting in new[] { Setting.Min, Setting.Max })
            foreach (var (source, engineOutcome, engineHostCall) in RawBoundarySources)
                data.Add(setting, source, engineOutcome, engineHostCall);
        return data;
    }

    /// <summary>
    /// The raw evaluator never reads a source setting: it executes none of its effects and none of
    /// its failures; the engine reads and validates it. This divergence is the decided
    /// host-presentation boundary (Q-10 D-F, X-35), not a route defect.
    /// </summary>
    [Theory]
    [MemberData(nameof(RawBoundaryCases))]
    public async Task RawEvaluator_NeverReadsTheSourceSetting_WhileTheEngineDoes(
        Setting setting, string template, string engineOutcome, string engineHostCall)
    {
        var source = Fill(template, setting);
        SourceProvenance.ParseValid(source);
        foreach (var route in new[] { SixRouteAgreement.Route.Generic, SixRouteAgreement.Route.Optimized, SixRouteAgreement.Route.ForcedTwin })
        {
            var raw = await SixRouteAgreement.ObserveAsync(route, source);
            Assert.Equal("ok", raw.Kind);
            Assert.Equal("0.3333333333333333333333333333333333", raw.Value);
            Assert.Empty(raw.HostCalls);
        }

        Assert.False(Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root)).IsError);

        foreach (var host in new int?[] { null, 5 })
        {
            var engine = await OnEveryEngineRouteAsync(setting, source, host);
            if (engineOutcome == "ok")
                Assert.Equal("ok", engine.Kind);
            else
                Assert.StartsWith(engineOutcome + ": ", Assert.Single(engine.Errors), StringComparison.Ordinal);
            Assert.Equal(engineHostCall.Length == 0 ? [] : new[] { engineHostCall }, engine.HostCalls);
        }
    }

    /// <summary>The raw evaluator completes a program whose source PAIR the engine refuses.</summary>
    [Fact]
    public async Task RawEvaluator_NeverChecksTheSourcePair_WhileTheEngineDoes()
    {
        const string source = "MinDecimalPlaces = trace(5)\nMaxDecimalPlaces = trace(3)\n1 / 3";
        var root = SourceProvenance.ParseValid(source).Root;

        foreach (var route in new[] { SixRouteAgreement.Route.Generic, SixRouteAgreement.Route.Optimized, SixRouteAgreement.Route.ForcedTwin })
        {
            var raw = await SixRouteAgreement.ObserveAsync(route, source);
            Assert.Equal("ok", raw.Kind);
            Assert.Empty(raw.HostCalls);
        }

        Assert.False(Evaluator.Run(new Expr.AlgorithmExpr(root)).IsError);

        var engine = await OnEveryEngineRouteAsync(source, null, null);
        Assert.StartsWith(nameof(KatLangErrorCode.IllegalInEval) + ": ", Assert.Single(engine.Errors), StringComparison.Ordinal);
        Assert.Equal(["trace(5)", "trace(3)"], engine.HostCalls);
    }

    // ── Rendering is inert: values, representations, .string ────────────────────

    public static TheoryData<int?, int?, int?, int?> SettingCombinations => new()
    {
        { null, null, null, null },
        { null, 2, null, null },
        { null, null, null, 1 },
        { null, 2, null, 1 },
        { null, 1, null, 2 },
        { null, 0, null, 0 },
        { null, 99, null, 99 },
        { 2, null, null, null },
        { null, null, 1, null },
        { 2, null, 1, null },
        { 0, null, 0, null },
        { 99, null, 99, null },
        { 2, 2, null, null },
        { null, null, 2, 2 },
        { 1, 4, 2, 3 },
        { 0, 99, 0, 99 },
    };

    /// <summary>
    /// No setting — source, host, minimum, maximum, or their composition — reaches
    /// <c>.string</c>, a comparison, or the value: with source max 2 and host max 1 the effective
    /// maximum is 1, yet <c>x.string</c> is <c>'1.555'</c> and <c>x == 1.555</c> holds.
    /// </summary>
    [Theory]
    [MemberData(nameof(SettingCombinations))]
    public async Task Settings_NeverChangeStringValueOrComparison(int? sourceMin, int? sourceMax, int? hostMin, int? hostMax)
    {
        var source = WithSource(Setting.Min, sourceMin, WithSource(Setting.Max, sourceMax,
            "x = 1.555\ny = 1.50\nx, x.string, x == 1.555, x == 1.6, y.string, (-0).string, y == 1.5"));

        var outcome = await OnEveryEngineRouteAsync(source, hostMin, hostMax);

        Assert.Equal("S[1.555, '1.555', true, false, '1.50', '-0', true]", outcome.Value);
        Assert.Equal(KatLangEngine.CombineDecimalPlaces(sourceMin, hostMin), outcome.Min);
        Assert.Equal(KatLangEngine.CombineDecimalPlaces(sourceMax, hostMax), outcome.Max);
        // Strings are shown raw and untouched under every setting; only the numbers are displayed
        // under the pair.
        var rows = outcome.Display.Split('\n');
        Assert.Equal(["1.555", "true", "false", "1.50", "-0", "true"], [rows[1], rows[2], rows[3], rows[4], rows[5], rows[6]]);
        if (outcome.Max == 1)
            Assert.Equal("1.6", rows[0]);
    }

    /// <summary>
    /// Rendering never mutates the returned result: the exact Decimal128 value, its representation
    /// and the host atoms are those of the unconfigured run before AND after every rendering
    /// surface has rendered it.
    /// </summary>
    [Fact]
    public void Rendering_NeverMutatesTheReturnedValueOrItsRepresentation()
    {
        const string program = "1.555, 1.50, -0, -0.0, 1e3, 2 / 3, (2.5, [-2.5])";
        var baseline = Assert.IsType<RunResult.Success>(KatLangEngine.Run(program));
        var baselineValue = NumericRepresentativeSelectionTests.Exact(baseline.Value);
        var baselineAtoms = baseline.Atoms.Select(NumericRepresentativeSelectionTests.Number).ToArray();

        foreach (var (sourceMin, sourceMax, hostMin, hostMax) in new (int?, int?, int?, int?)[]
                 {
                     (null, 2, null, null), (null, null, null, 1), (null, 2, null, 1), (null, 0, null, 99), (null, 99, null, 0),
                     (2, null, null, null), (null, null, 1, null), (2, null, 1, null), (0, null, 99, null), (99, null, 0, null),
                     (2, 2, null, null), (null, null, 2, 2), (1, 4, 2, 3),
                 })
        {
            var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
                WithSource(Setting.Min, sourceMin, WithSource(Setting.Max, sourceMax, program)),
                new RunOptions { MinDecimalPlaces = hostMin, MaxDecimalPlaces = hostMax }));
            Assert.Equal(baselineValue, NumericRepresentativeSelectionTests.Exact(run.Value));

            _ = run.ToDisplayString();
            _ = run.RenderDisplay();
            foreach (var formatter in new[] { OutputFormatters.Exact, OutputFormatters.Readable, OutputFormatters.Concise })
                _ = formatter.Format(run);

            Assert.Equal(baselineValue, NumericRepresentativeSelectionTests.Exact(run.Value));
            Assert.Equal(baselineAtoms, run.Atoms.Select(NumericRepresentativeSelectionTests.Number).ToArray());
        }
    }

    /// <summary>
    /// A display setting never changes a LATER calculation or comparison: a value computed from a
    /// number that a maximum displays rounded is computed from the unrounded number.
    /// </summary>
    [Theory]
    [MemberData(nameof(SettingCombinations))]
    public async Task Settings_NeverChangeALaterCalculationOrComparison(int? sourceMin, int? sourceMax, int? hostMin, int? hostMax)
    {
        const string program =
            "Third = 1 / 3\nTriple = Third * 3\nTriple == 1, Triple < 1, Third * 3000 > 999, Math.Round(Third, 2) == 0.33, Third == 0.33, [Third, 0.33].distinct.count";
        var source = WithSource(Setting.Min, sourceMin, WithSource(Setting.Max, sourceMax, program));

        var outcome = await OnEveryEngineRouteAsync(source, hostMin, hostMax);

        // 1/3 carries 34 threes; three of them are 0.999...9, not the 1 a rounded 0.33 * 3 = 0.99
        // or a rounded-to-1 display would suggest.
        Assert.Equal("S[false, true, true, true, false, 2]", outcome.Value);
    }

    // ── A host setting is configuration, never a binding ───────────────────────

    [Theory]
    [MemberData(nameof(BothSettings))]
    public async Task HostSetting_IsNoBinding_ForAProgramReadingTheName(Setting setting)
    {
        var source = Fill("{0} + 1", setting);
        var without = await OnEveryEngineRouteAsync(source, null, null);
        var with = await OnEveryEngineRouteAsync(source, 5, 5);

        Assert.Equal("err", without.Kind);
        Assert.Equal(without.Errors, with.Errors);

        var parsed = Parser.Parse(source, new RunOptions { MinDecimalPlaces = 5, MaxDecimalPlaces = 5 });
        Assert.False(parsed.HasErrors);
        Assert.DoesNotContain(parsed.Root.Properties, p => p.Name == Name(setting));
    }

    // ── Runs do not leak configuration ─────────────────────────────────────────

    /// <summary>
    /// Repeated and concurrent runs with different settings, through shared and separate options
    /// objects: every run displays exactly its own pair, in any interleaving, and no run's source
    /// setting reaches another run or the shared options.
    /// </summary>
    [Fact]
    public void RepeatedAndConcurrentRuns_WithDifferentSettings_DoNotLeakConfiguration()
    {
        var shared = new RunOptions { MinDecimalPlaces = 1, MaxDecimalPlaces = 3 };
        var cases = new (string Source, RunOptions? Options, string Expected)[]
        {
            ("10, 1 / 7", null, $"10\n{OneSeventh}"),
            ("10, 1 / 7", shared, "10.0\n0.143"),
            ("MinDecimalPlaces = 2\n10, 1 / 7", null, $"10.00\n{OneSeventh}"),
            ("MaxDecimalPlaces = 2\n10, 1 / 7", null, "10\n0.14"),
            ("MaxDecimalPlaces = 2\n10, 1 / 7", shared, "10.0\n0.14"),
            ("MinDecimalPlaces = 0\n10, 1 / 7", shared, "10\n0.143"),
            ("10, 1 / 7", new RunOptions { MinDecimalPlaces = 4 }, $"10.0000\n{OneSeventh}"),
            ("10, 1 / 7", new RunOptions { MaxDecimalPlaces = 0 }, "10\n0"),
            ("MinDecimalPlaces = 2\nMaxDecimalPlaces = 2\n10, 1 / 7", null, "10.00\n0.14"),
        };

        // Repeated, in order and in reverse: the same text every time.
        for (var pass = 0; pass < 3; pass++)
        {
            foreach (var (source, options, expected) in pass == 1 ? Enumerable.Reverse(cases) : cases)
                Assert.Equal(expected, KatLangEngine.Run(source, options).ToDisplayString().ReplaceLineEndings("\n"));
        }

        // Concurrent, interleaved.
        var displays = new string[cases.Length * 24];
        Parallel.For(0, displays.Length, i =>
        {
            var (source, options, _) = cases[i % cases.Length];
            displays[i] = KatLangEngine.Run(source, options).ToDisplayString().ReplaceLineEndings("\n");
        });
        for (var i = 0; i < displays.Length; i++)
            Assert.Equal(cases[i % cases.Length].Expected, displays[i]);

        Assert.Equal(((int?)1, (int?)3), (shared.MinDecimalPlaces, shared.MaxDecimalPlaces));
        Assert.Equal($"10\n{OneSeventh}", KatLangEngine.Run("10, 1 / 7").ToDisplayString().ReplaceLineEndings("\n"));
    }
}
