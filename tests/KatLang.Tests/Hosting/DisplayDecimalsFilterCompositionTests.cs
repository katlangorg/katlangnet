using System.Globalization;
using System.Numerics;
using KatLang.Formatting;
using KatLang.Tests.Randomness;

namespace KatLang.Tests.Hosting;

/// <summary>
/// Q-10, decided D-F (2026-10-07): every active <c>DisplayDecimals</c> setting is a PRESENTATION
/// FILTER — an upper bound on displayed decimal places. A run has two: the SOURCE filter, the
/// program root's OWN declared <c>DisplayDecimals</c> property, and the HOST filter,
/// <see cref="RunOptions.DefaultDisplayDecimals"/> (the CLI's <c>--display-decimals</c>, a host UI
/// setting). An absent filter imposes no limit; one present filter is effective; both present give
/// their MINIMUM; neither gives canonical rendering. The contract pinned here:
/// <list type="bullet">
///   <item>the composition table, exactly, on the three engine routes (sync, async, async twin);</item>
///   <item>"off" (<c>null</c>) is no host filter — never zero places, never a suppressed source filter;</item>
///   <item>a declared source filter is evaluated and validated after successful output WHATEVER the
///   host filter is — a stricter host filter never skips the read, never excuses an invalid or
///   failing value, and never changes its effects, draws, step charges, cancellation or cache reuse
///   (the ordinary cached zero-argument VALUE read of the same run; an explicit
///   <c>DisplayDecimals()</c> stays a fresh call that does not satisfy it);</item>
///   <item>evaluation order: output, then the source read, then validation, composition and
///   rendering — an output failure is never masked;</item>
///   <item>only the root's own declaration is a filter (no nested, opened, inline-opened, member,
///   module, module-root or parameter <c>DisplayDecimals</c>);</item>
///   <item>the raw <see cref="Evaluator"/> never reads it (the intentional engine/evaluator
///   boundary, X-35);</item>
///   <item>rendering is inert: no filter changes a value, its Decimal128 representation,
///   <c>.string</c>, comparisons, atoms, or anything already evaluated.</item>
/// </list>
/// </summary>
public sealed class DisplayDecimalsFilterCompositionTests
{
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

    /// <summary>
    /// One engine run, comparably: the outcome kind, the effective display decimals the result
    /// carries, its display text, its value rendered representation-exactly, every error, and the
    /// exact host-call log.
    /// </summary>
    private sealed record Outcome(
        string Kind,
        int? Decimals,
        string Display,
        string? Value,
        IReadOnlyList<string> Errors,
        IReadOnlyList<string> HostCalls)
    {
        public bool AgreesWith(Outcome other)
            => Kind == other.Kind
                && Decimals == other.Decimals
                && Display == other.Display
                && Value == other.Value
                && Errors.SequenceEqual(other.Errors)
                && HostCalls.SequenceEqual(other.HostCalls);

        public override string ToString()
            => $"{Kind} decimals={Decimals?.ToString(CultureInfo.InvariantCulture) ?? "canonical"} value={Value} " +
               $"display=[{Display}] errors=[{string.Join(" | ", Errors)}] host=[{string.Join(",", HostCalls)}]";
    }

    private sealed class HostLog
    {
        private int _ticks;

        public List<string> Calls { get; } = [];

        public CancellationTokenSource? Cancellation { get; init; }

        public Result Tick()
        {
            var tick = Interlocked.Increment(ref _ticks);
            lock (Calls)
                Calls.Add($"tick#{tick}");
            return new Result.Atom((Decimal128)tick);
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
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return log.Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x"),
                HostOperation.CreateAsync("cancel", async (_, _) => { await Task.Yield(); return log.Cancel(); }))
            : HostOperations.Create(
                HostOperation.Create("tick", (_, _) => log.Tick()),
                HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x"),
                HostOperation.Create("cancel", (_, _) => log.Cancel()));

    private static async Task<(RunResult Result, HostLog Log)> RunAsync(
        EngineRoute route,
        string source,
        int? hostFilter,
        long? seed = null,
        EvaluationLimits? limits = null,
        CancellationTokenSource? cancellation = null,
        Func<string, CancellationToken, ValueTask<string>>? download = null)
    {
        var log = new HostLog { Cancellation = cancellation };
        var options = new RunOptions
        {
            HostOperations = OperationsFor(log, route == EngineRoute.AsyncTwin),
            DefaultDisplayDecimals = hostFilter,
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

    private static Outcome Describe(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new(
            "ok",
            success.DisplayOptions.Decimals,
            success.ToDisplayString().ReplaceLineEndings("\n"),
            NumericRepresentativeSelectionTests.Exact(success.Value),
            [],
            [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", failure.DisplayOptions.Decimals, "", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.ParseFailure failure => new("parse", failure.DisplayOptions.Decimals, "", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", none.DisplayOptions.Decimals, "", null, [Describe(none.Diagnostic)], [.. log.Calls]),
    };

    private static string Describe(KatLangError error) => $"{error.Code}: {error.Message} @ {error.Span}";

    /// <summary>
    /// Runs <paramref name="source"/> on the three engine routes with <paramref name="hostFilter"/>
    /// and requires them to agree on everything — kind, effective decimals, display, exact value,
    /// errors with spans, and the host-call log. Returns the synchronous oracle.
    /// </summary>
    private static async Task<Outcome> OnEveryEngineRouteAsync(
        string source,
        int? hostFilter,
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
            var (result, log) = await RunAsync(route, source, hostFilter, seed, limits, download: download);
            var outcome = Describe(result, log);
            oracle ??= outcome;
            Assert.True(oracle.AgreesWith(outcome), $"{route}: expected {oracle}, got {outcome}\nhost filter: {hostFilter}\nsource:\n{source}");
        }

        return oracle!;
    }

    private static readonly int?[] HostFilters = [null, 0, 1, 5, 7, 10, RunOptions.MaxDisplayDecimals];

    private const string OneSeventh = "0.1428571428571428571428571428571429";

    /// <summary>The expected display of <c>1 / 7, 2.5, -2.5</c> at an effective count, hand-written.</summary>
    private static string ExpectedDisplay(int? effective) => effective switch
    {
        null => $"{OneSeventh}\n2.5\n-2.5",
        0 => "0\n3\n-3",
        5 => "0.14286\n2.50000\n-2.50000",
        7 => "0.1428571\n2.5000000\n-2.5000000",
        RunOptions.MaxDisplayDecimals => $"{OneSeventh}{new string('0', 99 - 34)}\n2.5{new string('0', 98)}\n-2.5{new string('0', 98)}",
        _ => throw new ArgumentOutOfRangeException(nameof(effective), effective, null),
    };

    private static string WithSource(int? sourceFilter, string program)
        => sourceFilter is { } decimals
            ? $"DisplayDecimals = {decimals.ToString(CultureInfo.InvariantCulture)}\n{program}"
            : program;

    // ── The composition law ─────────────────────────────────────────────────────

    /// <summary>The ONE composition helper against an independent oracle, over the whole domain.</summary>
    [Fact]
    public void CombineDisplayDecimals_IsTheMinimumOfThePresentFilters_OverTheWholeDomain()
    {
        var domain = Enumerable.Range(0, RunOptions.MaxDisplayDecimals + 1).Select(static n => (int?)n).Prepend(null).ToArray();
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
                Assert.Equal(expected, KatLangEngine.CombineDisplayDecimals(source, host));
            }
        }
    }

    /// <summary>The D-F composition table, with the exact display, on every engine route.</summary>
    [Theory]
    [InlineData(null, null, null)]
    [InlineData(7, null, 7)]
    [InlineData(null, 5, 5)]
    [InlineData(7, 5, 5)]
    [InlineData(5, 7, 5)]
    [InlineData(0, 7, 0)]
    [InlineData(7, 0, 0)]
    [InlineData(99, 99, 99)]
    [InlineData(5, 5, 5)]
    [InlineData(0, null, 0)]
    [InlineData(null, 0, 0)]
    [InlineData(99, 0, 0)]
    [InlineData(0, 99, 0)]
    public async Task CompositionTable_EffectiveIsTheMinimumOfThePresentFilters(int? sourceFilter, int? hostFilter, int? effective)
    {
        var source = WithSource(sourceFilter, "1 / 7, 2.5, -2.5");
        SourceProvenance.ParseValid(source);

        var outcome = await OnEveryEngineRouteAsync(source, hostFilter);

        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(effective, outcome.Decimals);
        Assert.Equal(ExpectedDisplay(effective), outcome.Display);
        Assert.Equal($"S[{OneSeventh}, 2.5, -2.5]", outcome.Value);
    }

    /// <summary>
    /// The portability property: one shared program with <c>DisplayDecimals = 7</c> shows 7 places
    /// for a recipient without a filter, 5 under a host filter of 5, and still 7 under 10.
    /// </summary>
    [Fact]
    public async Task SharedSourceFilter_CarriesItsIntent_AndAStricterHostStillWins()
    {
        const string shared = "DisplayDecimals = 7\n1 / 3";
        Assert.Equal("0.3333333", (await OnEveryEngineRouteAsync(shared, null)).Display);
        Assert.Equal("0.33333", (await OnEveryEngineRouteAsync(shared, 5)).Display);
        Assert.Equal("0.3333333", (await OnEveryEngineRouteAsync(shared, 10)).Display);
    }

    /// <summary>"Off" is no host filter: never zero places, never canonicalization of a declared filter.</summary>
    [Fact]
    public async Task HostFilterOff_IsNoFilter_NeverZeroPlaces_NeverASuppressedSourceFilter()
    {
        var off = await OnEveryEngineRouteAsync("DisplayDecimals = 7\n2.5", null);
        var zero = await OnEveryEngineRouteAsync("DisplayDecimals = 7\n2.5", 0);
        var canonical = await OnEveryEngineRouteAsync("2.5", null);

        Assert.Equal((7, "2.5000000"), (off.Decimals!.Value, off.Display));
        Assert.Equal((0, "3"), (zero.Decimals!.Value, zero.Display));
        Assert.Equal((null, "2.5"), (canonical.Decimals, canonical.Display));

        // And a declared 0 is a real filter, never absence.
        var declaredZero = await OnEveryEngineRouteAsync("DisplayDecimals = 0\n2.5", 7);
        Assert.Equal((0, "3"), (declaredZero.Decimals!.Value, declaredZero.Display));
    }

    // ── Source-filter validation, with and without a host filter ───────────────

    public static TheoryData<string, int> ValidSourceFilters => new()
    {
        { "DisplayDecimals = 2", 2 },
        { "DisplayDecimals = 0", 0 },
        { "DisplayDecimals = 99", 99 },
        { "DisplayDecimals = 2.0", 2 },
        { "DisplayDecimals = -0", 0 },
        { "DisplayDecimals = 1 + 1", 2 },
        { "Two = 2\nDisplayDecimals = Two", 2 },
        { "DisplayDecimals(*xs) = 2 + xs.count", 2 },
        { "public DisplayDecimals = 3", 3 },
        { "DisplayDecimals = { 4 }", 4 },
    };

    [Theory]
    [MemberData(nameof(ValidSourceFilters))]
    public async Task ValidSourceFilter_ComposesWithEveryHostFilter(string declaration, int value)
    {
        var source = declaration + "\n1 / 7, 2.5, -2.5";
        SourceProvenance.ParseValid(source);

        foreach (var host in HostFilters)
        {
            var outcome = await OnEveryEngineRouteAsync(source, host);
            Assert.Equal("ok", outcome.Kind);
            Assert.Equal(host is { } h ? Math.Min(value, h) : value, outcome.Decimals);
        }
    }

    public static TheoryData<string, KatLangErrorCode, string?> InvalidSourceFilters => new()
    {
        { "DisplayDecimals = -1", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be a non-negative integer." },
        { "DisplayDecimals = 1.5", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be an integer." },
        { "DisplayDecimals = 100", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be between 0 and 99." },
        { "DisplayDecimals = Math.Sqrt(-1)", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be an integer." },
        { "DisplayDecimals = 9e6144 * 10", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be an integer." },
        { "DisplayDecimals = -9e6144 * 10", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be a non-negative integer." },
        { "DisplayDecimals = 'x'", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be a single numeric value." },
        { "DisplayDecimals = true", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be a single numeric value." },
        { "DisplayDecimals = 2, 3", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be a single numeric value." },
        { "DisplayDecimals = (2, 3)", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be a single numeric value." },
        { "DisplayDecimals = [2]", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be a single numeric value." },
        { "DisplayDecimals = ()", KatLangErrorCode.IllegalInEval, "DisplayDecimals must be a single numeric value." },
        { "DisplayDecimals = 1 / 0", KatLangErrorCode.DivisionByZero, null },
        { "DisplayDecimals(x) = x", KatLangErrorCode.ArityMismatch, null },
        { "DisplayDecimals = n + 1", KatLangErrorCode.ArityMismatch, null },
        { "DisplayDecimals(0) = 1\nDisplayDecimals(n) = 2", KatLangErrorCode.NoMatchingBranch, null },
    };

    /// <summary>
    /// A host filter never hides an invalid or failing source filter — not even a stricter one: the
    /// failure is exactly the failure without a host filter (code, message, span), on every route.
    /// </summary>
    [Theory]
    [MemberData(nameof(InvalidSourceFilters))]
    public async Task InvalidSourceFilter_FailsTheEngineRun_WhateverTheHostFilter(string declaration, KatLangErrorCode code, string? message)
    {
        var source = declaration + "\n1 / 7";
        SourceProvenance.ParseValid(source);

        var baseline = await OnEveryEngineRouteAsync(source, null);
        Assert.Equal("err", baseline.Kind);
        var error = Assert.Single(baseline.Errors);
        Assert.StartsWith(code + ": ", error, StringComparison.Ordinal);
        if (message is not null)
            Assert.Contains($"{message} @ ", error, StringComparison.Ordinal);

        foreach (var host in HostFilters)
        {
            var outcome = await OnEveryEngineRouteAsync(source, host);
            Assert.Equal(baseline.Kind, outcome.Kind);
            Assert.Equal(baseline.Errors, outcome.Errors);
            Assert.Equal(baseline.HostCalls, outcome.HostCalls);
        }
    }

    // ── Effects, draws, steps, cancellation, cache ─────────────────────────────

    [Theory]
    [InlineData(null, 7)]
    [InlineData(5, 5)]
    [InlineData(10, 7)]
    [InlineData(0, 0)]
    public async Task EffectfulSourceFilter_RunsExactlyOnce_WhateverTheHostFilter(int? hostFilter, int effective)
    {
        var outcome = await OnEveryEngineRouteAsync("DisplayDecimals = trace(7)\n1 / 7", hostFilter);

        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(effective, outcome.Decimals);
        Assert.Equal(["trace(7)"], outcome.HostCalls);
    }

    /// <summary>The engine's read is the ordinary cached VALUE read: an output that already read the property is reused.</summary>
    [Theory]
    [InlineData(null)]
    [InlineData(5)]
    [InlineData(0)]
    public async Task ProgramThatReadsTheSourceFilter_SharesTheOneCachedEvaluation(int? hostFilter)
    {
        var outcome = await OnEveryEngineRouteAsync("DisplayDecimals = trace(7)\nDisplayDecimals, 1 / 7", hostFilter);

        Assert.Equal(["trace(7)"], outcome.HostCalls);
        Assert.StartsWith("S[7, ", outcome.Value, StringComparison.Ordinal);
        Assert.Equal(hostFilter is { } h ? Math.Min(7, h) : 7, outcome.Decimals);
    }

    /// <summary>
    /// An explicit <c>DisplayDecimals()</c> is a fresh call: it neither reads nor populates the
    /// cached entry, so it never satisfies the engine's later cached read — which evaluates the
    /// property again, and whose value (not the explicit call's) is the source filter.
    /// </summary>
    [Theory]
    [InlineData(null)]
    [InlineData(5)]
    [InlineData(99)]
    public async Task ExplicitCall_IsFresh_AndNeverSatisfiesTheCachedEngineRead(int? hostFilter)
    {
        var explicitOnly = await OnEveryEngineRouteAsync("DisplayDecimals = tick() + 4\nDisplayDecimals(), 1 / 7", hostFilter);
        Assert.Equal(["tick#1", "tick#2"], explicitOnly.HostCalls);
        Assert.StartsWith("S[5, ", explicitOnly.Value, StringComparison.Ordinal);
        Assert.Equal(hostFilter is { } h ? Math.Min(6, h) : 6, explicitOnly.Decimals);

        // A cached read in the output, then an explicit call: the engine reuses the cached 5.
        var cachedFirst = await OnEveryEngineRouteAsync("DisplayDecimals = tick() + 4\nDisplayDecimals, DisplayDecimals(), 1 / 7", hostFilter);
        Assert.Equal(["tick#1", "tick#2"], cachedFirst.HostCalls);
        Assert.StartsWith("S[5, 6, ", cachedFirst.Value, StringComparison.Ordinal);
        Assert.Equal(hostFilter is { } h2 ? Math.Min(5, h2) : 5, cachedFirst.Decimals);
    }

    [Theory]
    [InlineData(null)]
    [InlineData(0)]
    [InlineData(5)]
    [InlineData(99)]
    public async Task SeededRandomSourceFilter_DrawsAfterTheOutput_WhateverTheHostFilter(int? hostFilter)
    {
        const long seed = 20261007;
        var words = SeededRun.Words(seed);
        var fraction = ReferenceRandomOracle.Random(words, 0, 1);
        var digits = (int)ReferenceRandomOracle.RandomInt(words, 6, 9);

        var outcome = await OnEveryEngineRouteAsync(
            "Math.Random(0, 1)\nDisplayDecimals = Math.RandomInt(6, 9)", hostFilter, seed);

        Assert.Equal(NumericRepresentativeSelectionTests.Number(fraction), outcome.Value);
        Assert.Equal(hostFilter is { } h ? Math.Min(digits, h) : digits, outcome.Decimals);
    }

    /// <summary>
    /// The source read is charged to the run's budget whatever the host filter is: a step-heavy
    /// source filter exceeds a tight step budget the program alone fits — with a stricter host
    /// filter too — while the raw evaluator, which never reads it, completes.
    /// </summary>
    [Fact]
    public async Task StepHeavySourceFilter_IsChargedToTheRun_WhateverTheHostFilter()
    {
        const string source = "S(x) = x + 1\nDisplayDecimals = repeat(S, 500, 0) * 0 + 2\n1 / 3";
        var limits = new EvaluationLimits { MaxSteps = 200 };

        foreach (var host in new int?[] { null, 0, 1, 5 })
        {
            var outcome = await OnEveryEngineRouteAsync(source, host, limits: limits);
            Assert.Equal("err", outcome.Kind);
            Assert.StartsWith(nameof(KatLangErrorCode.EvaluationStepLimitExceeded) + ": ", Assert.Single(outcome.Errors), StringComparison.Ordinal);
        }

        var raw = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), limits: limits);
        Assert.False(raw.Result.IsError);
    }

    [Theory]
    [InlineData(EngineRoute.Sync, null)]
    [InlineData(EngineRoute.Sync, 0)]
    [InlineData(EngineRoute.Sync, 5)]
    [InlineData(EngineRoute.Async, 0)]
    [InlineData(EngineRoute.AsyncTwin, null)]
    [InlineData(EngineRoute.AsyncTwin, 5)]
    public async Task CancellationDuringTheSourceFilter_CancelsTheRun_WhateverTheHostFilter(EngineRoute route, int? hostFilter)
    {
        using var cancellation = new CancellationTokenSource();
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await RunAsync(route, "DisplayDecimals = cancel() + 2\n1 / 3", hostFilter, cancellation: cancellation));
        Assert.Equal(cancellation.Token, error.CancellationToken);
    }

    // ── Evaluation order ────────────────────────────────────────────────────────

    [Theory]
    [InlineData(null)]
    [InlineData(0)]
    [InlineData(5)]
    public async Task OutputFailure_IsNeverMasked_AndTheSourceFilterIsNotRead(int? hostFilter)
    {
        var divide = await OnEveryEngineRouteAsync("DisplayDecimals = trace(2)\n1 / 0", hostFilter);
        Assert.StartsWith(nameof(KatLangErrorCode.DivisionByZero) + ": ", Assert.Single(divide.Errors), StringComparison.Ordinal);
        Assert.Empty(divide.HostCalls);

        var index = await OnEveryEngineRouteAsync("DisplayDecimals = 1 / 0\n[1]:5", hostFilter);
        Assert.StartsWith(nameof(KatLangErrorCode.BadIndex) + ": ", Assert.Single(index.Errors), StringComparison.Ordinal);

        var none = await OnEveryEngineRouteAsync("DisplayDecimals = trace(2)", hostFilter);
        Assert.Equal("none", none.Kind);
        Assert.Empty(none.HostCalls);
    }

    [Theory]
    [InlineData(null)]
    [InlineData(5)]
    public async Task SourceFilterFailure_FollowsTheOutputsEffects(int? hostFilter)
    {
        var outcome = await OnEveryEngineRouteAsync("DisplayDecimals = trace(1) / 0\ntrace(10), 1 / 3", hostFilter);

        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith(nameof(KatLangErrorCode.DivisionByZero) + ": ", Assert.Single(outcome.Errors), StringComparison.Ordinal);
        Assert.Equal(["trace(10)", "trace(1)"], outcome.HostCalls);
    }

    // ── Only the program root's own declaration is a source filter ──────────────

    private const string ModuleUrl = "https://katlang.org/display-filter-audit.kat";
    private const string ModuleRootUrl = "https://katlang.org/display-filter-root.kat";

    private static ValueTask<string> Download(string url, CancellationToken token)
        => ValueTask.FromResult(url == ModuleRootUrl
            ? "DisplayDecimals = 2\n1 / 7"
            : "public DisplayDecimals = 2\npublic Third = 1 / 7");

    public static TheoryData<string, bool> NonRootDeclarations => new()
    {
        { "A = {\n    DisplayDecimals = 2\n    1 / 7\n}\nA", false },
        { "open M\nM = {\n    public DisplayDecimals = 2\n}\n1 / 7, DisplayDecimals", false },
        { "open { public DisplayDecimals = 2 }\n1 / 7, DisplayDecimals", false },
        { "Obj = {\n    public DisplayDecimals = 2\n    public V = 1 / 7\n}\nObj.V, Obj.DisplayDecimals", false },
        { "F(DisplayDecimals) = DisplayDecimals / 7\nF(1)", false },
        { $"open '{ModuleUrl}'\nThird, DisplayDecimals", true },
        { $"M = load('{ModuleUrl}')\nM.Third, M.DisplayDecimals", true },
        { $"M = load('{ModuleRootUrl}')\nM", true },
    };

    [Theory]
    [MemberData(nameof(NonRootDeclarations))]
    public async Task NonRootDisplayDecimals_IsAnOrdinaryBinding_NeverAFilter(string source, bool loads)
    {
        var download = loads ? Download : (Func<string, CancellationToken, ValueTask<string>>?)null;

        var unfiltered = await OnEveryEngineRouteAsync(source, null, download: download);
        Assert.Equal("ok", unfiltered.Kind);
        Assert.Null(unfiltered.Decimals);
        Assert.StartsWith(OneSeventh, unfiltered.Display, StringComparison.Ordinal);

        var hosted = await OnEveryEngineRouteAsync(source, 4, download: download);
        Assert.Equal(4, hosted.Decimals);
        Assert.StartsWith("0.1429", hosted.Display, StringComparison.Ordinal);
        Assert.Equal(unfiltered.Value, hosted.Value);
    }

    [Fact]
    public async Task RootDeclaration_IsTheFilter_EvenWhenAnOpenAlsoProvidesTheName()
    {
        // The owner walk selects the root's own declaration before any open; the opened member
        // stays an ordinary binding the program can read.
        var outcome = await OnEveryEngineRouteAsync(
            "open M\nM = {\n    public DisplayDecimals = 5\n}\nDisplayDecimals = 2\n1 / 7, M.DisplayDecimals", null);
        Assert.Equal(2, outcome.Decimals);
        Assert.Equal("0.14\n5", outcome.Display);
    }

    // ── The intentional engine / raw-evaluator boundary ─────────────────────────

    /// <summary>
    /// The raw evaluator never reads a source <c>DisplayDecimals</c>: it executes none of its
    /// effects and none of its failures; the engine reads and validates it. This divergence is the
    /// decided host-presentation boundary (Q-10 D-F, X-35), not a route defect.
    /// </summary>
    [Theory]
    [InlineData("DisplayDecimals = trace(2)\n1 / 3", "ok", "trace(2)")]
    [InlineData("DisplayDecimals = 1 / 0\n1 / 3", nameof(KatLangErrorCode.DivisionByZero), "")]
    [InlineData("DisplayDecimals = 100\n1 / 3", nameof(KatLangErrorCode.IllegalInEval), "")]
    [InlineData("DisplayDecimals = trace(1.5)\n1 / 3", nameof(KatLangErrorCode.IllegalInEval), "trace(1.5)")]
    public async Task RawEvaluator_NeverReadsTheSourceFilter_WhileTheEngineDoes(string source, string engineOutcome, string engineHostCall)
    {
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
            var engine = await OnEveryEngineRouteAsync(source, host);
            if (engineOutcome == "ok")
                Assert.Equal("ok", engine.Kind);
            else
                Assert.StartsWith(engineOutcome + ": ", Assert.Single(engine.Errors), StringComparison.Ordinal);
            Assert.Equal(engineHostCall.Length == 0 ? [] : new[] { engineHostCall }, engine.HostCalls);
        }
    }

    // ── Rendering is inert: values, representations, .string ────────────────────

    /// <summary>
    /// No filter — source, host, or their composition — reaches <c>.string</c>, a comparison, or
    /// the value: with source 2 and host 1 the effective filter is 1, yet <c>x.string</c> is
    /// <c>'1.555'</c> and <c>x == 1.555</c> holds.
    /// </summary>
    [Theory]
    [InlineData(null, null)]
    [InlineData(2, null)]
    [InlineData(null, 1)]
    [InlineData(2, 1)]
    [InlineData(1, 2)]
    [InlineData(0, 0)]
    [InlineData(99, 99)]
    public async Task Filters_NeverChangeStringValueOrComparison(int? sourceFilter, int? hostFilter)
    {
        var source = WithSource(sourceFilter, "x = 1.555\ny = 1.50\nx, x.string, x == 1.555, x == 1.6, y.string, (-0).string");

        var outcome = await OnEveryEngineRouteAsync(source, hostFilter);

        Assert.Equal("S[1.555, '1.555', true, false, '1.50', '-0']", outcome.Value);
        Assert.Equal(KatLangEngine.CombineDisplayDecimals(sourceFilter, hostFilter), outcome.Decimals);
        if (outcome.Decimals == 1)
            Assert.StartsWith("1.6\n", outcome.Display, StringComparison.Ordinal);
    }

    /// <summary>
    /// Rendering never mutates the returned result: the exact Decimal128 value, its representation
    /// and the host atoms are those of the unfiltered run before AND after every rendering surface
    /// has rendered it.
    /// </summary>
    [Fact]
    public void Rendering_NeverMutatesTheReturnedValueOrItsRepresentation()
    {
        const string program = "1.555, 1.50, -0, -0.0, 1e3, 2 / 3, (2.5, [-2.5])";
        var baseline = Assert.IsType<RunResult.Success>(KatLangEngine.Run(program));
        var baselineValue = NumericRepresentativeSelectionTests.Exact(baseline.Value);
        var baselineAtoms = baseline.Atoms.Select(NumericRepresentativeSelectionTests.Number).ToArray();

        foreach (var (sourceFilter, hostFilter) in new (int?, int?)[] { (2, null), (null, 1), (2, 1), (0, 99), (99, 0) })
        {
            var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
                WithSource(sourceFilter, program), new RunOptions { DefaultDisplayDecimals = hostFilter }));
            Assert.Equal(baselineValue, NumericRepresentativeSelectionTests.Exact(run.Value));

            _ = run.ToDisplayString();
            _ = run.RenderDisplay();
            foreach (var formatter in new[] { OutputFormatters.Exact, OutputFormatters.Readable, OutputFormatters.Concise })
                _ = formatter.Format(run);

            Assert.Equal(baselineValue, NumericRepresentativeSelectionTests.Exact(run.Value));
            Assert.Equal(baselineAtoms, run.Atoms.Select(NumericRepresentativeSelectionTests.Number).ToArray());
        }
    }

    // ── The host filter is configuration, never a binding ──────────────────────

    [Fact]
    public async Task HostFilter_IsNoBinding_ForAProgramReadingTheName()
    {
        const string source = "DisplayDecimals + 1";
        var without = await OnEveryEngineRouteAsync(source, null);
        var with = await OnEveryEngineRouteAsync(source, 5);

        Assert.Equal("err", without.Kind);
        Assert.Equal(without.Errors, with.Errors);

        var parsed = Parser.Parse(source, new RunOptions { DefaultDisplayDecimals = 5 });
        Assert.False(parsed.HasErrors);
        Assert.DoesNotContain(parsed.Root.Properties, p => p.Name == "DisplayDecimals");
    }
}
