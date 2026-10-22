using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// VARIADIC POSTFIX SELECTION — demand order and effects (owner-approved October 2026). When a
/// selection <c>R[s1, …, sn]</c> is demanded: (1) the receiver is demanded ONCE through its ordinary
/// value path (the cached property read for <c>Data</c>, one fresh invocation for <c>Data()</c>),
/// even when no selector is supplied; (2) the selector supply is formed like a call's — explicit
/// spreads run during formation, in written order, while ordinary selectors stay suspended; (3) the
/// supplied indices are demanded, validated and selected LEFT TO RIGHT, the first failure ending
/// the selection with no later ordinary selector demanded; (4) the selected values are normalized.
/// An otherwise unused selection is never demanded.
///
/// <para>Evidence is deterministic host instrumentation — <c>tick</c> counts its invocations,
/// <c>trace</c> logs its argument — compared on every execution route against the synchronous
/// engine: the public sync and async engines, the async twin (an async host operation present, so
/// evaluation genuinely suspends), the generic and optimized evaluators, and the twin forced by an
/// async-capable property cache. Distinct error categories (and the host log) tell which failure
/// won. Lean: <c>CoreTests/VariadicSelection.lean</c>, laws <c>selectWith_runs_as_its_trace</c>,
/// <c>selectWith_stops_at_first_failure</c>.</para>
/// </summary>
public class VariadicSelectionDemandTests
{
    public enum Route { EngineSync, EngineAsync, EngineAsyncTwin, Generic, Optimized, ForcedTwin }

    private static readonly Route[] Routes = Enum.GetValues<Route>();

    private sealed class HostLog
    {
        private int _ticks;
        public List<string> Calls { get; } = [];

        public Result Tick()
        {
            var tick = Interlocked.Increment(ref _ticks);
            lock (Calls) Calls.Add($"tick#{tick}");
            return new Result.Atom((Decimal128)tick);
        }

        public Result Trace(Result value)
        {
            lock (Calls) Calls.Add($"trace({Neutral(value)})");
            return value;
        }
    }

    private static HostOperations OperationsFor(HostLog log, bool withAsyncOperation)
    {
        var tick = withAsyncOperation
            ? HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return log.Tick(); })
            : HostOperation.Create("tick", (_, _) => log.Tick());
        var trace = withAsyncOperation
            ? HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x")
            : HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x");
        return HostOperations.Create(tick, trace);
    }

    private sealed record Observation(string Kind, string? Value, IReadOnlyList<string> Codes, IReadOnlyList<string> HostCalls)
    {
        public override string ToString() => $"{Kind} {Value} codes=[{string.Join(",", Codes)}] host=[{string.Join(",", HostCalls)}]";
    }

    private static async Task<Observation> ObserveAsync(Route route, string source, EvaluationLimits? limits)
    {
        var log = new HostLog();
        var options = new RunOptions
        {
            EvaluationLimits = limits,
            HostOperations = OperationsFor(log, route is Route.EngineAsyncTwin or Route.ForcedTwin),
        };

        switch (route)
        {
            case Route.EngineSync:
                return FromRunResult(KatLangEngine.Run(source, options), log);
            case Route.EngineAsync:
            case Route.EngineAsyncTwin:
                return FromRunResult(await KatLangEngine.RunAsync(source, options), log);
        }

        var parsed = Parser.Parse(source, options);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        var program = new Expr.AlgorithmExpr(parsed.Root);
        var (result, _) = route switch
        {
            Route.Generic => Evaluator.RunCountedObserved(program, limits: limits, enableOptimizations: false, hostOperations: options.HostOperations),
            Route.Optimized => Evaluator.RunCountedObserved(program, limits: limits, enableOptimizations: true, hostOperations: options.HostOperations),
            Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), limits: limits, hostOperations: options.HostOperations),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };

        return result.IsError
            ? new Observation("err", null, [KatLangError.FromEvalError(result.Error).Code.ToString()], [.. log.Calls])
            : new Observation("ok", Neutral(result.Value.Value), [], [.. log.Calls]);
    }

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", Neutral(success.Value), [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(static e => e.Code.ToString())], [.. log.Calls]),
        RunResult.ParseFailure failure => new("parse", null, [.. failure.Errors.Select(static e => e.Code.ToString())], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", null, [none.Diagnostic.Code.ToString()], [.. log.Calls]),
    };

    private static string Neutral(Result value) => value switch
    {
        Result.Atom atom => ValueTextRenderer.FormatNumberInvariant(atom.Value),
        Result.Str text => "'" + text.Value + "'",
        Result.Bool boolean => boolean.Value ? "true" : "false",
        Result.SequenceValue sequence => "S[" + string.Join(", ", sequence.Items.Select(Neutral)) + "]",
        Result.ListValue list => "L[" + string.Join(", ", list.Items.Select(Neutral)) + "]",
        // A run result never holds one (the run boundary refuses it).
        Result.CallReference => "CallReference",
    };

    /// <summary>Runs on every route, requires agreement with the synchronous engine (value, codes, exact host log), and returns the oracle.</summary>
    private static async Task<Observation> OnEveryRouteAsync(string source, EvaluationLimits? limits = null)
    {
        SourceProvenance.ParseValid(source);
        var oracle = await Task.Run(() => ObserveAsync(Route.EngineSync, source, limits));
        foreach (var route in Routes.Skip(1))
        {
            var observation = await Task.Run(() => ObserveAsync(route, source, limits));
            Assert.True(
                oracle.Kind == observation.Kind && oracle.Value == observation.Value
                    && oracle.Codes.SequenceEqual(observation.Codes) && oracle.HostCalls.SequenceEqual(observation.HostCalls),
                $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
        }

        return oracle;
    }

    private static void AssertValue(Observation observation, string value, params string[] hostCalls)
    {
        Assert.True(observation.Kind == "ok", $"expected success, got {observation}");
        Assert.Equal(value, observation.Value);
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    private static void AssertFails(Observation observation, KatLangErrorCode code, params string[] hostCalls)
    {
        Assert.True(observation.Kind == "err", $"expected an evaluation failure, got {observation}");
        Assert.Equal([code.ToString()], observation.Codes);
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    private const string Data = "Data = [10, 20, 30]\n";

    // ── (1) The receiver: once, through its ordinary value path ─────────────

    [Fact]
    public async Task AFreshInvocation_IsOneInvocationForEverySelectorRepetitionsIncluded()
        => AssertValue(await OnEveryRouteAsync("Data = [tick(), tick(), tick()]\nData()[2, 0, 2]"),
            "S[3, 1, 3]", "tick#1", "tick#2", "tick#3");

    [Fact]
    public async Task ACachedRead_IsEvaluatedOnceAcrossSelections()
        => AssertValue(await OnEveryRouteAsync("Data = [tick(), tick()]\nData[0], Data[1], Data[1, 0]"),
            "S[1, 2, S[2, 1]]", "tick#1", "tick#2");

    [Fact]
    public async Task AFreshInvocation_NeverReadsThePropertyCache_ButEstablishesAnEmptyEntry()
        // `Data()` runs afresh (tick 1) and, finding Data's entry empty, establishes it (CACHE-PUB-1);
        // the bare reads that follow reuse it; a later `Data()` runs afresh again (tick 2) and replaces
        // nothing. Formerly the first call populated nothing: S[1, 2, 2, 3] over three ticks.
        => AssertValue(await OnEveryRouteAsync("Data = [tick()]\nData()[0], Data[0], Data[0], Data()[0]"),
            "S[1, 1, 1, 2]", "tick#1", "tick#2");

    [Fact]
    public async Task AnEmptySelection_StillDemandsItsReceiver()
    {
        AssertValue(await OnEveryRouteAsync("Data = [trace(1)]\nData()[]"), "S[]", "trace(1)");
        AssertFails(await OnEveryRouteAsync("Bad = trace(1) / 0\nBad()[]"), KatLangErrorCode.DivisionByZero, "trace(1)");
        AssertFails(await OnEveryRouteAsync("Bad = trace(1) / 0\nBad[]"), KatLangErrorCode.DivisionByZero, "trace(1)");
    }

    [Fact]
    public async Task AReceiverFailure_WinsBeforeAnySelectorSpreadRuns()
        // Distinct categories and the host log: the receiver's division by zero, and the selector
        // spread (a kind failure after its own trace) never ran.
        => AssertFails(await OnEveryRouteAsync("Bad = trace(1) / 0\nBad[(trace(2) + true)*]"),
            KatLangErrorCode.DivisionByZero, "trace(1)");

    // ── (2) Supply formation: spreads first, ordinary selectors suspended ───

    [Fact]
    public async Task EverySpreadRuns_BeforeTheFirstOrdinarySelectorIsDemanded()
        // The ordinary selector `trace(0) + true` would fail with a kind error, but the later spread
        // fails first, during formation — and the ordinary selector was never demanded.
        => AssertFails(await OnEveryRouteAsync(Data + "Data[trace(0) + true, (trace(1) / 0)*]"),
            KatLangErrorCode.DivisionByZero, "trace(1)");

    [Fact]
    public async Task SpreadsRunInWrittenOrder_ThenOrdinarySelectorsInSupplyOrder()
        // Formation: trace(1) (first spread), then trace(0) (last spread); then demand: trace(2)
        // (the ordinary selector) at its supply position. Supply = [1, 0, 2, 0].
        => AssertValue(await OnEveryRouteAsync(Data + "Data[(trace(1), 0)*, trace(2), trace(0)*]"),
            "S[20, 10, 30, 10]", "trace(1)", "trace(0)", "trace(2)");

    [Fact]
    public async Task TheIssuePair_BadIndexStopsBeforeALaterOrdinarySelector_ButASpreadRunsDuringFormation()
    {
        AssertFails(await OnEveryRouteAsync("[10, 20][99, trace(1) / 0]"), KatLangErrorCode.BadIndex);
        AssertFails(await OnEveryRouteAsync("[10, 20][99, (trace(1) / 0)*]"), KatLangErrorCode.DivisionByZero, "trace(1)");
    }

    // ── (3) Left to right, each selector once, first failure stops ──────────

    [Fact]
    public async Task OrdinarySelectors_AreDemandedLeftToRight_EachOnce()
        => AssertValue(await OnEveryRouteAsync(Data + "Data[trace(2), trace(0), trace(2)]"),
            "S[30, 10, 30]", "trace(2)", "trace(0)", "trace(2)");

    [Fact]
    public async Task AfterAFailure_NoLaterOrdinarySelectorIsDemanded()
    {
        AssertFails(await OnEveryRouteAsync(Data + "Data[trace(5), trace(0)]"), KatLangErrorCode.BadIndex, "trace(5)");
        AssertFails(await OnEveryRouteAsync(Data + "Data[trace(0), trace(true), trace(1)]"),
            KatLangErrorCode.TypeMismatch, "trace(0)", "trace(true)");
        AssertFails(await OnEveryRouteAsync(Data + "Data[trace(1) / 0, trace(0)]"), KatLangErrorCode.DivisionByZero, "trace(1)");
    }

    [Fact]
    public async Task AParameterSelector_IsItsSuppliedCell_DemandedOnce()
        => AssertValue(await OnEveryRouteAsync(Data + "Pick(i) = Data[i, i]\nPick(trace(1))"),
            "S[20, 20]", "trace(1)");

    [Fact]
    public async Task ACollectorSlice_IsTransportedUnforced_AndDemandedLeftToRight()
    {
        const string pick = Data + "Pick(*is) = Data[is*]\n";
        AssertValue(await OnEveryRouteAsync(pick + "Pick(trace(2), trace(0))"), "S[30, 10]", "trace(2)", "trace(0)");
        AssertFails(await OnEveryRouteAsync(pick + "Pick(trace(9), trace(0))"), KatLangErrorCode.BadIndex, "trace(9)");
        AssertValue(await OnEveryRouteAsync(pick + "Pick()"), "S[]");
    }

    // ── Laziness: an unused selection is never demanded ─────────────────────

    [Fact]
    public async Task AnUnusedSelection_IsNeverDemanded()
    {
        AssertValue(await OnEveryRouteAsync("Data = [tick()]\nK(x) = 7\nK(Data()[trace(0)])"), "7");
        AssertValue(await OnEveryRouteAsync("Data = [tick()]\nif(false, Data()[trace(0)], 0)"), "0");
        AssertValue(await OnEveryRouteAsync("Data = [tick()]\nUnused = Data()[trace(0)]\n5"), "5");
    }

    // ── Normalization through every route ────────────────────────────────────

    [Fact]
    public async Task SelectedEmptyValues_StayElements_OnEveryRoute()
        => AssertValue(await OnEveryRouteAsync("Nested = [(10, 20), [30, 40], (), []]\nNested[trace(2), trace(3), trace(0)]"),
            "S[S[], L[], S[10, 20]]", "trace(2)", "trace(3)", "trace(0)");

    // ── Laws over a value in hand, never rewrites (C) ───────────────────────

    [Fact]
    public async Task FirstAndLast_AreLawsOverAValueInHand_NeverRewritesOfTheCall()
        // `last(x)` demands `x` once; the written `x[count(x) - 1]` demands it twice (the receiver,
        // then the selector's count). Neither form is rewritten into the other on any route.
        => AssertValue(
            await OnEveryRouteAsync(
                "BuildData = tick(), tick()\nlast(BuildData()), BuildData()[count(BuildData()) - 1], first(BuildData()), BuildData()[0]"),
            "S[2, 4, 7, 9]",
            "tick#1", "tick#2", "tick#3", "tick#4", "tick#5", "tick#6", "tick#7", "tick#8", "tick#9", "tick#10");

    // ── Budgets ──────────────────────────────────────────────────────────────

    [Fact]
    public async Task ALargeRepeatedSelection_IsChargedAgainstTheCollectionBudget()
    {
        // 30 supplied selectors select 30 values: the result reserves its stored slots like any
        // capture, so a collection bound below 30 is crossed by the selection result itself —
        // every collection the program writes holds at most 3 items — on every route.
        var source = "Data = [7]\nIs = [0, 0, 0]\nData[" + string.Join(", ", Enumerable.Repeat("Is*", 10)) + "]";
        var within = await OnEveryRouteAsync(source, new EvaluationLimits { MaxCollectionItems = 30 });
        Assert.Equal("ok", within.Kind);
        var crossed = await OnEveryRouteAsync(source, new EvaluationLimits { MaxCollectionItems = 29 });
        Assert.Equal("err", crossed.Kind);
        Assert.Equal([nameof(KatLangErrorCode.CollectionSizeLimitExceeded)], crossed.Codes);
    }

    [Fact]
    public void Cancellation_IsObservedBetweenSuppliedSelectors()
    {
        // A host operation in the FIRST selector requests cancellation; the selection's next
        // machine transition observes it before the second selector is demanded.
        using var cancellation = new CancellationTokenSource();
        var log = new HostLog();
        var options = new RunOptions
        {
            EvaluationCancellationToken = cancellation.Token,
            HostOperations = HostOperations.Create(
                HostOperation.Create("cancel", (_, _) => { cancellation.Cancel(); return new Result.Atom(0); }),
                HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x")),
        };
        const string source = Data + "Data[cancel(), trace(1)]";
        Assert.ThrowsAny<OperationCanceledException>(() => KatLangEngine.Run(source, options));
        Assert.Empty(log.Calls);
    }
}
