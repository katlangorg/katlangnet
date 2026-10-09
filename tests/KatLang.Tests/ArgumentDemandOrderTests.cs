using KatLang.Evaluation.Caching;
using static KatLang.Tests.SixRouteAgreement;

namespace KatLang.Tests;

/// <summary>
/// The order in which a callee DEMANDS its supplied argument computations (Model C, NEED-01..05;
/// constitution CALL-03, restated 2026-10-09). Every callee forms its supply the same way — only
/// arbitrary explicit spreads are evaluated at formation, and cardinality is checked before any
/// other demand — so what a callee owns is which suspended computations it demands, and when:
/// <list type="bullet">
/// <item>a collection builtin demands its collection first, then its value controls in parameter
/// order, and a failure ends the run before any later slot is demanded;</item>
/// <item>a Math or random wrapper demands its arguments in parameter order and requires each to be
/// a number before it demands the next (<c>CollectMathNativeArguments</c>);</item>
/// <item>a host operation demands every argument in parameter order before the host runs
/// (<c>CollectHostOperationArguments</c>).</item>
/// </list>
/// Each program runs on the six routes, which must agree exactly (value, every error's code,
/// message and span, host-call log); the expected outcome and host log are written by hand.
/// <c>pair(a, b)</c> is a two-parameter host operation that logs its arguments when it runs.
/// </summary>
public class ArgumentDemandOrderTests
{
    [Theory]
    [InlineData("take(trace([1, 2, 3]), trace(2))", "ok L[1, 2]", "trace(L[1, 2, 3]) | trace(2)")]
    [InlineData("contains(trace([1, 2]), trace(2))", "ok true", "trace(L[1, 2]) | trace(2)")]
    [InlineData("Add(x, y) = x + y\nreduce(trace([1, 2]), Add, trace(0))", "ok 3", "trace(L[1, 2]) | trace(0)")]
    [InlineData("contains(1 / 0, trace(2))", "err DivisionByZero", "")]
    // Formation comes first: the spread control is evaluated before the builtin demands its collection.
    [InlineData("take(trace([1, 2, 3]), trace(2)*)", "ok L[1, 2]", "trace(2) | trace(L[1, 2, 3])")]
    public async Task CollectionBuiltin_DemandsItsCollection_ThenItsControls(string source, string outcome, string hostCalls)
        => AssertOutcome(await OnEveryRouteAsync(source), outcome, hostCalls);

    [Theory]
    [InlineData("pow(trace('a'), trace(1))", "err TypeMismatch", "trace('a')")]
    [InlineData("pow(trace(2), trace('a'))", "err TypeMismatch", "trace(2) | trace('a')")]
    [InlineData("pow(trace(2), trace(3))", "ok 8", "trace(2) | trace(3)")]
    [InlineData("Math.Pow(trace('a'), trace(1))", "err TypeMismatch", "trace('a')")]
    [InlineData("randomInt(trace('a'), trace(1))", "err TypeMismatch", "trace('a')")]
    public async Task MathAndRandomWrappers_DemandAndCheckOneArgumentAtATime(string source, string outcome, string hostCalls)
        => AssertOutcome(await OnEveryRouteAsync(source), outcome, hostCalls);

    [Theory]
    [InlineData("pair(trace(1), trace(2))", "ok 1", "trace(1) | trace(2) | pair(1, 2)")]
    [InlineData("pair(trace(1), 1 / 0)", "err DivisionByZero", "trace(1)")]
    [InlineData("pair(1 / 0, trace(2))", "err DivisionByZero", "")]
    // The parameters are the caller's transported cells: pair demands F's b, then F's a.
    [InlineData("F(a, b) = pair(b, a)\nF(trace(1), trace(2))", "ok 2", "trace(2) | trace(1) | pair(2, 1)")]
    public async Task HostOperation_DemandsEveryArgumentInParameterOrder_BeforeItRuns(string source, string outcome, string hostCalls)
        => AssertOutcome(await OnEveryRouteAsync(source), outcome, hostCalls);

    /// <summary>
    /// Each value slot is demanded AND validated before the next is demanded, so the second
    /// argument's division by zero is reached only where the first argument passes its check.
    /// </summary>
    [Theory]
    [InlineData("pow('a', 1 / 0)", "err TypeMismatch", "")]
    [InlineData("randomInt('a', 1 / 0)", "err TypeMismatch", "")]
    [InlineData("take('a', 1 / 0)", "err DivisionByZero", "")]
    [InlineData("range('a', 1 / 0)", "err TypeMismatch", "")]
    [InlineData("if('a', 1 / 0, 2)", "err TypeMismatch", "")]
    [InlineData("range(trace('a'), trace(1))", "err TypeMismatch", "trace('a')")]
    [InlineData("repeat({x + 1}, trace('a'), trace(1))", "err TypeMismatch", "trace('a')")]
    public async Task EachValueSlot_IsValidatedBeforeTheNextIsDemanded(string source, string outcome, string hostCalls)
        => AssertOutcome(await OnEveryRouteAsync(source), outcome, hostCalls);

    private static void AssertOutcome(Observation observation, string outcome, string hostCalls)
    {
        string[] expectedCalls = hostCalls.Length == 0 ? [] : hostCalls.Split(" | ");
        if (outcome.StartsWith("ok ", StringComparison.Ordinal))
        {
            Assert.True(observation.Kind == "ok", $"expected {outcome}, got {observation}");
            Assert.Equal(outcome["ok ".Length..], observation.Value);
        }
        else
        {
            var code = outcome["err ".Length..];
            Assert.True(observation.Kind == "err", $"expected {outcome}, got {observation}");
            Assert.StartsWith(code + ":", Assert.Single(observation.Errors), StringComparison.Ordinal);
        }

        Assert.Equal(expectedCalls, observation.HostCalls);
    }

    /// <summary>
    /// Runs <paramref name="source"/> on the six routes with the logging host operations and
    /// requires every route to agree with the synchronous engine. Returns the oracle.
    /// </summary>
    private static async Task<Observation> OnEveryRouteAsync(string source)
    {
        var oracle = await ObserveAsync(Route.EngineSync, source);
        foreach (var route in Routes.Skip(1))
        {
            var observation = await ObserveAsync(route, source);
            Assert.True(oracle.AgreesWith(observation), $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
        }

        return oracle;
    }

    private sealed class HostLog
    {
        public List<string> Calls { get; } = [];

        public Result Trace(Result value)
        {
            lock (Calls)
                Calls.Add($"trace({Neutral(value)})");
            return value;
        }

        public Result Pair(Result first, Result second)
        {
            lock (Calls)
                Calls.Add($"pair({Neutral(first)}, {Neutral(second)})");
            return first;
        }
    }

    private static HostOperations OperationsFor(HostLog log, bool suspending)
        => suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x"),
                HostOperation.CreateAsync("pair", async (args, _) => { await Task.Yield(); return log.Pair(args[0], args[1]); }, "a", "b"))
            : HostOperations.Create(
                HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x"),
                HostOperation.Create("pair", (args, _) => log.Pair(args[0], args[1]), "a", "b"));

    private static async Task<Observation> ObserveAsync(Route route, string source)
    {
        var log = new HostLog();
        var options = new RunOptions
        {
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
            Route.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false, hostOperations: options.HostOperations),
            Route.Optimized => Evaluator.RunCountedObserved(program, enableOptimizations: true, hostOperations: options.HostOperations),
            Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: options.HostOperations),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };

        return result.IsError
            ? new Observation("err", null, [Describe(KatLangError.FromEvalError(result.Error))], [.. log.Calls])
            : new Observation("ok", Neutral(result.Value.Value), [], [.. log.Calls]);
    }

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", Neutral(success.Value), [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.ParseFailure failure => new("parse", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", null, [none.Diagnostic.Code.ToString()], [.. log.Calls]),
    };

    private static string Describe(KatLangError error) => $"{error.Code}: {error.Message} @ {error.Span}";
}
