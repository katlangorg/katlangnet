using System.Numerics;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// The established execution routes of a source program that LOADS modules, observed as one
/// comparable record (the module counterpart of <see cref="SixRouteAgreement"/>, whose synchronous
/// engine route cannot run a downloader: source loading is async-only). Routes: the async engine with
/// synchronous and with genuinely suspending host operations, the generic and the optimized evaluator
/// over the async front end's tree, and the forced async twin. A program with a deferred module region
/// (a load-bearing clause branch) runs on the asynchronous routes only — the synchronous evaluator
/// routes refuse such a tree by contract. <c>tick()</c> and <c>trace(x)</c> are host operations that
/// log every call; the module server counts fetches per URL.
/// </summary>
internal static class ModuleRouteAgreement
{
    internal enum Route { EngineAsync, EngineAsyncTwin, Generic, Optimized, ForcedTwin }

    internal static readonly Route[] Routes = Enum.GetValues<Route>();

    internal static readonly Route[] AsyncRoutes = [Route.EngineAsync, Route.EngineAsyncTwin, Route.ForcedTwin];

    /// <summary>A module server over fixed sources: unknown URLs fail like a missing file.</summary>
    internal sealed class Modules(params (string Url, string Source)[] modules)
    {
        private readonly Dictionary<string, string> _sources = modules.ToDictionary(m => m.Url, m => m.Source, StringComparer.Ordinal);

        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public ValueTask<string> Download(string url, CancellationToken _)
        {
            lock (Fetches)
                Fetches[url] = Fetches.GetValueOrDefault(url) + 1;
            return _sources.TryGetValue(url, out var source)
                ? ValueTask.FromResult(source)
                : throw new InvalidOperationException($"404: {url}");
        }

        public RunOptions Options(HostOperations? hostOperations = null, long? seed = null) => new()
        {
            DownloadCode = Download,
            AllowedHosts = ["mods.test"],
            HostOperations = hostOperations,
            RandomSeed = seed,
        };
    }

    private sealed class HostLog
    {
        private int _ticks;

        public List<string> Calls { get; } = [];

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
                Calls.Add($"trace({SixRouteAgreement.Neutral(value)})");
            return value;
        }
    }

    private static HostOperations OperationsFor(HostLog log, bool suspending)
        => suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return log.Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x"))
            : HostOperations.Create(
                HostOperation.Create("tick", (_, _) => log.Tick()),
                HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x"));

    /// <summary>One route's observation of <paramref name="source"/> over a fresh module server built by <paramref name="server"/>.</summary>
    internal static async Task<SixRouteAgreement.Observation> ObserveAsync(
        Route route, string source, Func<Modules> server, long? seed = 7)
    {
        var log = new HostLog();
        var modules = server();
        var options = modules.Options(OperationsFor(log, route is Route.EngineAsyncTwin or Route.ForcedTwin), seed);

        if (route is Route.EngineAsync or Route.EngineAsyncTwin)
            return FromRunResult(await KatLangEngine.RunAsync(source, options), log);

        var parsed = await Parser.ParseAsync(source, options);
        if (parsed.HasErrors)
        {
            return new SixRouteAgreement.Observation(
                "parse",
                null,
                [.. parsed.Diagnostics.Where(static d => d.Severity == DiagnosticSeverity.Error).Select(static d => Describe(KatLangError.FromDiagnostic(d)))],
                [.. log.Calls]);
        }

        var program = new Expr.AlgorithmExpr(parsed.Root);
        var (result, _) = route switch
        {
            Route.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false, hostOperations: options.HostOperations, randomSeed: seed),
            Route.Optimized => Evaluator.RunCountedObserved(program, enableOptimizations: true, hostOperations: options.HostOperations, randomSeed: seed),
            Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: options.HostOperations,
                randomSeed: seed),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };

        return result.IsError
            ? new SixRouteAgreement.Observation("err", null, [Describe(KatLangError.FromEvalError(result.Error))], [.. log.Calls])
            : new SixRouteAgreement.Observation("ok", SixRouteAgreement.Neutral(result.Value.Value), [], [.. log.Calls]);
    }

    /// <summary>
    /// Runs <paramref name="source"/> on every route in <paramref name="routes"/> (all by default) and
    /// requires each to agree with the async engine — outcome, value, every error's code, message and
    /// position, and the exact host-call log. Returns the oracle.
    /// </summary>
    internal static async Task<SixRouteAgreement.Observation> OnEveryRouteAsync(
        string source, Func<Modules> server, Route[]? routes = null, long? seed = 7)
    {
        routes ??= Routes;
        var oracle = await ObserveAsync(routes[0], source, server, seed);
        foreach (var route in routes.Skip(1))
        {
            var observation = await ObserveAsync(route, source, server, seed);
            Assert.True(oracle.AgreesWith(observation), $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
        }

        return oracle;
    }

    private static SixRouteAgreement.Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", SixRouteAgreement.Neutral(success.Value), [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.ParseFailure failure => new("parse", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", null, [none.Diagnostic.Code.ToString()], [.. log.Calls]),
    };

    private static string Describe(KatLangError error) => $"{error.Code}: {error.Message} @ {error.Span}";
}
