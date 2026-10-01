using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// The six established execution routes of a source program — the sync and async engines, the
/// engine's genuinely suspending async twin, the generic and the optimized evaluator, and the forced
/// async twin — observed as one comparable record, for the suites that pin a behavior on every route
/// (<see cref="SiblingDependencyCycleTests"/>, <see cref="InferredParameterOutputValidationTests"/>,
/// <see cref="BuiltinArityRenderingParityTests"/>). A source the front end rejects is observed on
/// every route as its front-end errors: the engines' <see cref="RunResult.ParseFailure"/>, and the
/// parse result the evaluator routes would otherwise evaluate. <c>tick()</c> and <c>trace(x)</c>
/// are host operations that log every call (suspending on the twin routes), so the host-call log is
/// part of every observation.
/// </summary>
internal static class SixRouteAgreement
{
    internal enum Route
    {
        /// <summary>The oracle: <see cref="KatLangEngine.Run"/>.</summary>
        EngineSync,

        /// <summary><see cref="KatLangEngine.RunAsync"/> with synchronous host operations.</summary>
        EngineAsync,

        /// <summary><see cref="KatLangEngine.RunAsync"/> with genuinely suspending host operations: the async twin.</summary>
        EngineAsyncTwin,

        /// <summary>The generic evaluator (optimizations disabled).</summary>
        Generic,

        /// <summary>The optimized evaluator (loop planning and sequence fusion enabled).</summary>
        Optimized,

        /// <summary>The async twin forced by an async-capable property cache, with suspending host operations.</summary>
        ForcedTwin,
    }

    internal static readonly Route[] Routes = Enum.GetValues<Route>();

    /// <summary>
    /// One route's outcome: <see cref="Kind"/> is <c>ok</c>, <c>err</c> (evaluation failure),
    /// <c>parse</c> (front-end failure) or <c>none</c>; <see cref="Errors"/> renders every error as
    /// <c>Code: message @ span</c>.
    /// </summary>
    internal sealed record Observation(string Kind, string? Value, IReadOnlyList<string> Errors, IReadOnlyList<string> HostCalls)
    {
        public bool AgreesWith(Observation other)
            => Kind == other.Kind
                && Value == other.Value
                && Errors.SequenceEqual(other.Errors)
                && HostCalls.SequenceEqual(other.HostCalls);

        public override string ToString()
            => $"{Kind} {Value} errors=[{string.Join(" | ", Errors)}] host=[{string.Join(",", HostCalls)}]";
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
                Calls.Add($"trace({Neutral(value)})");
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

    internal static async Task<Observation> ObserveAsync(Route route, string source)
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
        if (parsed.HasErrors)
        {
            return new Observation(
                "parse",
                null,
                [.. parsed.Diagnostics.Where(static d => d.Severity == DiagnosticSeverity.Error).Select(static d => Describe(KatLangError.FromDiagnostic(d)))],
                [.. log.Calls]);
        }

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

    /// <summary>
    /// Runs <paramref name="source"/> on every route and requires each to agree with the synchronous
    /// engine — outcome kind, value, every error's code, message and position, and the exact host-call
    /// log. Returns the oracle.
    /// </summary>
    internal static async Task<Observation> OnEveryRouteAsync(string source)
    {
        var oracle = await ObserveAsync(Route.EngineSync, source);
        foreach (var route in Routes.Skip(1))
        {
            var observation = await ObserveAsync(route, source);
            Assert.True(oracle.AgreesWith(observation), $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
        }

        return oracle;
    }

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", Neutral(success.Value), [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.ParseFailure failure => new("parse", null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", null, [none.Diagnostic.Code.ToString()], [.. log.Calls]),
    };

    private static string Describe(KatLangError error) => $"{error.Code}: {error.Message} @ {error.Span}";

    internal static string Neutral(Result value) => value switch
    {
        Result.Atom atom => ValueTextRenderer.FormatNumberInvariant(atom.Value),
        Result.Str text => "'" + text.Value + "'",
        Result.Bool boolean => boolean.Value ? "true" : "false",
        Result.SequenceValue sequence => "S[" + string.Join(", ", sequence.Items.Select(Neutral)) + "]",
        Result.ListValue list => "L[" + string.Join(", ", list.Items.Select(Neutral)) + "]",
    };
}
