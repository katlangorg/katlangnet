using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using System.Numerics;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// SEC-F5 follow-up (F0474–F0479): an async entry point decides its deferred-region route
/// fact ONCE per call and hands it to the cache-pairing factory, the route rule and the fast
/// path's synchronous guard, and <see cref="KatLangEngine.RunAsync"/> observes the evaluation
/// token right after the front end.
///
/// <list type="bullet">
///   <item><b>A.</b> On an uncancelled run with no asynchronous component, every public
///   <c>RunAsync</c>/<c>RunFlatAsync</c> family reads a host-built graph exactly as often as
///   its synchronous counterpart reads an identical fresh root: the one deferred-region walk
///   replaces the synchronous guard's walk, and nothing else walks the tree.</item>
///   <item><b>B.</b> The same holds for the internal funnels, including the engine's
///   (factory, then <c>RunCountedWithTopLevelPropertyAsync</c>), with or without a fact
///   decided by the caller.</item>
///   <item><b>C.</b> A deferred-region root still takes the twin path; the synchronous entry
///   rejects it with the same message, and an internal caller pairing it with a
///   synchronous-only cache still fails loud with the cache-pairing message.</item>
///   <item><b>D.</b> Engine cancellation: a pre-cancelled evaluation token cancels the task with
///   that token and invokes no host operation; a front-end failure still wins over it.</item>
/// </list>
/// </summary>
public class AsyncRouteDecisionTests
{
    private const int MemberCount = 4096;

    private const string SynchronousDeferredRegionMessage =
        "The program contains conditional branches whose module dependencies load on demand " +
        "(deferred module regions), which a synchronous evaluation entry point cannot await. " +
        "Use RunAsync (or an async KatLangEngine entry point).";

    private const string DeferredRegionCachePairingMessage =
        "A program with deferred module regions (conditional branches whose module dependencies load " +
        "on demand) requires an async-capable zero-argument property result cache for the run; use an " +
        "async evaluation entry point that constructs one.";

    /// <summary>Counts every structural access a traversal can make.</summary>
    private sealed class AccessCountingList<T>(IReadOnlyList<T> items) : IReadOnlyList<T>
    {
        public int Accesses { get; private set; }

        public int Count
        {
            get { Accesses++; return items.Count; }
        }

        public T this[int index]
        {
            get { Accesses++; return items[index]; }
        }

        public IEnumerator<T> GetEnumerator()
        {
            Accesses++;
            return items.GetEnumerator();
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    /// <summary>A host-built root whose property collection is instrumented (a DAG: one shared output node).</summary>
    private static (Expr Root, AccessCountingList<Property> Members) CountedRoot()
    {
        var shared = new Expr.Num(7);
        var members = new AccessCountingList<Property>(Enumerable.Range(0, MemberCount)
            .Select(i => new Property($"P{i}", new Algorithm.User(null, [], [], [], [shared])))
            .ToArray());
        var root = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], members, [new Expr.Num(1)]));
        return (root, members);
    }

    private static HostOperations SynchronousOperations(Action onInvoke) =>
        HostOperations.Create(HostOperation.Create("Data", (_, _) =>
        {
            onInvoke();
            return new Result.Atom(1);
        }));

    private static HostOperations AsynchronousOperations(Action onInvoke) =>
        HostOperations.Create(HostOperation.CreateAsync("Data", (_, _) =>
        {
            onInvoke();
            return ValueTask.FromResult<Result>(new Result.Atom(1));
        }));

    private static async Task<Expr> DeferredRegionRoot()
    {
        var parsed = await Parser.ParseAsync(
            "F(0) = 1\nF(1) = {\n    open 'https://katlang.org/lazy/b.kat'\n    B\n}\nF(1)",
            new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("public B = 2") });
        Assert.False(parsed.HasErrors);
        var root = new Expr.AlgorithmExpr(parsed.Root);
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(root));
        return root;
    }

    /// <summary>Reads made by one action over a fresh counted root, and that action's outcome.</summary>
    private static int ReadsOf(Func<Expr, string> run, out string outcome)
    {
        var (root, members) = CountedRoot();
        outcome = run(root);
        return members.Accesses;
    }

    /// <summary>Same, for an action that must complete synchronously (the fast path runs inline).</summary>
    private static int ReadsOfInline<T>(Func<Expr, Task<T>> run, Func<T, string> neutral, out string outcome)
    {
        var (root, members) = CountedRoot();
        var task = run(root);
        Assert.True(task.IsCompletedSuccessfully, "no async component: the sync fast path completes inline");
        outcome = neutral(task.Result);
        return members.Accesses;
    }

    private static int ReadsOfInline<T>(Func<Expr, ValueTask<T>> run, Func<T, string> neutral, out string outcome)
    {
        var (root, members) = CountedRoot();
        var pending = run(root);
        Assert.True(pending.IsCompletedSuccessfully, "no async component: the sync fast path completes inline");
        outcome = neutral(pending.Result);
        return members.Accesses;
    }

    // ── A. Public entries read the graph exactly as often as the sync entries ─

    public static TheoryData<string> PublicEntries() =>
    [
        "RunAsync(limits, token)",
        "RunAsync(limits, seed, token)",
        "RunAsync(sync host operations)",
        "RunFlatAsync(limits, token)",
        "RunFlatAsync(limits, seed, token)",
        "RunFlatAsync(sync host operations)",
    ];

    [Theory]
    [MemberData(nameof(PublicEntries))]
    public void UncancelledPublicAsyncEntry_ReadsTheGraphAsOftenAsItsSynchronousCounterpart(string entry)
    {
        var token = CancellationToken.None;
        var operations = SynchronousOperations(() => { });
        Func<Expr, string> sync = entry switch
        {
            "RunAsync(limits, token)" => root => AsyncEvaluationHarness.NeutralOf(Evaluator.Run(root, limits: null, token)),
            "RunAsync(limits, seed, token)" => root => AsyncEvaluationHarness.NeutralOf(Evaluator.Run(root, limits: null, randomSeed: 42, token)),
            "RunAsync(sync host operations)" => root => AsyncEvaluationHarness.NeutralOf(Evaluator.Run(root, operations, null, null, token)),
            "RunFlatAsync(limits, token)" => root => AsyncEvaluationHarness.NeutralOfFlat(Evaluator.RunFlat(root, limits: null, token)),
            "RunFlatAsync(limits, seed, token)" => root => AsyncEvaluationHarness.NeutralOfFlat(Evaluator.RunFlat(root, limits: null, randomSeed: 42, token)),
            "RunFlatAsync(sync host operations)" => root => AsyncEvaluationHarness.NeutralOfFlat(Evaluator.RunFlat(root, operations, null, null, token)),
            _ => throw new ArgumentOutOfRangeException(nameof(entry)),
        };

        var syncReads = ReadsOf(sync, out var syncOutcome);
        int asyncReads;
        string asyncOutcome;
        if (entry.StartsWith("RunFlatAsync", StringComparison.Ordinal))
        {
            Func<Expr, Task<EvalResult<IReadOnlyList<Decimal128>>>> flat = entry switch
            {
                "RunFlatAsync(limits, token)" => root => Evaluator.RunFlatAsync(root, limits: null, token),
                "RunFlatAsync(limits, seed, token)" => root => Evaluator.RunFlatAsync(root, limits: null, randomSeed: 42, token),
                _ => root => Evaluator.RunFlatAsync(root, operations, null, null, token),
            };
            asyncReads = ReadsOfInline(flat, AsyncEvaluationHarness.NeutralOfFlat, out asyncOutcome);
        }
        else
        {
            Func<Expr, Task<EvalResult<Result>>> value = entry switch
            {
                "RunAsync(limits, token)" => root => Evaluator.RunAsync(root, limits: null, token),
                "RunAsync(limits, seed, token)" => root => Evaluator.RunAsync(root, limits: null, randomSeed: 42, token),
                _ => root => Evaluator.RunAsync(root, operations, null, null, token),
            };
            asyncReads = ReadsOfInline(value, AsyncEvaluationHarness.NeutralOf, out asyncOutcome);
        }

        Assert.True(syncReads > 0, "the instrument must observe the synchronous run");
        Assert.Equal(syncOutcome, asyncOutcome);
        Assert.Equal(syncReads, asyncReads);
    }

    // ── B. Internal funnels, the engine's included ──────────────────────────

    [Fact]
    public void EngineFunnel_FactoryThenTopLevelPropertyTwin_ReadsTheGraphAsOftenAsTheSynchronousFunnel()
    {
        const string topLevel = "DisplayDecimals";
        static string Neutral(EvalResult<Evaluator.CountedRootProgramResult> r)
            => r.IsError
                ? $"err {SemanticExplorerHarness.ErrorCategory(r.Error)}"
                : $"ok raw={SemanticExplorerHarness.Neutral(r.Value.Output.Value)}";

        var syncReads = ReadsOf(
            root => Neutral(Evaluator.RunCountedWithTopLevelProperty(
                root, topLevel, new RunScopedZeroArgPropertyResultCache())),
            out var syncOutcome);

        // Exactly the engine's sequence: decide once, pair the cache, route with the same fact.
        var engineReads = ReadsOfInline(
            root =>
            {
                var fact = Evaluator.DecideTreeRequiresAsyncEvaluation(root, hostOperations: null);
                Assert.False(fact);
                var cache = Evaluator.CreateRunScopedZeroArgPropertyResultCache(
                    root, hostOperations: null, observationSink: null, fact);
                Assert.IsType<RunScopedZeroArgPropertyResultCache>(cache);
                return Evaluator.RunCountedWithTopLevelPropertyAsync(
                    root, topLevel, cache, treeRequiresAsyncEvaluation: fact, cancellationToken: CancellationToken.None);
            },
            Neutral,
            out var engineOutcome);

        // An internal caller passing no fact: the route rule decides it once and the fast
        // path's guard reuses it.
        var undecidedReads = ReadsOfInline(
            root => Evaluator.RunCountedWithTopLevelPropertyAsync(
                root, topLevel, new RunScopedZeroArgPropertyResultCache()),
            Neutral,
            out var undecidedOutcome);

        Assert.True(syncReads > 0);
        Assert.Equal(syncOutcome, engineOutcome);
        Assert.Equal(syncOutcome, undecidedOutcome);
        Assert.Equal(syncReads, engineReads);
        Assert.Equal(syncReads, undecidedReads);
    }

    [Fact]
    public void OtherInternalFunnels_ReadTheGraphAsOftenAsTheirSynchronousCounterparts()
    {
        var countedReads = ReadsOf(
            root => AsyncEvaluationHarness.NeutralOf(Evaluator.RunCounted(root, new RunScopedZeroArgPropertyResultCache())),
            out var countedOutcome);
        var countedAsyncReads = ReadsOfInline(
            root => Evaluator.RunCountedAsync(root, new RunScopedZeroArgPropertyResultCache()),
            AsyncEvaluationHarness.NeutralOf,
            out var countedAsyncOutcome);

        var valueReads = ReadsOf(
            root => AsyncEvaluationHarness.NeutralOf(Evaluator.Run(root)),
            out var valueOutcome);
        var valueAsyncReads = ReadsOfInline(
            root => Evaluator.RunAsync(root, new RunScopedZeroArgPropertyResultCache()),
            AsyncEvaluationHarness.NeutralOf,
            out var valueAsyncOutcome);

        var observedReads = ReadsOf(
            root => AsyncEvaluationHarness.NeutralOf(Evaluator.RunCountedObserved(root).Result),
            out var observedOutcome);
        // No cache supplied: the observed twin builds one through the factory, deciding the fact once.
        var observedAsyncReads = ReadsOfInline(
            root => Evaluator.RunCountedObservedAsync(root),
            r => AsyncEvaluationHarness.NeutralOf(r.Result),
            out var observedAsyncOutcome);

        Assert.Equal(countedOutcome, countedAsyncOutcome);
        Assert.Equal(valueOutcome, valueAsyncOutcome);
        Assert.Equal(observedOutcome, observedAsyncOutcome);
        Assert.Equal(countedReads, countedAsyncReads);
        Assert.Equal(valueReads, valueAsyncReads);
        Assert.Equal(observedReads, observedAsyncReads);
    }

    [Fact]
    public void AsynchronousHostOperationConfiguration_DecidesNoTreeFact()
    {
        var (root, members) = CountedRoot();
        Assert.Null(Evaluator.DecideTreeRequiresAsyncEvaluation(root, AsynchronousOperations(() => { })));
        Assert.Equal(0, members.Accesses);

        Assert.IsType<RunScopedAsyncZeroArgPropertyResultCache>(
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(
                root, AsynchronousOperations(() => { }), observationSink: null, treeRequiresAsyncEvaluation: null));
        Assert.Equal(0, members.Accesses);
    }

    // ── C. Deferred-region roots keep their routes and rejections ───────────

    [Fact]
    public async Task DeferredRegionRoot_TakesTheTwinPath_AndTheSynchronousEntriesRejectItUnchanged()
    {
        var root = await DeferredRegionRoot();

        var syncRejection = Assert.Throws<InvalidOperationException>(() => Evaluator.Run(root));
        Assert.Equal(SynchronousDeferredRegionMessage, syncRejection.Message);
        var countedRejection = Assert.Throws<InvalidOperationException>(
            () => Evaluator.RunCountedWithTopLevelProperty(root, "DisplayDecimals", new RunScopedZeroArgPropertyResultCache()));
        Assert.Equal(SynchronousDeferredRegionMessage, countedRejection.Message);

        // Public entry: the once-decided fact pairs the async-capable cache, which routes to the twin path.
        var fact = Evaluator.DecideTreeRequiresAsyncEvaluation(root, hostOperations: null);
        Assert.True(fact);
        Assert.IsType<RunScopedAsyncZeroArgPropertyResultCache>(
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(root, hostOperations: null, observationSink: null, fact));
        var result = await Evaluator.RunAsync(root, limits: null, CancellationToken.None);
        Assert.Equal("ok raw=2", AsyncEvaluationHarness.NeutralOf(result));

        // Engine funnel, as KatLangEngine.RunAsync drives it.
        var engineResult = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedWithTopLevelPropertyAsync(
            root,
            "DisplayDecimals",
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(root, hostOperations: null, observationSink: null, fact),
            treeRequiresAsyncEvaluation: fact,
            cancellationToken: CancellationToken.None));
        Assert.True(engineResult.IsOk);
        Assert.Equal("2", SemanticExplorerHarness.Neutral(engineResult.Value.Output.Value));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task DeferredRegionRoot_WithASynchronousOnlyCache_StillFailsLoudWithTheCachePairingMessage(bool decided)
    {
        var root = await DeferredRegionRoot();
        bool? fact = decided ? Evaluator.DecideTreeRequiresAsyncEvaluation(root, hostOperations: null) : null;

        var rejection = await Assert.ThrowsAsync<InvalidOperationException>(async () =>
            await Evaluator.RunCountedWithTopLevelPropertyAsync(
                root,
                "DisplayDecimals",
                new RunScopedZeroArgPropertyResultCache(),
                treeRequiresAsyncEvaluation: fact,
                cancellationToken: CancellationToken.None));
        Assert.Equal(DeferredRegionCachePairingMessage, rejection.Message);
    }

    // ── D. Engine cancellation ──────────────────────────────────────────────

    public static TheoryData<bool> AsynchronousOperationFlags() => [false, true];

    [Theory]
    [MemberData(nameof(AsynchronousOperationFlags))]
    public async Task EngineRunAsync_PreCancelledEvaluationToken_CancelsWithThatToken_AndInvokesNoHostOperation(bool asynchronous)
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var invoked = 0;
        var operations = asynchronous
            ? AsynchronousOperations(() => invoked++)
            : SynchronousOperations(() => invoked++);

        var task = KatLangEngine.RunAsync(
            "Data + 1",
            new RunOptions { HostOperations = operations, EvaluationCancellationToken = cts.Token });

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => task);
        Assert.True(task.IsCanceled);
        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(0, invoked);
    }

    [Fact]
    public void EngineRun_PreCancelledEvaluationToken_ThrowsThatToken_AndInvokesNoHostOperation()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var invoked = 0;

        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => KatLangEngine.Run(
            "Data + 1",
            new RunOptions { HostOperations = SynchronousOperations(() => invoked++), EvaluationCancellationToken = cts.Token }));
        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(0, invoked);
    }

    [Fact]
    public async Task EngineRunAsync_FrontEndFailure_StillWinsOverACancelledEvaluationToken()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var options = new RunOptions { EvaluationCancellationToken = cts.Token };

        var task = KatLangEngine.RunAsync("2 +", options);
        Assert.True(task.IsCompletedSuccessfully);
        Assert.IsType<RunResult.ParseFailure>(await task);
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("2 +", options));
    }
}
