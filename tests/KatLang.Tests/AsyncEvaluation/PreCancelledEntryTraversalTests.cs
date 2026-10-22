using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using System.Numerics;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// SEC-F5: the public cancellation-capable async evaluator entry points observe an
/// already-cancelled token immediately after public argument validation — before the
/// cache-pairing factory and the route selection each scan the host-built tree.
///
/// <list type="bullet">
///   <item><b>A.</b> A pre-cancelled call reads no child of a host-built graph (an
///   instrumented property collection counts every access) and delivers the supplied
///   token through a Canceled task, on every public <c>RunAsync</c>/<c>RunFlatAsync</c>
///   family, with and without host operations.</item>
///   <item><b>B.</b> Null public arguments keep precedence over the cancelled token and
///   are still delivered through the returned task.</item>
///   <item><b>C.</b> Uncancelled calls are unchanged: the instrument is live (the scan
///   does read the graph), the result matches the synchronous evaluator, and the
///   no-host-component run still completes synchronously.</item>
/// </list>
/// </summary>
public class PreCancelledEntryTraversalTests
{
    private const int MemberCount = 4096;

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

    /// <summary>
    /// A host-built root whose property collection is instrumented; every member shares one
    /// output node, so the graph is a DAG rather than a tree.
    /// </summary>
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

    private static Expr ParsedWithData(string source)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = SynchronousOperations(() => { }) });
        Assert.False(parsed.HasErrors);
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static async Task AssertCanceledWithToken(Task task, CancellationToken token)
    {
        Assert.True(task.IsCanceled);
        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => task);
        Assert.Equal(token, thrown.CancellationToken);
    }

    public static TheoryData<string> PublicEntries() =>
    [
        "RunAsync(limits, token)",
        "RunAsync(limits, seed, token)",
        "RunAsync(sync host operations)",
        "RunAsync(async host operations)",
        "RunFlatAsync(limits, token)",
        "RunFlatAsync(limits, seed, token)",
        "RunFlatAsync(sync host operations)",
        "RunFlatAsync(async host operations)",
    ];

    private static Task Invoke(string entry, Expr root, Action onInvoke, CancellationToken token) => entry switch
    {
        "RunAsync(limits, token)" => Evaluator.RunAsync(root, limits: null, token),
        "RunAsync(limits, seed, token)" => Evaluator.RunAsync(root, limits: null, randomSeed: 42, token),
        "RunAsync(sync host operations)" => Evaluator.RunAsync(root, SynchronousOperations(onInvoke), null, null, token),
        "RunAsync(async host operations)" => Evaluator.RunAsync(root, AsynchronousOperations(onInvoke), null, null, token),
        "RunFlatAsync(limits, token)" => Evaluator.RunFlatAsync(root, limits: null, token),
        "RunFlatAsync(limits, seed, token)" => Evaluator.RunFlatAsync(root, limits: null, randomSeed: 42, token),
        "RunFlatAsync(sync host operations)" => Evaluator.RunFlatAsync(root, SynchronousOperations(onInvoke), null, null, token),
        "RunFlatAsync(async host operations)" => Evaluator.RunFlatAsync(root, AsynchronousOperations(onInvoke), null, null, token),
        _ => throw new ArgumentOutOfRangeException(nameof(entry)),
    };

    // ── A. A pre-cancelled call never touches the graph ─────────────────────

    [Theory]
    [MemberData(nameof(PublicEntries))]
    public async Task PreCancelledPublicEntry_ReadsNoGraphChild_AndCancelsWithTheSuppliedToken(string entry)
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var (root, members) = CountedRoot();
        var invoked = 0;

        var task = Invoke(entry, root, () => invoked++, cts.Token);

        await AssertCanceledWithToken(task, cts.Token);
        Assert.Equal(0, members.Accesses);
        Assert.Equal(0, invoked);
    }

    [Fact]
    public async Task PreCancelledHostOperationEntry_InvokesNoOperation_ForAProgramThatCallsIt()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var program = ParsedWithData("Data + 1");
        var invoked = 0;

        await AssertCanceledWithToken(
            Evaluator.RunAsync(program, SynchronousOperations(() => invoked++), null, null, cts.Token), cts.Token);
        await AssertCanceledWithToken(
            Evaluator.RunAsync(program, AsynchronousOperations(() => invoked++), null, null, cts.Token), cts.Token);
        await AssertCanceledWithToken(
            Evaluator.RunFlatAsync(program, AsynchronousOperations(() => invoked++), null, null, cts.Token), cts.Token);
        Assert.Equal(0, invoked);
    }

    // ── B. Argument validation keeps precedence ─────────────────────────────

    [Fact]
    public async Task NullArguments_KeepPrecedenceOverACancelledToken_DeliveredThroughTheTask()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var operations = SynchronousOperations(() => { });
        var program = new Expr.Num(0);

        Task[] tasks =
        [
            Evaluator.RunAsync(null!, limits: null, cts.Token),
            Evaluator.RunAsync(null!, limits: null, randomSeed: null, cts.Token),
            Evaluator.RunAsync(null!, operations, null, null, cts.Token),
            Evaluator.RunAsync(program, null!, null, null, cts.Token),
            Evaluator.RunFlatAsync(null!, limits: null, cts.Token),
            Evaluator.RunFlatAsync(null!, operations, null, null, cts.Token),
            Evaluator.RunFlatAsync(program, null!, null, null, cts.Token),
        ];

        foreach (var task in tasks)
        {
            Assert.True(task.IsFaulted);
            await Assert.ThrowsAsync<ArgumentNullException>(() => task);
        }
    }

    // ── C. Uncancelled calls are unchanged ──────────────────────────────────

    [Fact]
    public async Task UncancelledPublicEntry_StillScansTheGraph_AndMatchesTheSynchronousRun()
    {
        var (root, members) = CountedRoot();
        var expected = Evaluator.Run(root);
        Assert.True(expected.IsOk);
        Assert.True(members.Accesses > 0);

        var before = members.Accesses;
        var task = Evaluator.RunAsync(root, limits: null, CancellationToken.None);
        Assert.True(task.IsCompletedSuccessfully, "no async component: the sync fast path completes inline");
        var actual = await task;

        Assert.True(members.Accesses > before, "the instrument must observe the route scan");
        Assert.True(actual.IsOk);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(expected), AsyncEvaluationHarness.NeutralOf(actual));

        var flat = await Evaluator.RunFlatAsync(root, limits: null, CancellationToken.None);
        Assert.True(flat.IsOk);
        Assert.Equal([(Decimal128)1], flat.Value);
    }

    [Fact]
    public async Task UncancelledHostOperationEntries_KeepTheirRoutes()
    {
        var program = ParsedWithData("Data + 1");
        var invoked = 0;

        // Synchronous-only operations: the sync fast path, completing inline.
        var syncTask = Evaluator.RunAsync(program, SynchronousOperations(() => invoked++), null, null, CancellationToken.None);
        Assert.True(syncTask.IsCompletedSuccessfully);
        var syncResult = await syncTask;

        // Asynchronous operations: the twin path, same value.
        var asyncResult = await Evaluator.RunAsync(
            program, AsynchronousOperations(() => invoked++), null, null, CancellationToken.None);

        Assert.True(syncResult.IsOk);
        Assert.True(asyncResult.IsOk);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(syncResult), AsyncEvaluationHarness.NeutralOf(asyncResult));
        Assert.Equal(2, invoked);
    }

    [Fact]
    public async Task UncancelledDeferredRegionRoot_StillRunsOnTheTwinPath()
    {
        var parsed = await Parser.ParseAsync(
            "F(0) = 1\nF(1) = {\n    open 'https://katlang.org/lazy/b.kat'\n    B\n}\nF(1)",
            new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("public B = 2") });
        Assert.False(parsed.HasErrors);
        var lazyRoot = new Expr.AlgorithmExpr(parsed.Root);

        // The synchronous entry rejects it, so a successful async run proves the twin route.
        Assert.Throws<InvalidOperationException>(() => Evaluator.Run(lazyRoot));
        var result = await Evaluator.RunAsync(lazyRoot, limits: null, CancellationToken.None);
        Assert.True(result.IsOk);
        Assert.Equal("ok raw=2", AsyncEvaluationHarness.NeutralOf(result));
    }
}
