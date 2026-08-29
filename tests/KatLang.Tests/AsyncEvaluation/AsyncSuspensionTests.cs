namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Genuine-asynchrony semantics of the twin family: every property access suspends and
/// resumes (usually across threads), and the run must still produce exactly the
/// synchronous outcome for every construct family the twins mirror — calls, recursion,
/// loops, callbacks, deconstruction, dot-calls, spread/capture, clause families,
/// strings, and expression spines. Also pins deterministic mid-run suspension (the run
/// is observably incomplete while held, and completes correctly after release) and
/// concurrent sync/async runs over one shared parsed structure.
/// </summary>
public class AsyncSuspensionTests
{
    /// <summary>
    /// Construct-family programs, each with property accesses INSIDE the construct so
    /// suspension happens mid-construct, not merely at the top level.
    /// </summary>
    public static TheoryData<string, string> ConstructPrograms() => new()
    {
        { "nested-calls", "A = 10\nF(x) = G(x) + A\nG(y) = y * A\nF(2)" },
        { "recursion", "A = 1\nFib(0) = A - 1\nFib(1) = A\nFib(n) = Fib(n - 1) + Fib(n - 2)\nFib(10)" },
        { "repeat-loop", "Base = 2\nStep(n) = n * Base\nrepeat(Step, 8, 1)" },
        { "while-loop", "Limit = 5\nStep(n, acc) = (n + 1, acc + n, n < Limit)\nwhile(Step, 0, 0)" },
        { "map-callback", "Offset = 10\nF(x) = x + Offset\n[1, 2, 3].map(F)" },
        { "filter-callback", "Threshold = 2\nP(x) = x > Threshold\n[1, 2, 3, 4].filter(P)" },
        // The callback body touches `Zero` per step and the initial accumulator is an
        // expression whose spine resolves `Base` — both route through the property
        // cache seam. (A bare property name in a builtin ARGUMENT position resolves
        // through the argument funnel and deliberately bypasses the cache — the
        // documented builtin-argument reuse gap — so it would not exercise the seam.)
        { "reduce-callback", "Base = 100\nZero = 0\nR(el, acc) = acc + el + Zero\n[1, 2, 3].reduce(R, Base * 1)" },
        { "deconstruction", "Src = (1, (2, 3), 4)\nx, y, z = Src\ny" },
        { "structural-dot", "Lib = {public V = 41}\nLib.V + 1" },
        { "lexical-dot-fallback", "A = (1, 2, 3)\nA.count" },
        { "fluent-spread", "A = (1, 2, 3)\nTotal(*v) = v.sum\nA*.Total" },
        { "spread-capture", "A = (1, 2)\nB = (A*, A*)\nB.count" },
        { "clause-family", "F(0) = Zero\nF(n) = NonZero\nZero = 100\nNonZero = 200\nF(0), F(7)" },
        // Spine-shaped branch/condition arguments so the property resolutions happen
        // inside expression evaluation (cache seam), not in bare builtin-argument
        // position (argument funnel, which bypasses the cache by design).
        { "if-builtin", "Cond = 1\nT = 10\nE = 20\nif(Cond > 0, T * 1, E * 1)" },
        { "string-building", "Name = 'Kat'\nName + 'Lang'" },
        { "expression-spine", "A = 1\n(A + 1) * (A + 2) * (A + 3) - A" },
        { "range-pipeline", "N = 3\nrange(1, N + 0).sum" },
        { "index-projection", "S = ((1, 2), (3, 4))\nS:1" },
        { "zero-arg-cache-shape", "A = 1, 2\nA, A, A()" },
    };

    [Theory]
    [MemberData(nameof(ConstructPrograms))]
    public async Task SuspendingRun_ProducesTheSynchronousOutcome(string caseId, string source)
    {
        _ = caseId;
        var ast = AsyncEvaluationHarness.Ast(source);
        var sync = Evaluator.RunCounted(ast);

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var async = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        if (sync.IsOk)
            Assert.True(Result.ValueComparer.Equals(sync.Value.Value, async.Value.Value));

        // Every construct program touches at least one property, so the async seam was
        // genuinely exercised (each access suspended through the host-side yield).
        Assert.True(cache.AsyncAccesses > 0);
        Assert.Equal(0, cache.SyncAccesses);
        Assert.Equal(cache.AsyncAccesses, cache.ThreadHops.Count);
    }

    [Fact]
    public async Task HeldRun_IsObservablyIncomplete_AndCompletesCorrectlyAfterRelease()
    {
        // Deterministic suspension: the run is provably not complete while the seam
        // holds it, and resuming produces exactly the synchronous result — including
        // when the resumed continuation runs on a different thread than the starter.
        const string source = "A = 20\nB = A + 2\nA + B";
        var ast = AsyncEvaluationHarness.Ast(source);
        var sync = Evaluator.RunCounted(ast);

        var cache = new HoldingAsyncZeroArgPropertyResultCache(holdAtAccess: 1);
        var runTask = Evaluator.RunCountedAsync(ast, cache).AsTask();

        await AsyncEvaluationHarness.Complete(new ValueTask<object?>(WaitReached(cache)));
        Assert.False(runTask.IsCompleted);

        cache.Release();
        var async = await AsyncEvaluationHarness.Complete(new ValueTask<EvalResult<Evaluator.CountedResult>>(runTask));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
    }

    [Fact]
    public async Task SuspendedCacheMiss_EvaluatesPropertyExactlyOnce_AndDoesNotReplayOnHits()
    {
        const string source = "A = 21\nA + A + A";
        var ast = AsyncEvaluationHarness.Ast(source);
        var sync = Evaluator.RunCounted(ast);
        var cache = new CountingSuspendingAsyncZeroArgPropertyResultCache();

        var async = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        Assert.Equal(3, cache.AsyncAccesses);
        Assert.Equal(1, cache.AsyncEvaluations);
        Assert.Equal(0, cache.SyncAccesses);
    }

    [Fact]
    public async Task AwaitedHostException_PropagatesUnchanged_WithoutReplay_AndConservesDepth()
    {
        var expected = new InvalidOperationException("injected async host failure");
        var cache = new ThrowingAsyncZeroArgPropertyResultCache(expected);
        var runTask = Evaluator.RunCountedAsync(
            AsyncEvaluationHarness.Ast("A = 1\nA"), cache).AsTask();

        var thrown = await Assert.ThrowsAsync<InvalidOperationException>(() => runTask);

        Assert.Same(expected, thrown);
        Assert.True(runTask.IsFaulted);
        Assert.Equal(1, cache.AsyncAccesses);
        Assert.Equal(0, cache.AsyncEvaluations);
        Assert.Equal(0, cache.SyncAccesses);
        Assert.Equal(0, cache.ObservedBudget!.CurrentDepth);
    }

    [Fact]
    public async Task SuspendingAssignmentDeconstruction_BindsSharedGroupExactlyOnce()
    {
        const string source = "Src = 1, 2, 3\nx, y, z = Src\nx, y, z";
        var ast = AsyncEvaluationHarness.Ast(source);
        var sync = Evaluator.RunCounted(ast);
        var observations = new EvaluationObservations();

        var (async, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(
                ast,
                zeroArgPropertyResultCache: new SuspendingAsyncZeroArgPropertyResultCache(),
                observations: observations));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        Assert.Equal(1, observations.DeconstructionFullBindCount);
    }

    private static async Task<object?> WaitReached(HoldingAsyncZeroArgPropertyResultCache cache)
    {
        await cache.Reached;
        return null;
    }

    [Fact]
    public async Task SuspendingRun_BudgetIsConservedOnSuccess()
    {
        const string source = "A = 1\nF(x) = x + A\n[1, 2, 3].map(F)";
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var (result, budget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(
                AsyncEvaluationHarness.Ast(source), zeroArgPropertyResultCache: cache));

        Assert.True(result.IsOk);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.InRange(budget.PeakDepth, 1, budget.MaxDepth);
    }

    [Fact]
    public async Task ConcurrentSyncAndAsyncRuns_OverOneSharedParsedStructure_AllObserveTheBaseline()
    {
        // One parsed root, evaluated concurrently by synchronous lanes, twin-path lanes,
        // and genuinely-suspending lanes. Runs are isolated by construction (fresh
        // budget and caches per run), so every lane must observe the sequential
        // baseline. Test-side scheduling uses tasks; the evaluator itself never
        // schedules.
        const string source = "A = 7\nF(x) = x * A + 1\nG(0) = A\nG(n) = G(n - 1) + F(n)\nG(6)";
        var ast = AsyncEvaluationHarness.Ast(source);
        var baseline = AsyncEvaluationHarness.NeutralOf(Evaluator.RunCounted(ast));

        const int lanesPerKind = 8;
        var lanes = new List<Task<string>>();
        for (var i = 0; i < lanesPerKind; i++)
        {
            lanes.Add(Task.Run(() => AsyncEvaluationHarness.NeutralOf(Evaluator.RunCounted(ast))));
            lanes.Add(Task.Run(async () => AsyncEvaluationHarness.NeutralOf(
                await Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache()))));
            lanes.Add(Task.Run(async () => AsyncEvaluationHarness.NeutralOf(
                await Evaluator.RunCountedAsync(ast, new SuspendingAsyncZeroArgPropertyResultCache()))));
        }

        var outcomes = await AsyncEvaluationHarness.Complete(new ValueTask<string[]>(Task.WhenAll(lanes)));
        Assert.All(outcomes, outcome => Assert.Equal(baseline, outcome));
    }

    [Fact]
    public async Task SuspendingRun_ErrorOutcomes_MatchTheSynchronousErrors()
    {
        // Error equivalence under genuine suspension, including an error raised INSIDE
        // a suspended-and-resumed callback and a retained resource-limit binding.
        var cases = new[]
        {
            "A = 0\n1 / A",
            "A = 1\nF(x) = (x + A) / (x - x)\n[1].map(F)",
            "A = (1, 2)\nA.first(9)",
        };

        foreach (var source in cases)
        {
            var ast = AsyncEvaluationHarness.Ast(source);
            var sync = Evaluator.RunCounted(ast);
            Assert.True(sync.IsError);

            var async = await AsyncEvaluationHarness.Complete(
                Evaluator.RunCountedAsync(ast, new SuspendingAsyncZeroArgPropertyResultCache()));

            Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        }
    }

    [Fact]
    public async Task SuspendingRun_RetainedResourceLimitBindings_MatchTheSynchronousOutcome()
    {
        // A parameter's eager value evaluation failing on a resource limit is RETAINED
        // on the binding and the run continues — that retention must survive the async
        // twin path identically, and cancellation semantics must stay separate from it.
        const string source = "Deep(0) = 0\nDeep(n) = Deep(n - 1)\nUse(x) = 42\nUse(Deep(500))";
        var limits = new EvaluationLimits { MaxDepth = 16 };
        var ast = AsyncEvaluationHarness.Ast(source);

        var sync = Evaluator.RunCounted(ast, new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(), limits);
        var async = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, new SuspendingAsyncZeroArgPropertyResultCache(), limits));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
    }
}
