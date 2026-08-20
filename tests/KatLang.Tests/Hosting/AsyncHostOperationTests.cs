using System.Numerics;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests.Hosting;

/// <summary>
/// Asynchronous host operations through the PUBLIC surface: genuine suspension and
/// resumption (deterministically gated, never timing-based), exactly-once invocation
/// across suspension, cancellation while suspended, host exception and faulted-awaitable
/// identity, fast-path routing for synchronous configurations, concurrency isolation,
/// and shared-parsed-tree reuse across host configurations.
/// </summary>
public class AsyncHostOperationTests
{
    private static readonly TimeSpan Timeout = TimeSpan.FromSeconds(45);

    private static Result Atom(Decimal128 value) => new Result.Atom(value);

    /// <summary>Bounded await so a wedged run fails the test instead of hanging the suite.</summary>
    private static async Task<T> Complete<T>(Task<T> task)
    {
        var completed = await Task.WhenAny(task, Task.Delay(Timeout));
        Assert.Same(task, completed);
        return await task;
    }

    private static async Task Reached(Task reached)
    {
        var completed = await Task.WhenAny(reached, Task.Delay(Timeout));
        Assert.Same(reached, completed);
    }

    /// <summary>
    /// Deterministic suspension gate: the operation reports when evaluation has
    /// genuinely reached it (and is therefore suspended awaiting the gate), counts its
    /// invocations, and completes only when the test releases it.
    /// </summary>
    private sealed class HeldOperation
    {
        private readonly TaskCompletionSource<Result> _gate = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private readonly TaskCompletionSource _reached = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private int _invocations;

        public int Invocations => Volatile.Read(ref _invocations);

        public Task ReachedTask => _reached.Task;

        public CancellationToken ObservedToken { get; private set; }

        public IReadOnlyList<Result>? ObservedArguments { get; private set; }

        public void Release(Result value) => _gate.TrySetResult(value);

        public void Fail(Exception exception) => _gate.TrySetException(exception);

        public async ValueTask<Result> InvokeAsync(IReadOnlyList<Result> args, CancellationToken cancellationToken)
        {
            Interlocked.Increment(ref _invocations);
            ObservedToken = cancellationToken;
            ObservedArguments = args;
            _reached.TrySetResult();
            return await _gate.Task;
        }
    }

    /// <summary>
    /// A deterministic sequence of independent suspension points. Evaluation is
    /// sequential, so invocation N cannot finish until the test releases gate N.
    /// </summary>
    private sealed class HeldOperationSequence(int count)
    {
        private readonly TaskCompletionSource<Result>[] _gates = Enumerable.Range(0, count)
            .Select(_ => new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously))
            .ToArray();
        private readonly TaskCompletionSource[] _reached = Enumerable.Range(0, count)
            .Select(_ => new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously))
            .ToArray();
        private int _invocations;

        public int Invocations => Volatile.Read(ref _invocations);

        public Task ReachedTask(int index) => _reached[index].Task;

        public void Release(int index, Result value) => _gates[index].TrySetResult(value);

        public async ValueTask<Result> InvokeAsync(
            IReadOnlyList<Result> args,
            CancellationToken cancellationToken)
        {
            var index = Interlocked.Increment(ref _invocations) - 1;
            if ((uint)index >= (uint)_gates.Length)
                throw new InvalidOperationException("The held operation received more invocations than configured.");

            _reached[index].TrySetResult();
            return await _gates[index].Task;
        }
    }

    // ── Routing ─────────────────────────────────────────────────────────────

    [Fact]
    public async Task EngineRunAsync_SynchronousOperationsOnly_KeepsTheSynchronousFastPath()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => Atom(21))),
        };

        var task = KatLangEngine.RunAsync("Data * 2", options);

        // Nothing in a synchronous-operation configuration can suspend, so the fast
        // path runs the synchronous pipeline inline and the task is already complete.
        Assert.True(task.IsCompletedSuccessfully);
        Assert.Equal("42", Assert.IsType<RunResult.Success>(await task).ToDisplayString());
    }

    [Fact]
    public async Task EvaluatorRunAsync_HostOperationOverload_SyncConfigurationCompletesSynchronously()
    {
        var operations = HostOperations.Create(HostOperation.Create("Data", (_, _) => Atom(21)));
        var parsed = Parser.Parse("Data * 2", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);

        var task = Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root), operations, null, CancellationToken.None);
        Assert.True(task.IsCompletedSuccessfully);
        var result = await task;
        Assert.True(result.IsOk);
        Assert.Equal(42m, ((Result.Atom)result.Value).Value);
    }

    [Fact]
    public async Task InternalAsyncEntry_AsyncOperationsWithSyncOnlyCache_FailLoud()
    {
        var operations = HostOperations.Create(
            HostOperation.CreateAsync("Data", (_, _) => ValueTask.FromResult(Atom(1))));
        var parsed = Parser.Parse("Data", new RunOptions { HostOperations = operations });
        var ast = new Expr.AlgorithmExpr(parsed.Root);

        // Routing enforcement, not documentation: an internal caller cannot select the
        // twin path through async host operations while supplying a sync-only cache.
        await Assert.ThrowsAsync<InvalidOperationException>(async () => await Evaluator.RunCountedAsync(
            ast,
            new RunScopedZeroArgPropertyResultCache(),
            hostOperations: operations));
    }

    // ── Genuine suspension and resumption ───────────────────────────────────

    [Fact]
    public async Task EngineRunAsync_IncompleteHostAwaitable_SuspendsThenResumesWithTheValue()
    {
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Answer = Data + 1\nAnswer", options);

        await Reached(held.ReachedTask);
        Assert.False(task.IsCompleted);

        held.Release(Atom(41));
        var result = Assert.IsType<RunResult.Success>(await Complete(task));
        Assert.Equal("42", result.ToDisplayString());
        Assert.Equal(1, held.Invocations);
    }

    [Fact]
    public async Task SuspensionAtNestedEvaluationDepth_ResumesAtTheSamePoint()
    {
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("G(x) = Data * x\nF(x) = G(x) + 1\nF(3)", options);

        await Reached(held.ReachedTask);
        Assert.False(task.IsCompleted);

        held.Release(Atom(14));
        var result = Assert.IsType<RunResult.Success>(await Complete(task));
        Assert.Equal("43", result.ToDisplayString());
        Assert.Equal(1, held.Invocations);
    }

    [Fact]
    public async Task NestedAsyncOperations_SuspendInEvaluationOrder_WithoutReplay()
    {
        var inner = new HeldOperation();
        var outer = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Inner", inner.InvokeAsync),
                HostOperation.CreateAsync("Outer", outer.InvokeAsync, "value")),
        };

        var task = KatLangEngine.RunAsync("Outer(Inner())", options);

        await Reached(inner.ReachedTask);
        Assert.False(task.IsCompleted);
        Assert.False(outer.ReachedTask.IsCompleted);

        inner.Release(Atom(41));
        await Reached(outer.ReachedTask);
        Assert.False(task.IsCompleted);
        Assert.Equal(41m, ((Result.Atom)Assert.Single(outer.ObservedArguments!)).Value);

        outer.Release(Atom(42));
        Assert.Equal("42", Assert.IsType<RunResult.Success>(await Complete(task)).ToDisplayString());
        Assert.Equal(1, inner.Invocations);
        Assert.Equal(1, outer.Invocations);
    }

    [Fact]
    public async Task SuspendedOperation_DoesNotReevaluateItsArgument()
    {
        var argumentInvocations = 0;
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("MakeArgument", (_, _) =>
                {
                    Interlocked.Increment(ref argumentInvocations);
                    return Atom(41);
                }),
                HostOperation.CreateAsync("Fetch", held.InvokeAsync, "value")),
        };

        var task = KatLangEngine.RunAsync("Fetch(MakeArgument())", options);
        await Reached(held.ReachedTask);

        Assert.Equal(1, argumentInvocations);
        Assert.Equal(41m, ((Result.Atom)Assert.Single(held.ObservedArguments!)).Value);

        held.Release(Atom(42));
        Assert.Equal("42", Assert.IsType<RunResult.Success>(await Complete(task)).ToDisplayString());
        Assert.Equal(1, argumentInvocations);
        Assert.Equal(1, held.Invocations);
    }

    [Fact]
    public async Task SuspendedRun_IsInvokedExactlyOnce_NeverReplayed()
    {
        // A row evaluated BEFORE the suspension records its evaluation count; replay
        // after resumption would bump it. The held operation itself must also stay at
        // one invocation.
        var preludeInvocations = 0;
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Before", (_, _) =>
                {
                    Interlocked.Increment(ref preludeInvocations);
                    return Atom(100);
                }),
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Before() + Data", options);

        await Reached(held.ReachedTask);
        held.Release(Atom(11));

        var result = Assert.IsType<RunResult.Success>(await Complete(task));
        Assert.Equal("111", result.ToDisplayString());
        Assert.Equal(1, held.Invocations);
        Assert.Equal(1, preludeInvocations);
    }

    [Fact]
    public async Task AsyncOperationInsideMapCallback_SuspendsPerElement_ExactlyOncePerElement()
    {
        var held = new HeldOperationSequence(3);
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Enrich", held.InvokeAsync, "x")),
        };

        var task = KatLangEngine.RunAsync("Step(x) = Enrich(x)\n[1, 2, 3].map(Step)", options);
        for (var i = 0; i < 3; i++)
        {
            await Reached(held.ReachedTask(i));
            Assert.False(task.IsCompleted);
            held.Release(i, Atom((i + 1) * 10));
        }

        var result = Assert.IsType<RunResult.Success>(await Complete(task));
        Assert.Equal("[10, 20, 30]", result.ToDisplayString());
        Assert.Equal(3, held.Invocations);
    }

    [Fact]
    public async Task DirectFlatCallbackReference_InheritsTheMathMemberLimitation_Identically()
    {
        // A host operation referenced DIRECTLY as a flat map callback fails exactly
        // like an opened Math member does today ("open Math" + map(Abs)): the flat
        // callback funnel binds parameters into the counted environment, which a
        // native-call wrapper body does not read. Host operations deliberately
        // inherit Math-member behavior; wrap the operation in a user property
        // (Step(x) = Enrich(x)) for callback positions. If this limitation is ever
        // lifted, it must be lifted for Math members and host operations together.
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync(
                    "Enrich",
                    (args, _) => ValueTask.FromResult(Atom(((Result.Atom)args[0]).Value * 10)),
                    "x")),
        };

        var hostFailure = Assert.IsType<RunResult.EvalFailure>(
            await Complete(KatLangEngine.RunAsync("[1, 2, 3].map(Enrich)", options)));
        var mathFailure = Assert.IsType<RunResult.EvalFailure>(
            KatLangEngine.Run("open Math\n[1, 2, 3].map(Abs)"));

        Assert.Contains("Unknown name: x", hostFailure.Errors[0].Message, StringComparison.Ordinal);
        Assert.Contains("Unknown name: x", mathFailure.Errors[0].Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task PropertyStyleAccess_AsyncOperation_NoDuplicateHostWorkOnCacheHit()
    {
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Data\nData", options);
        await Reached(held.ReachedTask);
        Assert.False(task.IsCompleted);
        held.Release(Atom(42));

        var result = Assert.IsType<RunResult.Success>(await Complete(task));
        Assert.Equal($"42{Environment.NewLine}42", result.ToDisplayString());
        Assert.Equal(1, held.Invocations);
    }

    [Fact]
    public async Task ExplicitZeroArgCalls_AsyncOperation_BypassThePropertyCache()
    {
        var held = new HeldOperationSequence(2);
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Data()\nData()", options);
        for (var i = 0; i < 2; i++)
        {
            await Reached(held.ReachedTask(i));
            Assert.False(task.IsCompleted);
            held.Release(i, Atom(42));
        }

        var result = Assert.IsType<RunResult.Success>(await Complete(task));
        Assert.Equal($"42{Environment.NewLine}42", result.ToDisplayString());
        Assert.Equal(2, held.Invocations);
    }

    [Fact]
    public async Task ThreadHoppingResumption_ProducesTheSameResult()
    {
        var before = -1;
        var after = -1;
        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", async (_, _) =>
                {
                    before = Environment.CurrentManagedThreadId;
                    reached.TrySetResult();
                    var value = await gate.Task;
                    after = Environment.CurrentManagedThreadId;
                    return value;
                })),
        };

        var task = KatLangEngine.RunAsync("Data + 1", options);
        await Reached(reached.Task);
        Assert.False(task.IsCompleted);
        gate.TrySetResult(Atom(41));

        var result = Assert.IsType<RunResult.Success>(await Complete(task));
        Assert.Equal("42", result.ToDisplayString());
        // RunContinuationsAsynchronously permits a thread hop without requiring one;
        // only pin that both sides of the deterministic suspension executed.
        Assert.NotEqual(-1, before);
        Assert.NotEqual(-1, after);
    }

    // ── Cancellation ────────────────────────────────────────────────────────

    [Fact]
    public async Task OperationReceivesTheEvaluationToken_ByIdentity()
    {
        using var cts = new CancellationTokenSource();
        var held = new HeldOperation();
        var options = new RunOptions
        {
            EvaluationCancellationToken = cts.Token,
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Data", options);
        await Reached(held.ReachedTask);
        Assert.Equal(cts.Token, held.ObservedToken);

        held.Release(Atom(1));
        await Complete(task);
    }

    [Fact]
    public async Task CancelledWhileSuspended_RunBecomesCanceled_WithTokenIdentity_EvenIfHostCompletesNormally()
    {
        using var cts = new CancellationTokenSource();
        var held = new HeldOperation();
        var options = new RunOptions
        {
            EvaluationCancellationToken = cts.Token,
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Data + 1", options);
        await Reached(held.ReachedTask);
        Assert.False(task.IsCompleted);

        // Cancel while genuinely suspended; the host then completes normally. The
        // evaluator observes the token when evaluation resumes: the run is cancelled,
        // never continued, and never converted into a KatLang diagnostic.
        cts.Cancel();
        held.Release(Atom(41));

        var observed = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Complete(task));
        Assert.Equal(cts.Token, observed.CancellationToken);
        Assert.True(task.IsCanceled);
    }

    [Fact]
    public async Task HostSideCancellation_UsingTheSuppliedToken_FollowsTheSameContract()
    {
        using var cts = new CancellationTokenSource();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var options = new RunOptions
        {
            EvaluationCancellationToken = cts.Token,
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", async (_, cancellationToken) =>
                {
                    reached.TrySetResult();
                    // Honor cancellation the way a real IO-bound host would.
                    await Task.Delay(System.Threading.Timeout.InfiniteTimeSpan, cancellationToken);
                    return Atom(0);
                })),
        };

        var task = KatLangEngine.RunAsync("Data", options);
        await Reached(reached.Task);
        Assert.False(task.IsCompleted);

        cts.Cancel();

        var observed = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Complete(task));
        Assert.Equal(cts.Token, observed.CancellationToken);
        Assert.True(task.IsCanceled);
    }

    [Fact]
    public async Task DepthConservation_AfterHostFaultAtNestedDepth()
    {
        // The pass-through async cache records the run's budget (its RunIdentity) at
        // the property access that leads into the faulting host operation, so the
        // budget stays observable after the exceptional unwind discards the result.
        var exception = new InvalidDataException("host fault at depth");
        var held = new HeldOperation();
        var operations = HostOperations.Create(
            HostOperation.CreateAsync("Data", held.InvokeAsync));
        var parsed = Parser.Parse("G(x) = Data * x\nF(x) = G(x) + 1\nF(3)", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);

        var cache = new AsyncEvaluation.PassThroughAsyncZeroArgPropertyResultCache();
        var pending = Evaluator.RunCountedObservedAsync(
            new Expr.AlgorithmExpr(parsed.Root), zeroArgPropertyResultCache: cache, hostOperations: operations);
        await Reached(held.ReachedTask);
        held.Fail(exception);
        var observed = await Assert.ThrowsAsync<InvalidDataException>(async () => await pending);
        Assert.Same(exception, observed);

        // Every admitted depth level unwound through its finally: no leak (non-zero
        // residue) and no double release (the fail-loud ExitInvocation would have
        // replaced the host exception with an InvalidOperationException).
        Assert.NotNull(cache.ObservedBudget);
        Assert.Equal(0, cache.ObservedBudget!.CurrentDepth);
    }

    // ── Host exceptions and faulted awaitables ──────────────────────────────

    [Fact]
    public async Task AsyncDelegateThrowingBeforeReturningAwaitable_PropagatesByIdentity()
    {
        var exception = new InvalidDataException("host database offline");
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", (_, _) => throw exception)),
        };

        var observed = await Assert.ThrowsAsync<InvalidDataException>(
            () => Complete(KatLangEngine.RunAsync("Data + 1", options)));
        Assert.Same(exception, observed);
    }

    [Fact]
    public async Task FaultedAwaitable_PropagatesTheOriginalException()
    {
        var exception = new InvalidDataException("pre-faulted awaitable");
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync(
                    "Data",
                    (_, _) => new ValueTask<Result>(Task.FromException<Result>(exception)))),
        };

        var observed = await Assert.ThrowsAsync<InvalidDataException>(
            () => Complete(KatLangEngine.RunAsync("Data + 1", options)));
        Assert.Same(exception, observed);
    }

    [Fact]
    public async Task HeldHostFault_AfterGenuineSuspension_PropagatesByIdentity()
    {
        var exception = new InvalidDataException("failure after suspension");
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Data + 1", options);
        await Reached(held.ReachedTask);
        held.Fail(exception);

        var observed = await Assert.ThrowsAsync<InvalidDataException>(() => Complete(task));
        Assert.Same(exception, observed);
        Assert.Equal(1, held.Invocations);
    }

    [Fact]
    public async Task NullReturningAsyncOperation_IsAHostContractViolation()
    {
        var held = new HeldOperation();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var task = KatLangEngine.RunAsync("Data", options);
        await Reached(held.ReachedTask);
        held.Release(null!);
        var observed = await Assert.ThrowsAsync<InvalidOperationException>(
            () => Complete(task));
        Assert.Contains("returned null", observed.Message, StringComparison.Ordinal);
    }

    // ── Concurrency and isolation ───────────────────────────────────────────

    [Fact]
    public async Task ConcurrentIndependentRuns_SuspendIndependently_NoCrossTalk()
    {
        var heldA = new HeldOperation();
        var heldB = new HeldOperation();
        var optionsA = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("Data", heldA.InvokeAsync)),
        };
        var optionsB = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("Data", heldB.InvokeAsync)),
        };

        var taskA = KatLangEngine.RunAsync("Data + 1", optionsA);
        var taskB = KatLangEngine.RunAsync("Data + 2", optionsB);

        await Reached(heldA.ReachedTask);
        await Reached(heldB.ReachedTask);
        Assert.False(taskA.IsCompleted);
        Assert.False(taskB.IsCompleted);

        // Release in reverse start order; each run resumes with its own value.
        heldB.Release(Atom(200));
        Assert.Equal("202", Assert.IsType<RunResult.Success>(await Complete(taskB)).ToDisplayString());
        Assert.False(taskA.IsCompleted);

        heldA.Release(Atom(100));
        Assert.Equal("101", Assert.IsType<RunResult.Success>(await Complete(taskA)).ToDisplayString());

        Assert.Equal(1, heldA.Invocations);
        Assert.Equal(1, heldB.Invocations);
    }

    [Fact]
    public async Task OneSharedConfiguration_AcrossConcurrentRuns_KeepsRunsIsolated()
    {
        // One immutable HostOperations instance shared by two concurrent runs; each
        // run invokes the operation itself (no shared cache), so both complete with
        // their own draw of the counter.
        var held = new HeldOperationSequence(2);
        var shared = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", held.InvokeAsync)),
        };

        var first = KatLangEngine.RunAsync("Data * 10", shared);
        var second = KatLangEngine.RunAsync("Data * 10", shared);
        await Reached(held.ReachedTask(0));
        await Reached(held.ReachedTask(1));
        Assert.False(first.IsCompleted);
        Assert.False(second.IsCompleted);

        held.Release(0, Atom(1));
        held.Release(1, Atom(2));
        var results = await Complete(Task.WhenAll(first, second));

        var values = results
            .Select(r => Decimal128.Parse(Assert.IsType<RunResult.Success>(r).ToDisplayString(), System.Globalization.CultureInfo.InvariantCulture))
            .OrderBy(v => v)
            .ToArray();
        Assert.Equal(new Decimal128[] { 10m, 20m }, values);
        Assert.Equal(2, held.Invocations);
    }

    [Fact]
    public async Task SharedParsedTree_EvaluatedUnderDifferentHostConfigurations()
    {
        // Parse once with the names in scope; evaluate the SAME tree under different
        // host configurations (name-level agreement is what matters, not instance
        // identity), including a synchronous lane while an async lane is suspended.
        var parseOperations = HostOperations.Create(
            HostOperation.Create("Data", (_, _) => Atom(0)));
        var parsed = Parser.Parse("Data + 1", new RunOptions { HostOperations = parseOperations });
        Assert.False(parsed.HasErrors);
        var ast = new Expr.AlgorithmExpr(parsed.Root);

        var held = new HeldOperation();
        var asyncOperations = HostOperations.Create(HostOperation.CreateAsync("Data", held.InvokeAsync));
        var syncOperations = HostOperations.Create(HostOperation.Create("Data", (_, _) => Atom(700)));

        var suspended = Evaluator.RunAsync(ast, asyncOperations, null, CancellationToken.None);
        await Reached(held.ReachedTask);
        Assert.False(suspended.IsCompleted);

        // A synchronous run over the very same parsed tree completes while the async
        // run is suspended — no leakage of host state, caches, or configuration.
        var syncResult = Evaluator.Run(ast, syncOperations, null, CancellationToken.None);
        Assert.True(syncResult.IsOk);
        Assert.Equal(701m, ((Result.Atom)syncResult.Value).Value);

        held.Release(Atom(41));
        var asyncResult = await Complete(suspended);
        Assert.True(asyncResult.IsOk);
        Assert.Equal(42m, ((Result.Atom)asyncResult.Value).Value);
        Assert.Equal(1, held.Invocations);
    }

    // ── Sync/async semantic equivalence and conveniences ────────────────────

    [Fact]
    public async Task SyncAndAsyncOperations_WithIdenticalHostResults_ProduceIdenticalRuns()
    {
        const string source = "Total = Data.sum + Fetch(2)\nTotal\nTotal()";
        Result CollectionValue() => new Result.ListValue([Atom(1), Atom(2), Atom(3)]);

        var syncOptions = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => CollectionValue()),
                HostOperation.Create("Fetch", (args, _) => Atom(((Result.Atom)args[0]).Value * 100), "id")),
        };
        var asyncOptions = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", (_, _) => ValueTask.FromResult(CollectionValue())),
                HostOperation.CreateAsync(
                    "Fetch",
                    (args, _) => ValueTask.FromResult(Atom(((Result.Atom)args[0]).Value * 100)),
                    "id")),
        };

        var syncResult = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, syncOptions));
        var asyncResult = Assert.IsType<RunResult.Success>(
            await Complete(KatLangEngine.RunAsync(source, asyncOptions)));

        Assert.Equal(syncResult.ToDisplayString(), asyncResult.ToDisplayString());
        Assert.Equal(syncResult.Atoms, asyncResult.Atoms);
        Assert.True(Result.ValueComparer.Equals(syncResult.Value, asyncResult.Value));
    }

    [Fact]
    public async Task AsyncConveniences_ProjectLikeTheirSynchronousCounterparts()
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", (_, _) => ValueTask.FromResult<Result>(
                    new Result.SequenceValue([Atom(1), Atom(2)])))),
        };

        Assert.Equal(new Decimal128[] { 1m, 2m, 3m }, await Complete(KatLangEngine.EvaluateToAtomsAsync("Data*, 3", options)));
        Assert.Equal("1 2 3", await Complete(KatLangEngine.EvaluateToStringAsync("Data*, 3", options)));

        await Assert.ThrowsAsync<KatLangException>(
            () => Complete(KatLangEngine.EvaluateToAtomsAsync("Data +", options)));

        // Without any async component the conveniences complete synchronously.
        var syncTask = KatLangEngine.EvaluateToAtomsAsync("1 + 1");
        Assert.True(syncTask.IsCompletedSuccessfully);
        Assert.Equal(new Decimal128[] { 2m }, await syncTask);
    }
}
