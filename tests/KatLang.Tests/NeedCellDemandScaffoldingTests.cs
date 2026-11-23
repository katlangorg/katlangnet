using System.Numerics;
using System.Reflection;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.TestInfrastructure;
using KatLang.Tests.InvocationRoute;

namespace KatLang.Tests;

/// <summary>
/// The per-demand scaffolding of a need cell and the per-call Math argument array (2026-11-18, C#
/// implementation only). A VALUE demand nobody joins allocates no shared completion (the first joiner
/// creates it). Both families carry the current node in the logical execution context. A Math
/// native call keeps its one or two arguments in its own frame.
/// </summary>
public class NeedCellDemandScaffoldingTests
{
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    private static readonly EvalResult<Evaluator.CountedResult> Seven
        = EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom(7), 1));

    private static async Task Until(Func<bool> condition)
    {
        var deadline = DateTime.UtcNow + WaitLimit;
        while (!condition())
        {
            Assert.True(DateTime.UtcNow < deadline, "The awaited condition did not hold in time.");
            await Task.Delay(5);
        }
    }

    // ── Single flight with a lazily created completion ─────────────────────────────────────────────

    /// <summary>
    /// A running computation nobody joined has no shared completion; the first joiner creates it and
    /// waits on it, and both observers receive the one outcome of the one computation. The starter
    /// observes its own state from inside the computation.
    /// </summary>
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task ASecondObserver_CreatesTheSharedCompletion_AndJoinsTheOneComputation(bool asynchronousStarter, bool asynchronousJoiner)
    {
        var budget = EvaluationBudget.Create(null);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        var unjoinedInside = false;
        NeedCell? cell = null;
        EvalResult<Evaluator.CountedResult> Enter()
        {
            Interlocked.Increment(ref starts);
            unjoinedInside = cell!.HasValueInFlight && !cell.HasJoinedValueFlight;
            entered.SetResult();
            return Seven;
        }
        cell = new NeedCell(() =>
        {
            var outcome = Enter();
            release.Task.WaitAsync(WaitLimit).GetAwaiter().GetResult();
            return outcome;
        }, async () =>
        {
            var outcome = Enter();
            await release.Task.WaitAsync(WaitLimit);
            return outcome;
        }, budget: budget);

        var starter = asynchronousStarter
            ? Task.Run(async () => await cell.DemandAsync())
            : Task.Factory.StartNew(() => cell.Demand(), TaskCreationOptions.LongRunning);
        await entered.Task.WaitAsync(WaitLimit);
        Assert.True(unjoinedInside);
        Assert.False(cell.HasJoinedValueFlight);

        var joiner = asynchronousJoiner
            ? Task.Run(async () => await cell.DemandAsync())
            : Task.Factory.StartNew(() => cell.Demand(), TaskCreationOptions.LongRunning);
        await Until(() => cell.HasJoinedValueFlight || joiner.IsCompleted);
        Assert.False(joiner.IsCompleted);
        Assert.True(cell.HasValueInFlight);
        release.SetResult();

        var first = await starter.WaitAsync(WaitLimit);
        var second = await joiner.WaitAsync(WaitLimit);
        Assert.Same(Seven.Value.Value, first.Value.Value);
        Assert.Same(Seven.Value.Value, second.Value.Value);
        Assert.Equal(1, starts);
        Assert.False(cell.HasValueInFlight);
        Assert.False(cell.HasJoinedValueFlight);
        Assert.True(cell.HasCompletedValue);
    }

    /// <summary>
    /// A starter nobody joined still rethrows the original host exception and cancellation (the
    /// object and its token), exactly as awaiting a shared completion delivered them; the stored
    /// outcome stays sticky for every later demand.
    /// </summary>
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task AnUnjoinedStarter_RethrowsTheOriginalExceptionAndToken(bool asynchronous, bool cancellation)
    {
        using var host = new CancellationTokenSource();
        Exception thrown = cancellation
            ? new OperationCanceledException("host cancellation", host.Token)
            : new InvalidOperationException("original host failure");
        var starts = 0;
        var cell = new NeedCell(() =>
        {
            starts++;
            throw thrown;
        }, () =>
        {
            starts++;
            throw thrown;
        }, budget: EvaluationBudget.Create(null));

        var first = asynchronous
            ? await Assert.ThrowsAnyAsync<Exception>(() => cell.DemandAsync().AsTask())
            : Assert.ThrowsAny<Exception>(() => cell.Demand());
        Assert.Same(thrown, first);
        if (first is OperationCanceledException cancelled) Assert.Equal(host.Token, cancelled.CancellationToken);
        Assert.Same(thrown, Assert.ThrowsAny<Exception>(() => cell.Demand()));
        Assert.Same(thrown, await Assert.ThrowsAnyAsync<Exception>(() => cell.DemandAsync().AsTask()));
        Assert.Equal(1, starts);
        Assert.False(cell.HasValueInFlight);
        Assert.False(NeedNode.HasCurrentNode);
    }

    // ── The current node across synchronous and asynchronous computations ──────────────────────────

    /// <summary>
    /// The wait-for graph sees the innermost computation of the flow whichever family runs it: an
    /// asynchronous computation started inside a synchronous one is the parent of what it demands,
    /// and a synchronous computation started inside an asynchronous one is the parent of what IT
    /// demands. Re-entering any cell of the chain is a DemandCycle for the re-entry, and every edge
    /// is gone afterwards.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task TheInnermostComputation_IsTheParent_AcrossBothFamilies(bool outerAsynchronous)
    {
        var budget = EvaluationBudget.Create(null);
        NeedCell? outer = null, middle = null, inner = null;
        var observed = new List<string>();
        var reentry = default(EvalResult<Evaluator.CountedResult>);
        EvalResult<Evaluator.CountedResult> InnerBody()
        {
            observed.Add($"outer={outer!.ActiveDependencyCount} middle={middle!.ActiveDependencyCount} current={NeedNode.HasCurrentNode}");
            reentry = middle.Demand();
            return Seven;
        }
        inner = new NeedCell(InnerBody, () => new(InnerBody()), budget: budget);
        // The middle computation runs in the OTHER family than the outer one.
        middle = outerAsynchronous
            ? new NeedCell(() => inner.Demand(), () => new(inner.Demand()), budget: budget)
            : new NeedCell(() => inner.Demand(), async () => { await Task.Yield(); return await inner.DemandAsync(); }, budget: budget);
        outer = outerAsynchronous
            ? new NeedCell(() => throw new InvalidOperationException(), async () => { await Task.Yield(); return middle.Demand(); }, budget: budget)
            : new NeedCell(() => middle.DemandAsync().AsTask().WaitAsync(WaitLimit).GetAwaiter().GetResult(), () => throw new InvalidOperationException(), budget: budget);

        var outcome = outerAsynchronous ? await outer.DemandAsync().AsTask().WaitAsync(WaitLimit) : outer.Demand();

        Assert.True(outcome.IsOk, outcome.IsError ? outcome.Error.ToString() : null);
        Assert.Equal(["outer=1 middle=1 current=True"], observed);
        Assert.Equal(KatLangErrorCode.DemandCycle, reentry.Error.Code);
        Assert.Equal(0, outer.ActiveDependencyCount);
        Assert.Equal(0, middle.ActiveDependencyCount);
        Assert.Equal(0, inner.ActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
    }

    /// <summary>
    /// A run started inside a synchronous computation of another run takes no edge from it: the outer
    /// parent belongs to another run, so the inner run's cells record their own edges.
    /// </summary>
    [Fact]
    public void ANestedRunsCells_RecordTheirOwnEdges_InsideAnotherRunsSynchronousComputation()
    {
        var outerBudget = EvaluationBudget.Create(null);
        var innerBudget = EvaluationBudget.Create(null);
        NeedCell? outerCell = null, innerParent = null;
        var during = new List<string>();
        var innerChild = new NeedCell(() =>
        {
            during.Add($"outer={outerCell!.ActiveDependencyCount} innerParent={innerParent!.ActiveDependencyCount}");
            return Seven;
        }, () => new(Seven), budget: innerBudget);
        innerParent = new NeedCell(() => innerChild.Demand(), () => innerChild.DemandAsync(), budget: innerBudget);
        outerCell = new NeedCell(() => innerParent.Demand(), () => new(Seven), budget: outerBudget);

        Assert.True(outerCell.Demand().IsOk);
        // The outer cell took no edge to the inner run's cell; the inner parent took one to its child.
        Assert.Equal(["outer=0 innerParent=1"], during);
        Assert.Equal(0, outerCell.ActiveDependencyCount);
        Assert.Equal(0, innerParent.ActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SynchronousComputation_FollowsItsCapturedExecutionContext(bool projection)
    {
        var outside = ExecutionContext.Capture()!;
        NeedCell? cell = null;
        void Observe()
        {
            Assert.True(NeedNode.HasCurrentNode);
            ExecutionContext.Run(outside, _ => Assert.False(NeedNode.HasCurrentNode), null);
            // A new thread inherits the computation. Re-entry there must detect the cycle
            // before waiting for the synchronous computation that started the thread.
            var fork = Task.Factory.StartNew(() =>
            {
                Assert.True(NeedNode.HasCurrentNode);
                return projection ? cell!.ProjectCallable().Error : cell!.Demand().Error;
            }, CancellationToken.None, TaskCreationOptions.LongRunning, TaskScheduler.Default);
            var cycle = Assert.IsType<EvalError.DemandCycle>(fork.WaitAsync(WaitLimit).GetAwaiter().GetResult());
            Assert.Equal(cell!.Span, cycle.Span);
        }
        var span = new SourceSpan(1, 2, 1, 3);
        cell = NeedCell.WithRuntimeProjection(() => { Observe(); return Seven; }, () => new(Seven),
            () => { Observe(); return EvalResult<Algorithm?>.Ok(null); },
            () => throw new InvalidOperationException(), span: span, budget: EvaluationBudget.Create(null));

        Assert.True(projection ? cell.ProjectCallable().IsOk : cell.Demand().IsOk);
        Assert.False(NeedNode.HasCurrentNode);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public Task SuspendedComputation_RestoresItsParentBeforeWakingAnInlineWaiter(bool projection)
        => Task.Run(async () =>
        {
            // Run on the default scheduler. The gate and the unsafe awaiter deliberately permit
            // inline completion with no captured context of the waiter's own.
            var gate = new TaskCompletionSource();
            var observed = new TaskCompletionSource<bool>(TaskCreationOptions.RunContinuationsAsynchronously);
            var inner = NeedCell.WithRuntimeProjection(() => Seven,
                async () => { await gate.Task.ConfigureAwait(false); return Seven; },
                () => EvalResult<Algorithm?>.Ok(null),
                async () => { await gate.Task.ConfigureAwait(false); return EvalResult<Algorithm?>.Ok(null); });
            NeedCell? parent = null;
            parent = new NeedCell(() => Seven, async () =>
            {
                using (ExecutionContext.SuppressFlow())
                {
                    Task pending = projection ? inner.ProjectCallableAsync().AsTask() : inner.DemandAsync().AsTask();
                    pending.ConfigureAwait(false).GetAwaiter().UnsafeOnCompleted(
                        () => observed.SetResult(parent!.IsEvaluatingInCurrentFlow()));
                }
                await observed.Task.ConfigureAwait(false);
                return Seven;
            });
            var running = parent.DemandAsync().AsTask();
            gate.SetResult();
            Assert.True(await observed.Task.WaitAsync(WaitLimit));
            Assert.True((await running.WaitAsync(WaitLimit)).IsOk);
        });

    // ── Strict allocation counts (isolated child processes) ────────────────────────────────────────

    private static long Bytes(Action action)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        action();
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    // An async method's own state machine: a struct in an optimized build, which a synchronous
    // completion never boxes, but a heap class in a Debug build (one object per call).
    private static long StateMachineBytes(Type owner, string method)
    {
        var type = owner.GetMethod(method, BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static)!
            .GetCustomAttribute<AsyncStateMachineAttribute>()!.StateMachineType;
        return type.IsValueType ? 0 : InstanceSize.Of(type);
    }

    private static T CompleteSynchronously<T>(ValueTask<T> operation)
    {
        Assert.True(operation.IsCompletedSuccessfully, "The demand must complete without suspension.");
        return operation.Result;
    }

    // The logical context of `installs` nested computations on the measuring thread, including any
    // keys the test runner set: each installs its node, and each restores the context object captured
    // before its own installation (NeedNode.LeaveComputation), which allocates nothing. Since
    // 2026-11-20 a nested computation therefore costs one context, not two.
    private static long ContextBytes(int installs = 1)
    {
        var current = new AsyncLocal<object?>();
        var nodes = Enumerable.Range(0, installs).Select(static _ => new object()).ToArray();
        var outer = ExecutionContext.Capture()!;
        return Bytes(() =>
        {
            foreach (var node in nodes) current.Value = node;
            ExecutionContext.Restore(outer);
        });
    }

    private static NeedCell Projecting(NeedCell child, EvaluationBudget budget)
        => new(() => child.ProjectCallable().IsOk ? Seven : throw new InvalidOperationException(),
            () => CompleteSynchronously(child.ProjectCallableAsync()).IsOk ? new(Seven) : throw new InvalidOperationException(),
            budget: budget);

    [Fact]
    public void AnUnjoinedSynchronousDemand_AllocatesOnlyItsContext_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var budget = EvaluationBudget.Create(null);
        NeedCell Fresh() => new(static () => Seven, static () => new(Seven), budget: budget);
        _ = Fresh().Demand(); // warm-up: first-call initialization stays outside the window

        var cell = Fresh();
        Assert.Equal(ContextBytes(), Bytes(() => _ = cell.Demand()));
        Assert.True(cell.HasCompletedValue);
        Assert.False(cell.HasValueInFlight);

        // One context per level: the parent's one wait-for edge is held inline (216 bytes for the
        // former edge table on .NET 11 x64), and the child's exit restores the parent's own context
        // object (72 bytes for one more context on .NET 11 x64 with no other key in it).
        NeedCell Nested()
        {
            var child = Fresh();
            return new NeedCell(() => child.Demand(), () => child.DemandAsync(), budget: budget);
        }
        _ = Nested().Demand();
        var parent = Nested();
        Assert.Equal(ContextBytes(installs: 2), Bytes(() => _ = parent.Demand()));
        Assert.Equal(0, parent.ActiveDependencyCount);
        Assert.False(parent.HasPromotedDependencies);

        // The same for a runtime CALLABLE projection nested in a VALUE computation.
        NeedCell Projection() => NeedCell.WithRuntimeProjection(static () => Seven, static () => new(Seven),
            static () => EvalResult<Algorithm?>.Ok(null), static () => new(EvalResult<Algorithm?>.Ok(null)), budget: budget);
        _ = Projecting(Projection(), budget).Demand();
        var projecting = Projecting(Projection(), budget);
        Assert.Equal(ContextBytes(installs: 2), Bytes(() => _ = projecting.Demand()));
        Assert.Equal(0, projecting.ActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
        GcIsolatedAllocation.Complete();
    }

    [Fact]
    public void AnUnjoinedAsynchronousDemand_AllocatesOnlyItsContextAndStateMachines_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var budget = EvaluationBudget.Create(null);
        NeedCell Fresh() => new(static () => Seven, static () => new(Seven), budget: budget);
        _ = CompleteSynchronously(Fresh().DemandAsync()); // warm-up

        var demand = StateMachineBytes(typeof(NeedCell), "DemandAsync")
            + StateMachineBytes(typeof(NeedCell), "EvaluateAsync");

        var cell = Fresh();
        var allocated = Bytes(() => _ = CompleteSynchronously(cell.DemandAsync()));
        Assert.Equal(demand + ContextBytes(), allocated);

        // One context per level here too: the child's explicit exit restores the parent's own context
        // object, which the async method would have restored next anyway.
        NeedCell Nested()
        {
            var child = Fresh();
            return new NeedCell(() => child.Demand(), () => child.DemandAsync(), budget: budget);
        }
        _ = CompleteSynchronously(Nested().DemandAsync());
        var parent = Nested();
        Assert.Equal(2 * demand + ContextBytes(installs: 2), Bytes(() => _ = CompleteSynchronously(parent.DemandAsync())));
        Assert.Equal(0, parent.ActiveDependencyCount);

        NeedCell Projection() => NeedCell.WithRuntimeProjection(static () => Seven, static () => new(Seven),
            static () => EvalResult<Algorithm?>.Ok(null), static () => new(EvalResult<Algorithm?>.Ok(null)), budget: budget);
        _ = CompleteSynchronously(Projecting(Projection(), budget).DemandAsync());
        var projecting = Projecting(Projection(), budget);
        var projection = StateMachineBytes(typeof(NeedCell), "ProjectRuntimeAsync")
            + StateMachineBytes(typeof(NeedCell), "ProjectRuntimeComputationAsync");
        Assert.Equal(demand + projection + ContextBytes(installs: 2), Bytes(() => _ = CompleteSynchronously(projecting.DemandAsync())));
        Assert.Equal(0, projecting.ActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
        GcIsolatedAllocation.Complete();
    }

    private delegate EvalResult<Result> NativeCall(string fnName, IReadOnlyList<string> argNames, Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> valEnv);

    private delegate EvalResult<Result> NativeArgument(Evaluator.EvalCtx ctx, IReadOnlyList<(string Name, Result Value)> valEnv, string name);

    private static T Private<T>(string name) where T : Delegate
        => typeof(Evaluator).GetMethod(name, BindingFlags.NonPublic | BindingFlags.Static)!.CreateDelegate<T>();

    [Fact]
    public void AMathNativeCall_AllocatesExactlyItsReadsAndItsResult_GcIsolatedChild()
    {
        // The native call reads its arguments (the ordinary parameter reads) and applies the member to
        // them; the arguments themselves are no allocation.
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var native = Private<NativeCall>("EvalNativeCall");
        var read = Private<NativeArgument>("LookupNativeArgument");
        var ctx = Evaluator.EvalCtx.Empty;
        IReadOnlyList<(string Name, Result Value)> values = [("value", new Result.Atom(Decimal128.Parse("-2.345", System.Globalization.CultureInfo.InvariantCulture))), ("digits", new Result.Atom(1))];
        // These small finite Abs and Round inputs each produce a single Atom.
        Result.Atom? measured = null;
        var resultBytes = Bytes(() => measured = new Result.Atom(7));
        GC.KeepAlive(measured);
        foreach (var (member, names) in new[] { ("Abs", new[] { "value" }), ("Round", new[] { "value", "digits" }) })
        {
            var warm = native(member, names, ctx, values);
            Assert.True(warm.IsOk, warm.IsError ? warm.Error.ToString() : null);
            var reads = 0L;
            foreach (var name in names)
            {
                _ = read(ctx, values, name);
                reads += Bytes(() => _ = read(ctx, values, name));
            }
            Assert.Equal(reads + resultBytes, Bytes(() => _ = native(member, names, ctx, values)));
        }
        GcIsolatedAllocation.Complete();
    }

    // ── Workload bounds (isolated child process) ───────────────────────────────────────────────────

    // The brief's three workloads: one `if` per element (three lazily demanded argument cells per
    // call), a recursive user call (2 * fib(13) - 1 = 465 calls of Fib(12)), and one unary plus one
    // binary Math member per element. Since 2026-11-19 also a runtime CALLABLE projection per element:
    // a supplied `.Algorithm` link, invoked through a parameter.
    private static (string Source, int Units) Workload(string name) => name switch
    {
        "IfHeavy" => ("F = if(x mod 2 == 0, x, 0 - x)\nrange(1, 2000).map(F).sum", 2000),
        "RecursiveCalls" => ("Fib = if(n < 2, n, Fib(n - 1) + Fib(n - 2))\nFib(12)", 465),
        "MathHeavy" => ("F = Math.Abs(x) + Math.Round(x, 1)\nrange(1, 2000).map(F).sum", 2000),
        "RuntimeProjection" => ("Capture(meta op) = op\nSq(y) = y * y\nUse(g, v) = g(v)\nF = Use(Capture(Sq(x)).Algorithm, x)\nrange(1, 2000).map(F).sum", 2000),
        _ => throw new ArgumentOutOfRangeException(nameof(name)),
    };

    private static double BytesPerUnit(string workload, bool asynchronous)
    {
        var (source, units) = Workload(workload);
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        void Run()
        {
            var result = asynchronous
                ? Evaluator.RunCountedAsync(program, new RunScopedAsyncZeroArgPropertyResultCache()).GetAwaiter().GetResult().IsError
                : Evaluator.Run(program, new RunScopedZeroArgPropertyResultCache(), enableLoopOptimization: true, loopDiagnostics: null).IsError;
            Assert.False(result, workload);
        }

        for (var i = 0; i < 3; i++)
            Run();
        var minimum = long.MaxValue;
        for (var i = 0; i < 3; i++)
            minimum = Math.Min(minimum, Bytes(Run));
        return minimum / (double)units;
    }

    /// <summary>
    /// A whole evaluator run's allocations divided by its element or user-call count. Debug and
    /// Release have separate bounds because a Debug async state machine allocates even when it
    /// completes inline. Each bound is below its measured pre-change value. Since 2026-11-20 every bound
    /// lies midway between the values measured before and after a nested computation's exit restores
    /// its caller's context object (72 bytes per nested computation on .NET 11 x64). On the twin route,
    /// RuntimeProjection's bound lies midway between the final value and the smaller value left by
    /// reverting either that change or the inline first pair of a resolution record (392 bytes per
    /// element in Release: two one-step records). Reverting either change on its own therefore fails a
    /// bound. Each margin is smaller than every saving of 2026-11-18/19 (the inline first wait-for edge,
    /// the cell's own monitor as its gate, the projection completion created by its first joiner), so
    /// those still fail too.
    ///
    /// <para>On 2026-11-23 every bound was moved by the MEASURED cost of evaluating lists on demand
    /// (issue #204), keeping its margin, so each earlier saving still fails its row. IfHeavy, MathHeavy
    /// and RuntimeProjection map 2,000 elements, and a mapped position is now a cell read on demand:
    /// +432.2 bytes per element in Release on both routes (+480.2 on the RuntimeProjection twin), and in
    /// Debug +1,336.5 synchronously and +1,880.7 to +2,200.5 on the twin, where the single-body step
    /// methods' state machines are heap objects. RecursiveCalls builds no list: only its Debug twin
    /// moved (+251.8, the twin spine machine's state object carries the locals of its lazy-selection
    /// and equality-materialization arms). Measured before (base <c>cd9bffa4</c>) and after with the
    /// same harness: Debug sync 2,862.9 → 4,199.4, 3,122.0 → 3,122.0, 4,198.9 → 5,535.4, 7,464.6 →
    /// 8,801.1; Debug twin 15,016.5 → 16,973.2, 19,803.3 → 20,055.1, 20,720.5 → 22,601.2, 27,290.4 →
    /// 29,490.9; Release sync 2,062.1 → 2,494.3, 2,361.8 → 2,361.8, 3,294.1 → 3,726.3, 5,368.0 →
    /// 5,800.2; Release twin 2,061.8 → 2,494.0, 2,360.7 → 2,360.7, 3,293.8 → 3,726.0, 5,904.0 →
    /// 6,384.2 (rows in the order of the table below).</para>
    /// </summary>
    [Fact]
    public void DemandAndMathWorkloads_StayBelowTheirMeasuredBounds_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var failures = new List<string>();
        foreach (var (workload, asynchronous, debugBound, releaseBound) in new (string, bool, int, int)[]
        {
            ("IfHeavy", false, 4_253, 2_540),
            ("RecursiveCalls", false, 3_203, 2_443),
            ("MathHeavy", false, 5_554, 3_738),
            ("RuntimeProjection", false, 8_944, 5_840),
            ("IfHeavy", true, 17_015, 2_539),
            ("RecursiveCalls", true, 20_116, 2_442),
            ("MathHeavy", true, 22_613, 3_737),
            ("RuntimeProjection", true, 29_523, 6_424),
        })
        {
#if DEBUG
            var bound = debugBound;
#else
            var bound = releaseBound;
#endif
            var perUnit = BytesPerUnit(workload, asynchronous);
            if (perUnit >= bound)
                failures.Add($"{workload} ({(asynchronous ? "twin" : "sync")}): {perUnit:F1} bytes per unit (bound {bound})");
        }
        Assert.True(failures.Count == 0, string.Join(Environment.NewLine, failures));
        GcIsolatedAllocation.Complete();
    }
}
