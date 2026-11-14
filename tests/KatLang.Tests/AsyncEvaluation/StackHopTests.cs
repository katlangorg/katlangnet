using System.Collections.Concurrent;
using System.Diagnostics;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// The async twin route's stack hop (<see cref="StackHop"/>, 2026-11-14): the awaiter's own
/// contract, the need-cell hop sites on a genuinely low stack, the flow-local state a hop must
/// carry (the need-cell wait-for graph through the <see cref="ExecutionContext"/>), and the
/// host patterns a hop must not deadlock — awaiting a deep run from a single-threaded
/// <see cref="SynchronizationContext"/>, and blocking on one there. The depth outcomes on the
/// documented minimum stack are pinned by <see cref="AsyncStackDepthTests"/>; cancellation across
/// hops by <see cref="EvaluationCancellationTests"/>.
/// </summary>
public class StackHopTests
{
    private const int OneMiB = 1_048_576;

    // A hang guard for work that runs on the thread pool, never a latency claim.
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(120);

    private static EvalResult<Evaluator.CountedResult> Value(int number = 7)
        => EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom((Decimal128)number), 1));

    // ── The awaiter ───────────────────────────────────────────────────────────

    [Fact]
    public void Hop_AlwaysSuspends_ResumesOnThePool_KeepsTheFlow_AndIgnoresTheCallersContext()
    {
        var hop = new StackHop();
        Assert.False(hop.IsCompleted);
        Assert.False(hop.GetAwaiter().IsCompleted);
        hop.GetResult();

        var local = new AsyncLocal<string?>();
        int startThread = 0, posts = -1;
        string? callerValueAfterward = "unset";
        (string? Value, bool OnPool, int Thread)? resumed = null;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () =>
        {
            var context = new SingleThreadedContext();
            SynchronizationContext.SetSynchronizationContext(context);
            try
            {
                startThread = Environment.CurrentManagedThreadId;
                var pending = HopOnce(local);
                // Blocking the context's only thread: the hop must not need it.
                Assert.True(pending.Wait(WaitLimit), "the hop never resumed");
                resumed = pending.Result;
                callerValueAfterward = local.Value;
                posts = context.Posts;
            }
            finally
            {
                SynchronizationContext.SetSynchronizationContext(null);
            }
        });

        Assert.Equal("flowing", resumed!.Value.Value);
        Assert.True(resumed.Value.OnPool);
        Assert.NotEqual(startThread, resumed.Value.Thread);
        Assert.Null(callerValueAfterward);
        Assert.Equal(0, posts);

        static async Task<(string? Value, bool OnPool, int Thread)> HopOnce(AsyncLocal<string?> local)
        {
            local.Value = "flowing";
            await new StackHop();
            return (local.Value, Thread.CurrentThread.IsThreadPoolThread, Environment.CurrentManagedThreadId);
        }
    }

    [Fact]
    public async Task OnCompleted_FlowsTheExecutionContext_UnsafeOnCompleted_LeavesItToTheBuilder()
    {
        var local = new AsyncLocal<string?> { Value = "captured" };
        var flowing = new TaskCompletionSource<(string?, bool)>(TaskCreationOptions.RunContinuationsAsynchronously);
        var raw = new TaskCompletionSource<(string?, bool)>(TaskCreationOptions.RunContinuationsAsynchronously);

        new StackHop().OnCompleted(() => flowing.SetResult((local.Value, Thread.CurrentThread.IsThreadPoolThread)));
        new StackHop().UnsafeOnCompleted(() => raw.SetResult((local.Value, Thread.CurrentThread.IsThreadPoolThread)));

        Assert.Equal(("captured", true), await flowing.Task.WaitAsync(WaitLimit));
        // The raw continuation runs in the pool's default context; an async method's builder
        // continuation restores the awaiting method's own context itself (see the test above).
        Assert.Equal(((string?)null, true), await raw.Task.WaitAsync(WaitLimit));
    }

    // ── The need-cell hop sites ───────────────────────────────────────────────

    [Fact]
    public async Task ValueDemand_OnALowStack_ContinuesOnAFreshStack_InsteadOfStopping()
    {
        // Before the hop, the demand's stack probe answered EvaluationStackExhausted here.
        var budget = EvaluationBudget.Create(null);
        bool? onPool = null, lowInside = null;
        var cell = new NeedCell(() => Value(), () =>
        {
            onPool = Thread.CurrentThread.IsThreadPoolThread;
            lowInside = StackHop.HostStackIsLow();
            return new(Value());
        }, budget: budget);

        var lowAtDemand = false;
        var pending = AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () => WithLowStack(() =>
        {
            lowAtDemand = !RuntimeHelpers.TryEnsureSufficientExecutionStack();
            return cell.DemandAsync().AsTask();
        }));
        var result = await pending.WaitAsync(WaitLimit);

        Assert.True(lowAtDemand, "the demand was not started on a low stack");
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        Assert.Equal(new Result.Atom(7), result.Value.Value);
        Assert.True(onPool);
        Assert.False(lowInside);
        Assert.Equal(0, budget.ConsumedSteps);
        Assert.Equal(0, budget.PeakDepth);
        Assert.Null(budget.CheckContinuation());
    }

    [Fact]
    public async Task RuntimeProjection_OnALowStack_ContinuesOnAFreshStack_InsteadOfStopping()
    {
        var budget = EvaluationBudget.Create(null);
        var algorithm = new Algorithm.User(null, [], [], [], [new Expr.Num(7)]);
        bool? onPool = null, lowInside = null;
        var cell = NeedCell.WithRuntimeProjection(
            () => Value(), () => new(Value()),
            () => EvalResult<Algorithm?>.Ok(algorithm),
            () =>
            {
                onPool = Thread.CurrentThread.IsThreadPoolThread;
                lowInside = StackHop.HostStackIsLow();
                return new(EvalResult<Algorithm?>.Ok(algorithm));
            },
            budget: budget);

        var lowAtDemand = false;
        var pending = AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () => WithLowStack(() =>
        {
            lowAtDemand = !RuntimeHelpers.TryEnsureSufficientExecutionStack();
            return cell.ProjectCallableAsync().AsTask();
        }));
        var result = await pending.WaitAsync(WaitLimit);

        Assert.True(lowAtDemand, "the projection was not started on a low stack");
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        Assert.Same(algorithm, result.Value);
        Assert.True(onPool);
        Assert.False(lowInside);
        Assert.Null(budget.CheckContinuation());
    }

    [Fact]
    public async Task SelfDemandAcrossAHop_IsStillADemandCycle()
    {
        // The wait-for graph is flow-local (AsyncLocal): a demand that hops before demanding
        // itself again must still find its own cell in progress in its flow, never wait on it.
        var span = new SourceSpan(new SourcePosition(2, 3), new SourcePosition(2, 4));
        NeedCell? direct = null;
        direct = new NeedCell(() => direct!.Demand(), async () =>
        {
            await new StackHop();
            return await direct!.DemandAsync();
        }, span: span);

        var result = await direct.DemandAsync().AsTask().WaitAsync(WaitLimit);

        Assert.Equal(KatLangErrorCode.DemandCycle, result.Error.Code);
        Assert.Equal(span, result.Error.Span);
    }

    // ── Host patterns: a deep twin run on a single-threaded context ──────────────

    /// <summary>
    /// <c>F(120)</c> outgrows a 1 MiB thread on the twin route (an asynchronous operation is
    /// configured, never called); the synchronous <c>here</c> operation at the bottom records
    /// whether that level ran on the thread pool, which proves the run hopped.
    /// </summary>
    private const string DeepSource = "F(n) = if(n == 0, here(0), F(n - 1) + 1)\nF(120)";

    private sealed class DeepRun
    {
        private int _bottomOnPool = -1;

        public DeepRun()
        {
            Operations = HostOperations.Create(
                HostOperation.CreateAsync("Ping", (_, _) => ValueTask.FromResult<Result>(new Result.Atom(1))),
                HostOperation.Create("here", (args, _) =>
                {
                    Volatile.Write(ref _bottomOnPool, Thread.CurrentThread.IsThreadPoolThread ? 1 : 0);
                    return args[0];
                }, "value"));
            var parsed = Parser.Parse(DeepSource, new RunOptions { HostOperations = Operations });
            Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
            Ast = new Expr.AlgorithmExpr(parsed.Root);
        }

        public HostOperations Operations { get; }

        public Expr Ast { get; }

        public bool BottomRanOnThePool => Volatile.Read(ref _bottomOnPool) == 1;

        public Task<EvalResult<Result>> Start()
            => Evaluator.RunAsync(Ast, Operations, limits: null, randomSeed: null, CancellationToken.None);
    }

    [Fact]
    public void DeepTwinRun_AwaitedOnASingleThreadedSynchronizationContext_CompletesAndResumesThere()
    {
        var run = new DeepRun();
        int contextThread = 0, resumedThread = -1, posts = -1;
        EvalResult<Result>? outcome = null;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () =>
        {
            var context = new SingleThreadedContext();
            contextThread = Environment.CurrentManagedThreadId;
            context.Run(async () =>
            {
                // No ConfigureAwait: the host's own continuation belongs on its context.
                outcome = await run.Start();
                resumedThread = Environment.CurrentManagedThreadId;
            }, WaitLimit);
            posts = context.Posts;
        });

        Assert.True(outcome!.Value.IsOk, outcome.Value.IsError ? outcome.Value.Error.ToString() : null);
        Assert.Equal(new Result.Atom(120), outcome.Value.Value);
        Assert.True(run.BottomRanOnThePool, "the run never left the 1 MiB thread, so no hop was exercised");
        Assert.Equal(contextThread, resumedThread);
        // At most the host's own continuation: the library posts nothing to the context.
        Assert.InRange(posts, 0, 1);
    }

    [Fact]
    public void DeepTwinRun_BlockedOnFromASingleThreadedSynchronizationContext_DoesNotDeadlock()
    {
        var run = new DeepRun();
        bool evaluatorCompleted = false, engineCompleted = false;
        EvalResult<Result>? outcome = null;
        RunResult? engineOutcome = null;
        var posts = -1;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () =>
        {
            var context = new SingleThreadedContext();
            SynchronizationContext.SetSynchronizationContext(context);
            try
            {
                // The context's only thread blocks: any continuation posted to it would deadlock.
                var pending = run.Start();
                evaluatorCompleted = pending.Wait(WaitLimit);
                if (evaluatorCompleted)
                    outcome = pending.Result;

                var engine = KatLangEngine.RunAsync(DeepSource, new RunOptions { HostOperations = run.Operations });
                engineCompleted = engine.Wait(WaitLimit);
                engineOutcome = engineCompleted ? engine.Result : null;
                posts = context.Posts;
            }
            finally
            {
                SynchronizationContext.SetSynchronizationContext(null);
            }
        });

        Assert.True(evaluatorCompleted, "blocking on the evaluator's deep twin run deadlocked");
        Assert.True(engineCompleted, "blocking on the engine's deep twin run deadlocked");
        Assert.True(outcome!.Value.IsOk, outcome.Value.IsError ? outcome.Value.Error.ToString() : null);
        Assert.Equal(new Result.Atom(120), outcome.Value.Value);
        Assert.Equal([120m], Assert.IsType<RunResult.Success>(engineOutcome).Atoms);
        Assert.True(run.BottomRanOnThePool, "the run never left the 1 MiB thread, so no hop was exercised");
        Assert.Equal(0, posts);
    }

    // ── Helpers ───────────────────────────────────────────────────────────────

    /// <summary>
    /// Runs <paramref name="body"/> once the current thread's stack is below the runtime's
    /// reserve, by recursing with a small stack allocation per level.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static T WithLowStack<T>(Func<T> body)
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return body();
        Span<byte> padding = stackalloc byte[512];
        padding[0] = 1;
        var result = WithLowStack(body);
        if (padding[0] != 1)
            throw new InvalidOperationException("unreachable: keeps the padding allocated across the call");
        return result;
    }

    /// <summary>
    /// A single-threaded <see cref="SynchronizationContext"/>: posted callbacks run only on the
    /// thread that pumps it, like a UI thread's, and it counts every post.
    /// </summary>
    private sealed class SingleThreadedContext : SynchronizationContext
    {
        private readonly BlockingCollection<(SendOrPostCallback Callback, object? State)> _queue = [];
        private int _posts;

        public int Posts => Volatile.Read(ref _posts);

        public override void Post(SendOrPostCallback d, object? state)
        {
            Interlocked.Increment(ref _posts);
            _queue.Add((d, state));
        }

        public override void Send(SendOrPostCallback d, object? state)
            => throw new NotSupportedException("The single-threaded test context accepts posts only.");

        public override SynchronizationContext CreateCopy() => this;

        /// <summary>Runs <paramref name="body"/> on the current thread with this context installed, pumping until it completes.</summary>
        public void Run(Func<Task> body, TimeSpan limit)
        {
            var previous = Current;
            SetSynchronizationContext(this);
            try
            {
                var clock = Stopwatch.StartNew();
                var task = body();
                while (!task.IsCompleted)
                {
                    if (_queue.TryTake(out var item, TimeSpan.FromMilliseconds(20)))
                        item.Callback(item.State);
                    else if (clock.Elapsed > limit)
                        throw new TimeoutException("The awaited run did not complete on the single-threaded context.");
                }

                task.GetAwaiter().GetResult();
            }
            finally
            {
                SetSynchronizationContext(previous);
            }
        }
    }
}
