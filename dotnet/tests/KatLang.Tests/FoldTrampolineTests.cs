using System.Runtime.CompilerServices;
using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// A GENERAL lazy <c>reduce</c> fold makes progress on ONE thread with a BOUNDED native stack (single-thread fold
/// progress, November 2026; C#-only host execution under Q-09a, <see cref="FoldTrampoline"/>). A fold whose reducer
/// uses every accumulator holds one suspended step per element. The synchronous evaluator keeps at most
/// <see cref="FoldTrampoline.HostStackAllowance"/> of them on the host stack and continues the chain on the heap,
/// pumped on the calling thread; the asynchronous twins keep every one of them on the heap through the same
/// trampoline. No thread is started and nothing waits for another thread, so the issue's programs complete on a
/// single-threaded worker, whose 1 MiB stack the tests stand in for.
/// <para>The semantic checks compare long folds — longer than the host stack's allowance — on the six established
/// routes (<see cref="SixRouteAgreement"/>: the synchronous engine, the Playground-shaped asynchronous engine that
/// completes inline, the engine's genuinely suspending twin, the generic and optimized evaluators and the forced
/// twin) with each other and with the explicitly nested ordinary calls over the already evaluated elements, which
/// are the fold's meaning (<c>reduce([a, b], R, i)</c> is <c>R(b, R(a, i))</c> in value and in demand).</para>
/// </summary>
public sealed class FoldTrampolineTests
{
    private const int OneMiB = 1024 * 1024;
    private const int Long = 10_000;

    // Every bounded wait in this file is a hang guard, never a latency claim.
    private static readonly TimeSpan WaitLimit = TimeSpan.FromMinutes(5);

    // The issue's program A (a maximum through a conditional), program B (sum and count through a structural
    // accumulator pattern), and a general reducer that calls the host before and after its accumulator read.
    private static string ProgramA(int count) => $"R(item, acc) = if(item > acc, item, acc)\nreduce(range(1, {count}), R, 0)";

    private static string ProgramB(int count) => $"Step(x, (total, n)) = total + x, n + 1\nreduce(range(1, {count}), Step, (0, 0))";

    private static string Effectful(int count) => $"R(item, acc) = mark(item) + acc + 0 * mark(0 - item)\nreduce(range(1, {count}), R, 0)";

    private static string Sum(long count) => (count * (count + 1) / 2).ToString();

    private static string Expected(string program, int count) => program switch
    {
        "A" => count.ToString(),
        "B" => $"S[{Sum(count)}, {count}]",
        _ => Sum(count),
    };

    private static string Source(string program, int count) => program switch
    {
        "A" => ProgramA(count),
        "B" => ProgramB(count),
        _ => Effectful(count),
    };

    // ── Single-thread progress ─────────────────────────────────────────────────────────────────────────────

    /// <summary>The host operation <c>mark(x)</c>, recording each call's argument and thread.</summary>
    private sealed class Marks
    {
        public List<(int Item, int Thread)> Calls { get; } = [];

        public HostOperations Operations()
            => HostOperations.Create(HostOperation.Create("mark", (args, _) =>
            {
                lock (Calls) Calls.Add(((int)((Result.Atom)args[0]).Value, Environment.CurrentManagedThreadId));
                return args[0];
            }, "x"));
    }

    // Runs `body` on a fresh thread with a 1 MiB stack, the stack of a browser worker, and returns its value.
    private static T OnOneMebibyteThread<T>(Func<T> body)
    {
        T result = default!;
        Exception? failure = null;
        var thread = new Thread(() =>
        {
            try { result = body(); }
            catch (Exception error) { failure = error; }
        }, OneMiB) { IsBackground = true };
        thread.Start();
        Assert.True(thread.Join(WaitLimit), "the fold did not finish");
        if (failure is not null) throw new InvalidOperationException("the run failed on its thread", failure);
        return result;
    }

    /// <summary>
    /// A, B and the effectful fold at 10,000 elements, entered through <see cref="KatLangEngine.Run"/> and through
    /// the Playground's call shape of <see cref="KatLangEngine.RunAsync(string, RunOptions?)"/> (a module downloader,
    /// both cancellation tokens; the program needs no download and no asynchronous operation, so the run completes
    /// inline). Each completes on its 1 MiB thread with the right value; the effectful fold's host calls run on that
    /// thread, one at a time, in the nested order (every descent call, last element first, then every ascent call);
    /// at least one synchronous pump continued a chain on the heap; and no pump ever waited for work from another
    /// thread. A synchronous pump with no ready work and an unfinished segment fails immediately
    /// (<see cref="FoldTrampoline.StalledPumps"/>).
    /// </summary>
    [Theory]
    [InlineData("A", false)]
    [InlineData("A", true)]
    [InlineData("B", false)]
    [InlineData("B", true)]
    [InlineData("Effectful", false)]
    [InlineData("Effectful", true)]
    public void IssuePrograms_CompleteOnTheCallingOneMebibyteThread(string program, bool playgroundRunAsync)
    {
        var marks = new Marks();
        var source = Source(program, Long);
        Assert.False(Parser.Parse(source, new RunOptions { HostOperations = marks.Operations() }).HasErrors);
        var pumpsBefore = FoldTrampoline.Pumps;
        var waitsBefore = FoldTrampoline.StalledPumps;

        var (result, calling) = OnOneMebibyteThread(() =>
        {
            var thread = Environment.CurrentManagedThreadId;
            if (!playgroundRunAsync)
                return (KatLangEngine.Run(source, new RunOptions { HostOperations = marks.Operations() }), thread);

            using var sourceCancellation = new CancellationTokenSource();
            using var evaluationCancellation = new CancellationTokenSource();
            var pending = KatLangEngine.RunAsync(source, new RunOptions
            {
                HostOperations = marks.Operations(),
                DownloadCode = static (_, _) => throw new InvalidOperationException("no module is loaded"),
                SourceProcessingCancellationToken = sourceCancellation.Token,
                EvaluationCancellationToken = evaluationCancellation.Token,
            });
            // The run completed inline on this thread: the task is complete when RunAsync returns.
            Assert.True(pending.IsCompleted, "RunAsync did not complete inline");
            return (pending.GetAwaiter().GetResult(), thread);
        });

        Assert.Equal(Expected(program, Long), SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(result).Value));
        Assert.True(FoldTrampoline.Pumps > pumpsBefore, "the chain never continued on the heap");
        Assert.Equal(waitsBefore, FoldTrampoline.StalledPumps);
        if (program != "Effectful")
            return;

        var descent = Enumerable.Range(1, Long).Reverse();
        var ascent = Enumerable.Range(1, Long).Select(static item => -item);
        Assert.Equal(descent.Concat(ascent), marks.Calls.Select(static call => call.Item));
        Assert.All(marks.Calls, call => Assert.True(call.Thread == calling, $"mark({call.Item}) ran on thread {call.Thread}"));
    }

    /// <summary>
    /// The genuinely asynchronous entry: <see cref="KatLangEngine.RunAsync(string, RunOptions?)"/> with an
    /// asynchronous host operation that yields before it answers, on both sides of every accumulator read. The
    /// twin route keeps every suspended step on the heap through the fold's trampoline; after each genuine
    /// suspension the chain resumes where the host's awaitable completes. The calls stay one at a time and in the
    /// nested order, and the value is the fold's.
    /// </summary>
    [Fact]
    public async Task GenuinelySuspendingSteps_KeepTheNestedOrder_OnTheAsynchronousEntry()
    {
        var calls = new List<int>();
        var active = 0;
        var overlapped = false;
        var operations = HostOperations.Create(HostOperation.CreateAsync("mark", async (args, _) =>
        {
            if (Interlocked.Increment(ref active) != 1) overlapped = true;
            await Task.Yield();
            lock (calls) calls.Add((int)((Result.Atom)args[0]).Value);
            Interlocked.Decrement(ref active);
            return args[0];
        }, "x"));
        var source = Effectful(Long);
        Assert.False(Parser.Parse(source, new RunOptions { HostOperations = operations }).HasErrors);

        var result = await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations }).WaitAsync(WaitLimit);

        Assert.Equal(Sum(Long), SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(result).Value));
        Assert.False(overlapped, "two host calls overlapped");
        Assert.Equal(Enumerable.Range(1, Long).Reverse().Concat(Enumerable.Range(1, Long).Select(static item => -item)), calls);
    }

    /// <summary>A host's own synchronization context (a UI thread's, a test framework's), counting its posts.</summary>
    private sealed class HostSynchronizationContext : SynchronizationContext
    {
        public int Posts;

        public override void Post(SendOrPostCallback callback, object? state)
        {
            Interlocked.Increment(ref Posts);
            base.Post(callback, state);
        }
    }

    /// <summary>
    /// A host with its own synchronization context and task scheduler keeps the fold on its thread. The
    /// evaluator posts to its private pump. Neither the host's scheduler nor the thread pool does fold work.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void HostSynchronizationContext_KeepsTheHeapChainOnTheCallingThread(bool forceTwin)
    {
        var marks = new Marks();
        var context = new HostSynchronizationContext();
        var waitsBefore = FoldTrampoline.StalledPumps;

        var (result, calling, after) = OnOneMebibyteThread(() =>
        {
            SynchronizationContext.SetSynchronizationContext(context);
            var task = new Task<RunResult>(() =>
            {
                var operations = marks.Operations();
                if (!forceTwin) return KatLangEngine.Run(Effectful(Long), new RunOptions { HostOperations = operations });
                var options = new RunOptions { HostOperations = HostOperations.Create(
                    operations.Operations.Single(), HostOperation.CreateAsync("unused", (_, _) => throw new InvalidOperationException())) };
                var pending = KatLangEngine.RunAsync(Effectful(Long), options);
                Assert.True(pending.IsCompleted, "The ready fold handed work off its thread.");
                return pending.GetAwaiter().GetResult();
            });
            task.RunSynchronously(TaskScheduler.FromCurrentSynchronizationContext());
            return (task.GetAwaiter().GetResult(), Environment.CurrentManagedThreadId, SynchronizationContext.Current);
        });

        Assert.Equal(Sum(Long), SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(result).Value));
        Assert.Equal(2 * Long, marks.Calls.Count);
        Assert.All(marks.Calls, call => Assert.True(call.Thread == calling, $"mark({call.Item}) ran on thread {call.Thread}"));
        Assert.Equal(0, context.Posts);
        Assert.Equal(waitsBefore, FoldTrampoline.StalledPumps);
        Assert.Same(context, after);
    }

    /// <summary>
    /// A host operation inside a heap step that starts a run of its own: that nested run's long fold continues on
    /// the heap too, pumped on the same thread inside the outer pump — no work of one run reaches the other's
    /// trampoline — so both complete on the 1 MiB thread. Kept in place instead, the nested fold's 10,000 steps
    /// would exhaust the stack that the outer fold's pump runs on.
    /// </summary>
    [Fact]
    public void NestedRunInsideAHeapStep_ContinuesItsOwnFoldOnTheHeap()
    {
        string? inner = null;
        var operations = HostOperations.Create(HostOperation.Create("inner", (args, _) =>
        {
            inner = SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(KatLangEngine.Run(ProgramA(Long))).Value);
            return args[0];
        }, "x"));
        // The step for 1, the deepest of the chain, runs on the heap and calls the host.
        var source = $"R(item, acc) = if(item == 1, inner(item), acc + item)\nreduce(range(1, {Long}), R, 0)";
        Assert.False(Parser.Parse(source, new RunOptions { HostOperations = operations }).HasErrors);
        var waitsBefore = FoldTrampoline.StalledPumps;

        var result = OnOneMebibyteThread(() => KatLangEngine.Run(source, new RunOptions { HostOperations = operations }));

        Assert.Equal(Sum(Long), SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(result).Value));
        Assert.Equal(Long.ToString(), inner);
        Assert.Equal(waitsBefore, FoldTrampoline.StalledPumps);
    }

    // A zero-argument property's read and fresh invocation straddle a pumped accumulator demand.
    [Theory]
    [InlineData("P + acc", "4", 2)]
    [InlineData("acc + P", "3", 1)]
    public void HeapStepsAndSynchronousCaller_SharePropertyPublications(string outer, string expected, int calls)
    {
        var invoked = 0;
        var operations = HostOperations.Create(HostOperation.Create("next", (_, _) => new Result.Atom(++invoked)));
        var source = $"P = next()\nR(item, acc) = if(item == 100, {outer}, if(item == 1, P() + P, acc))\nreduce(range(1, 100), R, 0)";
        var result = KatLangEngine.Run(source, new RunOptions { HostOperations = operations });
        Assert.Equal(expected, SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(result).Value));
        Assert.Equal(calls, invoked);
    }

    [Theory]
    [InlineData("reduce([1], S, 0)", true)]
    [InlineData("reduce([1, 2], Stream, 0)", true)]
    [InlineData("first([enter(0)])", true)]
    [InlineData("first(map([1], Callback))", true)]
    [InlineData("Pattern((enter(0), 1))", true)]
    [InlineData("[enter(0)][0]", true)]
    [InlineData("if(true, enter(0), 0)", false)]
    [InlineData("Plain(0)", false)]
    public void HeapCallbacks_MatchOrdinaryHostContextBoundaries(string inner, bool restoresOuter)
    {
        const int count = 100;
        var ambient = new AsyncLocal<int>();
        var observed = new List<int>();
        var operations = HostOperations.Create(
            HostOperation.Create("enter", (args, _) =>
            {
                ambient.Value = (int)((Result.Atom)args[0]).Value;
                return args[0];
            }, "x"),
            HostOperation.Create("observe", (_, _) =>
            {
                observed.Add(ambient.Value);
                return new Result.Atom(0);
            }, "x"));
        var source = "S(x,a) = enter(0)\nStream(x,a) = a + enter(0)\nCallback(x) = enter(0)\nPlain(x) = enter(0)\nPattern((x,y)) = x\n"
            + $"R(item, acc) = enter(item) + {inner} + acc + observe(item)\nreduce(range(1,{count}), R, 0)";
        var run = KatLangEngine.Run(source, new RunOptions { HostOperations = operations });
        Assert.Equal(Sum(count), SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(run).Value));
        Assert.Equal(restoresOuter ? Enumerable.Range(1, count) : Enumerable.Repeat(0, count), observed);
    }

    // ── A bounded native stack ─────────────────────────────────────────────────────────────────────────────

    // A fixed address to measure stack positions from (only differences of two readings on one thread count).
    [FixedAddressValueType] private static byte s_anchor = 0;

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static nint StackPosition()
    {
        byte marker = 0;
        return Unsafe.ByteOffset(ref s_anchor, ref marker);
    }

    /// <summary>
    /// The deepest host call of a fold, in bytes of native stack below the frame that started the run, and the
    /// run's budget, for a general fold of <paramref name="count"/> steps on a 1 MiB thread. The reducer calls the
    /// host before and after its accumulator read, so the deepest point of every step is observed.
    /// </summary>
    private static (long DeepestCall, EvaluationBudget Budget) ObserveDepth(int count)
    {
        var source = $"R(item, acc) = depth(item) + acc + 0 * depth(item)\nreduce(range(1, {count}), R, 0)";
        return OnOneMebibyteThread(() =>
        {
            var origin = StackPosition();
            long deepest = 0;
            var operations = HostOperations.Create(HostOperation.Create("depth", (args, _) =>
            {
                deepest = Math.Max(deepest, origin - StackPosition());
                return args[0];
            }, "x"));
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors);
            var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations);
            Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
            Assert.Equal(Sum(count), SixRouteAgreement.Neutral(result.Value.Value));
            return (deepest, budget!);
        });
    }

    /// <summary>
    /// The native stack of a general fold is bounded, whatever its length. Deterministically: a fold of 100 steps
    /// and one of 10,000 both suspend every step (one fold continuation per element, the start included), both keep
    /// a few of them on the host stack — never more than <see cref="FoldTrampoline.HostStackAllowance"/>, whatever
    /// the length — and run the rest as heap segments of the fold's trampoline. Directly: the deepest host call of
    /// the 10,000-step fold is no deeper than that of the 100-step fold, give or take a slack for frames the runtime
    /// may tier to a different size between the two runs (a few KiB a step); nested, the 9,900 further suspended
    /// steps alone would need tens of megabytes.
    /// </summary>
    [Fact]
    public void GeneralFold_KeepsABoundedNativeStack_HoweverLong()
    {
        var (shallowCall, shallow) = ObserveDepth(100);
        var (deepCall, deep) = ObserveDepth(Long);

        Assert.Equal(100, shallow.PeakFoldContinuations);
        Assert.Equal(Long, deep.PeakFoldContinuations);
        Assert.InRange(shallow.PeakHostStackFoldContinuations, 1, FoldTrampoline.HostStackAllowance);
        Assert.InRange(deep.PeakHostStackFoldContinuations, 1, FoldTrampoline.HostStackAllowance);
        // Every accumulator beyond the host stack's part of the chain is a heap segment.
        Assert.InRange(shallow.HeapFoldSegments, 100 - FoldTrampoline.HostStackAllowance, 100);
        Assert.InRange(deep.HeapFoldSegments, Long - FoldTrampoline.HostStackAllowance, Long);
        Assert.True(deepCall <= shallowCall + 64 * 1024,
            $"the deepest host call of {Long} steps is {deepCall} bytes below the run's frame, of 100 steps {shallowCall}");
        Assert.Equal(0, deep.ActiveFoldContinuations);
        Assert.Equal(0, deep.CurrentDepth);
    }

    /// <summary>
    /// Genuine recursion inside a reducer keeps its ordinary depth check where its fold runs on the heap: the fold's
    /// continuations add no depth, but a reducer that calls itself without end still reaches the depth limit, at
    /// whatever step of a long fold it is demanded.
    /// </summary>
    [Fact]
    public void GenuineRecursionInsideAHeapStep_StillReachesTheDepthLimit()
    {
        var source = "Deep(n) = Deep(n + 1) + 1\nR(item, acc) = if(item == 1, Deep(0), acc + item)\n"
            + $"reduce(range(1, {Long}), R, 0)";
        var result = OnOneMebibyteThread(() => KatLangEngine.Run(source));

        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Contains(failure.Errors, static error => error.Code is KatLangErrorCode.EvaluationDepthExceeded or KatLangErrorCode.EvaluationStackExhausted);
    }

    // ── Demand and effect order on every route, against the nested calls ───────────────────────────────────

    private const int Elements = 40;

    // `R(40, R(39, … R(1, initial)…))`: the fold of [1, 2, …, 40] written as nested ordinary calls over the
    // already evaluated elements.
    private static string Nested(string reducer, string initial)
    {
        var call = initial;
        for (var item = 1; item <= Elements; item++)
            call = $"R({item}, {call})";
        return reducer + "\n" + call;
    }

    private static string Fold(string reducer, string initial) => reducer + $"\nreduce(range(1, {Elements}), R, {initial})";

    /// <summary>reducer, initial, expected value, expected host-call log (hand-checked).</summary>
    public static TheoryData<string, string, string, string> NestedOrderCases()
    {
        var descent = string.Join(",", Enumerable.Range(1, Elements).Reverse().Select(static item => $"trace({item})"));
        var ascent = string.Join(",", Enumerable.Range(1, Elements).Select(static item => $"trace({100 + item})"));
        var bothSidesValue = Enumerable.Range(1, Elements).Sum(static item => 2 * item + 100).ToString();
        // R(item, acc) = trace(item) + acc + acc from 0: a(1) = 1, a(n) = n + 2 a(n - 1).
        long twice = 0;
        for (var item = 1; item <= Elements; item++)
            twice = item + 2 * twice;
        // The clause family from 0: a(1) = 1 (the literal clause), a(n) = a(n - 1) + 2 n + 100 (the general one).
        var familyValue = (1 + Enumerable.Range(2, Elements - 1).Sum(static item => 2 * item + 100)).ToString();
        var familyCalls = string.Join(",", Enumerable.Range(2, Elements - 1)
            .SelectMany(static item => new[] { $"trace({item})", $"trace({100 + item})" }).Prepend("trace(1)"));
        return new()
        {
            // An effect on both sides of the accumulator read: every step's first call on the way down, last
            // element first; every step's second call on the way up, first element first.
            { "R(item, acc) = trace(item) + acc + trace(100 + item)", "0", bothSidesValue, descent + "," + ascent },
            // The step for 5 ignores its accumulator: the steps for 1 to 4 and the failing initial never run.
            {
                "R(item, acc) = if(item == 5, trace(item), trace(item) + acc)", "1 / 0",
                Enumerable.Range(5, Elements - 4).Sum().ToString(),
                string.Join(",", Enumerable.Range(5, Elements - 4).Reverse().Select(static item => $"trace({item})"))
            },
            // An accumulator read twice is evaluated once: each step runs once, its effect once.
            { "R(item, acc) = trace(item) + acc + acc", "0", twice.ToString(), descent },
            // A clause family as the reducer: each step's dispatch tests the accumulator against the literal clause
            // before the step's own calls, so the descent has no effect and the ascent makes every call; only the
            // step for 1 meets the initial 0.
            { "R(item, 0) = trace(item)\nR(item, acc) = trace(item) + acc + trace(100 + item)", "0", familyValue, familyCalls },
        };
    }

    /// <summary>
    /// A builtin reducer (<c>contains</c>) over a long fold: each step is the builtin's ordinary call,
    /// which demands the accumulator as its item, so every step waits for the one before it, and the traced initial
    /// value is evaluated once, at the bottom of the chain — where the genuinely suspending routes suspend every step
    /// at once. The value alternates with each step; every route agrees with the explicitly nested builtin calls.
    /// </summary>
    [Fact]
    public async Task LongFoldWithABuiltinReducer_IsTheNestedCalls_OnEveryRoute()
    {
        var call = "trace(false)";
        for (var item = 1; item <= Elements; item++)
            call = $"contains([{item}, false], {call})";
        var nested = await SixRouteAgreement.OnEveryRouteAsync(call);
        var fold = await SixRouteAgreement.OnEveryRouteAsync(
            $"E(i) = [i, false]\nreduce(map(range(1, {Elements}), E), contains, trace(false))");

        // contains([k, false], false) is true and contains([k, false], true) is false: step k's value is k odd.
        Assert.Equal(("ok", Elements % 2 == 1 ? "true" : "false", "trace(false)"), (fold.Kind, fold.Value, string.Join(",", fold.HostCalls)));
        Assert.Equal((nested.Kind, nested.Value, string.Join(",", nested.HostCalls)), (fold.Kind, fold.Value, string.Join(",", fold.HostCalls)));
    }

    [Theory]
    [MemberData(nameof(NestedOrderCases))]
    public async Task LongFold_IsTheNestedCalls_InValueAndEffectOrder_OnEveryRoute(string reducer, string initial, string value, string hostCalls)
    {
        var nested = await SixRouteAgreement.OnEveryRouteAsync(Nested(reducer, initial));
        var fold = await SixRouteAgreement.OnEveryRouteAsync(Fold(reducer, initial));

        Assert.Equal(("ok", value, hostCalls), (fold.Kind, fold.Value, string.Join(",", fold.HostCalls)));
        Assert.Equal((nested.Kind, nested.Value, string.Join(",", nested.HostCalls)), (fold.Kind, fold.Value, string.Join(",", fold.HostCalls)));
    }

    /// <summary>
    /// A step limit that runs out inside a long fold stops every route at the same point: the same error code,
    /// message and position, and exactly the same host calls before it — the calls of the descent, of the ascent,
    /// or of both, wherever the limit falls.
    /// </summary>
    [Fact]
    public async Task StepLimitInsideALongFold_StopsEveryRouteAfterTheSameEffects()
    {
        var source = Fold("R(item, acc) = trace(item) + acc + trace(100 + item)", "0");
        var operations = HostOperations.Create(HostOperation.Create("trace", (args, _) => args[0], "x"));
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);
        var (unlimited, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations);
        Assert.True(unlimited.IsOk);
        var total = budget.ConsumedSteps;
        var full = (await SixRouteAgreement.OnEveryRouteAsync(source)).HostCalls;

        var stopped = new HashSet<int>();
        foreach (var limit in new[] { total / 4, total / 2, 3 * total / 4, total - 2 })
        {
            var observation = await SixRouteAgreement.OnEveryRouteAsync(source, limits: new EvaluationLimits { MaxSteps = limit });
            Assert.Equal("err", observation.Kind);
            Assert.StartsWith(nameof(KatLangErrorCode.EvaluationStepLimitExceeded) + ":", observation.Errors[0], StringComparison.Ordinal);
            // The effects before the stop are a prefix of the unlimited run's.
            Assert.Equal(full.Take(observation.HostCalls.Count), observation.HostCalls);
            stopped.Add(observation.HostCalls.Count);
        }

        // The limits fall at different points of the fold.
        Assert.True(stopped.Count > 1, string.Join(",", stopped));
    }
}
