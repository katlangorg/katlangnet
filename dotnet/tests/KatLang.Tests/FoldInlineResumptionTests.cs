using System.Reflection;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// INLINE RESUMPTIONS of pumped fold steps (the cost of a heap step, November 2026; C#-only host execution under
/// Q-09a, <see cref="FoldTrampoline"/>). A synchronous pump that starts under the default task scheduler with the
/// stack headroom its deepest admitted completion cascade needs runs its work with no synchronization context, and
/// a step suspended from the pump's own segment start registers its frames' continuations directly, within
/// <see cref="FoldTrampoline.InlineResumeByteAllowance"/> and <see cref="FoldTrampoline.InlineResumeFrameAllowance"/>
/// of its accumulator demand; the runtime resumes them in the pump's completion cascade. Every other suspension
/// captures a pump context: the cascading one where no inline frame waits above (its frames resume one inside the
/// other, as in every other pump), the per-frame one below the inline frames of a resumed step that suspends again.
/// The mechanism changes where a frame resumes, never what it computes: these tests pin the counts of each kind of
/// unwinding and of trips through the queue (deterministic per program), the continuation objects it saves, the
/// posting fallbacks, and agreement with a pump that withholds inline resumptions (<see cref="FoldResumeTestSeam"/>),
/// on the calling thread throughout.
/// </summary>
public sealed class FoldInlineResumptionTests
{
    private const int OneMiB = 1024 * 1024;
    private const int Long = 10_000;

    // Every bounded wait in this file is a hang guard, never a latency claim.
    private static readonly TimeSpan WaitLimit = TimeSpan.FromMinutes(5);

    // The issue's program A: a maximum through a conditional, about eighteen suspended frames per step.
    private static string ProgramA(int count) => $"R(item, acc) = if(item > acc, item, acc)\nreduce(range(1, {count}), R, 0)";

    // A host call on both sides of the accumulator read.
    private static string Traced(int count) => $"R(item, acc) = mark(item) + acc + 0 * mark(0 - item)\nreduce(range(1, {count}), R, 0)";

    // The accumulator is read under five levels of a user recursion, so a step's suspended frames reach far beyond the
    // inline byte allowance above its demand.
    private static string DeepRead(int count)
        => $"D(k, a) = if(k == 0, a, D(k - 1, a))\nR(item, acc) = mark(item) + D(5, acc) + 0 * mark(0 - item)\nreduce(range(1, {count}), R, 0)";

    // A clause family as the reducer, whose dispatch tests the accumulator against its literal clause first.
    private static string FamilyReducer(int count)
        => $"R(item, 0) = mark(item)\nR(item, acc) = mark(item) + acc + 0 * mark(0 - item)\nreduce(range(1, {count}), R, 0)";

    // A builtin reducer: `contains` over the lists `[i, false]`, whose item is the accumulator, from a traced `false`.
    private static string BuiltinReducer(int count)
        => $"E(i) = [i, false]\nreduce(map(range(1, {count}), E), contains, mark(0) > 0)";

    private static string Sum(long count) => (count * (count + 1) / 2).ToString();

    // The nested order of the traced programs' host calls: every descent call, last element first, then every
    // ascent call, first element first.
    private static IEnumerable<int> NestedOrder(int count)
        => Enumerable.Range(1, count).Reverse().Concat(Enumerable.Range(1, count).Select(static item => -item));

    private sealed record Observed(
        string Value, EvaluationBudget Budget, IReadOnlyList<(int Item, int Thread)> Calls, int Thread, long AllocatedBytes);

    /// <summary>A scheduler that runs a task inline on the calling thread and refuses to queue one.</summary>
    private sealed class InlineOnlyScheduler : TaskScheduler
    {
        protected override IEnumerable<Task> GetScheduledTasks() => [];

        protected override void QueueTask(Task task) => throw new InvalidOperationException("work was queued to the host's scheduler");

        protected override bool TryExecuteTaskInline(Task task, bool taskWasPreviouslyQueued) => TryExecuteTask(task);
    }

    // Runs `source` through the counted synchronous evaluator on a fresh thread with the given stack (optionally inside a
    // task on a custom scheduler, optionally with inline resumptions withheld), with the host operation `mark(x)`
    // recording each call's argument and thread, and the bytes the run allocated on that thread.
    private static Observed Run(string source, int stackBytes, bool withholdInline = false, bool customScheduler = false)
    {
        Observed? observed = null;
        Exception? failure = null;
        var thread = new Thread(() =>
        {
            try
            {
                Observed Evaluate()
                {
                    var calls = new List<(int, int)>();
                    var operations = HostOperations.Create(HostOperation.Create("mark", (args, _) =>
                    {
                        calls.Add(((int)((Result.Atom)args[0]).Value, Environment.CurrentManagedThreadId));
                        return args[0];
                    }, "x"));
                    var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
                    Assert.False(parsed.HasErrors);
                    var program = new Expr.AlgorithmExpr(parsed.Root);
                    using var seam = withholdInline ? FoldResumeTestSeam.Activate() : null;
                    var before = GC.GetAllocatedBytesForCurrentThread();
                    var (result, budget) = Evaluator.RunCountedObserved(program, hostOperations: operations);
                    var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
                    Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
                    return new Observed(SixRouteAgreement.Neutral(result.Value.Value), budget!, calls, Environment.CurrentManagedThreadId, allocated);
                }

                // glibc can reuse a larger stack. Keep the requested headroom while the fold runs.
                AstStructuralDepthProcessTests.RunBelowExcessStack(stackBytes, () =>
                {
                    if (customScheduler)
                    {
                        var task = new Task<Observed>(Evaluate);
                        task.RunSynchronously(new InlineOnlyScheduler());
                        observed = task.GetAwaiter().GetResult();
                    }
                    else
                    {
                        observed = Evaluate();
                    }
                });
            }
            catch (Exception error)
            {
                failure = error;
            }
        }, stackBytes) { IsBackground = true };
        thread.Start();
        Assert.True(thread.Join(WaitLimit), "the fold did not finish");
        if (failure is not null) throw new InvalidOperationException("the run failed on its thread", failure);
        return observed!;
    }

    /// <summary>
    /// Program A at 10,000 elements on a 1 MiB thread: all but a few steps run as heap segments of the pump, and every
    /// heap step that demands an accumulator — all but the segment of the start — suspends with inline resumptions,
    /// none of them cut by the allowances (a step of program A suspends a few tens of KiB of frames above its demand).
    /// </summary>
    [Fact]
    public void PumpedSteps_SuspendWithInlineResumptions_OnAOneMebibyteThread()
    {
        var run = Run(ProgramA(Long), OneMiB);

        Assert.Equal(Long.ToString(), run.Value);
        Assert.InRange(run.Budget.HeapFoldSegments, Long - FoldTrampoline.HostStackAllowance, Long);
        Assert.Equal(run.Budget.HeapFoldSegments - 1, run.Budget.InlineFoldUnwindings);
        Assert.Equal(0, run.Budget.InlineFoldUnwindingCuts);
        Assert.Equal(0, run.Budget.PostedFoldUnwindings);
        Assert.Equal(0, run.Budget.PostedFoldResumptions);
        Assert.Equal(0, run.Budget.ActiveFoldContinuations);
    }

    /// <summary>
    /// What inline resumptions save: a posted resumption costs each suspended frame a continuation object and a
    /// delegate (about a hundred bytes on x64), and program A suspends about eighteen frames per heap step. The same
    /// fold with inline resumptions withheld allocates at least 1 KiB more per heap step, on the same thread, with the
    /// same value and the same heap segments.
    /// </summary>
    [Fact]
    public void InlineResumptions_SaveEachSuspendedFrameItsContinuationObjects()
    {
        const int count = 2_000;
        // A first run tiers code and sizes caches for both runs.
        Run(ProgramA(count), OneMiB);
        var inline = Run(ProgramA(count), OneMiB);
        var posted = Run(ProgramA(count), OneMiB, withholdInline: true);

        Assert.Equal(posted.Value, inline.Value);
        Assert.Equal(posted.Budget.HeapFoldSegments, inline.Budget.HeapFoldSegments);
        Assert.Equal(0, posted.Budget.InlineFoldUnwindings);
        Assert.Equal(inline.Budget.HeapFoldSegments - 1, inline.Budget.InlineFoldUnwindings);
        var savedPerHeapStep = (posted.AllocatedBytes - inline.AllocatedBytes) / (double)inline.Budget.HeapFoldSegments;
        Assert.True(savedPerHeapStep >= 1024, $"inline resumptions saved {savedPerHeapStep:F0} bytes per heap step");
    }

    /// <summary>
    /// Inline and posted resumptions are the same evaluation: a fold with host calls on both sides of its accumulator
    /// read produces the same value, the same host calls in the nested order, all on the calling thread, and the same
    /// step and expression checkpoints, heap segments and suspended continuations either way.
    /// </summary>
    [Fact]
    public void InlineAndPostedResumptions_AreTheSameEvaluation()
    {
        const int count = 2_000;
        var inline = Run(Traced(count), OneMiB);
        var posted = Run(Traced(count), OneMiB, withholdInline: true);

        Assert.Equal(Sum(count), inline.Value);
        Assert.Equal(posted.Value, inline.Value);
        Assert.Equal(NestedOrder(count), inline.Calls.Select(static call => call.Item));
        Assert.Equal(posted.Calls.Select(static call => call.Item), inline.Calls.Select(static call => call.Item));
        Assert.All(inline.Calls, call => Assert.Equal(inline.Thread, call.Thread));
        Assert.All(posted.Calls, call => Assert.Equal(posted.Thread, call.Thread));
        Assert.Equal(posted.Budget.ConsumedSteps, inline.Budget.ConsumedSteps);
        Assert.Equal(posted.Budget.ConsumedExpressionCheckpoints, inline.Budget.ConsumedExpressionCheckpoints);
        Assert.Equal(posted.Budget.HeapFoldSegments, inline.Budget.HeapFoldSegments);
        Assert.Equal(posted.Budget.PeakFoldContinuations, inline.Budget.PeakFoldContinuations);
        Assert.True(inline.Budget.InlineFoldUnwindings > 0);
        Assert.Equal(0, posted.Budget.InlineFoldUnwindings);
    }

    /// <summary>
    /// A step whose suspended frames reach beyond the inline byte allowance above its demand keeps inline resumptions
    /// for the frames within it and posts the rest through the pump's queue: every such heap step is cut, and every
    /// frame above the cut — not only the first, since the method builder restores each frame's caller's context
    /// when the frame suspends — captures the pump's cascading context. So each cut step makes exactly one trip
    /// through the queue (its lowest posting frame, whose inline child completes with no context current), and the
    /// frames above it resume one inside the other from there. The fold completes on the calling thread with its
    /// host calls in the nested order.
    /// </summary>
    [Fact]
    public void DeepSuspensions_PostTheirFramesBeyondTheAllowance_OnTheCallingThread()
    {
        const int count = 300;
        var run = Run(DeepRead(count), 4 * OneMiB);

        Assert.Equal(Sum(count), run.Value);
        Assert.Equal(NestedOrder(count), run.Calls.Select(static call => call.Item));
        Assert.All(run.Calls, call => Assert.Equal(run.Thread, call.Thread));
        Assert.True(run.Budget.HeapFoldSegments > 0);
        Assert.Equal(run.Budget.HeapFoldSegments - 1, run.Budget.InlineFoldUnwindings);
        Assert.Equal(run.Budget.InlineFoldUnwindings, run.Budget.InlineFoldUnwindingCuts);
        Assert.Equal(run.Budget.InlineFoldUnwindingCuts, run.Budget.PostedFoldResumptions);
    }

    /// <summary>
    /// A pump that lacks the inline headroom below itself (a 512 KiB thread) posts every resumption, and so does a pump
    /// started inside a task of a host's own scheduler, where the runtime would not inline a completed task's
    /// continuation; both complete the long fold on the calling thread, and no work reaches the host's scheduler.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PumpsWithoutTheInlineConditions_PostEveryResumption(bool customScheduler)
    {
        var run = customScheduler ? Run(Traced(Long), OneMiB, customScheduler: true) : Run(Traced(Long), OneMiB / 2);

        Assert.Equal(Sum(Long), run.Value);
        Assert.Equal(NestedOrder(Long), run.Calls.Select(static call => call.Item));
        Assert.All(run.Calls, call => Assert.Equal(run.Thread, call.Thread));
        Assert.InRange(run.Budget.HeapFoldSegments, Long - FoldTrampoline.HostStackAllowance, Long);
        Assert.Equal(0, run.Budget.InlineFoldUnwindings);
    }

    /// <summary>
    /// Reducers whose steps are not a user algorithm's call — a clause family and a builtin — take the general route
    /// like program A, and their heap steps suspend through the same callback dispatch, which hands the step the
    /// family's or the builtin's own pending invocation. At 10,000 elements, on a 1 MiB thread with inline resumptions
    /// and with them withheld, and on a 512 KiB thread whose pump posts every resumption, each fold produces the nested
    /// evaluation's value and host calls on the calling thread, with the same heap segments, steps and checkpoints.
    /// </summary>
    [Theory]
    [InlineData("family", OneMiB)]
    [InlineData("family", OneMiB / 2)]
    [InlineData("builtin", OneMiB)]
    [InlineData("builtin", OneMiB / 2)]
    public void FamilyAndBuiltinReducers_SuspendThroughTheCallbackDispatch_OnEveryPump(string reducer, int stackBytes)
    {
        var family = reducer == "family";
        var source = family ? FamilyReducer(Long) : BuiltinReducer(Long);
        var run = Run(source, stackBytes);
        var withheld = Run(source, stackBytes, withholdInline: true);

        // The family: the dispatch reads every accumulator before its step's own calls, so the calls are the ascent's
        // alone; the step for 1 meets the initial 0. The builtin: contains([k, false], false) is true and
        // contains([k, false], true) is false, so step k's value is k odd, and the initial's call is the only one.
        Assert.Equal(family ? Sum(Long) : (Long % 2 == 1 ? "true" : "false"), run.Value);
        IEnumerable<int> calls = family ? Enumerable.Range(2, Long - 1).SelectMany(static item => new[] { item, -item }).Prepend(1) : [0];
        Assert.Equal(calls, run.Calls.Select(static call => call.Item));
        Assert.Equal(withheld.Value, run.Value);
        Assert.Equal(withheld.Calls.Select(static call => call.Item), run.Calls.Select(static call => call.Item));
        Assert.All(run.Calls, call => Assert.Equal(run.Thread, call.Thread));
        Assert.All(withheld.Calls, call => Assert.Equal(withheld.Thread, call.Thread));
        Assert.InRange(run.Budget.HeapFoldSegments, Long - FoldTrampoline.HostStackAllowance, Long);
        Assert.Equal(withheld.Budget.HeapFoldSegments, run.Budget.HeapFoldSegments);
        Assert.Equal(withheld.Budget.ConsumedSteps, run.Budget.ConsumedSteps);
        Assert.Equal(withheld.Budget.ConsumedExpressionCheckpoints, run.Budget.ConsumedExpressionCheckpoints);
        Assert.Equal(0, withheld.Budget.InlineFoldUnwindings);
        Assert.Equal(stackBytes == OneMiB ? run.Budget.HeapFoldSegments - 1 : 0, run.Budget.InlineFoldUnwindings);
        Assert.Equal(0, run.Budget.ActiveFoldContinuations);
    }

    /// <summary>
    /// The callback dispatch of a formed supply adds no frame to a suspended heap step: its asynchronous twin is not
    /// an async method, so a user algorithm's or a clause family's invocation is the step's own awaited computation,
    /// and only a builtin callee's result is finished in a frame of its own, once it has completed.
    /// </summary>
    [Fact]
    public void TheCallbackDispatchTwin_AddsNoFrameToASuspendedStep()
    {
        const BindingFlags flags = BindingFlags.NonPublic | BindingFlags.Static;
        var twin = typeof(Evaluator).GetMethod("EvalNeedCallbackSupplyAsync", flags)!;
        Assert.Equal(typeof(ValueTask<EvalResult<Evaluator.CountedResult>>), twin.ReturnType);
        Assert.Null(twin.GetCustomAttribute<AsyncStateMachineAttribute>());
        Assert.NotNull(typeof(Evaluator).GetMethod("NestMissingOutputAsync", flags)!.GetCustomAttribute<AsyncStateMachineAttribute>());
    }

    // A segment whose computation is the given asynchronous method.
    private sealed class TestSegment(Func<ValueTask<EvalResult<Evaluator.CountedResult>>> run) : FoldSegment
    {
        protected override ValueTask<EvalResult<Evaluator.CountedResult>> RunSegment() => run();
    }

    private static EvalResult<Evaluator.CountedResult> Number(int value)
        => EvalResult<Evaluator.CountedResult>.Ok(new Evaluator.CountedResult(new Result.Atom(value), 1));

    private static int NumberOf(EvalResult<Evaluator.CountedResult> result) => (int)((Result.Atom)result.Value.Value).Value;

    /// <summary>
    /// The one case where frames that registered inline wait above posting ones: a step resumed inline that
    /// suspends again. Directly on a pump (three frames, the innermost demanding a segment from the pump's own segment
    /// start, then, resumed, demanding another through a fourth frame): the first suspension is inline, the second a
    /// posting unwinding in work that inline frames wait above, so its frame captures the per-frame context and makes
    /// one trip through the queue, and the inline frames above then resume where the runtime inlines them — with no
    /// context current — on the calling thread. Resumed in the cascading context instead, they would be sent to the
    /// thread pool and the pump would stall.
    /// </summary>
    [Fact]
    public void AResumedInlineStepThatSuspendsAgain_PostsFrameByFrame_BelowItsInlineFrames()
    {
        Exception? failure = null;
        (EvalResult<Evaluator.CountedResult> Outcome, EvaluationBudget Budget, int Calling, List<int> Threads)? observed = null;
        var thread = new Thread(() =>
        {
            try
            {
                var budget = new EvaluationBudget(EvaluationLimits.Default);
                var trampoline = new FoldTrampoline(budget);
                var threads = new List<int>();

                async ValueTask<EvalResult<Evaluator.CountedResult>> Leaf()
                    => await trampoline.Demand(new TestSegment(() => new(Number(2)))).ConfigureAwait(FoldTrampoline.CaptureFoldContext);

                async ValueTask<EvalResult<Evaluator.CountedResult>> Inner()
                {
                    var first = await trampoline.Demand(new TestSegment(() => new(Number(1)))).ConfigureAwait(FoldTrampoline.CaptureFoldContext);
                    threads.Add(Environment.CurrentManagedThreadId);
                    var second = await Leaf().ConfigureAwait(FoldTrampoline.CaptureFoldContext);
                    threads.Add(Environment.CurrentManagedThreadId);
                    return Number(NumberOf(first) + NumberOf(second));
                }

                async ValueTask<EvalResult<Evaluator.CountedResult>> Middle()
                {
                    var result = await Inner().ConfigureAwait(FoldTrampoline.CaptureFoldContext);
                    threads.Add(Environment.CurrentManagedThreadId);
                    return result;
                }

                async ValueTask<EvalResult<Evaluator.CountedResult>> Outer()
                {
                    var result = await Middle().ConfigureAwait(FoldTrampoline.CaptureFoldContext);
                    threads.Add(Environment.CurrentManagedThreadId);
                    return result;
                }

                Assert.True(trampoline.TryRunSynchronously(new TestSegment(Outer), budget, out var outcome));
                observed = (outcome, budget, Environment.CurrentManagedThreadId, threads);
            }
            catch (Exception error)
            {
                failure = error;
            }
        }, OneMiB) { IsBackground = true };
        thread.Start();
        Assert.True(thread.Join(WaitLimit), "the pump did not finish");
        if (failure is not null) throw new InvalidOperationException("the pump failed on its thread", failure);

        var (result, budgetOf, calling, resumedOn) = observed!.Value;
        Assert.Equal(3, NumberOf(result));
        Assert.Equal(4, resumedOn.Count);
        Assert.All(resumedOn, id => Assert.Equal(calling, id));
        Assert.Equal(1, budgetOf.InlineFoldUnwindings);
        Assert.Equal(0, budgetOf.InlineFoldUnwindingCuts);
        Assert.Equal(1, budgetOf.PostedFoldUnwindings);
        Assert.Equal(1, budgetOf.PostedFoldResumptions);
    }

    /// <summary>
    /// A general fold inside a pumped step's reducer runs on a trampoline of its own, nested in the pump's work; its
    /// demands, and the outer accumulator its start reads, post their resumptions. The value is the nested evaluation's
    /// and every host call runs on the calling thread.
    /// </summary>
    [Fact]
    public void NestedGeneralFoldInsideAPumpedStep_PostsItsResumptions()
    {
        const int count = 400;
        var source = "Inner(x, a) = if(x > a, x, a)\n"
            + "R(item, acc) = mark(item) + reduce(range(1, 40), Inner, acc) + 0 * mark(0 - item)\n"
            + $"reduce(range(1, {count}), R, 0)";
        // a(n) = n + max(40, a(n - 1)) from a(0) = 0: a(1) = 41, and a(n) = n + a(n - 1) from there.
        var expected = ((long)count * (count + 1) / 2 + 40).ToString();
        var run = Run(source, OneMiB);
        var posted = Run(source, OneMiB, withholdInline: true);

        Assert.Equal(expected, run.Value);
        Assert.Equal(posted.Value, run.Value);
        Assert.Equal(NestedOrder(count), run.Calls.Select(static call => call.Item));
        Assert.All(run.Calls, call => Assert.Equal(run.Thread, call.Thread));
        Assert.Equal(posted.Budget.ConsumedSteps, run.Budget.ConsumedSteps);
        // The inner folds' demands inside the pump's work begin posting unwindings (a pump without inline
        // resumptions has nothing to switch). No inline frame waits above them, so their frames capture the pump's
        // cascading context and resume one inside the other, as in a pump without inline resumptions: none of them
        // makes a trip through the queue.
        Assert.True(run.Budget.PostedFoldUnwindings > 0);
        Assert.Equal(0, posted.Budget.PostedFoldUnwindings);
        Assert.Equal(0, run.Budget.PostedFoldResumptions);
        Assert.Equal(0, posted.Budget.PostedFoldResumptions);
    }
}
