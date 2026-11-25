using System.Text;
using KatLang.Evaluation;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// UNWINDING A DEEP FAILURE IS LINEAR IN ITS DEPTH on the asynchronous twin route (November 2026; C#
/// implementation only, no semantic change; the follow-up of audit finding 1 of the 2026-11-21
/// adversarial performance audit). Recursion routed through loop steps charges no depth, so on the twin
/// route — which continues on fresh stacks — a failure can leave thousands of levels, adding its context
/// frames at each. Each level asked whether the failure was terminal for the run
/// (<see cref="EvalError.IsTerminalForRun"/> before attaching a frame), whether it was an own missing
/// output (<see cref="Evaluator.NestMissingOutput"/>), and, completing a need cell, whether it was a
/// resource limit or the run's host-termination marker — and every answer walked the WHOLE chain grown so
/// far: about 1.5·F² frame reads for F frames, 4.5 to 5 s for 10,000 levels in Release, where the
/// successful control took 0.5 s. Each frame now records its chain's terminal when it is built
/// (<see cref="EvalError.WithContext"/>), so every answer is constant work.
///
/// <para>The gate is DETERMINISTIC work, never wall time: <see cref="ContextChainReadTestSeam"/> counts every
/// read of a frame's inner error in the run's flow — awaits, stack hops and the continuations of genuinely
/// suspending host operations included — so any walk of the chain is counted, apart from the frames the
/// run constructs. Across four depths of the forced twin, each control's evaluation reads the chain at
/// most once per level (in fact a constant: none, or the one nesting rebuild of a missing output), while
/// its frames, steps and checkpoints follow the linear prediction of two shallow synchronous runs and
/// formatting the failure reads each frame a bounded number of times. At safe depths the twin route
/// reports the generic and planned synchronous routes' result frame for frame (contexts, spans, terminal,
/// missing-output provenance, counters and message); the public asynchronous engine reports the same
/// failure. C# host execution only: Lean models neither the async surface nor host operations.</para>
/// </summary>
public class DeepFailureUnwindScalingTests
{
    /// <summary>The scaling depths: each doubles the last, so a per-level walk of the chain cannot hide.</summary>
    private static readonly int[] Depths = [250, 500, 1_000, 2_000];

    /// <summary>Depths every synchronous route holds on its 64 MiB thread in a Debug build.</summary>
    private static readonly int[] SafeDepths = [0, 1, 10, 40];

    private const int OracleStack = 64 * 1024 * 1024;

    /// <summary>Bounds a run even if a regression stops the recursion from reaching its base.</summary>
    private static readonly EvaluationLimits Limits = new() { MaxSteps = 1_000_000 };

    private sealed class HostFailure(string message) : Exception(message);

    private enum Expected
    {
        DivByZero,
        MissingOutput,
        DepthLimit,
        HostFailure,
        Value,
    }

    /// <summary>
    /// One recursion through loop steps, <c>R(n) = if(n == 0, bottom, step.repeat(1))</c>: <c>1 / 0</c> is the
    /// ordinary failure, <c>G</c> (a block without an output) the missing output, <c>D(0)</c> (an unbounded
    /// recursion reaching the depth limit) the resource-terminal failure, <c>fail(1)</c> / <c>afail(1)</c> the
    /// host failure thrown at once / after a genuine suspension, and <c>1</c> the successful control. A
    /// SUSPENDING step awaits a genuinely asynchronous host operation at every level, so the failure leaves
    /// the deep levels on thread-pool continuations.
    /// </summary>
    private sealed record Shape(string Bottom, bool SuspendsEveryLevel, Expected Expected);

    private static readonly Dictionary<string, Shape> Shapes = new()
    {
        ["ordinary"] = new("1 / 0", false, Expected.DivByZero),
        ["missing-output"] = new("G", false, Expected.MissingOutput),
        ["resource-terminal"] = new("D(0)", false, Expected.DepthLimit),
        ["host-terminal"] = new("fail(1)", false, Expected.HostFailure),
        ["suspending-host-terminal"] = new("afail(1)", false, Expected.HostFailure),
        ["success"] = new("1", false, Expected.Value),
        ["suspending-ordinary"] = new("1 / 0", true, Expected.DivByZero),
        ["suspending-missing-output"] = new("G", true, Expected.MissingOutput),
        ["suspending-success"] = new("1", true, Expected.Value),
    };

    public static TheoryData<string> ShapeNames()
    {
        var data = new TheoryData<string>();
        foreach (var name in Shapes.Keys)
            data.Add(name);
        return data;
    }

    private static string Source(Shape shape, int levels)
        => $"G = {{\n    public X = 1\n}}\nD(k) = D(k + 1) + 1\n"
            + $"R(n) = if(n == 0, {shape.Bottom}, {(shape.SuspendsEveryLevel ? "R(ayield(n) - 1)" : "R(n - 1)")}.repeat(1))\n"
            + $"R({levels})";

    /// <summary>One run's host: the same operation names on both routes, asynchronous ones on the twin route.</summary>
    private sealed class Host
    {
        private int _suspensions;
        private int _failures;

        public HostFailure Failure { get; } = new("host operation failed");

        public int Suspensions => Volatile.Read(ref _suspensions);

        public int Failures => Volatile.Read(ref _failures);

        public HostOperations Operations(bool twinRoute)
        {
            var fail = HostOperation.Create("fail", (_, _) => Throw(), "x");
            return twinRoute
                ? HostOperations.Create(
                    fail,
                    HostOperation.CreateAsync("ayield", async (a, _) =>
                    {
                        await Task.Yield();
                        Interlocked.Increment(ref _suspensions);
                        return a[0];
                    }, "x"),
                    HostOperation.CreateAsync("afail", async (_, _) =>
                    {
                        await Task.Yield();
                        Interlocked.Increment(ref _suspensions);
                        return Throw();
                    }, "x"))
                : HostOperations.Create(
                    fail,
                    HostOperation.Create("ayield", (a, _) => a[0], "x"),
                    HostOperation.Create("afail", (_, _) => Throw(), "x"));
        }

        private Result Throw()
        {
            Interlocked.Increment(ref _failures);
            throw Failure;
        }
    }

    /// <summary>A run's outcome, its budget, its host and the context-chain reads its evaluation made.</summary>
    private sealed record Run(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget? Budget, Exception? Thrown, long Reads, Host Host)
    {
        public EvalError Error => Result.Error;
    }

    private static Expr Program(Shape shape, int levels, HostOperations operations)
    {
        var parsed = Parser.Parse(Source(shape, levels), new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    /// <summary>The forced twin route (an asynchronous zero-argument cache), from the base of a pool thread's stack.</summary>
    private static async Task<Run> RunOnTwinRoute(Shape shape, int levels)
    {
        // Start where no earlier run's continuation left this thread's stack (see AsyncHostTerminationTests).
        await Task.Yield();
        var host = new Host();
        var operations = host.Operations(twinRoute: true);
        var program = Program(shape, levels, operations);
        using var reads = ContextChainReadTestSeam.Activate();
        try
        {
            var (result, budget) = await Evaluator.RunCountedObservedAsync(
                program,
                Limits,
                zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache(),
                hostOperations: operations);
            return new Run(result, budget, null, reads.Reads, host);
        }
        catch (HostFailure thrown)
        {
            return new Run(default, null, thrown, reads.Reads, host);
        }
    }

    /// <summary>The generic or planned synchronous evaluator on a 64 MiB thread: the oracle at safe depths.</summary>
    private static Run RunOnSynchronousRoute(Shape shape, int levels, bool planned)
        => AstStructuralDepthProcessTests.RunOnThreadWithStack(OracleStack, () =>
        {
            var host = new Host();
            var operations = host.Operations(twinRoute: false);
            var program = Program(shape, levels, operations);
            try
            {
                var (result, budget) = Evaluator.RunCountedObserved(program, Limits, enableOptimizations: planned, hostOperations: operations);
                return new Run(result, budget, null, -1, host);
            }
            catch (HostFailure thrown)
            {
                return new Run(default, null, thrown, -1, host);
            }
        });

    private static int FrameCount(EvalError error)
    {
        var frames = 0;
        for (; error is EvalError.WithContext frame; error = frame.Inner)
            frames++;
        return frames;
    }

    /// <summary>One line per context frame (its context and span) and the terminal with its span and missing-output provenance.</summary>
    private static string Describe(EvalError error)
    {
        var text = new StringBuilder();
        for (; error is EvalError.WithContext frame; error = frame.Inner)
            text.Append(frame.ErrorContext).Append(" @").Append(frame.Span).Append('\n');
        text.Append(error.GetType().Name).Append(" @").Append(error.Span);
        if (error is EvalError.MissingOutput missing)
            text.Append(" nested=").Append(missing.IsNested).Append(" keepsOwnBlame=").Append(missing.KeepsOwnBlame)
                .Append(" selectedMember=").Append(missing.IsSelectedMemberOutput);
        return text.ToString();
    }

    private static string Counters(EvaluationBudget budget)
        => $"steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} peak={budget.PeakDepth}"
            + $" depth={budget.CurrentDepth} items={budget.MaterializedItems} strings={budget.MaterializedStringChars}";

    /// <summary>Everything a route reports: the structured result frame by frame, the message, the counters, the host's calls.</summary>
    private static string Report(Run run)
    {
        if (run.Thrown is { } thrown)
            return $"threw {thrown.GetType().Name} same={ReferenceEquals(thrown, run.Host.Failure)} failures={run.Host.Failures}";
        var outcome = run.Result.IsOk
            ? "value " + SemanticExplorerHarness.Neutral(run.Result.Value.Value) + " n=" + run.Result.Value.EmittedCount
            : Describe(run.Error) + "\nmessage: " + KatLangError.FromEvalError(run.Error).Message;
        return outcome + "\n" + Counters(run.Budget!) + $" failures={run.Host.Failures}";
    }

    private static void AssertExpected(Shape shape, Run run, string where)
    {
        switch (shape.Expected)
        {
            case Expected.HostFailure:
                Assert.True(run.Thrown is not null, $"{where}: the run did not throw the host failure");
                Assert.Same(run.Host.Failure, run.Thrown);
                Assert.Equal(1, run.Host.Failures);
                return;
            case Expected.Value:
                Assert.True(run.Thrown is null && run.Result.IsOk, $"{where}: the successful control failed");
                Assert.Equal("1", SemanticExplorerHarness.Neutral(run.Result.Value.Value));
                return;
        }

        Assert.True(run.Thrown is null && run.Result.IsError, $"{where}: the run did not fail");
        var terminal = run.Error.UnwrapContext();
        switch (shape.Expected)
        {
            case Expected.DivByZero:
                Assert.IsType<EvalError.DivByZero>(terminal);
                break;
            case Expected.MissingOutput:
                // Someone else's at every consumer above the bottom (Q-36).
                Assert.True(Assert.IsType<EvalError.MissingOutput>(terminal).IsNested, $"{where}: the missing output was not nested");
                break;
            case Expected.DepthLimit:
                Assert.IsType<EvalError.EvaluationDepthExceeded>(terminal);
                // A resource limit gathers no context on the way out.
                Assert.Equal(0, FrameCount(run.Error));
                break;
        }

        Assert.NotNull(run.Error.Span);
    }

    // ── 1. At safe depths: the twin route is the synchronous routes, frame for frame ──────────────

    [Theory]
    [MemberData(nameof(ShapeNames))]
    public async Task AtSafeDepths_TheTwinRoute_ReportsTheSynchronousRoutesResult_FrameForFrame(string name)
    {
        var shape = Shapes[name];
        foreach (var levels in SafeDepths)
        {
            var generic = RunOnSynchronousRoute(shape, levels, planned: false);
            var planned = RunOnSynchronousRoute(shape, levels, planned: true);
            var twin = await RunOnTwinRoute(shape, levels);
            AssertExpected(shape, generic, $"{name}, {levels} levels, generic");
            AssertExpected(shape, twin, $"{name}, {levels} levels, twin");

            var expected = Report(generic);
            Assert.Equal(expected, Report(planned));
            Assert.Equal(expected, Report(twin));
            if (generic.Thrown is null && generic.Result.IsError)
            {
                // Record equality compares typed frame payloads, their order, spans and terminal payload.
                // The report above also checks missing-output provenance outside record equality.
                Assert.Equal(generic.Error, planned.Error);
                Assert.Equal(generic.Error, twin.Error);
            }
            if (shape.SuspendsEveryLevel)
                Assert.Equal(levels, twin.Host.Suspensions);
        }
    }

    // ── 2. The scaling gate: context-chain work per level is constant ────────────────────────────

    [Theory]
    [MemberData(nameof(ShapeNames))]
    public async Task UnwindingAFailureThroughDeepLoopStepRecursion_ReadsTheContextChainNoMoreThanOncePerLevel(string name)
    {
        var shape = Shapes[name];

        // Two shallow synchronous runs predict the deep run: every level adds the same frames, steps and
        // checkpoints (the frames and spans themselves are the synchronous ones, section 1).
        var ten = RunOnSynchronousRoute(shape, 10, planned: false);
        var twenty = RunOnSynchronousRoute(shape, 20, planned: false);
        static long At(long ten, long twenty, int levels) => ten + (twenty - ten) * (levels - 10) / 10;
        if (ten.Budget is not null)
        {
            // Below the first bulk block, so every step of the shallow runs is a call or a loop round.
            Assert.InRange(ten.Budget.ConsumedExpressionCheckpoints, 1, EvaluationBudget.ExpressionCheckpointsPerStep - 1);
            Assert.InRange(twenty.Budget!.ConsumedExpressionCheckpoints, 1, EvaluationBudget.ExpressionCheckpointsPerStep - 1);
        }

        long? constantReads = null;
        foreach (var levels in Depths)
        {
            var where = $"{name}, {levels} levels";
            var run = await RunOnTwinRoute(shape, levels);
            AssertExpected(shape, run, where);

            // THE GATE: no walk of the chain per level. A walk asked once per level reads about F²/2 frames for F
            // frames (125,000 at the first depth); the evaluation reads none, or the one missing-output rebuild,
            // at every depth.
            Assert.True(run.Reads <= levels, $"{where}: the evaluation read {run.Reads} context frames");
            constantReads ??= run.Reads;
            Assert.True(run.Reads == constantReads, $"{where}: {run.Reads} context-chain reads, {constantReads} at {Depths[0]} levels");
            if (shape.Expected == Expected.MissingOutput)
            {
                // The observation followed the run: the one rebuild ran at the bottom, after every suspension.
                Assert.True(run.Reads == 1, $"{where}: the nesting rebuild read {run.Reads} frames");
            }

            if (shape.SuspendsEveryLevel)
                Assert.Equal(levels, run.Host.Suspensions);
            if (run.Thrown is not null)
                continue;

            var budget = run.Budget!;
            var checkpoints = At(ten.Budget!.ConsumedExpressionCheckpoints, twenty.Budget!.ConsumedExpressionCheckpoints, levels);
            Assert.Equal(checkpoints, budget.ConsumedExpressionCheckpoints);
            // Every completed block of checkpoints charges one more step (the bulk expression-work unit).
            Assert.Equal(
                At(ten.Budget.ConsumedSteps, twenty.Budget.ConsumedSteps, levels) + checkpoints / EvaluationBudget.ExpressionCheckpointsPerStep,
                budget.ConsumedSteps);
            Assert.Equal(twenty.Budget.PeakDepth, budget.PeakDepth);
            Assert.Equal(0, budget.CurrentDepth);
            if (run.Result.IsOk)
                continue;

            var frames = FrameCount(run.Error);
            Assert.Equal(At(FrameCount(ten.Error), FrameCount(twenty.Error), levels), frames);

            // Formatting the failure is the necessary linear work: each frame is read a bounded number of times.
            using var formatting = ContextChainReadTestSeam.Activate();
            var message = KatLangError.FromEvalError(run.Error);
            Assert.Equal(run.Error.Code, message.Code);
            Assert.True(formatting.Reads <= 16L * Math.Max(frames, 1), $"{where}: formatting {frames} frames read {formatting.Reads}");
        }
    }

    // ── 3. The public asynchronous engine reports the same failure, with chain work linear in its frames ──

    [Theory]
    [MemberData(nameof(ShapeNames))]
    public async Task ThePublicAsynchronousEngine_ReportsTheSameFailure_WithContextChainWorkLinearInItsFrames(string name)
    {
        var shape = Shapes[name];
        foreach (var levels in new[] { 40, 1_000 })
        {
            var where = $"{name}, {levels} levels";
            await Task.Yield();
            var host = new Host();
            var source = Source(shape, levels);
            RunResult? result = null;
            Exception? thrown = null;
            long reads;
            using (var observation = ContextChainReadTestSeam.Activate())
            {
                try
                {
                    result = await KatLangEngine.RunAsync(source, new RunOptions
                    {
                        HostOperations = host.Operations(twinRoute: true),
                        EvaluationLimits = Limits,
                    });
                }
                catch (HostFailure hostFailure)
                {
                    thrown = hostFailure;
                }

                reads = observation.Reads;
            }

            switch (shape.Expected)
            {
                case Expected.HostFailure:
                    Assert.Same(host.Failure, thrown);
                    Assert.Equal(0, reads);
                    continue;
                case Expected.Value:
                    Assert.Equal("1", Assert.IsType<RunResult.Success>(result).ToDisplayString());
                    Assert.Equal(0, reads);
                    continue;
            }

            var failure = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
            var frames = FrameCount(failure.Source!);
            Assert.True(reads <= 16L * Math.Max(frames, 1), $"{where}: {reads} context-chain reads for {frames} frames");
            if (levels == 40)
            {
                // The synchronous engine on a thread that holds it reports the same failure and message.
                var synchronous = AstStructuralDepthProcessTests.RunOnThreadWithStack(OracleStack, () => KatLangEngine.Run(source, new RunOptions
                {
                    HostOperations = new Host().Operations(twinRoute: false),
                    EvaluationLimits = Limits,
                }));
                var expected = Assert.Single(Assert.IsType<RunResult.EvalFailure>(synchronous).Errors);
                Assert.Equal(expected.Code, failure.Code);
                Assert.Equal(expected.Message, failure.Message);
                Assert.Equal(expected.Span, failure.Span);
                Assert.Equal(expected.Source, failure.Source);
                Assert.Equal(Describe(expected.Source!), Describe(failure.Source!));
            }
        }
    }
}
