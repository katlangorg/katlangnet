using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// The loop-entry host-stack backstop (<see cref="EvaluationBudget.TryAdmitLoopEntry"/>, November 2026; C#-only
/// host policy under Q-09a, no Lean counterpart): the one probe a <c>while</c>/<c>repeat</c> that will run a round
/// passes before its step is projected, planned or invoked. A loop-step invocation charges a step and never
/// depth, so a step whose body starts a loop over itself nests host frames through no other probe.
///
/// <para>These tests pin the admission itself, in process and without any deep recursion: with host-stack
/// headroom it reads and charges nothing (Q-09b: an ordinary loop is the loop it always was), and on a
/// genuinely low stack its refusal follows the chokepoints' order — host cancellation, then a failure the run
/// already retained, then the stack refusal, retained as terminal — still without moving a counter. The
/// recursions it bounds would overflow the test host if it regressed, so they run in child processes:
/// <see cref="EvaluationLimitsProcessTests.RecursionThroughLoopSteps_StopsAtTheLoopEntryBackstop_InSubprocess"/>
/// and its twin-route companion.</para>
/// </summary>
public class LoopEntryBackstopTests
{
    private const int OneMiB = 1_048_576;

    private static (long Steps, long Checkpoints, int Depth, int Peak, long Items, long Strings) Counters(EvaluationBudget budget)
        => (budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.CurrentDepth, budget.PeakDepth,
            budget.MaterializedItems, budget.MaterializedStringChars);

    /// <summary>The admission on a stack below the runtime's reserve, where its probe refuses.</summary>
    private static T OnALowStack<T>(Func<T> admission)
        => AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () => StackHopTests.WithLowStack(() =>
        {
            Assert.False(RuntimeHelpers.TryEnsureSufficientExecutionStack(), "the stack is not low");
            return admission();
        }));

    [Fact]
    public void WithHeadroom_TheAdmissionReadsAndChargesNothing()
    {
        // An exhausted step budget, a retained terminal failure and a cancelled token: every chokepoint that
        // observes the run would report one of them. With headroom the admission observes none.
        using var cancellation = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 }, cancellationToken: cancellation.Token);
        Assert.Null(budget.TryChargeStep());
        var stepLimit = Assert.IsType<EvalError.EvaluationStepLimitExceeded>(budget.TryChargeStep());
        Assert.Same(stepLimit, budget.CheckContinuation());
        var before = Counters(budget);
        cancellation.Cancel();

        Assert.True(RuntimeHelpers.TryEnsureSufficientExecutionStack());
        Assert.Null(budget.TryAdmitLoopEntry());
        Assert.Null(budget.TryAdmitLoopEntry());
        Assert.Equal(before, Counters(budget));
    }

    [Fact]
    public void OnALowStack_TheRefusalIsTheRunsTerminalFailure_AndChargesNothing()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 100 });
        Assert.Null(budget.TryChargeStep());
        var before = Counters(budget);

        var refusal = OnALowStack(budget.TryAdmitLoopEntry);

        Assert.IsType<EvalError.EvaluationStackExhausted>(refusal);
        Assert.True(refusal!.IsResourceLimit);
        Assert.Null(refusal.Span);
        // Charge-free and level-free: no step, no depth, and the peak is untouched (Q-09b).
        Assert.Equal(before, Counters(budget));
        // Terminal for the run: every later chokepoint returns it and admits nothing.
        Assert.Same(refusal, budget.CheckContinuation());
        Assert.Same(refusal, budget.TryChargeStep());
        Assert.Same(refusal, budget.TryEnterInvocation());
        Assert.Same(refusal, budget.TryEnterArgumentEvaluation());
        Assert.Same(refusal, budget.TryChargeExpressionNodeWork());
        Assert.Equal(before, Counters(budget));
        // With headroom again the admission still observes nothing: the run's chokepoints own the verdict.
        Assert.Null(budget.TryAdmitLoopEntry());
    }

    [Fact]
    public void OnALowStack_HostCancellationPreemptsTheRefusal()
    {
        using var cancellation = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(null, cancellationToken: cancellation.Token);
        cancellation.Cancel();

        OperationCanceledException? cancelled = null;
        OnALowStack(() =>
        {
            try
            {
                return budget.TryAdmitLoopEntry();
            }
            catch (OperationCanceledException error)
            {
                cancelled = error;
                return null;
            }
        });

        // Cancellation is host demand: it throws, carrying the supplied token, and never becomes a limit verdict.
        Assert.NotNull(cancelled);
        Assert.Equal(cancellation.Token, cancelled.CancellationToken);
        Assert.Equal((0L, 0L, 0, 0, 0L, 0L), Counters(budget));
    }

    [Fact]
    public void OnALowStack_AFailureTheRunAlreadyRetainedKeepsItsPlace()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 });
        Assert.Null(budget.TryChargeStep());
        var stepLimit = Assert.IsType<EvalError.EvaluationStepLimitExceeded>(budget.TryChargeStep());
        var before = Counters(budget);

        Assert.Same(stepLimit, OnALowStack(budget.TryAdmitLoopEntry));
        Assert.Same(stepLimit, budget.CheckContinuation());
        Assert.Equal(before, Counters(budget));
    }

    /// <summary>
    /// An exhausted step budget that has NOT been reported yet does not turn the refusal into a step verdict:
    /// the admission reads no semantic limit, so a low stack never moves the point at which one fires (the
    /// round's own charge decides it; an ordinary failure of the step's projection could come first).
    /// </summary>
    [Fact]
    public void OnALowStack_AnUnreportedStepExhaustionIsNotReportedByTheAdmission()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 });
        Assert.Null(budget.TryChargeStep());
        Assert.Null(budget.CheckContinuation());

        Assert.IsType<EvalError.EvaluationStackExhausted>(OnALowStack(budget.TryAdmitLoopEntry));
        Assert.Equal(1, budget.ConsumedSteps);
    }

    /// <summary>
    /// Source pin, like <see cref="StructuralNestingStackBackstopTests.AllFourRowLoopFunnels_OpenWithTheStackProbe"/>:
    /// the loop's setup opens with the twin-only hop and the shared admission, before the step is projected.
    /// Moving either below the projection or the planner, or dropping the hop, changes no ordinary test result
    /// and re-opens the overflow (or the twin's early stack verdict) on that route.
    /// </summary>
    [Fact]
    public void TheLoopSetup_OpensWithTheHopAndTheAdmission_BeforeTheStepIsProjected()
    {
        var source = File.ReadAllText(Path.Combine(RepoRoot.Find(), "dotnet", "src", "KatLang", "Evaluator.Needs.cs")).ReplaceLineEndings("\n");
        var declaration = source.IndexOf("ValueTask<EvalResult<CountedResult>> EvalNeedLoop(", StringComparison.Ordinal);
        Assert.True(declaration >= 0, "EvalNeedLoop not found");
        var setup = source.IndexOf("if (!repeat || remaining > 0)", declaration, StringComparison.Ordinal);
        Assert.True(setup >= 0, "the loop's setup block not found");
        var statements = source[setup..]
            .Split('\n')
            .Skip(1)
            .Select(static line => line.Trim())
            .Where(static line => line.Length > 0 && line != "{" && !line.StartsWith("//", StringComparison.Ordinal))
            .Take(3)
            .ToArray();

        Assert.Equal("if (asynchronous && StackHop.HostStackIsLow()) await new StackHop();", statements[0]);
        Assert.Equal("if (ctx.Budget.TryAdmitLoopEntry() is { } stackRefusal) return stackRefusal;", statements[1]);
        Assert.StartsWith("var projection = asynchronous", statements[2], StringComparison.Ordinal);
        // One loop entry: nothing else starts the rounds of a loop.
        Assert.Equal(1, CountOccurrences(source, "TryAdmitLoopEntry()"));
    }

    private static int CountOccurrences(string text, string value)
    {
        var count = 0;
        for (var at = text.IndexOf(value, StringComparison.Ordinal); at >= 0; at = text.IndexOf(value, at + value.Length, StringComparison.Ordinal))
            count++;
        return count;
    }
}
