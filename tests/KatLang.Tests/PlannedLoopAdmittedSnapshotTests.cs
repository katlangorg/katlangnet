using KatLang.Evaluation;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// The planned loop binds the step head it ADMITTED, never the step's live head (October 2026).
/// <para>A host-built step may keep its parameter patterns in a caller-owned list, so a host
/// operation can rewrite the head while the loop runs. The AST contract forbids that, but the
/// routes must still agree. The generic route prepares its binding once per loop invocation
/// (<c>Evaluator.PrepareGenericLoopStep</c>) and keeps it, so the rewrite changes nothing there. The
/// planned route compiled its plans against one snapshot (<c>LoopPlanTemplate.AdmittedHead</c>) but
/// then re-read the live head in three places:</para>
/// <list type="bullet">
/// <item>each iteration's rebinding in a partially planned loop
/// (<c>LoopRunFrame.BeginIteration</c>): the binding context, and the activated head scope through
/// which a nested block reads the step's parameter once a callee's same-named parameter shadows the
/// binding. A grown head threw a raw <see cref="ArgumentOutOfRangeException"/>, a renamed or cleared
/// one reported <c>UnknownName</c> or, through the head scope alone, silently read the callee's
/// binding, and a permuted or shifted one silently bound the wrong state slots;</item>
/// <item>the name of a pending initial-state read (<c>LoopRunFrame.GetStateSlot</c>): a shrunk or
/// cleared head threw a raw <see cref="ArgumentOutOfRangeException"/>;</item>
/// <item>the generic continuation after a handover, which prepared from the live head and so
/// reported an arity, name or type error where the generic route succeeds.</item>
/// </list>
/// <para>The oracle is the generic route. For every scenario the planned run must equal it, as must
/// the suspending async twin (which never plans): the same value or error, the same host calls and
/// the same budgets. Each scenario's generic outcome is also pinned by hand, as the value the
/// admitted head gives. Every rewrite fails on the pre-fix planner, except the collecting one in the
/// rebinding and permutation scenarios, which keeps the names; that row is a control.
/// <see cref="Planner_RefusesAHeadItCannotBindByPosition"/> pins the planner's own precondition on
/// the snapshot it binds.</para>
/// </summary>
public class PlannedLoopAdmittedSnapshotTests
{
    private const string ShapeMismatch = "loop plan parameter/property shape mismatch";

    private sealed record Budget(long Steps, long Checkpoints, int PeakDepth, long MaterializedItems, long MaterializedStringChars)
    {
        public static Budget Of(EvaluationBudget budget)
            => new(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
                budget.MaterializedItems, budget.MaterializedStringChars);
    }

    private sealed record Run(string Outcome, string Error, Budget Budget, IReadOnlyList<string> HostCalls, string Head);

    // ── Scenarios ────────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// A loop over the property <c>Step</c> of <paramref name="Source"/>. The host operation
    /// <c>mutate()</c> returns its call number and rewrites Step's head on call
    /// <paramref name="Trigger"/>. <paramref name="Expected"/> is the generic outcome: the admitted
    /// head's value, which a mid-loop rewrite cannot change. <paramref name="HandsOver"/> marks a
    /// planned run that hands over to the generic continuation in the rewriting iteration.
    /// </summary>
    private sealed record Scenario(string Source, int Trigger, string Expected, bool HandsOver);

    private static readonly IReadOnlyDictionary<string, Scenario> Scenarios = new Dictionary<string, Scenario>
    {
        // The host call keeps the row generic, so the loop is partially planned and REBINDS its state
        // every iteration; the rewrite happens in iteration 1.
        ["rebind repeat"] = new("Step(state) = state + mutate()\nrepeat(Step, 3, 0)", 1, "ok 6", HandsOver: false),
        ["rebind while"] = new("Step(state) = state + mutate(), state < 2\nwhile(Step, 0)", 1, "ok 3", HandsOver: false),
        // A block in the generic row reads the step's parameter as a CAPTURED parameter, found in the
        // need environment the rebinding builds.
        ["captured repeat"] = new("Call(f) = f()\nStep(state) = Call({ state + mutate() })\nrepeat(Step, 3, 0)", 1, "ok 6", HandsOver: false),
        ["captured while"] = new("Call(f) = f()\nStep(state) = Call({ state + mutate() }), state < 2\nwhile(Step, 0)", 1, "ok 3", HandsOver: false),
        // The callee's own `state` shadows that environment, so the block's read of the STEP's `state`
        // goes through the activated head scope, whose parameter names the rebinding supplies.
        ["shadowed repeat"] = new("Call(state) = state()\nStep(state) = Call({ state + mutate() })\nrepeat(Step, 3, 0)", 1, "ok 6", HandsOver: false),
        ["shadowed while"] = new("Call(state) = state()\nStep(state) = Call({ state + mutate() }), state < 2\nwhile(Step, 0)", 1, "ok 3", HandsOver: false),
        // Two state slots; the generic call row reads `a` through the rebinding.
        ["two-slot repeat"] = new("Add(x, y) = x + y\nStep(a, b) = b, Add(a, mutate())\nrepeat(Step, 3, 1, 10)", 1, "ok S[12, 5]", HandsOver: false),
        ["two-slot while"] = new("Add(x, y) = x + y\nStep(a, b) = b, Add(a, mutate()), a < 20\nwhile(Step, 1, 10)", 1, "ok S[22, 17]", HandsOver: false),
        // A FULLY planned loop whose first initial-state value is pending: demanding it runs the host
        // call, and the next state read happens after the rewrite.
        ["pending repeat"] = new("Step(a, b) = a + b, b\nrepeat(Step, 1, mutate(), 5)", 1, "ok S[6, 5]", HandsOver: false),
        ["pending while"] = new("Step(a, b) = a + b, b, false\nwhile(Step, mutate(), 5)", 1, "ok S[1, 5]", HandsOver: false),
        // Iteration 2 rewrites the head and emits `()`, so the planned loop hands over in that very
        // iteration; the generic continuation runs the rest.
        ["handover repeat"] = new("Empty = ()\nStep(s) = if(mutate() == 2, Empty, if(s == (), 10, s + 1))\nrepeat(Step, 4, 0)", 2, "ok 11", HandsOver: true),
        ["handover while"] = new("Empty = ()\nStep(s) = if(mutate() == 2, Empty, if(s == (), 10, s + 1)), s != 11\nwhile(Step, 0)", 2, "ok 11", HandsOver: true),
    };

    /// <summary>The head rewrites. <c>permute</c>, <c>shift</c> and <c>shrink</c> need two slots.</summary>
    private static readonly IReadOnlyDictionary<string, (Action<List<ParameterPattern>> Apply, bool NeedsTwoSlots)> Rewrites =
        new Dictionary<string, (Action<List<ParameterPattern>>, bool)>
        {
            ["grow"] = (head => head.Add(new CaptureParameterPattern("extra")), false),
            ["rename"] = (head =>
            {
                var count = head.Count;
                head.Clear();
                for (var index = 0; index < count; index++)
                    head.Add(new CaptureParameterPattern("renamed" + index));
            }, false),
            ["clear"] = (head => head.Clear(), false),
            ["collector"] = (head => head[0] = new CaptureParameterPattern(Name(head[0]), Kind: ParameterKind.Collecting), false),
            ["structural"] = (head => head[0] = new SequenceValueParameterPattern(
                [new CaptureParameterPattern("left"), new CaptureParameterPattern("right")]), false),
            // The silent cases: every name the generic call row reads still exists, at another slot.
            ["permute"] = (head => head.Reverse(), true),
            ["shift"] = (head =>
            {
                var first = Name(head[0]);
                head.Clear();
                head.Add(new CaptureParameterPattern("x"));
                head.Add(new CaptureParameterPattern(first));
            }, true),
            ["shrink"] = (head => head.RemoveAt(head.Count - 1), true),
        };

    private static string Name(ParameterPattern pattern) => ((CaptureParameterPattern)pattern).Name;

    public static TheoryData<string, string> ScenarioAndRewrite
    {
        get
        {
            var cases = new TheoryData<string, string>();
            foreach (var (scenario, definition) in Scenarios)
            {
                var twoSlots = definition.Source.Contains("Step(a, b)", StringComparison.Ordinal);
                foreach (var (rewrite, (_, needsTwoSlots)) in Rewrites)
                {
                    if (!needsTwoSlots || twoSlots)
                        cases.Add(scenario, rewrite);
                }
            }

            return cases;
        }
    }

    // ── 1. The planned run binds its admitted head: it equals the generic run ───────────────────

    [Theory]
    [MemberData(nameof(ScenarioAndRewrite))]
    public async Task MidLoopHeadRewrite_PlannedRun_EqualsTheGenericRun(string scenario, string rewrite)
    {
        var generic = RunSync(scenario, rewrite, optimize: false, out _, out var genericObservations);
        var planned = RunSync(scenario, rewrite, optimize: true, out var loops, out var plannedObservations);
        var suspending = await RunSuspendingAsync(scenario, rewrite);

        // The rewrite really happened, during the run, on every route.
        var expectedHead = RewrittenHead(scenario, rewrite);
        Assert.Equal(expectedHead, generic.Head);
        Assert.Equal(expectedHead, planned.Head);
        Assert.Equal(expectedHead, suspending.Head);

        // The generic route bound its once-per-invocation snapshot: the admitted head's value.
        Assert.Equal(Scenarios[scenario].Expected, generic.Outcome);

        // The planned route ran planned, and it equals the generic run exactly.
        Assert.Equal(1, loops.OptimizedLoopHits);
        Assert.Equal(generic.Outcome, planned.Outcome);
        Assert.Equal(generic.Error, planned.Error);
        Assert.Equal(generic.HostCalls, planned.HostCalls);
        Assert.Equal(generic.Budget, planned.Budget);

        // The suspending async twin never plans; it equals the generic run too.
        Assert.Equal(generic.Outcome, suspending.Outcome);
        Assert.Equal(generic.Error, suspending.Error);
        Assert.Equal(generic.HostCalls, suspending.HostCalls);
        Assert.Equal(generic.Budget, suspending.Budget);

        // The strategies' work timing is unchanged (M16): the generic route prepares once; a planned
        // run prepares only for a handover, once, from the admitted head.
        Assert.Equal(1, genericObservations.GenericLoopStepBindingPreparationCount);
        var handsOver = Scenarios[scenario].HandsOver;
        Assert.Equal(handsOver ? 1 : 0, plannedObservations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(handsOver ? 1 : 0, plannedObservations.GenericLoopStepBindingPreparationCount);
    }

    // ── 2. The planner's own precondition on the snapshot it binds ───────────────────────────────

    /// <summary>
    /// The planned frame binds one plain fixed capture per state slot, by position. The shape gate
    /// (<c>Evaluator.IsOptimizedLoopShapeEligible</c>) admits only such a head, and the planner
    /// checks the snapshot it takes as well, so it never binds a head it cannot represent. Called
    /// directly, without the gate, the planner refuses each head below with its shape-mismatch
    /// reason, and the generic continuation is never reached. Before the planner checked its
    /// snapshot, it planned every one of them by their flattened capture count.
    /// </summary>
    [Theory]
    [InlineData("repeated name", 2)]
    [InlineData("collecting capture", 1)]
    [InlineData("structural pattern", 2)]
    [InlineData("repeated name beyond the scanned length", 10)]
    [InlineData("fewer captures than state slots", 2)]
    public void Planner_RefusesAHeadItCannotBindByPosition(string head, int stateArity)
    {
        IReadOnlyList<ParameterPattern> patterns = head switch
        {
            "repeated name" => [new CaptureParameterPattern("x"), new CaptureParameterPattern("x")],
            "fewer captures than state slots" => [new CaptureParameterPattern("x")],
            "collecting capture" => [new CaptureParameterPattern("xs", Kind: ParameterKind.Collecting)],
            "structural pattern" => [new SequenceValueParameterPattern([new CaptureParameterPattern("a"), new CaptureParameterPattern("b")])],
            "repeated name beyond the scanned length" =>
                [.. Enumerable.Range(0, 9).Select(index => new CaptureParameterPattern("p" + index)), new CaptureParameterPattern("p3")],
            _ => throw new ArgumentOutOfRangeException(nameof(head)),
        };
        var (planned, diagnostics, _) = PlanDirectly(patterns, stateArity);

        Assert.False(planned);
        Assert.Equal(0, diagnostics.OptimizedLoopHits);
        Assert.Equal(1, Assert.Contains(ShapeMismatch, diagnostics.FallbackReasons));
    }

    /// <summary>The control: a flat fixed head with distinct names is planned and runs.</summary>
    [Theory]
    [InlineData(1)]
    [InlineData(10)]
    public void Planner_PlansAFlatFixedHeadWithDistinctNames(int stateArity)
    {
        var patterns = Enumerable.Range(0, stateArity).Select(index => (ParameterPattern)new CaptureParameterPattern("p" + index)).ToArray();
        var (planned, diagnostics, result) = PlanDirectly(patterns, stateArity);

        Assert.True(planned);
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.DoesNotContain(ShapeMismatch, diagnostics.FallbackReasons.Keys);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
    }

    // ── Helpers ──────────────────────────────────────────────────────────────────────────────────

    private static (bool Planned, LoopOptimizationDiagnostics Diagnostics, EvalResult<Evaluator.CountedResult> Result) PlanDirectly(
        IReadOnlyList<ParameterPattern> patterns, int stateArity)
    {
        // One output row per state slot: the state values themselves.
        var rows = Enumerable.Range(0, stateArity).Select(index => (Expr)new Expr.Num(index)).ToArray();
        var step = new Algorithm.User(Parent: null, ParameterPatterns: patterns, Opens: [], Properties: [], Output: OutputBundle.From(rows));
        var diagnostics = new LoopOptimizationDiagnostics();
        var ctx = Evaluator.EvalCtx.Empty with { Budget = EvaluationBudget.Create(null), LoopDiagnostics = diagnostics };
        var state = Enumerable.Range(0, stateArity).Select(index => (Result)new Result.Atom(index)).ToArray();

        var planned = LoopOptimizer.TryEvaluateRepeat(
            step,
            count: 2,
            state,
            ctx,
            [],
            (_, _, _) => throw new Xunit.Sdk.XunitException("no generic continuation is expected"),
            out var result);
        return (planned, diagnostics, result);
    }

    /// <summary>The head's display after the rewrite, computed from the scenario's original head.</summary>
    private static string RewrittenHead(string scenario, string rewrite)
    {
        var head = OriginalHead(scenario);
        Rewrites[rewrite].Apply(head);
        return Display(head);
    }

    private static List<ParameterPattern> OriginalHead(string scenario)
    {
        var parsed = Parser.Parse(Scenarios[scenario].Source, new RunOptions { HostOperations = HostOperations.Create(
            HostOperation.Create("mutate", (_, _) => new Result.Atom(0))) });
        var step = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(static property => property.Name == "Step").Value);
        return [.. step.ParameterPatterns];
    }

    private static string Display(IReadOnlyList<ParameterPattern> head)
        => string.Join(", ", head.Select(static pattern => pattern.DisplayName));

    /// <summary>
    /// The scenario's program, with Step's head moved into a caller-owned list that
    /// <c>mutate()</c> rewrites on the trigger call. Every run builds its own program and log.
    /// </summary>
    private sealed class MutatingProgram
    {
        private int _calls;

        public MutatingProgram(string scenario, string rewrite, bool suspending)
        {
            var definition = Scenarios[scenario];
            var apply = Rewrites[rewrite].Apply;
            Result Mutate()
            {
                lock (HostCalls)
                    HostCalls.Add("mutate");
                var call = Interlocked.Increment(ref _calls);
                if (call == definition.Trigger)
                    apply(Head);
                return new Result.Atom(call);
            }

            var operation = suspending
                ? HostOperation.CreateAsync("mutate", async (_, _) => { await Task.Yield(); return Mutate(); })
                : HostOperation.Create("mutate", (_, _) => Mutate());
            Operations = HostOperations.Create(operation);

            var parsed = Parser.Parse(definition.Source, new RunOptions { HostOperations = Operations });
            Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
            var properties = parsed.Root.Properties.ToArray();
            var index = Array.FindIndex(properties, static property => property.Name == "Step");
            var step = Assert.IsType<Algorithm.User>(properties[index].Value);
            Head.AddRange(step.ParameterPatterns);
            properties[index] = properties[index] with { Value = step with { ParameterPatterns = Head } };
            Expression = new Expr.AlgorithmExpr(parsed.Root with { Properties = properties });
        }

        public List<ParameterPattern> Head { get; } = [];

        public Expr Expression { get; }

        public HostOperations Operations { get; }

        public List<string> HostCalls { get; } = [];
    }

    private static Run RunSync(
        string scenario, string rewrite, bool optimize,
        out LoopOptimizationDiagnostics loops, out EvaluationObservations observations)
    {
        var program = new MutatingProgram(scenario, rewrite, suspending: false);
        loops = new LoopOptimizationDiagnostics();
        observations = new EvaluationObservations();
        var (result, budget) = Evaluator.RunCountedObserved(
            program.Expression,
            enableOptimizations: optimize,
            loopDiagnostics: loops,
            observations: observations,
            hostOperations: program.Operations);
        return new Run(Outcome(result), ErrorText(result), Budget.Of(budget), [.. program.HostCalls], Display(program.Head));
    }

    private static async Task<Run> RunSuspendingAsync(string scenario, string rewrite)
    {
        var program = new MutatingProgram(scenario, rewrite, suspending: true);
        var loops = new LoopOptimizationDiagnostics();
        var (result, budget) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            program.Expression,
            zeroArgPropertyResultCache: new SuspendingAsyncZeroArgPropertyResultCache(),
            loopDiagnostics: loops,
            hostOperations: program.Operations));
        Assert.Equal(0, loops.OptimizedLoopHits);
        return new Run(Outcome(result), ErrorText(result), Budget.Of(budget), [.. program.HostCalls], Display(program.Head));
    }

    private static string Outcome(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? "err " + LoopDiagnosticParityAssertions.Innermost(result.Error).GetType().Name
            : "ok " + SixRouteAgreement.Neutral(result.Value.Value);

    /// <summary>The whole reported error: public code, message and span, then every context frame.</summary>
    private static string ErrorText(EvalResult<Evaluator.CountedResult> result)
    {
        if (!result.IsError)
            return "";
        var error = KatLangError.FromEvalError(result.Error);
        return $"{error.Code}: {error.Message} @ {error.Span} | {string.Join(" / ", LoopDiagnosticParityAssertions.ContextChain(result.Error))}";
    }
}
