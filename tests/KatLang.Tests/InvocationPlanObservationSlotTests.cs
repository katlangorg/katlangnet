using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// P1 (J7 per-transition allocation): an invocation plan keeps its route, its one reference and its
/// canonical callee cell in ONE observation slot — the route alone while only executions have read it,
/// an out-of-line holder once an observation needs the reference or the callee cell. These cases pin
/// that the representation change is unobservable: every route is retained first-writer-wins across the
/// slot's move to the holder, the reference and callee cell stay unique, an unobserved plan's VALUE
/// allocates no holder, and racing route publications and observations agree on one of each.
/// </summary>
public partial class InvocationPlanTests
{
    // A plain call (no route slot use), a member route and an extension route; each plan's VALUE traces
    // its argument once, whether VALUE or the observation comes first.
    public static TheoryData<string, string, bool> ObservationSlotPlans => new()
    {
        { "F(x) = x + 1\nMeta(F(trace(1)))", "2", false },
        { "Box = { F(x) = x + 1 }\nMeta(Box.F(trace(1)))", "2", true },
        { "Add(a, b) = a + b\nMeta(trace(1).Add(2))", "3", true },
    };

    [Theory]
    [MemberData(nameof(ObservationSlotPlans))]
    public void ObservationSlot_ValueThenMeta_KeepsTheRetainedRoute(string source, string value, bool routed)
    {
        var probe = new Probe();
        probe.OnMeta = cells =>
        {
            var cell = cells[0]!;
            var plan = Assert.IsType<Evaluator.InvocationPlan>(cell.Suspension);
            Assert.Equal(routed, plan.NeedsRoute);
            Assert.False(plan.HasObservationHolder);
            Assert.Null(plan.RouteState);

            Assert.Equal(value, Neutral(cell.Demand().Value.Value));
            // VALUE publishes a route-bearing plan's route into the slot itself: no holder.
            Assert.False(plan.HasObservationHolder);
            var route = plan.RouteState;
            if (routed) Assert.IsType<Evaluator.PlanRoute>(route);
            else Assert.Null(route);

            var reference = Reify(cell);
            Assert.True(plan.HasObservationHolder);
            Assert.Same(route, plan.RouteState);
            Assert.Same(reference, Reify(cell));
            var callee = plan.CalleeCell;
            Assert.True(plan.HasCalleeCell);
            Assert.Same(callee, plan.CalleeCell);
            Assert.Same(route, plan.RouteState);

            Assert.Equal(value, Neutral(reference.Invoke().Value.Value));
            Assert.Same(route, plan.RouteState);
            Assert.Equal(1, plan.SupplyFormations);
            Assert.Equal(1, probe.Traces);
            return Zero;
        };
        Assert.Equal("0", probe.Run(source));
    }

    [Theory]
    [MemberData(nameof(ObservationSlotPlans))]
    public void ObservationSlot_MetaThenValue_PublishesTheRouteIntoTheHolder(string source, string value, bool routed)
    {
        var probe = new Probe();
        probe.OnMeta = cells =>
        {
            var cell = cells[0]!;
            var plan = Assert.IsType<Evaluator.InvocationPlan>(cell.Suspension);
            var reference = Reify(cell);
            // Capture is inert: a holder, but no route, no callee cell, nothing prepared or demanded.
            Assert.True(plan.HasObservationHolder);
            Assert.Null(plan.RouteState);
            Assert.False(plan.HasCalleeCell);
            Assert.Equal(0, plan.SupplyFormations);
            Assert.Equal(0, probe.Traces);

            Assert.Equal(value, Neutral(cell.Demand().Value.Value));
            var route = plan.RouteState;
            if (routed)
            {
                Assert.IsType<Evaluator.PlanRoute>(route);
                Assert.Same(route, Evaluator.PlanRouteOf(plan).Value);
            }
            else Assert.Null(route);
            Assert.Same(reference, Reify(cell));
            Assert.Same(plan.CalleeCell, plan.CalleeCell);
            Assert.Equal(value, Neutral(reference.Invoke().Value.Value));
            Assert.Same(route, plan.RouteState);
            Assert.Equal(1, plan.SupplyFormations);
            Assert.Equal(1, probe.Traces);
            return Zero;
        };
        Assert.Equal("0", probe.Run(source));
    }

    [Fact]
    public void ObservationSlot_RetainedRouteFailure_SurvivesTheMoveToTheHolder_FirstWriterWins()
    {
        // A route failure is retained exactly like a route (never absence); the slot's move to the holder
        // carries it, and a later publication never replaces it.
        var plan = new Evaluator.InvocationPlan(Evaluator.EvalCtx.Empty, []);
        EvalError failure = new EvalError.NotAnAlgorithm("route failure");
        Assert.Same(failure, plan.PublishRouteState(failure));
        Assert.False(plan.HasObservationHolder);
        Assert.Same(failure, plan.PublishRouteState(Evaluator.PlanRoute.Call));
        var reference = plan.Reference;
        Assert.True(plan.HasObservationHolder);
        Assert.Same(failure, plan.RouteState);
        Assert.Same(failure, plan.PublishRouteState(Evaluator.PlanRoute.Intrinsic));
        Assert.Same(reference, plan.Reference);

        // Holder first, then the route: published into the holder, first writer wins there too.
        var observed = new Evaluator.InvocationPlan(Evaluator.EvalCtx.Empty, []);
        var observedReference = observed.Reference;
        Assert.Null(observed.RouteState);
        Assert.Same(Evaluator.PlanRoute.AlgorithmIntrinsic, observed.PublishRouteState(Evaluator.PlanRoute.AlgorithmIntrinsic));
        Assert.Same(Evaluator.PlanRoute.AlgorithmIntrinsic, observed.PublishRouteState(failure));
        Assert.Same(Evaluator.PlanRoute.AlgorithmIntrinsic, observed.RouteState);
        Assert.Same(observedReference, observed.Reference);
    }

    [Fact]
    public void ObservationSlot_RacingRoutePublicationsAndObservations_AgreeOnOneOfEach()
    {
        const int Workers = 4;
        const int Rounds = 2000;
        Evaluator.InvocationPlan? plan = null;
        var routes = new object[Workers];
        var references = new Result.CallReference?[Workers];
        var failures = new List<Exception>();
        using var barrier = new Barrier(Workers + 1);
        var threads = Enumerable.Range(0, Workers).Select(worker => new Thread(() =>
        {
            for (var round = 0; round < Rounds; round++)
            {
                barrier.SignalAndWait();
                try
                {
                    var target = plan!;
                    // Even workers publish a fresh candidate route, odd workers observe first.
                    if (worker % 2 == 0)
                    {
                        routes[worker] = target.PublishRouteState(worker == 0
                            ? new Evaluator.PlanRoute(Evaluator.PlanRouteKind.Member)
                            : new EvalError.NotAnAlgorithm("racing route failure"));
                        references[worker] = target.Reference;
                    }
                    else
                    {
                        references[worker] = target.Reference;
                        routes[worker] = target.PublishRouteState(new Evaluator.PlanRoute(Evaluator.PlanRouteKind.Extension));
                    }
                    Assert.Same(routes[worker], target.RouteState);
                }
                catch (Exception error)
                {
                    lock (failures) failures.Add(error);
                }
                barrier.SignalAndWait();
            }
        }) { IsBackground = true }).ToArray();
        foreach (var thread in threads) thread.Start();

        for (var round = 0; round < Rounds; round++)
        {
            plan = new Evaluator.InvocationPlan(Evaluator.EvalCtx.Empty, []);
            barrier.SignalAndWait();
            barrier.SignalAndWait();
            try
            {
                var retained = plan.RouteState;
                Assert.NotNull(retained);
                Assert.All(routes, route => Assert.Same(retained, route));
                Assert.All(references, reference => Assert.Same(plan.Reference, reference));
                Assert.True(plan.HasObservationHolder);
            }
            catch (Exception error)
            {
                // Drain every worker before reporting failure; disposing a barrier with workers
                // still waiting would obscure the assertion with unhandled thread exceptions.
                lock (failures) failures.Add(error);
            }
        }
        foreach (var thread in threads) Assert.True(thread.Join(WaitLimit));
        Assert.Empty(failures);
    }

    // ── The P1 workloads keep their values on every engine ──────────────────────────────────────────────

    public static TheoryData<string, string, int, int, int> ObservationSlotWorkloads => new()
    {
        // F11/F12: two plannable nested arguments per accepted transition, plus the captured step.
        { "Id(x) = x\nS(x) = Id(Id(Id(x + 1))), x < 1000\n\nS(0).while", "1000", 2001, 1, 0 },
        { "Id(x) = x\nS(x) = Id(Id(Id(x + 1))), x < 0\n\nS(0).while", "0", 1, 1, 0 },
        { "Step(x) = x + 1, x < 3\n\nLoop(meta op) = op.Algorithm(op.Arguments*).while\n\nStep(0).Loop", "3", 2, 1, 0 },
        { "Inc(x) = x + 1\nInc(0).repeat(1000)", "1000", 1, 1, 0 },
        { "Inc(x) = x + 1\nInc(0).repeat(0)", "0", 1, 0, 0 },
        { "Fib(a, b) = b, a + b\nFib(0, 1).repeat(10)", "S[55, 89]", 1, 1, 0 },
        { "Z = false\nZ().while", "S[]", 1, 0, 2 },
    };

    [Theory]
    [MemberData(nameof(ObservationSlotWorkloads))]
    public async Task ObservationSlot_LoopWorkloads_KeepValuesAndPlanCounts_OnEveryEngine(
        string source, string expected, int plans, int optimizedHits, int optimizedFallbacks)
    {
        var root = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        foreach (var optimized in new[] { false, true })
        {
            var observations = new EvaluationObservations();
            var loops = new LoopOptimizationDiagnostics();
            var (result, _) = Evaluator.RunCountedObserved(root, enableOptimizations: optimized, loopDiagnostics: loops, observations: observations);
            Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
            Assert.Equal(expected, Neutral(result.Value.Value));
            Assert.Equal(plans, observations.InvocationPlanCount);
            Assert.Equal(plans, observations.PlanSupplyFormationCount);
            var snapshot = loops.GetSnapshot();
            Assert.Equal(optimized ? optimizedHits : 0, snapshot.OptimizedLoopHits);
            if (optimized) Assert.Equal(optimizedFallbacks, snapshot.OptimizedLoopFallbacks);
        }

        var asyncObservations = new EvaluationObservations();
        var (asyncResult, _) = await Evaluator.RunCountedObservedAsync(
            root, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), observations: asyncObservations);
        Assert.True(asyncResult.IsOk, asyncResult.IsError ? asyncResult.Error.ToString() : "");
        Assert.Equal(expected, Neutral(asyncResult.Value.Value));
        Assert.Equal(plans, asyncObservations.InvocationPlanCount);
        Assert.Equal(plans, asyncObservations.PlanSupplyFormationCount);
    }
}
