using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// PLAN RETENTION: the lightweight invocation-plan representation. A written argument's cell keeps its
/// suspension as DATA (<see cref="Evaluator.ExpressionSuspension"/>); a call-shaped cell's suspension IS its
/// invocation plan (<see cref="Evaluator.InvocationPlan"/>), whose one supply slot keeps the ACTUAL formed
/// supply after the cell's VALUE has completed. Every program runs on the production supplied cells.
/// <c>Meta</c> is the internal META receiver seam of <see cref="InvocationPlanTestSeam"/>; these cases pin the
/// representation below the surface <c>meta</c> binder, whose language-level behaviour is pinned by
/// <c>CallReferenceS1Tests</c>/<c>CallReferenceS2Tests</c>. <c>trace</c>, <c>tick</c> and <c>pair</c> count effects.
/// </summary>
public partial class InvocationPlanTests
{
    // ── Representation ──────────────────────────────────────────────────────

    [Fact]
    public void S0_SupplyCell_KeepsItsSuspensionAsData_AndIsAPlanOnlyInAPlanRun()
    {
        var call = new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(1)]);

        if (!ForcedInvocationPlansHook.Forced)
        {
            var ordinaryCtx = Evaluator.EvalCtx.Empty;
            var ordinary = Evaluator.SupplyCell(call, ordinaryCtx, []);
            var suspension = Assert.IsType<Evaluator.ExpressionSuspension>(ordinary.Suspension);
            Assert.Same(ordinaryCtx.Budget, suspension.Caller.Budget);
            Assert.Same(call, ordinary.Source);
            Assert.False(Evaluator.ReifyMeta(ordinary).IsOk);
        }

        using (InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()))
        {
            var planCtx = Evaluator.EvalCtx.Empty;
            var planned = Evaluator.SupplyCell(call, planCtx, []);
            var plan = Assert.IsType<Evaluator.InvocationPlan>(planned.Suspension);
            Assert.Same(planned, plan.Owner);
            Assert.Same(call, plan.Source);
            Assert.Null(plan.Supply);
            Assert.Equal(0, plan.SupplyFormations);

            // A transported parameter is the ORIGINAL cell: no new cell, no new plan.
            var withParameter = planCtx.WithNeedEnv([("x", planned)]);
            Assert.Same(planned, Evaluator.SupplyCell(new Expr.Param("x"), withParameter, []));

            // A non-call expression keeps a plain suspension even in a plan run.
            var other = Evaluator.SupplyCell(new Expr.Num(5), planCtx, []);
            Assert.IsType<Evaluator.ExpressionSuspension>(other.Suspension);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void S0_OnlyCallShapedSuppliedCellsArePlans_AndEachCellIsOnePlan(bool optimized)
    {
        var probe = new Probe();
        var observed = new List<NeedCell>();
        var references = new List<Result.CallReference>();
        probe.OnMeta = cells =>
        {
            observed.Add(cells[0]!);
            if (Evaluator.ReifyMeta(cells[0]) is { IsOk: true } reified) references.Add(reified.Value);
            return Zero;
        };

        Assert.Equal("S[0, 0, 0, 0, 0]", probe.Run("""
            F(v) = v + 1
            Box = { public V = 2 }
            Look(a, b, c, d) = { Meta(a), Meta(a), Meta(b), Meta(c), Meta(d) }
            Look(F(1), 1 + 2, Box.V, (1, 2))
            """, optimized));

        Assert.IsType<Evaluator.InvocationPlan>(observed[0].Suspension);
        Assert.Same(observed[0], observed[1]);
        Assert.All(observed.Skip(2), cell => Assert.IsNotType<Evaluator.InvocationPlan>(cell.Suspension));
        // Two META observations of one cell are the same handle; nothing else is a plan.
        Assert.Equal(2, references.Count);
        Assert.Same(references[0], references[1]);
        // One plan for the one call-shaped written argument; META formed no supply.
        Assert.Equal(1, probe.Observations.InvocationPlanCount);
        Assert.Equal(0, probe.Observations.PlanSupplyFormationCount);
    }

    // ── VALUE before META: completion keeps the actual formed supply ────────

    /// <summary>
    /// The case that fails if completing the cell's VALUE discarded the plan's formed supply: at META the
    /// plan still holds the SAME cell list the VALUE execution bound (its argument already completed), and
    /// invocations reuse it without running the argument again.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void S0_ValueCompletion_RetainsTheFormedSupply_ForALaterMeta(bool optimized)
    {
        var probe = new Probe();
        Result.CallReference? reference = null;
        probe.OnMeta = cells =>
        {
            reference = Reify(cells[0]);
            var plan = reference.Plan;
            Assert.True(plan.Owner.HasCompletedValue);
            var prepared = plan.PreparedCells;
            Assert.NotNull(prepared);
            var argument = Assert.Single(prepared);
            Assert.True(argument.HasCompletedValue);
            Assert.Equal(1, probe.Traces);
            var first = reference.Invoke();
            var second = reference.Invoke();
            // One retained supply object, never a copy, and the argument ran once.
            Assert.Same(prepared, plan.PreparedCells);
            Assert.Equal(1, probe.Traces);
            return new Result.SequenceValue([first.Value.Value, second.Value.Value]);
        };

        Assert.Equal("S[11, S[12, 13]]", probe.Run("""
            F(v) = v + tick()
            Probe(x) = (x, Meta(x))
            Probe(F(trace(10)))
            """, optimized));
        Assert.Equal(1, reference!.Plan.SupplyFormations);
        Assert.Equal("11", Neutral(reference.Plan.Owner.Demand().Value.Value));
    }

    /// <summary>
    /// The case that fails if a plan were reconstructed by running an arbitrary spread again: VALUE opened
    /// <c>pair()*</c> once; after completion META sees the two Ready cells VALUE formed, and two invocations
    /// reuse them with no further <c>pair</c> call.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void S0_ValueFirst_ArbitrarySpread_IsNeverFormedAgain(bool optimized)
    {
        var probe = new Probe();
        Result.CallReference? reference = null;
        probe.OnMeta = cells =>
        {
            reference = Reify(cells[0]);
            Assert.True(reference.Plan.Owner.HasCompletedValue);
            Assert.Equal(1, probe.Pairs);
            var prepared = reference.Plan.PreparedCells!;
            Assert.Equal(2, prepared.Count);
            Assert.All(prepared, cell => Assert.True(cell.TryGetReadyValue(out _)));
            var first = reference.Invoke();
            var second = reference.Invoke();
            Assert.Equal(1, probe.Pairs);
            Assert.Same(prepared, reference.Plan.PreparedCells);
            return new Result.SequenceValue([first.Value.Value, second.Value.Value]);
        };

        Assert.Equal("S[4, S[5, 6]]", probe.Run("""
            Add2(a, b) = a + b + tick()
            Probe(x) = (x, Meta(x))
            Probe(Add2(pair()*))
            """, optimized));
        Assert.Equal(1, probe.Pairs);
        Assert.Equal(1, reference!.Plan.SupplyFormations);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void S0_ForwardingThroughThreePlainParameters_AfterValue_ReachesTheOriginalPlan(bool optimized)
    {
        var probe = new Probe();
        probe.OnMeta = cells =>
        {
            var owner = cells[0]!;
            Assert.IsType<Expr.Call>(owner.Source);
            Assert.True(owner.HasCompletedValue);
            var reference = Reify(owner);
            Assert.Same(owner, reference.Plan.Owner);
            return reference.Invoke().Value.Value;
        };

        Assert.Equal("S[11, 12]", probe.Run("""
            F(v) = v + tick()
            Hop3(c) = Meta(c)
            Hop2(b) = Hop3(b)
            Hop1(a) = Hop2(a)
            Start(x) = (x, Hop1(x))
            Start(F(trace(10)))
            """, optimized));
        Assert.Equal(1, probe.Traces);
        // Two plans, F(trace(10)) and its argument trace(10), each formed once; the hops and the
        // invocation added none.
        Assert.Equal(2, probe.Observations.InvocationPlanCount);
        Assert.Equal(2, probe.Observations.PlanSupplyFormationCount);
    }

    [Fact]
    public void S0_ShadowedNamesAtTheReceiver_KeepTheArgumentsLexicalOwner()
    {
        var probe = new Probe();
        probe.OnMeta = cells => Reify(cells[0]).Invoke().Value.Value;

        Assert.Equal("S[6, 6]", probe.Run("""
            x = 5
            F(v) = v + 1
            Box = {
                x = 100
                F(v) = v * 100
                public Run(y) = (y, Meta(y))
            }
            Box.Run(F(x))
            """));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void S0_HigherOrderCallableArgument_KeepsItsCallableIdentity_AndIsNeverDemanded(bool optimized)
    {
        var probe = new Probe();
        probe.OnMeta = cells =>
        {
            var reference = Reify(cells[0]);
            Assert.True(reference.Plan.Owner.HasCompletedValue);
            var prepared = reference.Plan.PreparedCells!;
            Assert.Equal(2, prepared.Count);
            var projected = prepared[0].ProjectCallable();
            Assert.True(projected.IsOk);
            Assert.NotNull(projected.Value);
            Assert.False(prepared[0].HasCompletedValue);
            Assert.True(prepared[1].HasCompletedValue);
            var invoked = reference.Invoke();
            Assert.False(prepared[0].HasCompletedValue);
            Assert.Same(prepared, reference.Plan.PreparedCells);
            return invoked.Value.Value;
        };

        Assert.Equal("S[42, 42]", probe.Run("""
            Inc(n) = n + 1
            Apply(f, v) = f(v)
            Probe(r) = (r, Meta(r))
            Probe(Apply(Inc, 41))
            """, optimized));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void S0_CollectorSliceTransport_AfterValue_ReifiesTheOriginalCallCells(bool optimized)
    {
        var probe = new Probe();
        var owners = new List<NeedCell>();
        probe.OnMeta = cells =>
        {
            var reference = Reify(cells[0]);
            Assert.True(reference.Plan.Owner.HasCompletedValue);
            Assert.IsType<Expr.Call>(reference.Plan.Owner.Source);
            owners.Add(reference.Plan.Owner);
            return reference.Invoke().Value.Value;
        };

        Assert.Equal("S[6, 7, 8, 9]", probe.Run("""
            F(v) = v + tick()
            Observe(a, b) = { a, b, Meta(a), Meta(b) }
            Pack(*xs) = Observe(xs*)
            Pack(F(trace(5)), F(trace(5)))
            """, optimized));
        Assert.Equal(2, owners.Count);
        Assert.NotSame(owners[0], owners[1]);
        Assert.Equal(2, probe.Traces);
    }

    [Fact]
    public void S0_NestedArgumentPlans_AreRetainedTransitively_AfterValue()
    {
        var probe = new Probe();
        probe.OnMeta = cells =>
        {
            var outer = Reify(cells[0]);
            var inner = Reify(Assert.Single(outer.Plan.PreparedCells!));
            Assert.True(inner.Plan.Owner.HasCompletedValue);
            var innermost = Assert.Single(inner.Plan.PreparedCells!);
            Assert.True(innermost.HasCompletedValue);
            Assert.Equal(1, inner.Plan.SupplyFormations);
            return inner.Invoke().Value.Value;
        };

        // F(F(trace(1))): the outer plan retains the inner plan cell, which retains trace(1)'s plan cell.
        Assert.Equal("S[3, 2]", probe.Run("""
            F(v) = v + 1
            Probe(x) = (x, Meta(x))
            Probe(F(F(trace(1))))
            """));
        Assert.Equal(1, probe.Traces);
        Assert.Equal(3, probe.Observations.InvocationPlanCount);
    }

    // ── Re-entrant preparation (both directions) ───────────────────────────

    [Fact]
    public void S0_InvocationInsideTheValuePreparation_IsADemandCycle_AndTheValueStillCompletes()
    {
        Result.CallReference? reference = null;
        EvalResult<Evaluator.CountedResult>? reentered = null;
        var pairs = 0;
        var probe = new Probe
        {
            PairOverride = HostOperation.Create("pair", (_, _) =>
            {
                pairs++;
                reentered = reference!.Invoke();
                return new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]);
            }),
        };
        probe.OnMeta = cells => { reference = Reify(cells[0]); return Zero; };

        Assert.Equal("S[0, 3]", probe.Run("""
            Add2(a, b) = a + b
            Probe(x) = (Meta(x), x)
            Probe(Add2(pair()*))
            """));

        Assert.True(reentered!.Value.IsError);
        Assert.Equal(KatLangErrorCode.DemandCycle, reentered.Value.Error.Code);
        Assert.Equal(1, pairs);
        Assert.Equal(1, reference!.Plan.SupplyFormations);
    }

    [Fact]
    public void S0_ValueInsideAnInvocationPreparation_IsAStickyDemandCycle()
    {
        Result.CallReference? reference = null;
        EvalResult<Evaluator.CountedResult>? demanded = null;
        EvalResult<Evaluator.CountedResult>? invoked = null;
        var probe = new Probe
        {
            PairOverride = HostOperation.Create("pair", (_, _) =>
            {
                demanded = reference!.Plan.Owner.Demand();
                return new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]);
            }),
        };
        probe.OnMeta = cells =>
        {
            reference = Reify(cells[0]);
            invoked = reference.Invoke();
            return invoked.Value.Value.Value;
        };

        var outcome = probe.Observe("""
            Add2(a, b) = a + b
            Probe(x) = (Meta(x), x)
            Probe(Add2(pair()*))
            """, experiment: true, optimized: false);

        // The invocation prepared the supply; the owner's VALUE, demanded from inside that preparation,
        // is the plan's own preparation in this flow (Lean: prepare of a `preparing` plan → demandCycle),
        // and the completed failure is sticky, so the program's later read of the cell reports it.
        Assert.Equal("3", Neutral(invoked!.Value.Value.Value));
        Assert.True(demanded!.Value.IsError);
        Assert.Equal(KatLangErrorCode.DemandCycle, demanded.Value.Error.Code);
        Assert.StartsWith("err DemandCycle", outcome);
        Assert.Same(demanded.Value.Error, reference!.Plan.Owner.Demand().Error);
        Assert.Equal(1, reference.Plan.SupplyFormations);
    }

    // ── Concurrent observation of one preparation ───────────────────────────

    [Fact]
    public async Task S0_ConcurrentWaiters_JoinOnePreparation_AndObserveOneRetainedSupply()
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var pairCalls = 0;
        var probe = new Probe
        {
            PairOverride = HostOperation.CreateAsync("pair", async (_, token) =>
            {
                Interlocked.Increment(ref pairCalls);
                entered.TrySetResult();
                return await release.Task.WaitAsync(token);
            }),
        };
        Result.CallReference? reference = null;
        probe.OnMeta = cells => { reference = Reify(cells[0]); return Zero; };
        var run = probe.RunAsyncTwin("Add2(a, b) = a + b + tick()\nProbe(x) = (Meta(x), x)\nProbe(Add2(pair()*))");
        try
        {
            await entered.Task.WaitAsync(TimeSpan.FromSeconds(30));
            var plan = reference!.Plan;
            Assert.Null(plan.PreparedCells);
            var asyncWaiters = Enumerable.Range(0, 8).Select(_ => plan.PrepareSupply(asynchronous: true).AsTask()).ToArray();
            var syncWaiters = Enumerable.Range(0, 4).Select(_ => Task.Run(() => plan.PrepareSupply(asynchronous: false).AsTask())).ToArray();
            Assert.All(asyncWaiters, waiter => Assert.False(waiter.IsCompleted));
            release.TrySetResult(new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]));
            Assert.Equal("S[0, 4]", await run.WaitAsync(TimeSpan.FromSeconds(30)));
            var supplies = await Task.WhenAll(asyncWaiters.Concat(syncWaiters)).WaitAsync(TimeSpan.FromSeconds(30));
            Assert.All(supplies, supply => Assert.Same(plan.PreparedCells, supply.Value.Cells));
            Assert.Equal(1, plan.SupplyFormations);
            Assert.Equal(1, pairCalls);
        }
        finally
        {
            release.TrySetResult(Zero);
        }
    }

    // ── Optimizations kept and fail-closed ─────────────────────────────────

    [Fact]
    public void S0_Optimizations_DotAndExpressionPositionFusionAndPlannedLoopsStayAvailable()
    {
        static (string Outcome, long Fusions, long Loops) Observe(string source, bool plans)
        {
            var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
            var sequences = new SequencePipelineDiagnostics();
            var loops = new LoopOptimizationDiagnostics();
            using var activation = plans ? InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()) : null;
            var (result, budget) = Evaluator.RunCountedObserved(program, enableOptimizations: true,
                loopDiagnostics: loops, sequenceDiagnostics: sequences);
            Assert.Equal(plans || ForcedInvocationPlansHook.Forced, budget.PlanTestSeam is not null);
            var outcome = (result.IsOk ? "ok " + Neutral(result.Value.Value) : "err " + result.Error.Code)
                + $" steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} items={budget.MaterializedItems}";
            return (outcome, sequences.FilterCountFusionHits, loops.OptimizedLoopHits);
        }

        // A supplied DOT pipeline is not call-shaped, so it is no plan and keeps fusion.
        const string dotPipeline = "G(x) = x\nG(range(1, 20).filter({v > 2}).count)";
        // An expression-position pipeline is no supplied cell at all.
        const string rowPipeline = "count(filter(range(1, 20), {v > 2}))";
        // A planned loop inside a plan's builtin arm: the loop optimizer is untouched.
        const string supplyLoop = "Step(k) = k + 1\nG(x) = x\nG(repeat(Step(0), 200))";
        foreach (var source in new[] { dotPipeline, rowPipeline, supplyLoop })
        {
            var ordinary = Observe(source, plans: false);
            var planned = Observe(source, plans: true);
            Assert.Equal(ordinary, planned);
        }
        Assert.True(Observe(dotPipeline, plans: true).Fusions > 0);
        Assert.True(Observe(rowPipeline, plans: true).Fusions > 0);
        Assert.True(Observe(supplyLoop, plans: true).Loops > 0);

        // The one fail-closed case: a supplied PLAIN-call pipeline is a plan and runs generically,
        // with identical value and budgets (the M1 case PlannedSupply_DisablesFusion_…).
        const string plainSupplied = "G(x) = x\nG(count(filter(range(1, 20), {v > 2})))";
        var plainOrdinary = Observe(plainSupplied, plans: false);
        var plainPlanned = Observe(plainSupplied, plans: true);
        Assert.Equal(plainOrdinary.Outcome, plainPlanned.Outcome);
        Assert.Equal(ForcedInvocationPlansHook.Forced, plainOrdinary.Fusions == 0);
        Assert.Equal(0, plainPlanned.Fusions);
    }

    // ── Call-heavy programs: plan VALUE = ordinary VALUE, sync = async twin ──

    /// <summary>
    /// Programs dense in call-shaped supplied arguments: recursion through <c>if</c> branches, variadic
    /// and spread supplies, callbacks with nested supplied calls, loops, families, aliases, opened and
    /// parameter callees, explicit fresh property calls, selection, interpolation, unused and deep failures.
    /// </summary>
    public static TheoryData<string> CallHeavySources => new()
    {
        "Sq(x) = x * x\nSum(*xs) = sum(xs)\nSum(Sq(trace(1)), Sq(trace(2)), Sq(trace(3)))",
        "Down(n) = if(n == 0, trace(0), Down(n - 1))\nDown(25)",
        "Inc(n) = n + 1\nG(x) = x\nG(map(range(1, 5), {Inc(Inc(v))}))",
        "Pick(c, a, b) = if(c, a, b)\nPick(true, trace(1), trace(1 / 0))",
        "Step(k) = k + 1\nG(x) = x\nG(repeat(Step(trace(0)), 50))",
        "Step(k) = k + 1, k < 10\nG(x) = x\nG(while(Step(trace(0))))",
        "Fib(0) = 0\nFib(1) = 1\nFib(n) = Fib(n - 1) + Fib(n - 2)\nG(x) = x\nG(Fib(trace(10)))",
        "F(v) = v / 0\nH(x) = x + 1\nG(x) = x\nG(H(F(trace(3))))",
        "F(v) = v + 1\nG(x) = \"{x}!\"\nG(F(trace(2)))",
        "F(v) = (v, v + 1)\nG(x) = x[1]\nG(F(trace(2)))",
        "F(v) = (v, v)\nAdd2(a, b) = a + b\nG(x) = x\nG(Add2(F(trace(4))*))",
        "P = tick()\nG(x) = (x, x)\nG(P()), P, P, G(P())",
        "open Lib\nLib = { public F(v) = v * 2 }\nG(x) = x\nG(F(trace(3)))",
        "G(x) = x\nApply(f, v) = G(f(v))\nApply({k * 3}, trace(2))",
        "G(x) = x\nG(abs(trace(-3)))",
        "Keep(a, b) = a\nG(x) = x\nG(Keep(trace(1), Keep(trace(2), 1 / 0)))",
        "G(x) = x\nG(count(filter(range(1, trace(30)), {v > 2})))",
        "Pair2(v) = (v, v)\na, b = Pair2(trace(7))\nG(x) = x + 1\nG(a), G(b)",
        "F(v) = v + tick()\nTwice(x) = (x, x)\nTwice(F(trace(1))), Twice(F(trace(2)))",
        "Count(*xs) = xs.count\nWrap(*ys) = Count(ys*)\nWrap(trace(1), trace(2), pair()*)",
    };

    [Theory]
    [MemberData(nameof(CallHeavySources))]
    public void S0_PlanRoutedValue_ObservesExactlyTheOrdinaryValue_OnCallHeavyPrograms(string source)
    {
        foreach (var optimized in new[] { false, true })
        {
            var ordinary = new Probe();
            var expected = ordinary.Observe(source, experiment: false, optimized);
            var planned = new Probe();
            var actual = planned.Observe(source, experiment: true, optimized);
            Assert.Equal(expected, actual);
            Assert.Equal(ordinary.Log, planned.Log);
            Assert.Equal(ordinary.Accounting, planned.Accounting);
            Assert.True(planned.Observations.InvocationPlanCount > 0);
        }
    }

    [Theory]
    [MemberData(nameof(CallHeavySources))]
    public async Task S0_PlanRuns_SyncAndAsyncTwinAgree_OnCallHeavyPrograms(string source)
    {
        var sync = new Probe();
        var syncOutcome = sync.Observe(source, experiment: true, optimized: false);
        var twin = new Probe();
        var twinOutcome = await twin.ObserveAsyncTwin(source);
        Assert.Equal(syncOutcome, twinOutcome);
        Assert.Equal(sync.Log, twin.Log);
        Assert.Equal(sync.Observations.InvocationPlanCount, twin.Observations.InvocationPlanCount);
        Assert.Equal(sync.Observations.PlanSupplyFormationCount, twin.Observations.PlanSupplyFormationCount);
    }

    [Fact]
    public void S0_PlanRoutedValue_PreservesTightBudgetFailuresAndAccounting_OnRecursion()
    {
        const string source = "Down(n) = if(n == 0, trace(0), Down(n - 1))\nDown(6)";
        foreach (var optimized in new[] { false, true })
        foreach (var steps in Enumerable.Range(1, 45))
        {
            var limits = new EvaluationLimits { MaxSteps = steps };
            var ordinary = new Probe { Limits = limits };
            var planned = new Probe { Limits = limits };
            Assert.Equal(ordinary.Observe(source, false, optimized), planned.Observe(source, true, optimized));
            Assert.Equal(ordinary.Log, planned.Log);
            Assert.Equal(ordinary.Accounting, planned.Accounting);
        }
        foreach (var depth in Enumerable.Range(1, 12))
        {
            var limits = new EvaluationLimits { MaxDepth = depth };
            var ordinary = new Probe { Limits = limits };
            var planned = new Probe { Limits = limits };
            Assert.Equal(ordinary.Observe(source, false, false), planned.Observe(source, true, false));
            Assert.Equal(ordinary.Accounting, planned.Accounting);
        }
    }

    // ── Sync / async agreement in plan runs ─────────────────────────────────

    [Theory]
    [InlineData("F(v) = v + tick()\nG(x) = (x, x)\nG(F(trace(10)))")]
    [InlineData("F(a, b) = a\nG(x) = x\nG(F(trace(1), 1 / 0))")]
    [InlineData("F(v) = v\nG(x) = x\nG(F(trace(1), trace(2)))")]
    [InlineData("Add2(a, b) = a + b\nG(x) = (x, x)\nG(Add2(pair()*))")]
    [InlineData("Bad(v) = v / 0\nG(x) = x\nG(Bad(trace(1)))")]
    [InlineData("F(v) = v + 1\nG(x) = x * 2\nG(F(F(trace(1))))")]
    [InlineData("E(0) = 100\nE(n) = n\nG(x) = x\nG(E(trace(0)))")]
    [InlineData("G(x) = x\nG(count(trace([1, 2])))")]
    [InlineData("G(x) = x\nG(sum(map([1, 2, 3], {v * 2})))")]
    [InlineData("Fact(n) = if(n < 2, 1, n * Fact(n - 1))\nG(x) = x\nG(Fact(trace(5)))")]
    [InlineData("F(*xs) = count(xs)\nG(x) = x\nG(F(trace(1), trace(2), pair()*))")]
    [InlineData("G(x) = x\nG(Missing(trace(1)))")]
    [InlineData("F(v) = v + tick()\nAlias = F\nG(x) = x\nG(Alias(trace(5)))")]
    [InlineData("F(a, b) = a + b\nPack(*xs) = F(xs*)\nG(x) = x\nG(Pack(trace(1), trace(2)))")]
    [InlineData("F(0) = 1\nF(1) = 2\nG(x) = x\nG(F(trace(2)))")]
    [InlineData("F((a, b)) = b + a\nG(x) = x\nG(F((trace(1), trace(2))))")]
    [InlineData("Down(n) = if(n == 0, 0, Down(n - 1))\nDown(trace(30))")]
    [InlineData("Inc(n) = n + 1\nApply(f, v) = f(v)\nG(x) = x\nG(Apply(Inc, trace(41)))")]
    public async Task S0_PlanRuns_SyncAndAsyncTwinAgree(string source)
    {
        var sync = new Probe();
        var syncOutcome = sync.Observe(source, experiment: true, optimized: false);
        var twin = new Probe();
        var twinOutcome = await twin.ObserveAsyncTwin(source);
        Assert.Equal(syncOutcome, twinOutcome);
        Assert.Equal(sync.Log, twin.Log);
        Assert.Equal(sync.Observations.InvocationPlanCount, twin.Observations.InvocationPlanCount);
        Assert.Equal(sync.Observations.PlanSupplyFormationCount, twin.Observations.PlanSupplyFormationCount);
    }

    // ── Ordinary programs: plan runs observe exactly the ordinary runs ──────

    /// <summary>
    /// NO OBSERVABLE DIFFERENCE ON EXISTING PROGRAMS: every corpus program
    /// (<see cref="CorpusExecutionEquivalenceTests.Corpus"/>: language-spec cases and probes, semantic
    /// explorer surface cases) has the same value or error (code, message, span) and the same budget
    /// accounting — steps, expression checkpoints, peak depth, materialized items and string units — with
    /// plans as without, on the generic and the optimized strategy. The plan counts prove the comparison
    /// actually ran plan executions.
    /// </summary>
    [Fact]
    public void S0_PlanRuns_MatchOrdinaryRuns_OverTheCorpora()
    {
        var mismatches = new List<string>();
        long plans = 0, formations = 0;
        foreach (var (id, program) in CorpusExecutionEquivalenceTests.Corpus)
        foreach (var optimized in new[] { false, true })
        {
            var ordinary = ObserveCorpusRun(program, optimized, plans: false, observations: null);
            var observations = new EvaluationObservations();
            var planned = ObserveCorpusRun(program, optimized, plans: true, observations);
            plans += observations.InvocationPlanCount;
            formations += observations.PlanSupplyFormationCount;
            if (ordinary != planned)
                mismatches.Add($"{id} (optimized={optimized}): ordinary=[{ordinary}] planned=[{planned}]");
        }

        Assert.True(mismatches.Count == 0,
            $"{mismatches.Count} corpus runs disagreed:\n" + string.Join("\n", mismatches.Take(25)));
        // Non-vacuity: the corpora are short programs, but hundreds of their supplied arguments are
        // call-shaped (445 plans and their formations at the time of writing, over both strategies).
        Assert.True(plans >= 200 && formations >= 100, $"only {plans} plans were created and {formations} supplies formed");
    }

    /// <summary>The async twin of <see cref="S0_PlanRuns_MatchOrdinaryRuns_OverTheCorpora"/>.</summary>
    [Fact]
    public async Task S0_PlanRuns_MatchOrdinaryRuns_OverTheCorpora_OnTheAsyncTwin()
    {
        var mismatches = new List<string>();
        long plans = 0;
        foreach (var (id, program) in CorpusExecutionEquivalenceTests.Corpus)
        {
            var ordinary = await ObserveCorpusRunAsync(program, plans: false, observations: null);
            var observations = new EvaluationObservations();
            var planned = await ObserveCorpusRunAsync(program, plans: true, observations);
            plans += observations.InvocationPlanCount;
            if (ordinary != planned)
                mismatches.Add($"{id}: ordinary=[{ordinary}] planned=[{planned}]");
        }

        Assert.True(mismatches.Count == 0,
            $"{mismatches.Count} corpus runs disagreed:\n" + string.Join("\n", mismatches.Take(25)));
        Assert.True(plans >= 100, $"only {plans} plans were created");
    }

    private static string ObserveCorpusRun(Expr program, bool optimized, bool plans, EvaluationObservations? observations)
    {
        using var activation = plans ? InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()) : null;
        var (result, budget) = Evaluator.RunCountedObserved(program, enableOptimizations: optimized,
            observations: observations, randomSeed: 5);
        Assert.Equal(plans || ForcedInvocationPlansHook.Forced, budget.PlanTestSeam is not null);
        return CorpusOutcome(result, budget);
    }

    private static async Task<string> ObserveCorpusRunAsync(Expr program, bool plans, EvaluationObservations? observations)
    {
        using var activation = plans ? InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()) : null;
        var (result, budget) = await Evaluator.RunCountedObservedAsync(program,
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
            observations: observations, randomSeed: 5);
        Assert.Equal(plans || ForcedInvocationPlansHook.Forced, budget.PlanTestSeam is not null);
        return CorpusOutcome(result, budget);
    }

    private static string CorpusOutcome(EvalResult<Evaluator.CountedResult> result, EvaluationBudget budget)
        => (result.IsOk
                ? $"ok {Neutral(result.Value.Value)} n={result.Value.EmittedCount}"
                : $"err {result.Error.Code}: {result.Error} @ {result.Error.Span}")
            + $" steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} depth={budget.PeakDepth}"
            + $" items={budget.MaterializedItems} strings={budget.MaterializedStringChars}";
}
