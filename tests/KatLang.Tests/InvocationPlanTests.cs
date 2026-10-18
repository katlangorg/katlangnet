using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// INVOCATION-PLAN INVARIANTS: one invocation plan shared by VALUE and META, observed directly through the
/// internal <see cref="InvocationPlanTestSeam"/> (the authoritative Lean plan is <c>NeedPlan</c> in
/// <c>lean/KatLang.lean</c>; laws <c>lean/KatLangArityLaws/InvocationPlan.lean</c>). Every program runs through
/// the PRODUCTION supplied cells: <c>SupplyCell</c> → <c>NeedCell</c> → <c>Demand</c>/<c>DemandAsync</c>.
/// <c>Meta</c> is a host operation registered as an internal META receiver: it receives the transported cells
/// unforced and reaches the plan below the surface <c>meta</c> binder (whose language-level cases are
/// <c>CallReferenceS1Tests</c>/<c>CallReferenceS2Tests</c>). <c>trace(x)</c>, <c>tick()</c> and <c>pair()</c>
/// are counting host operations. The assertions check object identity of plans, references and need cells,
/// in addition to values. The retention-representation cases are in <c>CallPlanRetentionTests.cs</c>.
/// </summary>
public partial class InvocationPlanTests
{
    // Every bounded wait in this file is a hang guard, never a latency claim: what it waits for
    // runs as thread-pool work, which a loaded CI runner can delay well past a tight bound (a
    // 10 s guard timed out in CI in October 2026).
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    // ── Plan identity and capture inertia ───────────────────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MetaTwice_ReifiesOnePlan_WithoutRunningAnything(bool optimized)
    {
        var probe = new Probe();
        Result.CallReference? first = null, second = null;
        probe.OnMeta = cells =>
        {
            first = Reify(cells[0]);
            second = Reify(cells[0]);
            return Zero;
        };

        var value = probe.Run("""
            F(v) = v + tick()
            Probe(x) = Meta(x)
            Probe(F(trace(10)))
            """, optimized);

        Assert.Equal("0", value);
        Assert.Same(first, second);
        Assert.Same(first!.Plan, second!.Plan);
        Assert.Equal(0, probe.Traces);
        Assert.Equal(0, probe.Ticks);
        Assert.Equal(0, first.Plan.SupplyFormations);
        Assert.Null(first.Plan.PreparedCells);
        Assert.False(first.Plan.Owner.HasCompletedValue);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ValueThenMeta_ThenTwoInvocations_ReuseTheArgumentCell_AndLeaveTheValueMemoized(bool optimized)
    {
        var probe = new Probe();
        Result.CallReference? reference = null;
        IReadOnlyList<NeedCell>? before = null;
        probe.OnMeta = cells =>
        {
            reference = Reify(cells[0]);
            Assert.True(reference.Plan.Owner.HasCompletedValue);
            Assert.Same(cells[0], reference.Plan.Owner);
            before = reference.Plan.PreparedCells;
            var first = reference.Invoke();
            var second = reference.Invoke();
            Assert.Same(Assert.Single(before!), Assert.Single(reference.Plan.PreparedCells!));
            return new Result.SequenceValue([first.Value.Value, second.Value.Value]);
        };

        var value = probe.Run("""
            F(v) = v + tick()
            Probe(x) = (x, Meta(x))
            Probe(F(trace(10)))
            """, optimized);

        // VALUE ran the target once (tick 1); each invocation ran it afresh (ticks 2 and 3) over the
        // SAME argument cell, whose trace ran once.
        Assert.Equal("S[11, S[12, 13]]", value);
        Assert.Equal(1, probe.Traces);
        Assert.Equal(3, probe.Ticks);
        Assert.Equal(1, reference!.Plan.SupplyFormations);
        // The original VALUE is still the first completion, not an invocation's.
        Assert.Equal("11", Neutral(reference.Plan.Owner.Demand().Value.Value));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MetaThenInvocation_ThenValue_SharesTheSupply_AndComputesTheOriginalValueSeparately(bool optimized)
    {
        var probe = new Probe();
        Result.CallReference? reference = null;
        probe.OnMeta = cells =>
        {
            reference = Reify(cells[0]);
            var invoked = reference.Invoke();
            Assert.False(reference.Plan.Owner.HasCompletedValue);
            return invoked.Value.Value;
        };

        var value = probe.Run("""
            F(v) = v + tick()
            Probe(x) = (Meta(x), x)
            Probe(F(trace(10)))
            """, optimized);

        Assert.Equal("S[11, 12]", value);
        Assert.Equal(1, probe.Traces);
        Assert.Equal(2, probe.Ticks);
        Assert.Equal(1, reference!.Plan.SupplyFormations);
        Assert.True(reference.Plan.Owner.HasCompletedValue);
        Assert.Equal("12", Neutral(reference.Plan.Owner.Demand().Value.Value));
    }

    /// <summary>
    /// M1.5 parity with Lean <c>nestedCallUsesThePlan</c>: a call supplied INSIDE a user body is its own
    /// plan, and the nested VALUE demand (Probe's read of <c>x</c>) executes through that plan.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void NestedSuppliedCall_InsideABody_ValueRunsThroughItsOwnPlan(bool optimized)
    {
        var probe = new Probe();
        Result.CallReference? reference = null;
        probe.OnMeta = cells =>
        {
            reference = Reify(cells[0]);
            Assert.True(reference.Plan.Owner.HasCompletedValue);
            Assert.Equal(1, reference.Plan.SupplyFormations);
            var prepared = Assert.Single(reference.Plan.PreparedCells!);
            var invoked = reference.Invoke();
            Assert.Same(prepared, Assert.Single(reference.Plan.PreparedCells!));
            return invoked.Value.Value;
        };

        var value = probe.Run("""
            F(v) = v + tick()
            Probe(x) = (x, Meta(x))
            G(v) = Probe(F(v))
            G(trace(41))
            """, optimized);

        Assert.Equal("S[42, 43]", value);
        Assert.Equal(1, probe.Traces);
        Assert.Equal(2, probe.Ticks);
        Assert.Equal(1, reference!.Plan.SupplyFormations);
        Assert.Equal("42", Neutral(reference.Plan.Owner.Demand().Value.Value));
    }

    // ── Transparent forwarding ──────────────────────────────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PlainForwarding_ThroughOneAndTwoWrappers_TransportsTheOriginalCellAndPlan(bool optimized)
    {
        var probe = new Probe();
        var received = new List<NeedCell?>();
        probe.OnMeta = cells =>
        {
            received.Add(cells[0]);
            var reference = Reify(cells[0]);
            Assert.Same(cells[0], reference.Plan.Owner);
            return reference.Invoke().Value.Value;
        };

        var value = probe.Run("""
            F(v) = v + tick()
            Forward(y) = Meta(y)
            Forward2(z) = Forward(z)
            (Forward(F(trace(10))), Forward2(F(trace(20))))
            """, optimized);

        Assert.Equal("S[11, 22]", value);
        Assert.Equal(2, received.Count);
        // Each receiver got the ORIGINAL call cell, not a cell for the forwarding parameter.
        Assert.All(received, cell => Assert.IsType<Expr.Call>(cell!.Source));
        Assert.NotSame(received[0], received[1]);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ForwardedCell_AlreadyDemanded_StillReifiesItsOriginalPlan_WithoutReformingTheSupply(bool optimized)
    {
        var probe = new Probe();
        Result.CallReference? reference = null;
        probe.OnMeta = cells =>
        {
            reference = Reify(cells[0]);
            Assert.True(reference.Plan.Owner.HasCompletedValue);
            return reference.Invoke().Value.Value;
        };

        var value = probe.Run("""
            F(v) = v + tick()
            Forward(y) = Meta(y)
            Forward2(z) = (z, Forward(z))
            Forward2(F(trace(10)))
            """, optimized);

        Assert.Equal("S[11, 12]", value);
        Assert.Equal(1, probe.Traces);
        Assert.Equal(1, reference!.Plan.SupplyFormations);
    }

    // ── Distinctness ────────────────────────────────────────────────────────

    [Fact]
    public void SameWrittenCall_AtTwoDynamicOccurrences_IsTwoPlans_WithTwoArgumentCells()
    {
        var probe = new Probe();
        var references = new List<Result.CallReference>();
        probe.OnMeta = cells =>
        {
            var reference = Reify(cells[0]);
            references.Add(reference);
            return reference.Invoke().Value.Value;
        };

        var value = probe.Run("""
            F(v) = v + tick()
            G(k) = Meta(F(trace(k)))
            (G(1), G(2))
            """);

        Assert.Equal("S[2, 4]", value);
        Assert.Equal(2, references.Count);
        Assert.NotSame(references[0].Plan, references[1].Plan);
        Assert.NotSame(references[0].Plan.Owner, references[1].Plan.Owner);
        Assert.NotSame(Assert.Single(references[0].Plan.PreparedCells!), Assert.Single(references[1].Plan.PreparedCells!));
        Assert.Equal(2, probe.Traces);
    }

    [Fact]
    public void TwoCalls_TransportingOneParameter_AreTwoPlans_SharingExactlyThatCell()
    {
        var probe = new Probe();
        var references = new List<Result.CallReference>();
        probe.OnMeta = cells =>
        {
            var reference = Reify(cells[0]);
            references.Add(reference);
            return reference.Invoke().Value.Value;
        };

        var value = probe.Run("""
            F(v) = v + tick()
            H(x) = (Meta(F(x)), Meta(F(x)))
            H(trace(5))
            """);

        Assert.Equal("S[6, 7]", value);
        Assert.NotSame(references[0].Plan, references[1].Plan);
        Assert.Same(Assert.Single(references[0].Plan.PreparedCells!), Assert.Single(references[1].Plan.PreparedCells!));
        Assert.Equal(1, probe.Traces);
    }

    // ── Strictness: unused failures, spreads, cardinality ───────────────────

    [Fact]
    public void UnusedFailingArgument_IsNeverDemanded_ByMetaInvocationOrValue()
    {
        var probe = new Probe();
        Result.CallReference? reference = null;
        probe.OnMeta = cells =>
        {
            reference = Reify(cells[0]);
            return reference.Invoke().Value.Value;
        };

        var value = probe.Run("""
            Keep(a, b) = a
            Probe(x) = (Meta(x), x)
            Probe(Keep(trace(7), 1 / 0))
            """);

        Assert.Equal("S[7, 7]", value);
        Assert.Equal(1, probe.Traces);
        Assert.False(reference!.Plan.PreparedCells![1].HasCompletedValue);
    }

    [Fact]
    public void ArbitrarySpread_IsNotOpenedByMeta_IsPreparedOnce_AndIsReusedByEveryExecution()
    {
        var probe = new Probe();
        Result.CallReference? reference = null;
        probe.OnMeta = cells =>
        {
            reference = Reify(cells[0]);
            Assert.Equal(0, probe.Pairs);
            var first = reference.Invoke();
            Assert.Equal(1, probe.Pairs);
            var second = reference.Invoke();
            Assert.Equal(1, probe.Pairs);
            return new Result.SequenceValue([first.Value.Value, second.Value.Value]);
        };

        var value = probe.Run("""
            Add2(a, b) = a + b + tick()
            Probe(x) = (Meta(x), x)
            Probe(Add2(pair()*))
            """);

        Assert.Equal("S[S[4, 5], 6]", value);
        Assert.Equal(1, probe.Pairs);
        Assert.Equal(1, reference!.Plan.SupplyFormations);
        Assert.Equal(2, reference.Plan.PreparedCells!.Count);
    }

    [Fact]
    public void WrongCardinality_IsRejectedBeforeAnyArgumentDemand_OnInvocation()
    {
        var probe = new Probe();
        EvalResult<Evaluator.CountedResult>? invoked = null;
        probe.OnMeta = cells =>
        {
            invoked = Reify(cells[0]).Invoke();
            return Zero;
        };

        Assert.Equal("0", probe.Run("""
            F(v) = v
            Probe(x) = Meta(x)
            Probe(F(trace(1), trace(2)))
            """));

        Assert.True(invoked!.Value.IsError);
        Assert.Equal(KatLangErrorCode.ArityMismatch, invoked.Value.Error.Code);
        Assert.Equal(0, probe.Traces);
    }

    [Fact]
    public void FailingValue_ThenMeta_KeepsTheStickyFailure_AndAnInvocationFailsAfresh()
    {
        var probe = new Probe();
        probe.OnMeta = cells =>
        {
            var owner = cells[0]!;
            var failed = owner.Demand();
            Assert.True(failed.IsError);
            Assert.Equal(1, probe.Ticks);
            var reference = Reify(owner);
            Assert.Same(owner, reference.Plan.Owner);
            var again = owner.Demand();
            Assert.Same(failed.Error, again.Error);
            Assert.Equal(1, probe.Ticks);
            var invoked = reference.Invoke();
            Assert.True(invoked.IsError);
            Assert.Equal(failed.Error.Code, invoked.Error.Code);
            Assert.Equal(2, probe.Ticks);
            Assert.Same(failed.Error, owner.Demand().Error);
            return Zero;
        };

        Assert.Equal("0", probe.Run("""
            Bad(v) = tick() + v / 0
            Probe(x) = Meta(x)
            Probe(Bad(1))
            """));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FailingSpread_PreparationIsSticky_InEitherExecutionOrder(bool valueFirst)
    {
        var probe = new Probe();
        probe.OnMeta = cells =>
        {
            var owner = cells[0]!;
            var reference = Reify(owner);
            Assert.Equal(0, probe.Ticks);
            var first = valueFirst ? owner.Demand() : reference.Invoke();
            var second = valueFirst ? reference.Invoke() : owner.Demand();
            var third = reference.Invoke();
            Assert.All(new[] { first, second, third }, result =>
            {
                Assert.True(result.IsError);
                Assert.Equal(KatLangErrorCode.DivisionByZero, result.Error.Code);
            });
            Assert.Equal(1, probe.Ticks);
            Assert.Equal(1, reference.Plan.SupplyFormations);
            Assert.Null(reference.Plan.PreparedCells);
            Assert.Same(reference, Reify(owner));
            Assert.Same((valueFirst ? first : second).Error, owner.Demand().Error);
            return Zero;
        };

        Assert.Equal("0", probe.Run("F(*xs) = count(xs)\nMeta(F((tick() + 1 / 0)*))"));
    }

    [Fact]
    public void CollectorSpread_TransportsOriginalCallCells_ThroughMetaAndValue()
    {
        var probe = new Probe();
        var references = new List<Result.CallReference>();
        probe.OnMeta = cells =>
        {
            references.Add(Reify(cells[0]));
            return Zero;
        };

        Assert.Equal("S[0, 0, 6, 7]", probe.Run("""
            F(v) = v + tick()
            Observe(a, b) = { Meta(a), Meta(b), a, b }
            Pack(*xs) = Observe(xs*)
            Pack(F(trace(5)), F(trace(5)))
            """));
        Assert.Equal(2, references.Count);
        Assert.NotSame(references[0].Plan.Owner, references[1].Plan.Owner);
        Assert.All(references, reference => Assert.IsType<Expr.Call>(reference.Plan.Owner.Source));
        Assert.Equal(2, probe.Traces);
    }

    [Fact]
    public void HostExceptionDuringPreparation_IsSticky_AcrossInvocationAndValue()
    {
        var expected = new InvalidOperationException("spread failure");
        var calls = 0;
        var probe = new Probe
        {
            PairOverride = HostOperation.Create("pair", (_, _) => { calls++; throw expected; }),
        };
        probe.OnMeta = cells =>
        {
            var reference = Reify(cells[0]);
            Assert.Same(expected, Assert.Throws<InvalidOperationException>(() => reference.Invoke()));
            Assert.Same(expected, Assert.Throws<InvalidOperationException>(() => reference.Plan.Owner.Demand()));
            Assert.Same(expected, Assert.Throws<InvalidOperationException>(() => reference.Invoke()));
            Assert.Equal(1, reference.Plan.SupplyFormations);
            Assert.Equal(1, calls);
            return Zero;
        };
        Assert.Equal("0", probe.Run("F(*xs) = count(xs)\nMeta(F(pair()*))"));
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public async Task TerminalFailure_PreventsAnotherTargetExecution_AndCannotBeAbsorbed(bool asyncTwin, bool invokeFirst)
    {
        var probe = new Probe { Limits = new EvaluationLimits { MaxCollectionItems = 2 } };
        probe.OnMeta = cells =>
        {
            var owner = cells[0]!;
            var reference = Reify(owner);
            var failed = invokeFirst ? reference.Invoke() : owner.Demand();
            Assert.True(failed.IsError && failed.Error.IsResourceLimit);
            Assert.Equal(1, probe.Ticks);
            var invoked = reference.Invoke();
            Assert.True(invoked.IsError);
            Assert.Equal(failed.Error.Code, invoked.Error.Code);
            var demanded = owner.Demand();
            Assert.Equal(failed.Error.Code, demanded.Error.Code);
            if (!invokeFirst) Assert.Same(failed.Error, demanded.Error);
            Assert.Equal(!invokeFirst, owner.HasCompletedValue);
            Assert.Equal(1, probe.Ticks);
            return Zero;
        };
        const string source = "F(v) = tick() + count(range(1, 4)) + v\nMeta(F(5))";
        var outcome = asyncTwin
            ? await probe.ObserveAsyncTwin(source)
            : probe.Observe(source, experiment: true, optimized: false);
        Assert.StartsWith("err CollectionSizeLimitExceeded", outcome);
    }

    // ── Lexical ownership ───────────────────────────────────────────────────

    [Fact]
    public void ForwardingIntoAShadowingScope_KeepsTheOriginalCallee()
    {
        var probe = new Probe();
        probe.OnMeta = cells => Reify(cells[0]).Invoke().Value.Value;

        Assert.Equal("6", probe.Run("""
            F(v) = v + 1
            Box = {
                F(v) = v * 100
                public Run(y) = Meta(y)
            }
            Box.Run(F(5))
            """));
    }

    [Fact]
    public void ParameterCallee_IsResolvedThroughTheCallersSuppliedCell()
    {
        var probe = new Probe();
        probe.OnMeta = cells => Reify(cells[0]).Invoke().Value.Value;

        Assert.Equal("8", probe.Run("""
            Double(n) = n * 2
            Apply(f, v) = Meta(f(v))
            Apply(Double, 4)
            """));
    }

    // ── META refusals and the ordinary path ─────────────────────────────────

    [Theory]
    [InlineData("Probe(5)")]
    [InlineData("Probe(5 + 1)")]
    [InlineData("Probe((1, 2))")]
    [InlineData("Probe(Box.V)")]
    [InlineData("Probe(Box.Get(1))")]
    [InlineData("Probe((Box.Get)(1))")]
    public void Meta_RefusesWhatIsNotAPlannableSuppliedCall_WithoutDemandingIt(string call)
    {
        var probe = new Probe();
        EvalResult<Result.CallReference>? refused = null;
        probe.OnMeta = cells =>
        {
            refused = Evaluator.ReifyMeta(cells[0]);
            Assert.False(cells[0]!.HasCompletedValue);
            return Zero;
        };

        Assert.Equal("0", probe.Run($$"""
            Box = {
                public V = trace(1)
                public Get(k) = trace(k)
            }
            Probe(x) = Meta(x)
            {{call}}
            """));

        Assert.True(refused!.Value.IsError);
        Assert.Equal(Evaluator.MetaRefusalDescription, Assert.IsType<EvalError.NotAnAlgorithm>(refused.Value.Error).Description);
        Assert.Equal(0, probe.Traces);
    }

    [Fact]
    public void OrdinaryRun_HasNoPlans()
    {
        var probe = new Probe();
        var value = probe.RunWithoutExperiment("""
            F(v) = v + tick()
            G(x) = (x, x)
            G(F(trace(10)))
            """);
        Assert.Equal("S[11, 11]", value);
        Assert.Equal(1, probe.Traces);
        Assert.Equal(1, probe.Ticks);
    }

    /// <summary>
    /// PLAN-ROUTED VALUE = ORDINARY VALUE. Without META, an experimental run observes exactly what the
    /// ordinary run observes: the same value or error (code, message and span) and the same host log,
    /// on the generic and the optimized strategies.
    /// </summary>
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
    [InlineData("a, b = tick(), 5\nG(x) = (x, x)\nG(a()), G(b()), a, b")]
    [InlineData("F(v) = v + tick()\nAlias = F\nG(x) = x\nG(Alias(trace(5)))")]
    [InlineData("F(a, b) = a + b\nPack(*xs) = F(xs*)\nG(x) = x\nG(Pack(trace(1), trace(2)))")]
    [InlineData("F(0) = 1\nF(1) = 2\nG(x) = x\nG(F(trace(2)))")]
    [InlineData("F((a, b)) = b + a\nG(x) = x\nG(F((trace(1), trace(2))))")]
    public void PlanRoutedValue_ObservesExactlyTheOrdinaryValue(string source)
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
        }
    }

    [Fact]
    public void PlanRoutedValue_PreservesTightBudgetFailuresAndAccounting()
    {
        const string source = "F(v) = tick() + v\nG(x) = (x, x)\nG(F(trace(5)))";
        foreach (var optimized in new[] { false, true })
        foreach (var steps in Enumerable.Range(1, 12))
        {
            var limits = new EvaluationLimits { MaxSteps = steps };
            var ordinary = new Probe { Limits = limits };
            var planned = new Probe { Limits = limits };
            Assert.Equal(ordinary.Observe(source, false, optimized), planned.Observe(source, true, optimized));
            Assert.Equal(ordinary.Log, planned.Log);
            Assert.Equal(ordinary.Accounting, planned.Accounting);
        }
    }

    [Fact]
    public void PlannedSupply_DisablesFusion_WhilePreservingValuesEffectsAndBudgets()
    {
        const string source = "G(x) = x\nG(count(filter(range(1, 20), {v > 2})))";
        var ordinary = new Probe();
        var planned = new Probe();
        Assert.Equal(ordinary.Observe(source, false, true), planned.Observe(source, true, true));
        Assert.Equal(ordinary.Accounting, planned.Accounting);
        Assert.Equal(ordinary.Log, planned.Log);
        // In the forced whole-suite plan run (ForcedInvocationPlansHook) the "ordinary" run is planned too.
        Assert.Equal(!ForcedInvocationPlansHook.Forced, ordinary.Sequences.FilterCountFusionHits > 0);
        Assert.Equal(0, planned.Sequences.FilterCountFusionHits);
    }

    // ── Async twin ──────────────────────────────────────────────────────────

    [Fact]
    public async Task AsyncTwin_ValueThenMeta_ThenInvocations_ShareThePlan()
    {
        var probe = new Probe();
        Result.CallReference? reference = null;
        probe.OnMeta = cells =>
        {
            reference = Reify(cells[0]);
            Assert.True(reference.Plan.Owner.HasCompletedValue);
            return reference.Invoke().Value.Value;
        };

        var value = await probe.RunAsyncTwin("""
            Add2(a, b) = a + b + tick()
            Probe(x) = (x, Meta(x))
            Probe(Add2(pair()*))
            """);

        Assert.Equal("S[4, 5]", value);
        Assert.Equal(1, probe.Pairs);
        Assert.Equal(1, reference!.Plan.SupplyFormations);
    }

    [Fact]
    public async Task SuspendedPreparation_JoinsValueFlight_AndInvokeAsyncReusesItsCells()
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
            await entered.Task.WaitAsync(WaitLimit);
            Assert.False(run.IsCompleted);
            Assert.False(reference!.Plan.Owner.HasCompletedValue);
            Assert.Null(reference.Plan.PreparedCells);
            var joined = reference.Plan.PrepareSupply(asynchronous: true).AsTask();
            Assert.False(joined.IsCompleted);
            // Concurrent META reads are inert while the real VALUE flight is suspended.
            var reads = await Task.WhenAll(Enumerable.Range(0, 16).Select(_ => Task.Run(() => Reify(reference.Plan.Owner))));
            Assert.All(reads, item => Assert.Same(reference, item));
            release.TrySetResult(new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]));
            Assert.Equal("S[0, 4]", await run.WaitAsync(WaitLimit));
            var supply = await joined.WaitAsync(WaitLimit);
            Assert.Same(supply.Value.Cells, reference.Plan.PreparedCells);
            Assert.Equal("5", Neutral((await reference.InvokeAsync()).Value.Value));
            Assert.Equal("6", Neutral((await reference.InvokeAsync()).Value.Value));
            Assert.Equal("4", Neutral((await reference.Plan.Owner.DemandAsync()).Value.Value));
            Assert.Equal(1, pairCalls);
            Assert.Equal(1, reference.Plan.SupplyFormations);
            Assert.Same(supply.Value.Cells, reference.Plan.PreparedCells);
        }
        finally
        {
            release.TrySetResult(Zero);
        }
    }

    [Fact]
    public async Task CancelledPreparation_IsSticky_AndNeitherValueNorInvokeCanRestartIt()
    {
        using var cancellation = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var probe = new Probe
        {
            PairOverride = HostOperation.CreateAsync("pair", async (_, token) =>
            {
                Interlocked.Increment(ref calls);
                entered.TrySetResult();
                return await release.Task.WaitAsync(token);
            }),
        };
        Result.CallReference? reference = null;
        probe.OnMeta = cells => { reference = Reify(cells[0]); return Zero; };
        var run = probe.RunAsyncTwin("F(*xs) = count(xs)\nProbe(x) = (Meta(x), x)\nProbe(F(pair()*))", cancellation.Token);
        try
        {
            await entered.Task.WaitAsync(WaitLimit);
            var joined = reference!.Plan.PrepareSupply(asynchronous: true).AsTask();
            cancellation.Cancel();
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(WaitLimit));
            Assert.Equal(cancellation.Token, error.CancellationToken);
            await Assert.ThrowsAnyAsync<OperationCanceledException>(() => joined.WaitAsync(WaitLimit));
            await Assert.ThrowsAnyAsync<OperationCanceledException>(() => reference.Plan.PrepareSupply(true).AsTask());
            await Assert.ThrowsAnyAsync<OperationCanceledException>(() => reference.InvokeAsync().AsTask());
            await Assert.ThrowsAnyAsync<OperationCanceledException>(() => reference.Plan.Owner.DemandAsync().AsTask());
            Assert.Same(reference, Reify(reference.Plan.Owner));
            Assert.True(reference.Plan.Owner.HasCompletedValue);
            Assert.Equal(1, reference.Plan.SupplyFormations);
            Assert.Equal(1, calls);
            Assert.Equal(0, probe.Ticks);
        }
        finally
        {
            cancellation.Cancel();
            release.TrySetResult(Zero);
        }
    }

    // ── Harness ─────────────────────────────────────────────────────────────

    private static readonly Result Zero = new Result.Atom(0);

    private static Result.CallReference Reify(NeedCell? cell)
    {
        var reified = Evaluator.ReifyMeta(cell);
        Assert.True(reified.IsOk, reified.IsError ? reified.Error.ToString() : null);
        return reified.Value;
    }

    private static string Neutral(Result value) => value switch
    {
        Result.Atom atom => ValueTextRenderer.FormatNumberInvariant(atom.Value),
        Result.Str text => "'" + text.Value + "'",
        Result.Bool boolean => boolean.Value ? "true" : "false",
        Result.SequenceValue sequence => "S[" + string.Join(", ", sequence.Items.Select(Neutral)) + "]",
        Result.ListValue list => "L[" + string.Join(", ", list.Items.Select(Neutral)) + "]",
        // A run result never holds one (the run boundary refuses it).
        Result.CallReference => "CallReference",
    };

    private sealed class Probe
    {
        public Func<IReadOnlyList<NeedCell?>, Result> OnMeta { get; set; } = _ => throw new InvalidOperationException("no META receiver");
        public List<string> Log { get; } = [];
        public int Traces { get; private set; }
        public int Ticks { get; private set; }
        public int Pairs { get; private set; }
        public EvaluationLimits? Limits { get; init; }
        public HostOperation? PairOverride { get; init; }
        public SequencePipelineDiagnostics Sequences { get; } = new();
        /// <summary>The last observed run's passive observations (plan and supply counts, S0).</summary>
        public EvaluationObservations Observations { get; private set; } = new();
        private EvaluationBudget? Budget { get; set; }
        public (long Steps, long Checkpoints, int Depth, long Items, long Chars) Accounting
            => (Budget!.ConsumedSteps, Budget.ConsumedExpressionCheckpoints, Budget.PeakDepth,
                Budget.MaterializedItems, Budget.MaterializedStringChars);

        private HostOperations Operations => HostOperations.Create(
            HostOperation.Create("trace", (args, _) => { Traces++; Log.Add("trace(" + Neutral(args[0]) + ")"); return args[0]; }, "x"),
            HostOperation.Create("tick", (_, _) => { Ticks++; Log.Add("tick"); return new Result.Atom(Ticks); }),
            PairOverride ?? HostOperation.Create("pair", (_, _) => { Pairs++; Log.Add("pair"); return new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]); }),
            HostOperation.Create("Meta", (_, _) => throw new InvalidOperationException("META receiver reached as an ordinary host operation"), "operation"));

        private InvocationPlanTestSeam Experiment => new(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>> { ["Meta"] = cells => OnMeta(cells) });

        public string Run(string source, bool optimized = false)
        {
            var observed = Observe(source, experiment: true, optimized);
            Assert.StartsWith("ok ", observed, StringComparison.Ordinal);
            return observed["ok ".Length..];
        }

        public string RunWithoutExperiment(string source)
        {
            var observed = Observe(source, experiment: false, optimized: false);
            Assert.StartsWith("ok ", observed, StringComparison.Ordinal);
            return observed["ok ".Length..];
        }

        public string Observe(string source, bool experiment, bool optimized)
        {
            var operations = Operations;
            var program = Program(source, operations);
            using var activation = experiment ? InvocationPlanTestSeam.Activate(Experiment) : null;
            Observations = new();
            var (result, budget) = Evaluator.RunCountedObserved(program, limits: Limits, enableOptimizations: optimized,
                sequenceDiagnostics: Sequences, observations: Observations, hostOperations: operations);
            Budget = budget;
            Assert.Equal(experiment || ForcedInvocationPlansHook.Forced, budget.PlanTestSeam is not null);
            return result.IsOk
                ? "ok " + Neutral(result.Value.Value)
                : $"err {result.Error.Code}: {result.Error} @ {result.Error.Span}";
        }

        public async Task<string> RunAsyncTwin(string source, CancellationToken cancellationToken = default)
        {
            var observed = await ObserveAsyncTwin(source, cancellationToken);
            Assert.StartsWith("ok ", observed, StringComparison.Ordinal);
            return observed["ok ".Length..];
        }

        public async Task<string> ObserveAsyncTwin(string source, CancellationToken cancellationToken = default)
        {
            var operations = Operations;
            var program = Program(source, operations);
            using var activation = InvocationPlanTestSeam.Activate(Experiment);
            Observations = new();
            var (result, budget) = await Evaluator.RunCountedObservedAsync(
                program,
                limits: Limits,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                observations: Observations,
                hostOperations: operations, cancellationToken: cancellationToken);
            Assert.NotNull(budget.PlanTestSeam);
            return result.IsOk
                ? "ok " + Neutral(result.Value.Value)
                : $"err {result.Error.Code}: {result.Error} @ {result.Error.Span}";
        }

        private static Expr Program(string source, HostOperations operations)
        {
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
            return new Expr.AlgorithmExpr(parsed.Root);
        }
    }
}
