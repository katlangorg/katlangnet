using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// INNER-PROPERTY LIFETIME (November 2026, owner decision): the storage of a zero-argument
/// property entry and of a runtime-alias binding cell follows the RESOLVED DECLARING BINDING AND
/// ITS OWNING INVOCATION. Exposure still governs accessibility and detachment; it no longer decides
/// how long an inner binding lives.
/// <list type="bullet">
///   <item>Every ACTUAL CALL of an owner has fresh bindings for the owner's inner properties,
///   whether their definitions use the call's arguments or are self-contained. Reads in the same
///   call share that call's result or cell, by the lexical spelling and by a qualified one alike,
///   and no callback, helper, open or referring caller gives a binding another lifetime.</item>
///   <item>Where no call owns the declaring chain — a member read from outside its owner's call, a
///   root or module property — the binding is the separate RUN-SCOPED one, shared by every such
///   reader of the run and independent of every activation of the owner, before or after.</item>
///   <item><c>A()</c> is fresh on every explicit call. A qualifying outermost success establishes an
///   EMPTY entry of the binding it resolves; an established entry is never read or replaced by it.</item>
/// </list>
/// Every expectation here is hand-written from that rule. Each program is parsed cleanly and runs
/// on the optimized synchronous route, the generic synchronous route and the forced async twin.
/// </summary>
public class InnerPropertyLifetimeTests
{
    public enum Route
    {
        Optimized,
        Generic,
        AsyncTwin,
    }

    public static TheoryData<Route> Routes() => [Route.Optimized, Route.Generic, Route.AsyncTwin];

    // ── Acceptance witness 1: the audit's b1 and the runtime-alias cell ────────────────────────

    /// <summary>The audit's <c>b1</c>, moved from the detachment neutrality pins to the lifetime rule.</summary>
    private const string B1 = """
        Cap(meta r) = if(tick() > 0, r, r)
        Inc(x) = x + 1
        F(y) = {
          A = Cap(Inc(5)).Algorithm
          P = A(1) + 0
          P + y, A(1), tick()
        }
        F(1), F(2)
        """;

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task B1_EachCallComputesItsReceiverOnce_AndTheSecondCallComputesItAgain(Route route)
    {
        var (result, budget) = await Run(B1, route);

        // First call: the receiver ticks once (1); P and the row's A(1) share that call's cell, so the
        // row's own tick() is 2. Second call: a fresh cell, so the receiver ticks again (3) and the
        // row's tick() is 4. (Until the lifetime rule the exported alias had ONE cell per run: the
        // second call did not tick and the last component was 3.)
        Assert.Equal("ok raw=S[S[3, 2, 2], S[4, 2, 4]] n=2", AsyncEvaluationHarness.NeutralOf(result));
        // Two receiver computations and the two written tick() rows: nothing else ticks.
        Assert.Equal(4, budget.TickCount);
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task RuntimeAlias_ReadFromOutsideItsOwner_HasItsOwnRunScopedCell_ApartFromEveryCall(Route route)
    {
        const string source = """
            Cap(meta r) = if(tick() > 0, r, r)
            Inc(x) = x + 1
            F(y) = {
              public A = Cap(Inc(5)).Algorithm
              A(1), tick()
            }
            F.A(1), F(1), F.A(1), tick()
            """;

        // Outside: the run-scoped cell is established by the first F.A(1) (receiver tick 1). The call
        // F(1) has its OWN cell (receiver tick 2; its row's tick() is 3). The second F.A(1) reuses the
        // outside cell (no tick), so the final tick() is 4. A cell shared between the outside binding
        // and the call would leave the call's row at 2 and the final tick at 3.
        Assert.Equal("ok raw=S[2, S[2, 3], 2, 4] n=4", await Observe(source, route));
    }

    // ── Acceptance witness 2: an unused owner input, both spellings, two outside readers ───────

    private const string OrdinaryMember = """
        F(y) = {
          public A = tick()
          A, F.A
        }

        """;

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task OrdinaryMember_IsFreshPerCall_SharedByBothSpellings_AndRunScopedOutside(Route route)
    {
        var (result, budget) = await Run(
            OrdinaryMember + "B = F.A + 0\nC = F.A + 0\nB, F(10), F(20), C, tick()\n", route);

        // B: the outside binding (1). F(10): its own A (2), read as `A` and as `F.A`. F(20): its own
        // A (3). C: the SAME outside binding B read (1) — not a new one, and not a call's. tick(): 4.
        Assert.Equal("ok raw=S[1, S[2, 2], S[3, 3], 1, 4] n=5", AsyncEvaluationHarness.NeutralOf(result));
        Assert.Equal(4, budget.TickCount);
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task OutsideBinding_IsIndependentOfCalls_BeforeAndAfterThem(Route route)
    {
        // The outside read comes AFTER two calls: it is still its own binding (tick 3), not theirs.
        Assert.Equal("ok raw=S[S[1, 1], S[2, 2], 3, 3, 4] n=5",
            await Observe(OrdinaryMember + "F(10), F(20), F.A, F.A, tick()\n", route));
        // And a call AFTER the outside read does not see the outside entry.
        Assert.Equal("ok raw=S[1, S[2, 2], 1, 3] n=4",
            await Observe(OrdinaryMember + "F.A, F(10), F.A, tick()\n", route));
    }

    // ── Acceptance witness 3: explicit calls outside any invocation ────────────────────────────

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task ExplicitCallsOutside_AreFresh_EstablishTheEmptyOutsideEntry_AndNeverReplaceIt(Route route)
    {
        // F.A() runs afresh (1) and, the outside entry being empty, establishes it; F.A reads it (1);
        // F.A() runs afresh again (2) and replaces nothing; F.A still reads 1.
        Assert.Equal("ok raw=S[1, 1, 2, 1] n=4", await Observe(OrdinaryMember + "F.A(), F.A, F.A(), F.A\n", route));
        // Bare read first: the read establishes (1); the call is fresh (2) and never read back.
        Assert.Equal("ok raw=S[1, 2, 1] n=3", await Observe(OrdinaryMember + "F.A, F.A(), F.A\n", route));
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task ExplicitCallsInsideACall_FollowTheSamePublicationLaw_PerCall(Route route)
    {
        const string source = """
            F(y) = {
              A = tick()
              A(), A, A(), A
            }
            F(1), F(2)
            """;

        // Each call of F has its own entry: A() establishes it (1 / 3), A reads it, A() is fresh
        // (2 / 4) and never replaces it.
        Assert.Equal("ok raw=S[S[1, 1, 2, 1], S[3, 3, 4, 3]] n=2", await Observe(source, route));
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task UndemandedProperty_DoesNoWork(Route route)
    {
        var (result, budget) = await Run("F(y) = {\n  public A = tick()\n  y\n}\nF(10), F(20), tick()\n", route);

        // No row reads A, inside or outside: the only tick is the written one.
        Assert.Equal("ok raw=S[10, 20, 1] n=3", AsyncEvaluationHarness.NeutralOf(result));
        Assert.Equal(1, budget.TickCount);
    }

    // ── Acceptance witness 4: the former neutrality pins h3 and n3 ─────────────────────────────

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task H3_ASelfContainedNestedProperty_IsComputedInEachCall(Route route)
        // Formerly (2, 3): one T per run.
        => Assert.Equal("ok raw=S[2, 4] n=2", await Observe("F(x) = {\n  T = tick()\n  T + x\n}\nF(1), F(2)\n", route));

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task N3_EachCallAndTheOutsideReadHaveTheirOwnBindings(Route route)
        // F(1): T = 1, P = 2, 3. F(2): T = 2, P = 3, 5. F.P outside: its own T (3), P = 4.
        // Formerly (3, 4, 2).
        => Assert.Equal("ok raw=S[3, 5, 4] n=3",
            await Observe("F(y) = {\n  T = tick()\n  P = T + 1\n  P + y\n}\nF(1), F(2), F.P\n", route));

    // ── No consumer gives a binding another lifetime ───────────────────────────────────────────

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task Helper_Callback_AndOpen_ShareTheOwningCallsBinding(Route route)
    {
        const string source = """
            F(y) = {
              open Lib
              Lib = { public U = tick() }
              T = tick()
              H = T + 0
              G(k) = T + k
              T, H, G(0), [0, 0].map(G), U, Lib.U
            }
            F(1), F(2)
            """;

        // In each call T is computed once (1 / 3): the sibling property H, the callable G — called
        // directly and as a map callback, each an actual call of G but not of T's owner — all read
        // the call's T. U is one binding per call too (2 / 4), by the opened name and by Lib.U.
        Assert.Equal("ok raw=S[S[1, 1, 1, L[1, 1], 2, 2], S[3, 3, 3, L[3, 3], 4, 4]] n=2", await Observe(source, route));
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task ReadOfAParameterlessOwner_InheritsItsDeclaringCall_AnExplicitCallOfItIsItsOwn(Route route)
    {
        const string source = """
            F(k) = {
              B = {
                V = tick()
                V + k
              }
              B, B, B(), B
            }
            F(10), F(20)
            """;

        // CACHE-OWNER-D1 is unchanged: the READ of B inherits F's call, so V is that call's (1 / 3) and
        // B's entry is reused. The explicit B() is an actual call of B: its V is fresh (2 / 4), and it
        // never replaces B's established entry.
        Assert.Equal("ok raw=S[S[11, 11, 12, 11], S[23, 23, 24, 23]] n=2", await Observe(source, route));
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task ExplicitCallOfAParameterlessOwner_HasFreshInnerBindings_ItsReadKeepsTheRunScopedOnes(Route route)
    {
        // B read: its T is the run-scoped one (1), B = 2. B(): an actual call, its own T (2 then 3).
        // B read again: the established entry. (Formerly B() reused the run-wide T: (2, 2, 2, 2).)
        Assert.Equal("ok raw=S[2, 4, 6, 2] n=4", await Observe("B = {\n  T = tick()\n  T + T\n}\nB, B(), B(), B\n", route));
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task NestedCalls_TheNearestActualCallOwnsTheBinding(Route route)
    {
        const string source = """
            F(y) = {
              G(k) = {
                T = tick()
                T + T + k
              }
              G(0), G(0)
            }
            F(1), F(2)
            """;

        // T is declared in G: each call of G owns its own (1, 2 in the first call of F; 3, 4 in the second).
        Assert.Equal("ok raw=S[S[2, 4], S[6, 8]] n=2", await Observe(source, route));
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task ClauseFamilyCall_IsAnActualCall(Route route)
    {
        const string source = """
            F(0) = 0
            F(n) = {
              T = tick()
              T + T
            }
            F(1), F(1), F(0)
            """;

        Assert.Equal("ok raw=S[2, 4, 0] n=3", await Observe(source, route));
    }

    // ── Loop rounds: each round is an actual call of the step ──────────────────────────────────

    [Fact]
    public async Task LoopRound_OwnsItsStepTemps_OnThePlannedAndGenericStrategies()
    {
        const string source = "Step(s) = {\n  T = tick()\n  s + T + T\n}\nStep(0).repeat(3)\n";
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var diagnostics = new LoopOptimizationDiagnostics();

        var (planned, plannedBudget) = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: false);

        // T is computed once per round (1, 2, 3) and read twice in it: 2 + 4 + 6. (Formerly one T per
        // run: 6 as well by coincidence of 1 + 1 three times — the tick count tells them apart.)
        Assert.Equal("ok raw=12 n=1", AsyncEvaluationHarness.NeutralOf(planned));
        Assert.Equal("ok raw=12 n=1", AsyncEvaluationHarness.NeutralOf(generic));
        Assert.Equal(3, plannedBudget.TickCount);
        Assert.Equal(3, genericBudget.TickCount);
        Assert.Equal(genericBudget.ConsumedSteps, plannedBudget.ConsumedSteps);
        Assert.Equal(genericBudget.PeakDepth, plannedBudget.PeakDepth);
        Assert.Equal(genericBudget.MaterializedItems, plannedBudget.MaterializedItems);
        // The loop was entered planned. `tick()` is no planned expression, so the row that reads the
        // temp runs as a generic fallback inside the planned loop, under the round's own activation.
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.Equal(3, diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal("ok raw=12 n=1", await Observe(source, Route.AsyncTwin));
    }

    [Fact]
    public async Task FullyPlannedLoopRound_MemoizesItsExportedTempPerRound_WithTheGenericCharges()
    {
        // A plannable exported temp: the round is fully planned, the temp is one memo per round, and
        // the planned charges are the generic ones, where the temp is one entry per round's call.
        const string source = "Step(s) = {\n  T = 5\n  s + T + T()\n}\nStep(0).repeat(4)\n";
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var diagnostics = new LoopOptimizationDiagnostics();
        var plannedCache = new RunScopedZeroArgPropertyResultCache();
        var genericCache = new RunScopedZeroArgPropertyResultCache();

        var (planned, plannedBudget) = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics, zeroArgPropertyResultCache: plannedCache);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: false, zeroArgPropertyResultCache: genericCache);

        Assert.Equal("ok raw=40 n=1", AsyncEvaluationHarness.NeutralOf(planned));
        Assert.Equal("ok raw=40 n=1", AsyncEvaluationHarness.NeutralOf(generic));
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.Equal(0, diagnostics.OptimizedLoopFallbacks);
        Assert.Equal(0, diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(genericBudget.ConsumedSteps, plannedBudget.ConsumedSteps);
        Assert.Equal(genericBudget.PeakDepth, plannedBudget.PeakDepth);
        Assert.Equal(genericBudget.MaterializedItems, plannedBudget.MaterializedItems);
        // The generic strategy publishes the temp once per round, under the round's invocation; the
        // planned strategy keeps it in the frame's per-round memo and publishes nothing run-wide.
        Assert.Equal(4, genericCache.GetSnapshot().Stores);
        Assert.Equal(0, plannedCache.GetSnapshot().Stores);
        Assert.Equal("ok raw=40 n=1", await Observe(source, Route.AsyncTwin));
    }

    [Fact]
    public async Task LoopRound_ExplicitTempCall_EstablishesTheRoundsEntry_OnEveryStrategy()
    {
        const string source = "Step(s) = {\n  T = tick()\n  s + T() + T + T()\n}\nStep(0).repeat(2)\n";

        // Round 1: T() fresh 1 (establishes), T 1, T() fresh 2: 4. Round 2: 3 + 3 + 4 = 10: 14.
        foreach (var route in new[] { Route.Optimized, Route.Generic, Route.AsyncTwin })
            Assert.Equal("ok raw=14 n=1", await Observe(source, route));
    }

    [Fact]
    public async Task PartiallyPlannedLoopRound_OwnsItsStepTemps()
    {
        // The inline block is a generic fallback row, so the round is partially planned and enters
        // the step with a real, invoked activation: T is still one binding per round.
        const string source = "Step(s, n) = {\n  T = tick()\n  { s + T + T }, n + 1\n}\nStep(0, 0).repeat(3)\n";
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var diagnostics = new LoopOptimizationDiagnostics();

        var planned = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics).Result;

        Assert.Equal("ok raw=S[12, 3] n=1", AsyncEvaluationHarness.NeutralOf(planned));
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.Equal(3, diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        foreach (var route in new[] { Route.Generic, Route.AsyncTwin })
            Assert.Equal("ok raw=S[12, 3] n=1", await Observe(source, route));
    }

    // ── Storage: a call's inner entries live with the call ─────────────────────────────────────

    [Fact]
    public void InnerEntriesOfACall_AreKeyedByTheCallsInvocation_NotRunWide()
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("F(x) = {\n  T = tick()\n  T + x\n}\nF(1), F(2), F(3)\n").Root);
        var cache = new RunScopedZeroArgPropertyResultCache();

        var result = Evaluator.RunCountedObserved(program, zeroArgPropertyResultCache: cache).Result;

        Assert.Equal("ok raw=S[2, 4, 6] n=3", AsyncEvaluationHarness.NeutralOf(result));
        // One publication of T per call (three), where the run-wide rule published one.
        Assert.Equal(3, cache.GetSnapshot().Stores);
    }

    // ── Every engine route, with and without retained invocation plans ─────────────────────────

    public static TheoryData<string, string> AcceptanceWitnesses() => new()
    {
        { B1, "S[S[3, 2, 2], S[4, 2, 4]]" },
        { OrdinaryMember + "B = F.A + 0\nC = F.A + 0\nB, F(10), F(20), C, tick()\n", "S[1, S[2, 2], S[3, 3], 1, 4]" },
        { OrdinaryMember + "F.A(), F.A, F.A(), F.A\n", "S[1, 1, 2, 1]" },
        { OrdinaryMember + "F.A, F.A(), F.A\n", "S[1, 2, 1]" },
        { "F(x) = {\n  T = tick()\n  T + x\n}\nF(1), F(2)\n", "S[2, 4]" },
        { "F(y) = {\n  T = tick()\n  P = T + 1\n  P + y\n}\nF(1), F(2), F.P\n", "S[3, 5, 4]" },
    };

    /// <summary>
    /// The acceptance witnesses on the six established routes (<see cref="SixRouteAgreement"/>: the
    /// public sync and async engines, the suspending async twin, the generic and the optimized
    /// evaluator, the forced twin), which must agree with each other and with the hand-written value,
    /// on the ORDINARY and on the PLANNED invocation route (<see cref="InvocationPlanTestSeam"/>
    /// retains an invocation plan for every call, also in programs that capture no call).
    /// </summary>
    [Theory]
    [MemberData(nameof(AcceptanceWitnesses))]
    public async Task AcceptanceWitness_HasItsHandWrittenValue_OnTheSixEngineRoutes_WithAndWithoutRetainedPlans(string source, string expected)
    {
        var ordinary = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", ordinary.Kind);
        Assert.Equal(expected, ordinary.Value);

        using (InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()))
        {
            var planned = await SixRouteAgreement.OnEveryRouteAsync(source);
            Assert.Equal("ok", planned.Kind);
            Assert.Equal(expected, planned.Value);
        }
    }

    // ── Harness ────────────────────────────────────────────────────────────────────────────────

    private static async Task<string> Observe(string source, Route route)
        => AsyncEvaluationHarness.NeutralOf((await Run(source, route)).Result);

    private static async Task<(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget)> Run(string source, Route route)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        return route switch
        {
            Route.Optimized => Evaluator.RunCountedObserved(program),
            Route.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false),
            Route.AsyncTwin => await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache())),
            _ => throw new ArgumentOutOfRangeException(nameof(route)),
        };
    }
}
