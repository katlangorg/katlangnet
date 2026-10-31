using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// CACHE-PUB-1 (owner decision, October 22 2026): EXPLICIT ZERO-ARGUMENT CALLS ESTABLISH THE PROPERTY
/// CACHE. When a property's cache entry is empty, its outermost qualifying evaluation owns publication,
/// whether it is a property-style read <c>A</c> or an explicit zero-supply invocation <c>A()</c>. The
/// owner's success establishes the entry; bare reads reuse it; explicit invocations stay FRESH — they
/// never obtain their result from an established entry and never replace it. It supersedes "an explicit
/// call neither reads, replaces, nor populates the entry" (PROP-06 before this decision).
///
/// <para>The evidence is deterministic: the logging <c>tock</c>/<c>trace</c> host operations on the six
/// execution routes (<see cref="SixRouteAgreement"/>: sync and async engines, the genuinely suspending
/// twin, the generic and optimized evaluators and the forced twin), internal publication statistics of
/// the run-scoped caches, and the IV-1/IV-2 observation snapshot. Lean: the <c>invoke</c> request of
/// <c>evalZeroArgPropertyAccessCounted</c>, <c>CoreTests/PropertyCachePublication.lean</c> and
/// <c>KatLangArityLaws/PropertyInvocationLaws.lean</c>.</para>
/// </summary>
public class ExplicitCallPublicationTests
{
    // ── 1. The call/read matrix ───────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("A, A", "S[1, 1]", 1, 1)]
    [InlineData("A(), A", "S[1, 1]", 1, 1)]
    [InlineData("A, A()", "S[1, 2]", 2, 1)]
    [InlineData("A(), A()", "S[1, 2]", 2, 1)]
    [InlineData("A(), A, A(), A", "S[1, 1, 2, 1]", 2, 1)]
    [InlineData("A, A(), A", "S[1, 2, 1]", 2, 1)]
    public async Task CallReadMatrix_OnEveryRoute(string rows, string expected, int ticks, int observedValue)
    {
        var source = "A = tock()\n" + rows;
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Ticks(ticks), oracle.HostCalls);

        // ONE observation: the established value (the first evaluation's), never the latest call's.
        var observed = Observe(source);
        var observation = Assert.Single(observed.Observations);
        Assert.Equal("A", observation.Name);
        Assert.Equal(1, observation.EmittedCount);
        Assert.Equal(new Result.Atom(observedValue), observation.Value);

        // Exactly one publication, and no owner left active.
        var (_, stores, invocationStores, active) = RunWithRunScopedCache(source);
        Assert.Equal(1, stores);
        Assert.Equal(rows.StartsWith("A()", StringComparison.Ordinal) ? 1 : 0, invocationStores);
        Assert.Equal(0, active);
    }

    [Fact]
    public async Task SeededDraw_TheBriefExample()
    {
        // `A = random(0, 100)` / `A(), A, A(), A`: r1, r1, r2, r1 — r1 and r2 are different DRAWS.
        const string source = "A = randomInt(0, 1000000)\nA(), A, A(), A";
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source, randomSeed: 7);
        var items = oracle.Value!.TrimStart('S', '[').TrimEnd(']').Split(", ");
        Assert.Equal(4, items.Length);
        Assert.Equal(items[0], items[1]);
        Assert.Equal(items[0], items[3]);
        var draws = await SixRouteAgreement.OnEveryRouteAsync(
            "randomInt(0, 1000000), randomInt(0, 1000000), randomInt(0, 1000000)", randomSeed: 7);
        // Exactly two draws were made, in that order: the third stream value is never consumed.
        Assert.Equal("S[" + items[0] + ", " + items[2] + ", " + draws.Value!.Split(", ")[2], draws.Value);
    }

    // ── 2. One ownership domain for reads and invocations ─────────────────────────────────────

    public static TheoryData<string, string, int> ReentrantPrograms => new()
    {
        // An explicit call owning an inner property read (formerly S[2, 1]).
        { "A = if(tock() < 3, A + 1, 0)\nA(), A", "S[2, 2]", 3 },
        // An explicit call owning an inner explicit call (formerly S[2, 0] over four ticks).
        { "A = if(tock() < 3, A() + 1, 0)\nA(), A", "S[2, 2]", 3 },
        // A property read owning an inner explicit call; a later explicit call is fresh.
        { "A = if(tock() < 3, A() + 1, 0)\nA, A, A()", "S[2, 2, 0]", 4 },
        // Indirect re-entry through a reference: `B = A` owns no entry (OD-E, M4★), so B() re-enters
        // A's own key and a bare B reads A's entry (formerly B published its own: S[2, 2, 1]).
        { "A = if(tock() < 3, B() + 1, 0)\nB = A\nA(), A, B", "S[2, 2, 2]", 3 },
        // A fresh explicit call while the entry is established: executes, replaces nothing.
        { "A = if(tock() < 3, A + 1, 0)\nA, A(), A", "S[2, 0, 2]", 4 },
    };

    [Theory]
    [MemberData(nameof(ReentrantPrograms))]
    public async Task OnlyTheSuccessfulOutermostOwnerPublishes_OnEveryRoute(string source, string expected, int ticks)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Ticks(ticks), oracle.HostCalls);
        Assert.Equal(0, RunWithRunScopedCache(source).Active);
    }

    [Fact]
    public async Task InnerSuccessThenOwnerFailure_PublishesNothingForTheOwnersKey_KeepsOtherKeys()
    {
        // A() owns A: its inner re-entrant A() succeeds with 5, then the owner fails. S's owner
        // completed inside the failed attempt, so S's entry stays; A has none.
        const string source = "S = tock() * 100\nA = if(tock() == 1, S + A() + 1 / 0, 5)\nA(), A";
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", oracle.Kind);
        Assert.Contains("DivisionByZero", oracle.Errors[0], StringComparison.Ordinal);
        Assert.Equal(Ticks(3), oracle.HostCalls);

        var observed = Observe(source);
        Assert.IsType<RunResult.EvalFailure>(observed.Result);
        var observation = Assert.Single(observed.Observations);
        Assert.Equal("S", observation.Name);
        Assert.Equal(new Result.Atom(200), observation.Value);

        var (_, stores, _, active) = RunWithRunScopedCache(source);
        Assert.Equal(1, stores);
        Assert.Equal(0, active);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationInsideAnOwningInvocation_ClearsOwnership_AndPublishesNothing(bool asynchronous)
    {
        const string source = "A = tock() + tock()\nA(), A";
        using var cancellation = new CancellationTokenSource();
        var ticks = 0;
        Result Tick()
        {
            if (++ticks == 2) cancellation.Cancel();
            return new Result.Atom(ticks);
        }

        var operations = HostOperations.Create(asynchronous
            ? HostOperation.CreateAsync("tock", async (_, _) => { await Task.Yield(); return Tick(); })
            : HostOperation.Create("tock", (_, _) => Tick()));
        var program = await ProgramAsync(source, operations);
        if (asynchronous)
        {
            var cache = new RunScopedAsyncZeroArgPropertyResultCache();
            await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: cache, hostOperations: operations, cancellationToken: cancellation.Token));
            Assert.Equal(0, cache.ActiveOwnerCount);
            Assert.Equal(0, cache.PublishedCount);
        }
        else
        {
            var cache = new RunScopedZeroArgPropertyResultCache();
            Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(
                program, zeroArgPropertyResultCache: cache, hostOperations: operations, cancellationToken: cancellation.Token));
            Assert.Equal(0, cache.ActiveOwnerCount);
            Assert.Equal(0, cache.GetSnapshot().Stores);
        }
    }

    [Fact]
    public async Task HostExceptionInsideAnOwningInvocation_ClearsOwnership_AndPublishesNothing()
    {
        var operations = HostOperations.Create(HostOperation.Create("boom", (_, _) => throw new InvalidOperationException("host")));
        var program = await ProgramAsync("B = 7\nA = B + boom()\nA(), A", operations);
        var cache = new RunScopedZeroArgPropertyResultCache();
        Assert.Throws<InvalidOperationException>(() => Evaluator.RunCountedObserved(
            program, zeroArgPropertyResultCache: cache, hostOperations: operations));
        Assert.Equal(0, cache.ActiveOwnerCount);
        // B's owner completed inside the failed attempt; A has no entry.
        Assert.Equal(1, cache.GetSnapshot().Stores);
    }

    // ── 3. Which invocations qualify: the EFFECTIVE supply ─────────────────────────────────────

    public static TheoryData<string, string, string, int> EligibilityPrograms => new()
    {
        // A spread contributing no slot is a zero supply: it establishes the entry.
        { "A = tock()\nE = []\nA(E*), A", "ok", "S[1, 1]", 1 },
        // A collecting-only callable accepts zero supplied slots: its zero supply qualifies …
        { "C(*xs) = tock()\nC(), C", "ok", "S[1, 1]", 1 },
        { "C(*xs) = tock()\nE = []\nC(E*), C", "ok", "S[1, 1]", 1 },
        // … one supplied EMPTY value is one slot, not zero: no publication.
        { "C(*xs) = tock()\nC(()), C", "ok", "S[1, 2]", 2 },
        { "C(*xs) = tock()\nC([]), C", "ok", "S[1, 2]", 2 },
        { "C(*xs) = tock()\nC(1), C", "ok", "S[1, 2]", 2 },
        // A nonempty spread is a nonzero supply.
        { "C(*xs) = tock()\nE = [5]\nC(E*), C", "ok", "S[1, 2]", 2 },
        // A callable that requires arguments never qualifies (its own arity rejection).
        { "F(x) = tock()\nF()", "err", "", 0 },
        // A builtin or host operation never acquires an entry from a zero-supply call.
        { "tock(), tock(), tock", "ok", "S[1, 2, 3]", 3 },
    };

    [Theory]
    [MemberData(nameof(EligibilityPrograms))]
    public async Task OnlyAnEffectivelyEmptySupplyQualifies_OnEveryRoute(string source, string kind, string expected, int ticks)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal(kind, oracle.Kind);
        if (kind == "ok") Assert.Equal(expected, oracle.Value);
        Assert.Equal(Ticks(ticks), oracle.HostCalls);
    }

    [Fact]
    public async Task ClauseFamily_ZeroArityBranch_Qualifies()
    {
        // DEFENSIVE, HOST-BUILT: a zero-arity clause family has no surface spelling (a clause head needs
        // a pattern). Its one `()` clause accepts zero supplied values, so `Fam()` is its qualifying
        // zero-supply invocation (here through the flat-binder arm) and establishes Fam's entry.
        var family = new Algorithm.Conditional(null, [],
            [new CondBranch(new Pattern.SequenceValue([]), new Algorithm.User(null, [], [], [],
                [new Expr.Call(new Expr.Resolve("tick"), OutputBundle.Empty)]))]);
        var root = new Algorithm.User(null, [], [], [new Property("Fam", family)],
            [
                new Expr.Call(new Expr.Resolve("Fam"), OutputBundle.Empty),
                new Expr.Resolve("Fam"),
                new Expr.Call(new Expr.Resolve("Fam"), OutputBundle.Empty),
            ]);
        foreach (var route in new[] { 0, 1, 2 })
        {
            var program = new Expr.AlgorithmExpr(root);
            var (result, budget) = route == 2
                ? await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache())
                : Evaluator.RunCountedObserved(program, enableOptimizations: route == 1);
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal([1m, 1m, 2m], result.Value.Value.ToAtoms());
            Assert.Equal(2, budget.TickCount);
        }
    }

    // ── 4. Binding and scope identity ─────────────────────────────────────────────────────────

    public static TheoryData<string, string, int> IdentityPrograms => new()
    {
        // A structural member, grouped or not, establishes the member's ONE entry.
        { "Box = { public V = tock() }\nBox.V(), Box.V, (Box.V)(), Box.V", "S[1, 1, 2, 1]", 2 },
        { "Box = { public V = tock() }\n(Box.V)(), Box.V", "S[1, 1]", 1 },
        // The opened spelling of the same binding shares that entry.
        { "open Box\nBox = { public V = tock() }\nV(), Box.V, V", "S[1, 1, 1]", 1 },
        // Activation-dependent locals: one entry per owner activation, never shared across inputs.
        { "F(x) = {\n    L = x * 100 + tock()\n    L(), L\n}\nF(1), F(2), F(1)", "S[S[101, 101], S[202, 202], S[103, 103]]", 3 },
        // A shadowing property is a different binding with its own entry.
        { "A = tock()\nInner = {\n    A = tock() * 10\n    A(), A\n}\nInner, A", "S[S[10, 10], 2]", 2 },
        // An intervening helper does not change which entry the explicit call establishes.
        { "A = tock()\nHelp = A\nA(), Help, A", "S[1, 1, 1]", 1 },
        { "A = tock()\nHelp = A()\nHelp, A, Help", "S[1, 1, 1]", 1 },
    };

    [Theory]
    [MemberData(nameof(IdentityPrograms))]
    public async Task TheExplicitCallEstablishesExactlyTheReadsEntry_OnEveryRoute(string source, string expected, int ticks)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Ticks(ticks), oracle.HostCalls);
    }

    [Fact]
    public void OnePropertyObject_UnderTwoOwners_KeepsTwoEntries()
    {
        // A host DAG reusing ONE Property instance under two owners: the owners stay distinct keys.
        var shared = new Property("P", new Algorithm.User(
            Parent: null, ParameterPatterns: [], Opens: [], Properties: [],
            Output: [new Expr.Call(new Expr.Resolve("tick"), OutputBundle.Empty)]), IsPublic: true);
        Property Box(string name) => new(name, new Algorithm.User(
            Parent: null, ParameterPatterns: [], Opens: [], Properties: [shared], Output: []));
        var root = new Algorithm.User(
            Parent: null, ParameterPatterns: [], Opens: [], Properties: [Box("Box1"), Box("Box2")],
            Output:
            [
                new Expr.DotCall(new Expr.Resolve("Box1"), "P", OutputBundle.Empty),
                new Expr.DotCall(new Expr.Resolve("Box2"), "P", null),
                new Expr.DotCall(new Expr.Resolve("Box1"), "P", null),
            ]);
        foreach (var optimized in new[] { false, true })
        {
            var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(root), enableOptimizations: optimized);
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal([1m, 2m, 1m], result.Value.Value.ToAtoms());
            Assert.Equal(2, budget.TickCount);
        }
    }

    // ── 5. Callable and META routes ───────────────────────────────────────────────────────────

    public static TheoryData<string, string, int> CallableRoutePrograms => new()
    {
        // A callable parameter: the invocation's origin is the cell's written `A`.
        { "A = tock()\nCall0(f) = f()\nCall0(A), A", "S[1, 1]", 1 },
        // Forwarding transports the cell, so its origin is unchanged.
        { "A = tock()\nCall0(f) = f()\nFwd(g) = Call0(g)\nFwd(A), A", "S[1, 1]", 1 },
        // Repeated invocation stays fresh.
        { "A = tock()\nTwice0(f) = f(), f()\nTwice0(A), A", "S[S[1, 2], 1]", 2 },
        // A STATIC reference owns no entry (OD-E, M4★): OA() publishes under its target Only, which OA
        // and Only then read (formerly the alias had an entry of its own: S[1, 1, 2]).
        { "Only(*xs) = tock()\nOA = Only\nOA(), OA, Only", "S[1, 1, 1]", 1 },
        // A RUNTIME reference publishes under its binding cell's origin — the supplied `Only` — whatever
        // its target's arity (formerly a parameterized runtime-callable alias never published: S[1, 2]).
        { "Only(*xs) = tock()\nUse(f) = {\n    A = f\n    A(), A\n}\nUse(Only)", "S[1, 1]", 1 },
        // A shared argument cell is demanded once: one invocation, which establishes A.
        { "A = tock()\nTwice(v) = v, v\nTwice(A()), A", "S[S[1, 1], 1]", 1 },
        // An UNDEMANDED supplied invocation stays undemanded (Model-C laziness is unchanged).
        { "A = tock()\nIgnore(v) = 0\nIgnore(A()), A", "S[0, 1]", 1 },
    };

    [Theory]
    [MemberData(nameof(CallableRoutePrograms))]
    public async Task EquivalentCallableRoutesAgree_OnEveryRoute(string source, string expected, int ticks)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Ticks(ticks), oracle.HostCalls);
    }

    private const string Meta = "Capture(meta c) = c\nId(x) = x\nA = tock()\n";

    public static TheoryData<string, string, int> MetaPrograms => new()
    {
        // A META program retains invocation plans (J7): an ordinary call argument executes as a plan.
        { Meta + "Id(A()), A", "S[1, 1]", 1 },
        // Capture and pure projection are inert: nothing executes or publishes.
        { Meta + "R = Capture(A())\ncount(R.Arguments), A", "S[0, 1]", 1 },
        // R.Invoke() is an actual zero-supply invocation of A: it establishes A, and repeats stay fresh.
        { Meta + "R = Capture(A())\nR.Invoke(), A", "S[1, 1]", 1 },
        { Meta + "R = Capture(A())\nR.Invoke(), R.Invoke(), A", "S[1, 2, 1]", 2 },
        // R.Algorithm(): the captured callee's CALLABLE invoked with zero supply.
        { Meta + "R = Capture(A())\nR.Algorithm(), A", "S[1, 1]", 1 },
        { Meta + "R = Capture(A())\n(R.Algorithm)(), A", "S[1, 1]", 1 },
        // A captured MEMBER call.
        { "Capture(meta c) = c\nBox = { public V = tock() }\nR = Capture(Box.V())\nR.Invoke(), Box.V", "S[1, 1]", 1 },
        // A capture with arguments: R.Algorithm() with zero supply still names the captured binding.
        { "Capture(meta c) = c\nC(*xs) = tock()\nR = Capture(C(5))\nR.Algorithm(), C, R.Invoke()", "S[1, 1, 2]", 2 },
    };

    [Theory]
    [MemberData(nameof(MetaPrograms))]
    public async Task MetaRoutes_InvokeOrStayInert_OnEveryRoute(string source, string expected, int ticks)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Ticks(ticks), oracle.HostCalls);
    }

    // ── 6. Counted results, observations and errors ───────────────────────────────────────────

    [Theory]
    [InlineData("P = 1, 2")]
    [InlineData("P = (1, 2)")]
    [InlineData("P = ()")]
    [InlineData("P = [1, [2]]")]
    [InlineData("P = (1, (2, 3)), 4")]
    public void TheEstablishedEntryHoldsThePropertyLevelCount_WhicheverEvaluationEstablishedIt(string declaration)
    {
        var readFirst = Observe(declaration + "\nP, P()");
        var callFirst = Observe(declaration + "\nP(), P");
        Assert.Equal(readFirst.Display, callFirst.Display);
        var expected = Assert.Single(readFirst.Observations);
        var actual = Assert.Single(callFirst.Observations);
        Assert.Equal(expected.EmittedCount, actual.EmittedCount);
        Assert.Equal(SixRouteAgreement.Neutral(expected.Value!), SixRouteAgreement.Neutral(actual.Value!));
        Assert.Equal(expected.DeclarationSpan, actual.DeclarationSpan);
    }

    [Fact]
    public void TheCallKeepsItsOrdinaryValueBoundary()
    {
        // `P = 1, 2` emits two rows (one sequence value); `P()` is ONE value at the call boundary.
        var observed = Observe("P = 1, 2\ncount([P()])");
        Assert.Equal("1", observed.Display);
        Assert.Equal(2, Assert.Single(observed.Observations).EmittedCount);
    }

    [Fact]
    public async Task ALaterExplicitFailure_Propagates_EvenWithACachedValue()
    {
        const string source = "A = if(tock() == 1, 5, 1 / 0)\nA, A()";
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", oracle.Kind);
        Assert.Contains("DivisionByZero", oracle.Errors[0], StringComparison.Ordinal);
        Assert.Equal(Ticks(2), oracle.HostCalls);
        // The failure is never replaced by the cached 5, and the earlier publication stays observed.
        var observation = Assert.Single(Observe(source).Observations);
        Assert.Equal(new Result.Atom(5), observation.Value);
    }

    [Fact]
    public void AValueHoldingACallReference_IsWithheld_WhenEstablishedByAnExplicitCall()
    {
        var observed = Observe("Capture(meta c) = c\nId(x) = x\nR = Capture(Id(5))\ncount(R().Arguments)");
        Assert.Equal("1", observed.Display);
        var observation = Assert.Single(observed.Observations);
        Assert.Equal("R", observation.Name);
        Assert.Equal(PropertyValueStatus.Withheld, observation.Status);
        Assert.Null(observation.Value);
    }

    [Theory]
    [InlineData("A = tock()\nA(), A, A(), A")]
    [InlineData("A = if(tock() < 3, A() + 1, 0)\nA(), A")]
    [InlineData("A = tock()\nCall0(f) = f()\nCall0(A), A")]
    [InlineData("Capture(meta c) = c\nA = tock()\nR = Capture(A())\nR.Invoke(), A")]
    public void ObservationIsPassive_TheSameRunWithAndWithoutIt(string source)
    {
        var plain = KatLangEngine.Run(source, new RunOptions { HostOperations = TickOperations(new List<string>()) });
        var log = new List<string>();
        var observed = KatLangEngine.Run(source, new RunOptions { HostOperations = TickOperations(log), ObservePropertyValues = true });
        Assert.Equal(plain.ToDisplayString(), observed.ToDisplayString());
        Assert.Null(plain.PropertyObservations);
        Assert.NotNull(observed.PropertyObservations);
        Assert.Equal(log.Count, CountTicks(source));
    }

    // ── 7. Routes, the planned loop and resource limits ───────────────────────────────────────

    public static TheoryData<string> PlannedLoopPrograms => new()
    {
        // A local-only temp called first establishes the iteration's memo; the sibling read reuses it.
        "Step(n) = {\n    A = n * 10 + 1\n    n + A() + A + A()\n}\nStep(0).repeat(3)",
        // An exported temp's call goes through the run cache's law.
        "Step(n) = {\n    E = 6 * 7\n    n + E() + E\n}\nStep(0).repeat(3)",
        // A temp with a forwarded argument is a nonempty supply.
        "Step(n) = {\n    A = n * 10 + 1\n    n + A + A\n}\nStep(0).repeat(3)",
    };

    [Theory]
    [MemberData(nameof(PlannedLoopPrograms))]
    public async Task PlannedLoopTempCalls_AgreeWithTheGenericRoute_IncludingCharges(string source)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var diagnostics = new LoopOptimizationDiagnostics();
        var (planned, plannedBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: true, loopDiagnostics: diagnostics);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        var (twin, twinBudget) = await Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);
        Assert.Equal(0, diagnostics.GetSnapshot().PlannedExpressionFallbacks);
        Assert.Equal(generic.Value.Value, planned.Value.Value);
        Assert.Equal(generic.Value.Value, twin.Value.Value);
        Assert.Equal(genericBudget.ConsumedSteps, plannedBudget.ConsumedSteps);
        Assert.Equal(genericBudget.ConsumedSteps, twinBudget.ConsumedSteps);
        Assert.Equal(genericBudget.PeakDepth, plannedBudget.PeakDepth);
    }

    public static TheoryData<string> LimitSweepPrograms => new()
    {
        "A = tock()\nA(), A, A(), A",
        "A = if(tock() < 3, A() + 1, 0)\nA(), A",
        "Box = { public V = tock() }\nCall0(f) = f()\nCall0(Box.V), Box.V, (Box.V)()",
        "Capture(meta c) = c\nA = tock()\nR = Capture(A())\nR.Invoke(), A, R.Algorithm()",
        "F(x) = {\n    L = x + tock()\n    L(), L\n}\nF(1), F(2)",
    };

    [Theory]
    [MemberData(nameof(LimitSweepPrograms))]
    public async Task StepLimitSweep_EveryRouteAgrees_AtEveryLimit(string source)
    {
        var unlimitedSteps = RunWithRunScopedCache(source).Budget.ConsumedSteps;
        Assert.True(unlimitedSteps > 0);
        for (var steps = 1L; steps <= unlimitedSteps + 1; steps++)
        {
            var oracle = await SixRouteAgreement.OnEveryRouteAsync(source, limits: new EvaluationLimits { MaxSteps = steps });
            if (steps < unlimitedSteps)
                Assert.Contains("EvaluationStepLimitExceeded", oracle.Errors.FirstOrDefault() ?? "", StringComparison.Ordinal);
            else
                Assert.Equal("ok", oracle.Kind);
        }
    }

    // ── Harness ───────────────────────────────────────────────────────────────────────────────

    private static string[] Ticks(int count) => [.. Enumerable.Range(1, count).Select(static i => $"tock#{i}")];

    private static HostOperations TickOperations(List<string> log)
        => HostOperations.Create(
            HostOperation.Create("tock", (_, _) =>
            {
                log.Add("tock");
                return new Result.Atom(log.Count);
            }),
            HostOperation.Create("trace", (args, _) => args[0], "x"));

    private static int CountTicks(string source)
    {
        var log = new List<string>();
        KatLangEngine.Run(source, new RunOptions { HostOperations = TickOperations(log) });
        return log.Count;
    }

    private sealed record Observed(RunResult Result, string Display, IReadOnlyList<PropertyValueObservation> Observations);

    private static Observed Observe(string source)
    {
        var result = KatLangEngine.Run(source, new RunOptions { HostOperations = TickOperations([]), ObservePropertyValues = true });
        return new Observed(result, result.ToDisplayString().ReplaceLineEndings("\n"), [.. result.PropertyObservations!]);
    }

    private static async Task<Expr> ProgramAsync(string source, HostOperations operations)
        => new Expr.AlgorithmExpr((await SourceProvenance.ParseValidAsync(source, new RunOptions { HostOperations = operations })).Root);

    private static (EvaluationBudget Budget, int Stores, int InvocationStores, int Active) RunWithRunScopedCache(string source)
    {
        var operations = TickOperations([]);
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValidAsync(source, new RunOptions { HostOperations = operations }).GetAwaiter().GetResult().Root);
        var cache = new RunScopedZeroArgPropertyResultCache();
        var (_, budget) = Evaluator.RunCountedObserved(program, zeroArgPropertyResultCache: cache, hostOperations: operations);
        var snapshot = cache.GetSnapshot();
        return (budget, snapshot.Stores, snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Invocation).Stores, cache.ActiveOwnerCount);
    }
}
