using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;
using NeedEnv = System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Evaluation.NeedCell Cell)>;
using ValEnv = System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Result Value)>;

namespace KatLang.Tests;

/// <summary>
/// CACHE-OWNER-D2 (October 2026): EVERY ORDINARY CALL BINDING BOUNDARY ESTABLISHES A FRESH BINDING CONTEXT,
/// however many parameters or need cells it binds. A zero-supply call of a parameterless owner made from a
/// context that carries no need cells — today reachable through META <c>R.Algorithm()</c> from the root —
/// used to take the CALLER's value environment as its binding identity, so two different call activations
/// shared one local-only property entry (and one deconstruction group bind): C# returned <c>(3, 3)</c>
/// where the authoritative Lean evaluator (<c>EvalCtx.bindParameters</c> allocates a fresh
/// <c>bindingContext</c> at every boundary) returns <c>(3, 4)</c>. The boundary's freshly minted need tier
/// is now that identity (<c>Evaluator.BindingContextIdentity</c>), even when it is empty.
///
/// <para>The witnesses are the research programs of <c>experimental/features/cache-owner-f1-research.md</c>
/// § 2.3 verbatim. Every program runs on the six established routes (<see cref="SixRouteAgreement"/>: the
/// sync and async engines, the genuinely suspending async twin, the generic and optimized evaluators and
/// the forced async twin) and must agree on value, errors and the exact host-call log; the generic,
/// optimized and suspending-twin evaluator routes must also agree on the semantic step count.
/// <c>tick()</c> counts body evaluations, so sharing and freshness are observed through effects, never
/// through final values alone. Lean: <c>CoreTests/PropertyCacheConsumers.lean</c> (the D2 guards).</para>
/// </summary>
public class MetaCallBindingContextTests
{
    private const string Capture = "Capture(meta op) = op\n";

    // F's B is a parameterless owner whose local-only V reads F's parameter k.
    private const string FWithB = "F(k) = {\n    B = {\n        V = k * 1\n        V\n    }\n    Capture(B())\n}\n";

    private const string FWithTickingB = "F(k) = {\n    B = {\n        V = k + tick()\n        V\n    }\n    Capture(B())\n}\n";

    private static readonly string Pv = Capture + FWithB + "R1 = F(3)\nR2 = F(4)\n";

    private static string[] Ticks(int count) => [.. Enumerable.Range(1, count).Select(static tick => $"tick#{tick}")];

    // ── 1. The research witnesses (wrong values before the fix) ─────────────────────────────

    public static TheoryData<string, string, string, int> Witnesses => new()
    {
        // D2-PV1
        { "D2-PV1", Pv + "R1.Algorithm(), R2.Algorithm()", "S[3, 4]", 0 },
        // D2-PV4: the order-reversed variant
        { "D2-PV4", Pv + "R2.Algorithm(), R1.Algorithm()", "S[4, 3]", 0 },
        // D2-PV3: inside a root zero-parameter property
        { "D2-PV3", Pv + "X = R1.Algorithm() * 100 + R2.Algorithm()\nX", "304", 0 },
        // D2-PV6: a literal-only clause branch selected through META
        {
            "D2-PV6",
            Capture + "G(k) = {\n    F(0) = {\n        V = k * 1\n        V\n    }\n    F(x) = 0\n    Capture(F(0))\n}\nR1 = G(3)\nR2 = G(4)\nR1.Algorithm(0), R2.Algorithm(0)",
            "S[3, 4]",
            0
        },
        // D2-OV7: each call is a fresh binding context, so V runs three times
        { "D2-OV7", Capture + FWithTickingB + "R1 = F(3)\nR2 = F(40)\nR1.Algorithm(), R2.Algorithm(), R1.Algorithm()", "S[4, 42, 6]", 3 },
    };

    [Theory]
    [MemberData(nameof(Witnesses))]
    public async Task ResearchWitness_EveryZeroSupplyCallIsAFreshActivation_OnEveryRoute(string id, string source, string expected, int ticks)
    {
        var oracle = await ObserveAsync(source);
        Assert.True(oracle.Kind == "ok", $"{id}: {oracle}");
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Ticks(ticks), oracle.HostCalls);
    }

    [Fact]
    public void ResearchWitness_TwoActivationsAreTwoLocalOnlyEntries()
    {
        // D2-PV1 seen at the cache seam: V's two requests carry two DISTINCT binding identities (they
        // were the same root value environment before the fix) and each misses once.
        var cache = new RecordingCache();
        var (result, _) = Evaluator.RunCountedObserved(Program(Pv + "R1.Algorithm(), R2.Algorithm()"), zeroArgPropertyResultCache: cache);

        Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());
        var v = cache.Requests.Where(static request => request.Binding.Name == "V").ToList();
        Assert.Equal(2, v.Count);
        Assert.All(v, static request => Assert.NotEqual(PropertyExposure.Exported, request.Binding.Exposure));
        Assert.Equal(2, v.Select(static request => request.ValueEnvironmentIdentity).Distinct(ReferenceEqualityComparer.Instance).Count());
        Assert.Equal(2, cache.Evaluations["V"]);
    }

    [Fact]
    public void AnEmptyMintedNeedTier_IsTheBindingIdentity()
    {
        ValEnv values = [("x", new Result.Atom(1))];
        NeedEnv none = [];

        // Below every boundary (the root's tier): the value environment identifies the context.
        var root = Evaluator.EvalCtx.Empty;
        Assert.Same(values, Evaluator.BindingContextIdentity(root, values));
        Assert.Same(values, Evaluator.BindingContextIdentity(root.WithNeedEnv(none), values));

        // A boundary that binds nothing and inherits nothing still mints its own identity.
        var minted = Evaluator.Concat(none, none);
        Assert.IsType<Evaluator.BoundNeedEnv>(minted);
        Assert.Empty(minted);
        Assert.NotSame(minted, Evaluator.Concat(none, none));
        Assert.Same(minted, Evaluator.BindingContextIdentity(root.WithNeedEnv(minted), values));
    }

    [Fact]
    public void AnEmptyMintedNeedTier_CostsNoExtraAllocation_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        NeedEnv none = [];
        // The minted tier costs exactly the list the boundary allocated before (no extra object).
        static long Allocated(Action mint)
        {
            for (var i = 0; i < 100; i++) mint();
            var before = GC.GetAllocatedBytesForCurrentThread();
            for (var i = 0; i < 1000; i++) mint();
            return GC.GetAllocatedBytesForCurrentThread() - before;
        }

        var boundBytes = Allocated(() => Evaluator.Concat(none, none));
        var plainBytes = Allocated(() => Evaluator.Concat<(string Name, NeedCell Cell)>(none, none));
        Assert.Equal(plainBytes, boundBytes);
        GcIsolatedAllocation.Complete();
    }

    // ── 2. Positive cases beyond the witnesses ───────────────────────────────────────────────

    [Theory]
    // The SAME captured activation invoked twice: two calls, two fresh contexts (was S[11, 11], 1 tick).
    [InlineData("R = F(10)\nR.Algorithm(), R.Algorithm()", "S[11, 12]", 2)]
    // The parenthesized projection call is the same ordinary call (CR-13).
    [InlineData("R1 = F(3)\nR2 = F(40)\n(R1.Algorithm)(), (R2.Algorithm)(), (R1.Algorithm)()", "S[4, 42, 6]", 3)]
    public async Task ZeroSupplyProjectionCalls_AreDistinctActivations_OnEveryRoute(string rows, string expected, int ticks)
    {
        var oracle = await ObserveAsync(Capture + FWithTickingB + rows);
        Assert.True(oracle.Kind == "ok", oracle.ToString());
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Ticks(ticks), oracle.HostCalls);
    }

    [Fact]
    public async Task RuntimeTargetAliasesOfTheProjection_ReadTheirPlansRetainedCalleeValue_FromTheRoot()
    {
        // FWD-02 / META-S3-2 D4: B declares no parameter pattern, so A1 = R1.Algorithm is A1's ordinary
        // zero-parameter property, not a D3 callable forward. Each A1() evaluates that terminal row afresh,
        // and the row's bare R1.Algorithm is the VALUE of R1's captured plan callee cell (CR-13/CR-14b),
        // computed once per plan: the second A1() reads that completed VALUE and requests neither B nor V
        // again (§ 5 pins this at the cache seam). It is NOT A1's binding cell caching V. Different plans
        // (different F activations) stay isolated. Unchanged by CACHE-OWNER-D2, and Lean agrees: the same
        // program without the effect leaves exactly two V entries for the three calls (three for the
        // direct R1.Algorithm(), R2.Algorithm(), R1.Algorithm(), which are fresh calls of B).
        const string rows = "R1 = F(3)\nR2 = F(40)\nA1 = R1.Algorithm\nA2 = R2.Algorithm\nA1(), A2(), A1()";
        var oracle = await ObserveAsync(Capture + FWithTickingB + rows);
        Assert.True(oracle.Kind == "ok", oracle.ToString());
        Assert.Equal("S[4, 42, 4]", oracle.Value);
        Assert.Equal(Ticks(2), oracle.HostCalls);
    }

    // ── 3. Controls: behavior that was already right and must stay unchanged ────────────────

    [Theory]
    // R.Invoke() replays the captured invocation: already fresh per call.
    [InlineData("R1.Invoke(), R2.Invoke()", "S[3, 4]")]
    // The bare projection is a VALUE demand of the callable, not an invocation.
    [InlineData("R1.Algorithm, R2.Algorithm", "S[3, 4]")]
    // The same calls inside a callback (a non-empty need tier).
    [InlineData("[0].map{ n + R1.Algorithm() * 100 + R2.Algorithm() }[0]", "304")]
    // The same calls from a parameterized caller (a non-empty need tier).
    [InlineData("G(z) = R1.Algorithm() * 100 + R2.Algorithm() + z\nG(0)", "304")]
    public async Task ProjectionControls_AreUnchanged_OnEveryRoute(string rows, string expected)
    {
        var oracle = await ObserveAsync(Pv + rows);
        Assert.True(oracle.Kind == "ok", oracle.ToString());
        Assert.Equal(expected, oracle.Value);
    }

    [Fact]
    public async Task TwoReadsOfALocalPropertyWithinOneActivation_ShareOneEvaluation()
    {
        // V is read twice by B's own body: one evaluation per activation, two activations in all.
        const string source = Capture + "F(k) = {\n    B = {\n        V = k + tick()\n        V + V\n    }\n    Capture(B())\n}\nR = F(10)\nR.Algorithm(), R.Algorithm()";
        var oracle = await ObserveAsync(source);
        Assert.Equal("S[22, 24]", oracle.Value);
        Assert.Equal(Ticks(2), oracle.HostCalls);
    }

    [Fact]
    public async Task AnExportedPropertyKeepsItsRunWideEntry_AcrossActivations()
    {
        // E reads no captured parameter, so it is Exported: ONE evaluation for the whole run, while the
        // local-only output of each activation still sees its own k.
        const string source = Capture + "F(k) = {\n    B = {\n        E = tick() * 100\n        E + k\n    }\n    Capture(B())\n}\nR1 = F(3)\nR2 = F(4)\nR1.Algorithm(), R2.Algorithm(), R1.Algorithm()";
        var root = SourceProvenance.ParseValid(source).Root;
        var b = Assert.Single(Assert.Single(root.Properties, static p => p.Name == "F").Value.Properties, static p => p.Name == "B");
        Assert.Equal(PropertyExposure.Exported, Assert.Single(b.Value.Properties, static p => p.Name == "E").Exposure);

        var oracle = await ObserveAsync(source);
        Assert.Equal("S[103, 104, 103]", oracle.Value);
        Assert.Equal(Ticks(1), oracle.HostCalls);
    }

    [Fact]
    public async Task TwoExplicitInnerCalls_StayTwoActivations_FromAParameterizedCaller()
    {
        // The established EnvironmentIdentityInvariantTests shape with an effect: each Inner() is fresh.
        const string source = "Outer(x) = {\n    Inner = {\n        P = x + tick()\n        P + P\n    }\n    Inner(), Inner()\n}\nOuter(10)";
        var oracle = await ObserveAsync(source);
        Assert.Equal("S[22, 24]", oracle.Value);
        Assert.Equal(Ticks(2), oracle.HostCalls);
    }

    [Fact]
    public async Task ProjectionCallsInsideALoopStep_AreFreshPerIteration()
    {
        // Every round's R.Algorithm() is its own call (from a step context with a bound state cell).
        const string source = Capture + FWithTickingB + "R = F(10)\nStep(s) = s + R.Algorithm()\nrepeat(Step(0), 3)";
        var oracle = await ObserveAsync(source);
        Assert.Equal("36", oracle.Value);
        Assert.Equal(Ticks(3), oracle.HostCalls);
    }

    [Theory]
    [InlineData("[0, 0].map{ n * 0 + R.Algorithm() }", "L[11, 12]", 2)]
    [InlineData("[0, 0].filter{ R.Algorithm() > n }", "L[0, 0]", 2)]
    [InlineData("Add(n, total) = total + n * 0 + R.Algorithm()\nreduce([0, 0], Add, 0)", "23", 2)]
    [InlineData("[0, 0].map{ n * 0 + sum([0, 0].map{ m * 0 + R.Algorithm() }) }", "L[23, 27]", 4)]
    [InlineData("Apply(f) = f()\nApply(R.Algorithm), Apply(R.Algorithm)", "S[11, 12]", 2)]
    [InlineData("Step(s) = s + R.Algorithm(), s < 20\nwhile(Step(0))", "23", 2)]
    public async Task ConsumerAndForwardingControls_KeepEachProjectedCallFresh(string rows, string expected, int ticks)
    {
        var oracle = await ObserveAsync(Capture + FWithTickingB + "R = F(10)\n" + rows);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Ticks(ticks), oracle.HostCalls);
    }

    [Fact]
    public async Task ZeroStateWhileCalls_KeepTheirZeroBindingRoundsDistinct()
    {
        // Each loop starts with no state and terminates on its first round. V must be cached
        // within that zero-binding round, then evaluated afresh in the other loop's round.
        // A successful true round with one output would feed that item back as state (Q-24).
        const string source = Capture
            + "F(k) = {\n    B = {\n        V = k + tick()\n        V == V and V < k\n    }\n    Capture(B())\n}\n"
            + "R = F(10)\ncount(while(R.Algorithm())), count(while(R.Algorithm()))";
        var oracle = await ObserveAsync(source);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal("S[0, 0]", oracle.Value);
        Assert.Equal(Ticks(2), oracle.HostCalls);
    }

    [Fact]
    public async Task ANewActivationDoesNotHideItsFailureBehindAPreviousSuccess()
    {
        const string source = Capture
            + "F(k) = {\n    B = {\n        V = if(tick() == 1, k, 1 / 0)\n        V\n    }\n    Capture(B())\n}\n"
            + "R = F(10)\nR.Algorithm(), R.Algorithm()";
        var oracle = await ObserveAsync(source);
        Assert.Equal("err", oracle.Kind);
        Assert.StartsWith("DivisionByZero: ", Assert.Single(oracle.Errors), StringComparison.Ordinal);
        Assert.Equal(Ticks(2), oracle.HostCalls);
    }

    [Fact]
    public async Task APlannedLoopInsideAZeroSupplyActivation_KeepsItsPerIterationIdentity()
    {
        // The step's local-only Val reads the step's state: once per iteration, reused within it, on the
        // planned route too (the optimized route must actually plan the loop).
        const string source = Capture
            + "F(k) = {\n    B = {\n        Step(x) = {\n            Val = x * 2 + k * 0 + tick() * 0\n            x + Val + Val + [0][0]\n        }\n        repeat(Step(1), 3)\n    }\n    Capture(B())\n}\n"
            + "R = F(5)\nR.Algorithm(), R.Algorithm()";
        var oracle = await ObserveAsync(source);
        Assert.Equal("S[125, 125]", oracle.Value);
        Assert.Equal(Ticks(6), oracle.HostCalls);

        var loops = new LoopOptimizationDiagnostics();
        var log = new List<string>();
        var (result, _) = Evaluator.RunCountedObserved(Program(source), enableOptimizations: true, loopDiagnostics: loops,
            hostOperations: Operations(log, suspending: false));
        Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());
        Assert.Equal(2, loops.GetSnapshot().OptimizedLoopHits);
    }

    // ── 4. The deconstruction shared bind follows the same binding context ──────────────────

    [Fact]
    public async Task DeconstructionGroupBind_IsSharedWithinAnActivation_AndSeparateAcrossCalls()
    {
        // a and b come from ONE bind per activation (a + b + a evaluates the right-hand side once), and the
        // two zero-supply activations never share it (the root value environment used to key both).
        const string source = Capture
            + "F(k) = {\n    B = {\n        a, b = (k + tick(), 1)\n        a + b + a\n    }\n    Capture(B())\n}\n"
            + "R1 = F(3)\nR2 = F(40)\nR1.Algorithm(), R2.Algorithm()";
        var oracle = await ObserveAsync(source);
        Assert.Equal("S[9, 85]", oracle.Value);
        Assert.Equal(Ticks(2), oracle.HostCalls);

        foreach (var path in new[] { 0, 1, 2 })
        {
            var observations = new EvaluationObservations();
            var log = new List<string>();
            var (result, _) = path == 2
                ? await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(Program(source),
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), observations: observations,
                    hostOperations: Operations(log, suspending: true)))
                : Evaluator.RunCountedObserved(Program(source), enableOptimizations: path == 1, observations: observations,
                    hostOperations: Operations(log, suspending: false));
            Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());
            Assert.Equal(2, observations.DeconstructionFullBindCount);
        }
    }

    [Theory]
    // No META: explicit root-level calls of a parameterless owner. The hoisted right-hand side reads no
    // captured parameter, so it is an EXPORTED property evaluated once per run, however many group binds
    // the activations perform.
    [InlineData("F = {\n    a, b = (tick(), 1)\n    a + b\n}\nF(), F()", "S[2, 2]", 1)]
    [InlineData("F = {\n    a, b = (tick(), 1)\n    a + b\n}\nF, F(), F", "S[2, 2, 2]", 1)]
    public async Task AnExportedDeconstructionSource_KeepsItsRunWideEntry_AcrossRootLevelCalls(string source, string expected, int ticks)
    {
        var oracle = await ObserveAsync(source);
        Assert.True(oracle.Kind == "ok", oracle.ToString());
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Ticks(ticks), oracle.HostCalls);
    }

    // ── 5. ALIAS-D4: a zero-parameter runtime alias row versus a fresh projected call ──────────
    //
    // experimental/features/alias-d4-1-research.md (ignored). B declares no parameter pattern, so an alias
    // of R.Algorithm is D4's terminal ordinary property: A() evaluates the alias ROW afresh, and that row's
    // bare R.Algorithm reads the captured plan's callee VALUE (CR-14b), computed once per PLAN. A direct
    // R.Algorithm() is a fresh call of B (CR-14c). trace(V) counts runs of B's body, tick() runs of V's.

    private const string FWithTracedB = "F(k) = {\n    B = {\n        V = k + tick()\n        trace(V)\n    }\n    Capture(B())\n}\n";

    private const string TwoPlans = "R1 = F(3)\nR2 = F(40)\n";

    public static TheoryData<string, string, string, string[]> ZeroParameterAliasWitnesses => new()
    {
        // M06: a new alias binding cell in every H activation, yet both H(R1) share R1's plan callee VALUE.
        {
            "M06", Capture + FWithTracedB + TwoPlans + "H(r) = {\n    A = r.Algorithm\n    A() * 100 + A()\n}\nH(R1), H(R1), H(R2)",
            "S[404, 404, 4242]", ["tick#1", "trace(4)", "tick#2", "trace(42)"]
        },
        // M27: a COMPUTED receiver. The second AM() re-evaluates the row, F(3) forms a new plan, and its callee
        // VALUE runs B again; the bare AM reads AM's entry published by the first call (CACHE-PUB-1).
        {
            "M27", Capture + FWithTracedB + "AM = F(3).Algorithm\nAM(), AM(), AM",
            "S[4, 5, 4]", ["tick#1", "trace(4)", "tick#2", "trace(5)"]
        },
        // M16: Call(A1) forwards A1's property (the retained VALUE); Call(R1.Algorithm) forwards B, called afresh.
        {
            "M16", Capture + FWithTracedB + TwoPlans + "A1 = R1.Algorithm\nCall(f) = f()\nCall(A1), Call(A1), Call(R1.Algorithm), Call(R1.Algorithm)",
            "S[4, 4, 5, 6]", ["tick#1", "trace(4)", "tick#2", "trace(5)", "tick#3", "trace(6)"]
        },
        // C04: the static zero-parameter control S = B shows the same split (S forwards B's property read).
        {
            "C04", "F(k) = {\n    B = {\n        V = k + tick()\n        trace(V)\n    }\n    S = B\n    Call(f) = f()\n    Call(S), Call(S), Call(B), Call(B)\n}\nF(3)",
            "S[4, 4, 5, 6]", ["tick#1", "trace(4)", "tick#2", "trace(5)", "tick#3", "trace(6)"]
        },
        // M04f: a direct call first publishes B's read entry in F(3)'s declaring activation (CACHE-PUB-1), and
        // the alias rows' callee VALUE then reads that entry: one run of B in all.
        {
            "M04f", Capture + FWithTracedB + TwoPlans + "A1 = R1.Algorithm\nR1.Algorithm(), A1(), A1()",
            "S[4, 4, 4]", ["tick#1", "trace(4)"]
        },
        // M07: D3 control. A parameterized projected callee is forwarded as a CALLABLE: every A(x) is a fresh
        // call. (Collecting-only D3 controls: RuntimeCallableAliasCorpusTests RF1-D3-zero-accepting and
        // RuntimeAliasPublicationTests.ParameterizedRuntimeTargets_PublishNeitherAliasNorTarget.)
        {
            "M07", Capture + "G(k) = {\n    Sq(x) = x * x + k + tick()\n    Capture(Sq(2))\n}\nR = G(10)\nA = R.Algorithm\nA(3), A(3), A(4), R.Algorithm(3)",
            "S[20, 21, 29, 23]", Ticks(4)
        },
    };

    [Theory]
    [MemberData(nameof(ZeroParameterAliasWitnesses))]
    public async Task ZeroParameterAliasRows_ShareThePlansCalleeValue_WhileDirectAndParameterizedCallsStayFresh(
        string id, string source, string expected, string[] hostCalls)
    {
        var oracle = await ObserveAsync(source);
        Assert.True(oracle.Kind == "ok", $"{id}: {oracle}");
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(hostCalls, oracle.HostCalls);
    }

    [Fact]
    public async Task ARepeatedTerminalAliasCall_ReevaluatesItsRow_ButNeverDemandsTheCalleeAgain()
    {
        // At the property-cache seam, on the generic, optimized and genuinely suspending async routes. Each
        // further A1() re-runs the alias row: one more A1 invocation and one more read of the receiver R1 (a
        // hit). It makes NO B or V request — it stops at the completed callee VALUE of R1's plan — so B and V
        // still evaluated once. The direct R1.Algorithm() control invokes B again and reads V afresh.
        const string declarations = Capture + FWithTracedB + TwoPlans + "A1 = R1.Algorithm\n";
        foreach (var path in new[] { 0, 1, 2 })
        {
            var once = await RecordAsync(declarations + "A1()", path);
            var twice = await RecordAsync(declarations + "A1(), A1()", path);
            var thrice = await RecordAsync(declarations + "A1(), A1(), A1()", path);

            Assert.Equal(["tick#1", "trace(4)"], once.Log);
            Assert.Equal(once.Log, twice.Log);
            Assert.Equal(once.Log, thrice.Log);
            Assert.Equal(1, once.Cache.Evaluations["B"]);
            Assert.Equal(1, once.Cache.Evaluations["V"]);
            foreach (var (later, calls) in new[] { (twice, 2), (thrice, 3) })
            {
                // What WAS re-evaluated: the terminal row.
                Assert.Equal(calls, later.Cache.Count("A1", invoked: true));
                Assert.Equal(calls, later.Cache.Count("R1", invoked: false));
                // What was NOT: the projected callee and its local V.
                foreach (var name in new[] { "B", "V" })
                {
                    Assert.Equal(once.Cache.Count(name, invoked: false), later.Cache.Count(name, invoked: false));
                    Assert.Equal(once.Cache.Count(name, invoked: true), later.Cache.Count(name, invoked: true));
                    Assert.Equal(1, later.Cache.Evaluations[name]);
                }
            }

            Assert.Equal(1, once.Cache.Count("A1", invoked: true));
            Assert.Equal(1, once.Cache.Count("R1", invoked: false));
            Assert.Equal(1, once.Cache.Count("B", invoked: false));
            Assert.Equal(1, once.Cache.Count("V", invoked: false));
            Assert.Equal(0, once.Cache.Count("B", invoked: true));

            var direct = await RecordAsync(declarations + "R1.Algorithm(), R1.Algorithm()", path);
            Assert.Equal(["tick#1", "trace(4)", "tick#2", "trace(5)"], direct.Log);
            Assert.Equal(2, direct.Cache.Count("B", invoked: true));
            Assert.Equal(2, direct.Cache.Count("V", invoked: false));
            Assert.Equal(2, direct.Cache.Evaluations["V"]);
        }
    }

    private static async Task<(List<string> Log, RecordingCache Cache)> RecordAsync(string source, int path)
    {
        var cache = new RecordingCache();
        var log = new List<string>();
        var (result, _) = path == 2
            ? await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(Program(source),
                zeroArgPropertyResultCache: cache, hostOperations: Operations(log, suspending: true)))
            : Evaluator.RunCountedObserved(Program(source), enableOptimizations: path == 1, zeroArgPropertyResultCache: cache,
                hostOperations: Operations(log, suspending: false));
        Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());
        return (log, cache);
    }

    // ── harness ──────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// The six-route observation of <paramref name="source"/> (value, errors and the exact host-call log
    /// agree on every route), after requiring the generic, optimized and genuinely suspending async twin
    /// evaluator routes to agree on value, host calls and semantic steps.
    /// </summary>
    private static async Task<SixRouteAgreement.Observation> ObserveAsync(string source)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);

        var generic = Steps(source, path: 0);
        Assert.Equal(generic, Steps(source, path: 1));
        Assert.Equal(generic, Steps(source, path: 2));
        return oracle;
    }

    private static string Steps(string source, int path)
    {
        var log = new List<string>();
        var (result, budget) = path == 2
            ? Evaluator.RunCountedObservedAsync(Program(source),
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: Operations(log, suspending: true)).AsTask().WaitAsync(TimeSpan.FromSeconds(30)).GetAwaiter().GetResult()
            : Evaluator.RunCountedObserved(Program(source), enableOptimizations: path == 1, hostOperations: Operations(log, suspending: false));
        var outcome = result.IsOk ? SixRouteAgreement.Neutral(result.Value.Value) : KatLangError.FromEvalError(result.Error).Message;
        return $"{outcome} host=[{string.Join(",", log)}] steps={budget.ConsumedSteps}";
    }

    private static HostOperations Operations(List<string> log, bool suspending)
    {
        var ticks = 0;
        Result Tick()
        {
            log.Add($"tick#{++ticks}");
            return new Result.Atom(ticks);
        }

        Result Trace(Result value)
        {
            log.Add($"trace({SixRouteAgreement.Neutral(value)})");
            return value;
        }

        return suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return Trace(args[0]); }, "x"))
            : HostOperations.Create(
                HostOperation.Create("tick", (_, _) => Tick()),
                HostOperation.Create("trace", (args, _) => Trace(args[0]), "x"));
    }

    private static Expr Program(string source)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = Operations([], suspending: false) });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private sealed class RecordingCache : IAsyncZeroArgPropertyResultCache
    {
        private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();

        // DECON-CACHE-2: the inner cache publishes every read, so its publication provenance is this cache's.
        public bool ReadObtainsPublishedValue(ZeroArgPropertyCacheKey key) => _inner.ReadObtainsPublishedValue(key);

        /// <summary>The VALUE reads (<c>GetOrEvaluate</c>), in request order.</summary>
        public List<ZeroArgPropertyExecution> Requests { get; } = [];

        /// <summary>The explicit zero-supply invocations (CACHE-PUB-1 <c>Invoke</c>), in request order.</summary>
        public List<ZeroArgPropertyExecution> Invocations { get; } = [];

        public Dictionary<string, int> Evaluations { get; } = new(StringComparer.Ordinal);

        public int Count(string name, bool invoked)
        {
            var requests = invoked ? Invocations : Requests;
            lock (requests) return requests.Count(request => request.Binding.Name == name);
        }

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Record(Requests, execution);
            return _inner.GetOrEvaluate(execution, () =>
            {
                Evaluated(execution);
                return evaluate();
            });
        }

        public ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
            ZeroArgPropertyExecution execution,
            Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            Record(Requests, execution);
            return _inner.GetOrEvaluateAsync(execution, () =>
            {
                Evaluated(execution);
                return evaluateAsync();
            });
        }

        // CACHE-PUB-1: an explicit zero-supply invocation keeps the inner cache's publication law.
        public EvalResult<ZeroArgPropertyResult> Invoke(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Record(Invocations, execution);
            return _inner.Invoke(execution, evaluate);
        }

        public ValueTask<EvalResult<ZeroArgPropertyResult>> InvokeAsync(
            ZeroArgPropertyExecution execution,
            Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            Record(Invocations, execution);
            return _inner.InvokeAsync(execution, evaluateAsync);
        }

        private static void Record(List<ZeroArgPropertyExecution> requests, ZeroArgPropertyExecution execution)
        {
            lock (requests) requests.Add(execution);
        }

        private void Evaluated(ZeroArgPropertyExecution execution)
        {
            lock (Evaluations) Evaluations[execution.Binding.Name] = Evaluations.GetValueOrDefault(execution.Binding.Name) + 1;
        }
    }
}
