using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// CACHE-OWNER-D1 (owner decision October 23 2026): DECLARING-CONTEXT INHERITANCE. A parameterless
/// property owner entered by a PROPERTY-STYLE read inherits the binding context of its declaring
/// activation, as resolved in the current lexical context; an explicit call establishes a fresh
/// binding context. Before the fix the owner's activation recorded the binding context of whichever
/// CONSUMER first read it (a callback, a helper call, a loop step), while a structural <c>B.V</c> or an
/// opened <c>V</c> keyed the same local-only binding on the declaring activation — so one activation of
/// <c>F</c> could evaluate <c>V</c> twice and observe two different values (D1-VAL: <c>false</c>). Lean
/// and C# shared the defect; Lean was corrected first (<c>EvalBody.evalPropertyDemandCounted</c>,
/// <c>enterPropertyOwnerBody</c>) and C# mirrors it (<c>Evaluator.EvalPropertyOwnerBodyCounted</c>).
///
/// <para>The witnesses are the research programs of <c>experimental/features/cache-owner-f1-research.md</c>
/// § 2.2 with the two-argument research <c>trace(tag, value)</c> written as the one-argument logging
/// <c>trace(x)</c> (the same values and the same evaluation counts). Every program runs on the six
/// established routes (<see cref="SixRouteAgreement"/>: the sync and async engines, the genuinely
/// suspending async twin, the generic and optimized evaluators and the forced async twin), which must
/// agree on value, errors and the exact host-call log; the generic, optimized and suspending-twin
/// evaluator routes must also agree on the semantic step count. Lean: <c>CoreTests/PropertyCacheConsumers.lean</c>
/// (the D1 guards).</para>
/// </summary>
public class ParameterlessOwnerEntryContextTests
{
    // F's B is a parameterless owner; its local-only V reads F's parameter k.
    private static string F(string bRows, string fRows, string call = "F(3)")
        => "F(k) = {\n" + Indent(bRows) + Indent(fRows) + "}\n" + call;

    private static string Indent(string rows)
        => string.Concat(rows.Split('\n').Select(static row => "    " + row + "\n"));

    // M4★: a body whose ONE row is the bare reference V is a structural forwarding CARRIER of V (it
    // declares V, so it is no transparent reference): it owns no zero-argument entry (OD-E), a bare read
    // is V's own read and an explicit B() is the fresh V() resolved at B's DECLARING activation — the
    // forwarding hop adds no activation. OwnerB keeps CACHE-OWNER-D1's subject, a parameterless OWNER
    // with an entry of its own (its row is a calculation), with the same values.
    private const string TracedB = "B = {\n    V = trace(k)\n    V\n}";

    private const string OwnerB = "B = {\n    V = trace(k)\n    V + 0\n}";

    private static readonly string[] BothOwnerForms = [TracedB, OwnerB];

    private static string[] Traces(params int[] values) => [.. values.Select(static value => $"trace({value})")];

    private static string[] Ticks(int count) => [.. Enumerable.Range(1, count).Select(static tick => $"tick#{tick}")];

    // ── 1. The research matrix (§ 2.2) ──────────────────────────────────────────────────────

    public static TheoryData<string, string, string, string[]> ResearchMatrix => new()
    {
        // D1-MIN: B first entered by a bare read inside a callback, then the structural B.V (was t3,t3).
        { "D1-MIN", F(TracedB, "[0].map{ n + B }[0] + B.V"), "6", Traces(3) },
        // D1-SWAP: the order does not matter (was t3,t3).
        { "D1-SWAP", F(TracedB, "B.V + [0].map{ n + B }[0]"), "6", Traces(3) },
        // D1-PRE (control): B first entered from F's own body.
        { "D1-PRE", F(TracedB, "B + [0].map{ n + B }[0] + B.V"), "9", Traces(3) },
        // D1-LEX (control): only lexical reads through B, from a helper and a callback.
        {
            "D1-LEX",
            F("B = {\n    V = trace(k) * k\n    V + V\n}\nG(x) = x + B", "G(1) + [1, 2].map{ n + B }[0]"),
            "38",
            Traces(3)
        },
        // D1-VAL: B's own V and B.V are ONE binding in one activation (was false, two ticks).
        { "D1-VAL", F("B = {\n    V = k + tick()\n    V\n}", "[1].map{ n * 0 + B }[0] == B.V"), "true", Ticks(1) },
        // D1-VALc (control).
        { "D1-VALc", F("B = {\n    V = k + tick()\n    V\n}", "B == B.V"), "true", Ticks(1) },
        // D1-OPEN: the opened V shares the callback's entry (was t3,t3).
        {
            "D1-OPEN",
            F("open B\nB = {\n    public V = trace(k) * k\n    V + 1\n}", "[1, 2].map{ n + B }[0] + V"),
            "20",
            Traces(3)
        },
        // D1-HELP: a helper call does not split the context (was t3,t3).
        { "D1-HELP", F("B = {\n    V = trace(k) * k\n    V + 1\n}\nG(x) = x + B", "G(1) + B.V"), "20", Traces(3) },
        // D1-DECON: one shared right-hand side (was t3,t3).
        {
            "D1-DECON",
            F("B = {\n    a, b = trace(k), k + 1\n    a + b\n}", "[1, 2].map{ n + B }[0] + B.a + B.b"),
            "15",
            Traces(3)
        },
        // D1-REAL: a configuration namespace used by a helper and directly (was t20,t20).
        {
            "D1-REAL",
            "Invoice(rate) = {\n    Tax = {\n        Factor = 1 + trace(rate) / 100\n        Factor * 1\n    }\n    Price(net) = net * Tax\n    Price(100) + Tax.Factor\n}\nInvoice(20)",
            "121.2",
            Traces(20)
        },
        // D1-LOOP: B first read inside a while step (was t3,t3).
        {
            "D1-LOOP",
            F("B = {\n    V = trace(k) * k\n    V + 1\n}\nStep(s) = s + B, s < 5", "Step(0).while + B.V"),
            "19",
            Traces(3)
        },
        // D1-ANON: the owner of B is an anonymous callback (was t3,t3).
        {
            "D1-ANON",
            "[3].map{\n    B = {\n        V = trace(n) * n\n        V + 1\n    }\n    n * 0 + [1, 2].map{ m + B }[0] + B.V\n}",
            "L[20]",
            Traces(3)
        },
        // D1-3X: three routes, one entry (was t3,t3,t3).
        {
            "D1-3X",
            F("B = {\n    C = {\n        V = trace(k)\n        V\n    }\n    C\n}", "[0].map{ n + B }[0] + [0].map{ n + B.C }[0] + B.C.V"),
            "9",
            Traces(3)
        },
        // D1-PUB: B.V() establishes V's entry (CACHE-PUB-1); B read in a callback reuses it (was t3,t3).
        { "D1-PUB", F("B = {\n    V = trace(k)\n    V + 1\n}", "B.V() + [1].map{ n * 0 + B }[0]"), "7", Traces(3) },
        // D1-ROOT (control): the same shape at the root, where V is exported.
        { "D1-ROOT", "B = {\n    V = trace(7)\n    V + 1\n}\n[1, 2].map{ n + B }[0] + B.V", "16", Traces(7) },
    };

    [Theory]
    [MemberData(nameof(ResearchMatrix))]
    public async Task ResearchMatrix_OneEvaluationPerOwningActivation_OnEveryRoute(string id, string source, string expected, string[] hostCalls)
    {
        var oracle = await ObserveAsync(source);
        Assert.True(oracle.Kind == "ok", $"{id}: {oracle}");
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(hostCalls, oracle.HostCalls);
    }

    [Fact]
    public async Task D1Val_TheBindingHasOneValueInOneActivation_WithASeededRandomDraw()
    {
        // A duplicate evaluation would draw twice; one shared entry compares equal.
        var source = F("B = {\n    V = random(0, 1000) + k * 0\n    V\n}", "[1].map{ n * 0 + B }[0] == B.V, B.V == [2].map{ n * 0 + B }[0]");
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source, randomSeed: 11);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal("S[true, true]", oracle.Value);
    }

    // ── 2. The cache seam: one key, one evaluation ──────────────────────────────────────────

    [Theory]
    [InlineData("[0].map{ n + B }[0] + B.V")]
    [InlineData("B.V + [0].map{ n + B }[0]")]
    [InlineData("G(x) = x + B\nG(1) + B.V + [0, 1].map{ n + B }[1]")]
    public async Task TheLexicalAndStructuralReadsOfV_ComputeOneKey(string rows)
    {
        foreach (var asynchronous in new[] { false, true })
        {
            var cache = new RecordingCache();
            var log = new List<string>();
            var program = Program(F(TracedB, rows));
            var (result, _) = asynchronous
                ? await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: cache,
                    hostOperations: Operations(log, suspending: true)))
                : Evaluator.RunCountedObserved(program, zeroArgPropertyResultCache: cache, hostOperations: Operations(log, suspending: false));

            Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());
            var v = cache.Requests.Where(static request => request.Binding.Name == "V").ToList();
            Assert.True(v.Count >= 2, $"V requested {v.Count} time(s)");
            Assert.All(v, static request => Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, request.Binding.Exposure));
            Assert.Single(v.Select(ZeroArgPropertyCacheKey.FromExecution).Distinct());
            Assert.Equal(1, cache.Evaluations["V"]);
            Assert.Equal(Traces(3), log);
        }
    }

    [Fact]
    public void ThePropertyReadEntry_InheritsTheIdentityTheOwnersOwnKeyCarries()
    {
        // B's own key and V's key (through B's inherited activation) carry F's binding identity, never the
        // callback's: the callback reader's binding identity differs from both.
        var cache = new RecordingCache();
        var (result, _) = Evaluator.RunCountedObserved(Program(F(OwnerB, "[0].map{ n + B }[0] + B.V")),
            zeroArgPropertyResultCache: cache, hostOperations: Operations([], suspending: false));
        Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());

        var bKey = ZeroArgPropertyCacheKey.FromExecution(Assert.Single(cache.Requests, static request => request.Binding.Name == "B"));
        var vKeys = cache.Requests.Where(static request => request.Binding.Name == "V").Select(ZeroArgPropertyCacheKey.FromExecution).Distinct().ToList();
        var bRead = Assert.Single(cache.Requests, static request => request.Binding.Name == "B");
        Assert.Same(bKey.ValueEnvironmentIdentity, Assert.Single(vKeys).ValueEnvironmentIdentity);
        Assert.NotSame(bRead.ValueEnvironmentIdentity, bKey.ValueEnvironmentIdentity);
    }

    [Fact]
    public async Task ACarrierOwner_RequestsNoEntryOfItsOwn_AndItsTargetKeepsOneKey()
    {
        // M4★ OD-E: the carrier's bare read in the callback IS V's read under V's declaring activation, so
        // the run requests no entry for B at all and V's two reads (through B and B.V) are one key.
        foreach (var asynchronous in new[] { false, true })
        {
            var cache = new RecordingCache();
            var log = new List<string>();
            var program = Program(F(TracedB, "[0].map{ n + B }[0] + B.V"));
            var (result, _) = asynchronous
                ? await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: cache,
                    hostOperations: Operations(log, suspending: true)))
                : Evaluator.RunCountedObserved(program, zeroArgPropertyResultCache: cache, hostOperations: Operations(log, suspending: false));

            Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());
            Assert.DoesNotContain(cache.Requests, static request => request.Binding.Name == "B");
            Assert.Single(cache.Requests.Where(static request => request.Binding.Name == "V").Select(ZeroArgPropertyCacheKey.FromExecution).Distinct());
            Assert.Equal(1, cache.Evaluations["V"]);
            Assert.Equal(Traces(3), log);
        }
    }

    // ── 3. Activation isolation ─────────────────────────────────────────────────────────────

    [Theory]
    // Two calls of F with different captured values: one evaluation each.
    [InlineData("[0].map{ n + B }[0] + B.V", "F(3), F(4)", "S[6, 8]", new[] { 3, 4 })]
    // Numerically equal arguments are still two activations.
    [InlineData("[0].map{ n + B }[0] + B.V", "F(3), F(3)", "S[6, 6]", new[] { 3, 3 })]
    // The two activations are separate even when the second one is reached inside a callback.
    [InlineData("[0].map{ n + B }[0] + B.V", "[3, 4].map{ F(n) }", "L[6, 8]", new[] { 3, 4 })]
    // Inside one activation, nested callbacks and a helper still share F's entry.
    [InlineData("G(x) = [0].map{ n + x + B }[0]\n[0].map{ n + G(1) }[0] + B.V + G(2)", "F(3), F(5)", "S[12, 18]", new[] { 3, 5 })]
    public async Task DistinctDeclaringActivations_NeverShareAnEntry(string fRows, string calls, string expected, int[] traces)
    {
        foreach (var bRows in BothOwnerForms)
        {
            var oracle = await ObserveAsync(F(bRows, fRows, calls));
            Assert.True(oracle.Kind == "ok", $"{bRows}: {oracle}");
            Assert.Equal(expected, oracle.Value);
            Assert.Equal(Traces(traces), oracle.HostCalls);
        }
    }

    [Fact]
    public async Task TwoSiblingOwnersWithSameNamedProperties_KeepTheirOwnEntries()
    {
        var source = F(
            "B = {\n    V = trace(k)\n    V\n}\nC = {\n    V = trace(k * 10)\n    V\n}",
            "[0].map{ n + B + C }[0] + B.V + C.V");
        var oracle = await ObserveAsync(source);
        Assert.Equal("66", oracle.Value);
        Assert.Equal(Traces(3, 30), oracle.HostCalls);
    }

    [Fact]
    public async Task AShadowedName_IsItsOwnBinding()
    {
        // F's V and B's V are two bindings: each evaluated once, whatever route reads it.
        var source = F("V = trace(k * 100)\nB = {\n    V = trace(k)\n    V\n}", "[0].map{ n + B + V }[0] + B.V + V");
        var oracle = await ObserveAsync(source);
        Assert.Equal("606", oracle.Value);
        Assert.Equal(Traces(3, 300), oracle.HostCalls);
    }

    [Fact]
    public async Task NestedOwnersAtDifferentDepths_ShareThroughEveryPath()
    {
        var source = F(
            "B = {\n    C = {\n        D = {\n            V = trace(k)\n            V\n        }\n        D\n    }\n    C\n}",
            "[0].map{ n + B.C }[0] + [0].map{ n + B.C.D }[0] + B.C.D.V + [0].map{ n + B }[0]");
        var oracle = await ObserveAsync(source);
        Assert.Equal("12", oracle.Value);
        Assert.Equal(Traces(3), oracle.HostCalls);
    }

    [Fact]
    public async Task TheNearestDeclaringActivation_WinsWithSeveralActiveAncestors()
    {
        const string source = "F(k) = {\n    G(x) = {\n        B = {\n            V = trace(k + x)\n            V\n        }\n        [0].map{ n + B }[0] + B.V\n    }\n    G(10), G(20)\n}\nF(3)";
        var oracle = await ObserveAsync(source);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal("S[26, 46]", oracle.Value);
        Assert.Equal(Traces(13, 23), oracle.HostCalls);
    }

    [Fact]
    public async Task RecursiveOwnerCalls_RestoreTheirOwnDeclaringActivation()
    {
        foreach (var bRows in BothOwnerForms)
        {
            var source = F(bRows, "[0].map{ n + B }[0] + if(k > 0, F(k - 1), 0) + B.V");
            var oracle = await ObserveAsync(source);
            Assert.True(oracle.Kind == "ok", $"{bRows}: {oracle}");
            Assert.Equal("12", oracle.Value);
            Assert.Equal(Traces(3, 2, 1, 0), oracle.HostCalls);
        }
    }

    [Fact]
    public async Task InheritingAnIdentity_DoesNotDemandUnusedAncestorParameters()
    {
        foreach (var bRows in BothOwnerForms)
        {
            var source = F(bRows, "[0].map{ n + B }[0] + B.V", "F(3, 1 / 0)")
                .Replace("F(k)", "F(k, unused)", StringComparison.Ordinal);
            var oracle = await ObserveAsync(source);
            Assert.True(oracle.Kind == "ok", $"{bRows}: {oracle}");
            Assert.Equal("6", oracle.Value);
            Assert.Equal(Traces(3), oracle.HostCalls);
        }
    }

    [Fact]
    public async Task OpenedLexicalAndStructuralSpellings_ShareOneEntry()
    {
        var source = F(
            "open B\nB = {\n    public V = trace(k)\n    V\n}",
            "[0].map{ n + V }[0] + [0].map{ n + B }[0] + B.V + V");
        var oracle = await ObserveAsync(source);
        Assert.Equal("12", oracle.Value);
        Assert.Equal(Traces(3), oracle.HostCalls);
    }

    // ── 4. Explicit calls stay fresh; publication is unchanged ──────────────────────────────

    [Theory]
    // B(), B(): two explicit calls, two fresh evaluations (an owner's two contexts; a carrier's two V()).
    [InlineData("B() + B()", 2, 2, "6")]
    [InlineData("[0].map{ n + B() }[0] + B()", 2, 2, "6")]
    // B() establishes the entry (CACHE-PUB-1: the owner's own; the carrier's TARGET V's) and the bare
    // read reuses it.
    [InlineData("B() + B", 1, 1, "6")]
    // B then B(): the call is fresh and never replaces the entry.
    [InlineData("B + B()", 2, 2, "6")]
    // An owner's explicit call is a fresh binding context whose locals are its own: B.V reads F's, a
    // second evaluation. A carrier's B() is V() at B's DECLARING activation (the hop adds none), so it
    // establishes the very entry B.V reads (M4★; formerly 2 for this lone-row form too).
    [InlineData("B() + B.V", 2, 1, "6")]
    // A bare read in a callback and the structural read share F's context; the call stays fresh.
    [InlineData("[0].map{ n + B }[0] + B() + B.V", 2, 2, "9")]
    public async Task ExplicitCalls_RemainFreshBindingContexts(string fRows, int ownerEvaluations, int carrierEvaluations, string expected)
    {
        foreach (var (bRows, evaluations) in new[] { (OwnerB, ownerEvaluations), (TracedB, carrierEvaluations) })
        {
            var oracle = await ObserveAsync(F(bRows, fRows));
            Assert.True(oracle.Kind == "ok", $"{bRows}: {oracle}");
            Assert.Equal(expected, oracle.Value);
            Assert.Equal(Traces([.. Enumerable.Repeat(3, evaluations)]), oracle.HostCalls);
        }
    }

    [Fact]
    public async Task AReentrantRead_PublishesOnlyTheOutermostOwnersResult()
    {
        // Q-37: B entered in a callback evaluates V, whose body re-enters V through B.V. Both spellings are
        // ONE key, so the inner reads are re-entrant and only the outermost result is published and reused.
        // A split key can instead publish an inner result for the later structural read.
        var source = F("B = {\n    V = if(tick() < 3, B.V + 1, k)\n    V\n}", "[0].map{ n + B }[0] + B.V", "F(10)");
        var oracle = await ObserveAsync(source);
        Assert.Equal("24", oracle.Value);
        Assert.Equal(Ticks(3), oracle.HostCalls);
    }

    [Fact]
    public async Task AFailingOutermostOwner_PublishesNothing()
    {
        var source = F("B = {\n    V = if(tick() == 1, 1 / 0, k)\n    V\n}", "[0].map{ n + B }[0] + B.V");
        var oracle = await ObserveAsync(source);
        Assert.Equal("err", oracle.Kind);
        Assert.StartsWith("DivisionByZero: ", Assert.Single(oracle.Errors), StringComparison.Ordinal);
        Assert.Equal(Ticks(1), oracle.HostCalls);

        foreach (var asynchronous in new[] { false, true })
        {
            var cache = new RecordingCache();
            var log = new List<string>();
            var (result, _) = asynchronous
                ? await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(Program(source),
                    zeroArgPropertyResultCache: cache, hostOperations: Operations(log, suspending: true)))
                : Evaluator.RunCountedObserved(Program(source), zeroArgPropertyResultCache: cache,
                    hostOperations: Operations(log, suspending: false));
            Assert.True(result.IsError);
            Assert.Equal(0, cache.PublishedCount);
            Assert.Equal(0, cache.ActiveOwnerCount);
        }
    }

    // ── 5. Owners that record no activation, and exported properties ─────────────────────────

    [Theory]
    // B reads nothing of F: B and E are exported, one evaluation for the run.
    [InlineData("B = {\n    E = trace(7)\n    E + 0\n}", "[0].map{ n + B }[0] + B.E + k", "F(3), F(4)", "S[17, 18]", new[] { 7 })]
    // B is local-only but declares only an exported E: no activation, no inheritance needed.
    [InlineData("B = {\n    E = trace(7)\n    E + k\n}", "[0].map{ n + B }[0] + B.E", "F(3), F(4)", "S[17, 18]", new[] { 7 })]
    public async Task OwnersWithoutLocalOnlyProperties_AreUnchanged(string bRows, string fRows, string calls, string expected, int[] traces)
    {
        var oracle = await ObserveAsync(F(bRows, fRows, calls));
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Traces(traces), oracle.HostCalls);
    }

    [Fact]
    public async Task AnExportedRootProperty_IsSharedAcrossEveryCallbackActivation()
    {
        var oracle = await ObserveAsync("E = trace(7)\nB = {\n    V = E * 2\n    V\n}\n[1, 2, 3].map{ n + B + E }, B.V");
        Assert.Equal("S[L[22, 23, 24], 14]", oracle.Value);
        Assert.Equal(Traces(7), oracle.HostCalls);
    }

    // ── 6. Consumer routes ──────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("[0, 1].filter{ n + B > 3 }.count + B.V", "4")]
    [InlineData("[0, 1].filter{ n * 0 + B > 0 }.count + B.V", "5")]
    [InlineData("Add(e, a) = a + e * B\nreduce([1, 2], Add, 0) + B.V", "12")]
    [InlineData("Step(s) = s + B\nrepeat(Step(0), 3) + B.V", "12")]
    [InlineData("Step(s) = s + 1 + B * 0, s < 3\nwhile(Step(0)) + B.V", "6")]
    [InlineData("if(k > 0, [0].map{ n + B }[0], 0) + B.V", "6")]
    [InlineData("H(0) = B\nH(x) = x\nH(0) + B.V", "6")]
    [InlineData("Capture(meta op) = op\nG(x) = x + B\nR = Capture(G(1))\nR.Invoke() + B.V", "7")]
    [InlineData("Capture(meta op) = op\nG(x) = x + B\nR = Capture(G(1))\nR.Algorithm(5) + B.V", "11")]
    [InlineData("Capture(meta op) = op\nG(x) = x + B\nR = Capture(G(1))\nA = R.Algorithm\nA(5) + A(6) + B.V", "20")]
    [InlineData("Apply(f, x) = f(x)\nApply({ x + B }, 1) + B.V", "7")]
    [InlineData("[0, 1].map{ n * 0 + [0].map{ m + n + B }[0] }[1] + B.V", "7")]
    public async Task EveryConsumerRoute_SharesTheDeclaringActivationsEntry(string fRows, string expected)
    {
        foreach (var bRows in BothOwnerForms)
        {
            var oracle = await ObserveAsync(F(bRows, fRows));
            Assert.True(oracle.Kind == "ok", $"{bRows}: {oracle}");
            Assert.Equal(expected, oracle.Value);
            Assert.Equal(Traces(3), oracle.HostCalls);
        }
    }

    [Theory]
    [InlineData("Step(s) = s + B\nrepeat(Step(0), 3) + B.V", "12", 1, 0)]
    [InlineData("[0, 1].filter{ n * 0 + B > 0 }.count + B.V", "5", 0, 1)]
    public void OptimizedConsumers_ActuallyExecuteTheIntendedStrategy(
        string rows, string expected, int loopHits, int fusionHits)
    {
        var loops = new LoopOptimizationDiagnostics();
        var sequences = new SequencePipelineDiagnostics();
        var cache = new RecordingCache();
        var log = new List<string>();
        var (result, _) = Evaluator.RunCountedObserved(Program(F(TracedB, rows)), enableOptimizations: true,
            loopDiagnostics: loops, sequenceDiagnostics: sequences, zeroArgPropertyResultCache: cache,
            hostOperations: Operations(log, suspending: false));
        Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());
        Assert.Equal(expected, SixRouteAgreement.Neutral(result.Value.Value));
        Assert.Equal(loopHits, loops.GetSnapshot().OptimizedLoopHits);
        Assert.Equal(fusionHits, sequences.GetSnapshot().FilterCountFusionHits);
        Assert.Equal(1, cache.Evaluations["V"]);
        Assert.Equal(Traces(3), log);
    }

    // ── 7. PAR-03 / F-1: a nested property's OWN inferred parameter is not a captured one ────

    public static TheoryData<string, string, string, int[]> ParameterOwnership => new()
    {
        // E40: n is used only inside Sq, so Sq(n) is Sq's own parameter and each use is a fresh lifted call.
        { "E40", "[1, 2].map{\n    Sq = trace(n) * n\n    Sq + Sq\n}", "L[2, 8]", [1, 1, 2, 2] },
        // N1: the named form with the same inferred shape behaves the same.
        { "N1", "Cb = {\n    Sq = trace(n) * n\n    Sq + Sq\n}\n[1, 2].map(Cb)", "L[2, 8]", [1, 1, 2, 2] },
        // A3: the callback's own row uses n, so n is the callback's and Sq is cached per activation.
        { "A3", "[1, 2].map{\n    Sq = trace(n) * n\n    n * 0 + Sq + Sq\n}", "L[2, 8]", [1, 2] },
        // E40b: the named control declares n explicitly.
        { "E40b", "Cb(n) = {\n    Sq = trace(n) * n\n    Sq + Sq\n}\n[1, 2].map(Cb)", "L[2, 8]", [1, 2] },
    };

    [Theory]
    [MemberData(nameof(ParameterOwnership))]
    public async Task ParameterOwnershipDecidesSharing_NotNaming(string id, string source, string expected, int[] traces)
    {
        var oracle = await ObserveAsync(source);
        Assert.True(oracle.Kind == "ok", $"{id}: {oracle}");
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Traces(traces), oracle.HostCalls);
    }

    [Fact]
    public void E40AndA3_ElaborateToTheirDocumentedShapes()
    {
        static Property Sq(string source)
        {
            var root = ParseWithHostOperations(source);
            var map = Assert.IsType<Expr.DotCall>(Assert.Single(root.Output));
            var callback = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(map.Args!));
            return Assert.Single(callback.Algorithm.Properties, static p => p.Name == "Sq");
        }

        // E40: Sq owns n (PAR-03); the rows are two explicit lifted calls.
        var e40 = Sq("[1, 2].map{\n    Sq = trace(n) * n\n    Sq + Sq\n}");
        Assert.Equal(["n"], e40.Value.Params);
        // A3: the callback owns n; Sq is a zero-parameter local-only property.
        var a3 = Sq("[1, 2].map{\n    Sq = trace(n) * n\n    n * 0 + Sq + Sq\n}");
        Assert.Empty(a3.Value.Params);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, a3.Exposure);
    }

    // ── harness ──────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// The six-route observation of <paramref name="source"/>, after requiring the generic, optimized and
    /// genuinely suspending async twin evaluator routes to agree on value, host calls and semantic steps.
    /// </summary>
    private static async Task<SixRouteAgreement.Observation> ObserveAsync(string source)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);

        var generic = await StepsAsync(source, path: 0);
        Assert.Equal(generic, await StepsAsync(source, path: 1));
        Assert.Equal(generic, await StepsAsync(source, path: 2));
        return oracle;
    }

    private static async Task<string> StepsAsync(string source, int path)
    {
        var log = new List<string>();
        var (result, budget) = path == 2
            ? await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(Program(source),
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: Operations(log, suspending: true)))
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

    private static Algorithm.User ParseWithHostOperations(string source)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = Operations([], suspending: false) });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return parsed.Root;
    }

    private static Expr Program(string source) => new Expr.AlgorithmExpr(ParseWithHostOperations(source));

    private sealed class RecordingCache : IAsyncZeroArgPropertyResultCache
    {
        private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();

        // DECON-CACHE-2: the inner cache publishes every read, so its publication provenance is this cache's.
        public bool ReadObtainsPublishedValue(ZeroArgPropertyCacheKey key) => _inner.ReadObtainsPublishedValue(key);

        public int PublishedCount => _inner.PublishedCount;

        public int ActiveOwnerCount => _inner.ActiveOwnerCount;

        public List<ZeroArgPropertyExecution> Requests { get; } = [];

        public Dictionary<string, int> Evaluations { get; } = new(StringComparer.Ordinal);

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Record(execution);
            return _inner.GetOrEvaluate(execution, () =>
            {
                Count(execution);
                return evaluate();
            });
        }

        public ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
            ZeroArgPropertyExecution execution,
            Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            Record(execution);
            return _inner.GetOrEvaluateAsync(execution, () =>
            {
                Count(execution);
                return evaluateAsync();
            });
        }

        // CACHE-PUB-1: an explicit zero-supply invocation keeps the inner cache's publication law.
        public EvalResult<ZeroArgPropertyResult> Invoke(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
            => _inner.Invoke(execution, evaluate);

        public ValueTask<EvalResult<ZeroArgPropertyResult>> InvokeAsync(
            ZeroArgPropertyExecution execution,
            Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
            => _inner.InvokeAsync(execution, evaluateAsync);

        private void Record(ZeroArgPropertyExecution execution)
        {
            lock (Requests) Requests.Add(execution);
        }

        private void Count(ZeroArgPropertyExecution execution)
        {
            lock (Evaluations) Evaluations[execution.Binding.Name] = Evaluations.GetValueOrDefault(execution.Binding.Name) + 1;
        }
    }
}
