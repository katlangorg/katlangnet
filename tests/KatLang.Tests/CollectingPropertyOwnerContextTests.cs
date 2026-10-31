using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// COLLECT-CACHE-1 (October 23 2026): a property-style READ of a collecting-only owner inherits its
/// declaring context. <c>Only(*xs)</c> accepts zero supplied arguments, so a bare <c>Only</c> is a
/// property read — it already used the zero-argument property cache — but its body was entered through
/// the ordinary zero-supply demand, whose binder recorded the FRESH bound context on <c>Only</c>'s
/// activation. Its local-only <c>V</c> was therefore keyed on that context, while a structural
/// <c>Only.V</c> keyed it on <c>F</c>'s activation: one activation of <c>F</c> evaluated <c>V</c>
/// twice and <c>Only == Only.V</c> was <c>false</c>. CACHE-OWNER-D1 had fixed exactly this for owners
/// with no pattern (<see cref="ParameterlessOwnerEntryContextTests"/>). The read now binds the empty
/// supply through the ordinary binder (so <c>xs</c> is <c>[]</c> and shadows an outer <c>xs</c>) and
/// records the declaring activation's identity; an explicit <c>Only()</c> stays a fresh call. Lean:
/// the pattern arm of <c>EvalBody.evalPropertyDemandCounted</c>, the <c>CollectCache1</c> guards of
/// <c>CoreTests/PropertyCacheConsumers.lean</c> and § 4 of <c>KatLangArityLaws/PropertyOwnerContext.lean</c>.
///
/// <para>Every program runs on the six established routes (<see cref="SixRouteAgreement"/>), which must
/// agree on value, errors and the exact host-call log; the generic, optimized and genuinely suspending
/// async twin evaluator routes must also agree on the semantic step count. The matrix ids (C1–C20) are
/// the brief's; <c>experimental/features/collect-cache-1-implementation.md</c> records the pre-fix
/// outcomes.</para>
/// </summary>
public class CollectingPropertyOwnerContextTests
{
    // F's Only is a collecting-only owner; its local-only V reads F's parameter k.
    private static string F(string onlyRows, string fRows, string call = "F(3)")
        => "F(k) = {\n" + Indent(onlyRows) + Indent(fRows) + "}\n" + call;

    private static string Indent(string rows)
        => string.Concat(rows.Split('\n').Select(static row => "    " + row + "\n"));

    private const string TracedOnly = "Only(*xs) = {\n    V = trace(k)\n    V\n}";

    private static string[] Traces(params int[] values) => [.. values.Select(static value => $"trace({value})")];

    private static string[] Ticks(int count) => [.. Enumerable.Range(1, count).Select(static tock => $"tock#{tock}")];

    // ── C1–C4, C7, C8, C12, C17: one evaluation per binding in one activation ────────────────

    public static TheoryData<string, string, string, string[]> ReadMatrix => new()
    {
        // C1: Only first read by a callback, then the structural Only.V (was two traces).
        { "C1", F(TracedOnly, "[0].map{ n + Only }[0] + Only.V"), "6", Traces(3) },
        // C2: the order does not matter (was two traces).
        { "C2", F(TracedOnly, "Only.V + [0].map{ n + Only }[0]"), "6", Traces(3) },
        // C3: a direct read from F's own body and the structural read are one binding (was two traces).
        { "C3", F(TracedOnly, "Only + Only.V"), "6", Traces(3) },
        // C3: a direct read before a nested consumer keeps its reuse (was two traces).
        { "C3-PRE", F(TracedOnly, "Only + [0].map{ n + Only }[0] + Only.V"), "9", Traces(3) },
        // C4: the value-sensitive witnesses (were false with two ticks).
        { "C4", F("Only(*xs) = {\n    V = k + tock()\n    V\n}", "[0].map{ n * 0 + Only }[0] == Only.V"), "true", Ticks(1) },
        { "C4-DIRECT", F("Only(*xs) = {\n    V = k + tock()\n    V\n}", "Only == Only.V"), "true", Ticks(1) },
        // C7: the bare read binds precisely the empty collection, which V's owner reads too.
        { "C7", F("Only(*xs) = {\n    V = trace(k)\n    V + xs.count\n}", "[0].map{ n + Only }[0] + Only.V"), "6", Traces(3) },
        { "C7-LIST", F("Only(*xs) = {\n    V = trace(k)\n    V, xs\n}", "[0].map{ n * 0 + Only.V }[0], Only, Only.V"), "S[3, S[3, L[]], 3]", Traces(3) },
        // C8: the collector shadows F's own xs inside Only; F's xs is untouched outside.
        {
            "C8",
            "F(k, xs) = {\n    Only(*xs) = {\n        V = trace(k)\n        V, xs\n    }\n    Only, xs, Only.V\n}\nF(3, 9)",
            "S[S[3, L[]], 9, 3]",
            Traces(3)
        },
        // C12: a helper call (was two traces).
        { "C12-HELP", F("Only(*xs) = {\n    V = trace(k) * k\n    V + 1\n}\nG(x) = x + Only", "G(1) + Only.V"), "20", Traces(3) },
        // C12: nested callbacks.
        { "C12-NESTED", F(TracedOnly, "[0, 1].map{ n * 0 + [0].map{ m + n + Only }[0] }[1] + Only.V"), "7", Traces(3) },
        // C12: the declaring owner is itself an anonymous callback.
        {
            "C12-ANON",
            "[3].map{\n    Only(*xs) = {\n        V = trace(n) * n\n        V + 1\n    }\n    n * 0 + [1, 2].map{ m + Only }[0] + Only.V\n}",
            "L[20]",
            Traces(3)
        },
        // C12: a nested parameterless owner and a nested collecting owner under Only (were 2 and 3 traces).
        {
            "C12-DEEP",
            F("Only(*xs) = {\n    C = {\n        V = trace(k)\n        V\n    }\n    C\n}", "[0].map{ n + Only }[0] + [0].map{ n + Only.C }[0] + Only.C.V"),
            "9",
            Traces(3)
        },
        {
            "C12-DEEPCOL",
            F("Only(*xs) = {\n    Inner(*ys) = {\n        V = trace(k)\n        V\n    }\n    Inner\n}", "[0].map{ n + Only }[0] + [0].map{ n + Only.Inner }[0] + Only.Inner.V"),
            "9",
            Traces(3)
        },
        // C17: one shared deconstruction right-hand side for the callback's Only and Only.a, Only.b.
        {
            "C17",
            F("Only(*xs) = {\n    a, b = trace(k), k + 1\n    a + b\n}", "[1, 2].map{ n + Only }[0] + Only.a + Only.b"),
            "15",
            Traces(3)
        },
        // C17: a deconstruction reading the collector is local to Only's bound activation.
        { "C17-XS", F("Only(*xs) = {\n    a, b = trace(k), xs.count\n    a + b\n}", "[1, 2].map{ n + Only }[0] + Only"), "7", Traces(3) },
    };

    [Theory]
    [MemberData(nameof(ReadMatrix))]
    public async Task ReadMatrix_OneEvaluationPerBindingAndActivation_OnEveryRoute(string id, string source, string expected, string[] hostCalls)
    {
        var oracle = await ObserveAsync(source);
        Assert.True(oracle.Kind == "ok", $"{id}: {oracle}");
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(hostCalls, oracle.HostCalls);
    }

    [Fact]
    public async Task C4_TheBindingHasOneValueInOneActivation_WithASeededRandomDraw()
    {
        var source = F("Only(*xs) = {\n    V = random(0, 1000) + k * 0\n    V\n}", "[1].map{ n * 0 + Only }[0] == Only.V, Only.V == Only");
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source, randomSeed: 11);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal("S[true, true]", oracle.Value);
    }

    // ── The cache seam: one key per binding, the declaring identity, the binder's own tier ────

    [Theory]
    [InlineData("[0].map{ n + Only }[0] + Only.V")]
    [InlineData("Only.V + [0].map{ n + Only }[0]")]
    [InlineData("Only + Only.V")]
    [InlineData("G(x) = x + Only\nG(1) + Only.V + [0, 1].map{ n + Only }[1]")]
    public async Task TheLexicalAndStructuralReadsOfV_ComputeOneKey(string rows)
    {
        foreach (var asynchronous in new[] { false, true })
        {
            var cache = new RecordingCache();
            var log = new List<string>();
            var program = Program(F(TracedOnly, rows));
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
    public void TheReadEntry_RecordsTheDeclaringIdentity_NotTheReadersNorTheBindersOwn()
    {
        // Only's own key and V's key (through Only's bound activation) carry F's binding identity. The
        // callback reader's identity differs from it, and so does the fresh identity of the bound tier.
        var cache = new RecordingCache();
        var (result, _) = Evaluator.RunCountedObserved(Program(F(TracedOnly, "[0].map{ n + Only }[0] + Only.V")),
            zeroArgPropertyResultCache: cache, hostOperations: Operations([], suspending: false));
        Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());

        var onlyRead = Assert.Single(cache.Requests, static request => request.Binding.Name == "Only");
        var onlyKey = ZeroArgPropertyCacheKey.FromExecution(onlyRead);
        var vRequests = cache.Requests.Where(static request => request.Binding.Name == "V").ToList();
        var vKey = Assert.Single(vRequests.Select(ZeroArgPropertyCacheKey.FromExecution).Distinct());
        Assert.Same(onlyKey.ValueEnvironmentIdentity, vKey.ValueEnvironmentIdentity);
        Assert.NotSame(onlyRead.ValueEnvironmentIdentity, onlyKey.ValueEnvironmentIdentity);
        // V's lexical request is made inside Only's body, whose reader identity is the BOUND tier (the
        // binder's fresh need list): it must not be the identity the entry is keyed on.
        Assert.Contains(vRequests, request => !ReferenceEquals(request.ValueEnvironmentIdentity, vKey.ValueEnvironmentIdentity));
    }

    // ── C5, C6: activation isolation ─────────────────────────────────────────────────────────

    [Theory]
    // C5: two calls of F with different captured values: one evaluation each.
    [InlineData("[0].map{ n + Only }[0] + Only.V", "F(3), F(4)", "S[6, 8]", new[] { 3, 4 })]
    // C6: numerically equal arguments are still two activations (was four traces).
    [InlineData("[0].map{ n + Only }[0] + Only.V", "F(3), F(3)", "S[6, 6]", new[] { 3, 3 })]
    // C6: the second activation reached inside a callback stays separate.
    [InlineData("[0].map{ n + Only }[0] + Only.V", "[3, 4].map{ F(n) }", "L[6, 8]", new[] { 3, 4 })]
    // Inside one activation, nested callbacks and a helper still share F's entry.
    [InlineData("G(x) = [0].map{ n + x + Only }[0]\n[0].map{ n + G(1) }[0] + Only.V + G(2)", "F(3), F(5)", "S[12, 18]", new[] { 3, 5 })]
    public async Task DistinctDeclaringActivations_NeverShareAnEntry(string fRows, string calls, string expected, int[] traces)
    {
        var oracle = await ObserveAsync(F(TracedOnly, fRows, calls));
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Traces(traces), oracle.HostCalls);
    }

    [Fact]
    public async Task TheNearestDeclaringActivation_WinsWithSeveralActiveAncestors()
    {
        const string source = "F(k) = {\n    G(x) = {\n        Only(*xs) = {\n            V = trace(k + x)\n            V\n        }\n        [0].map{ n + Only }[0] + Only.V\n    }\n    G(10), G(20)\n}\nF(3)";
        var oracle = await ObserveAsync(source);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal("S[26, 46]", oracle.Value);
        Assert.Equal(Traces(13, 23), oracle.HostCalls);
    }

    // ── C9, C10: written calls stay fresh; CACHE-PUB-1 publication is unchanged ──────────────

    [Theory]
    // C9: two explicit calls, two fresh contexts.
    [InlineData("Only() + Only()", 2, "6")]
    [InlineData("[0].map{ n + Only() }[0] + Only()", 2, "6")]
    // C10: Only() establishes Only's entry (CACHE-PUB-1) and the bare read reuses it.
    [InlineData("Only() + Only", 1, "6")]
    // C10: a bare read, then a call: the call is fresh and never replaces the entry.
    [InlineData("Only + Only()", 2, "6")]
    // C10: the first call publishes once with its OWN locals; reads reuse it, the second call is fresh,
    // and Only.V is F's entry.
    [InlineData("Only() + Only + Only() + Only + Only.V", 3, "15")]
    // An explicit call's locals belong to the call's own context: Only.V reads F's, a second evaluation.
    [InlineData("Only() + Only.V", 2, "6")]
    // The read in a callback and the structural read share F's context; the call stays fresh.
    [InlineData("[0].map{ n + Only }[0] + Only() + Only.V", 2, "9")]
    // A call with supplied items is an ordinary fresh call too.
    [InlineData("Only(1, 2) + Only + Only.V", 2, "9")]
    public async Task C9_C10_WrittenCalls_RemainFresh(string fRows, int evaluations, string expected)
    {
        var oracle = await ObserveAsync(F(TracedOnly, fRows));
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Traces([.. Enumerable.Repeat(3, evaluations)]), oracle.HostCalls);
    }

    [Theory]
    [InlineData("R.Invoke(), R.Invoke(), Only, Only.V", "S[4, 5, 4, 6]")]
    [InlineData("R.Algorithm(), R.Algorithm(), Only, Only.V", "S[4, 5, 4, 6]")]
    [InlineData("A = R.Algorithm\nA(), A(), Only, Only.V", "S[4, 5, 4, 6]")]
    public async Task C16_MetaCallsOfTheCollectingOwner_KeepFreshLocalsAndFirstPublication(string rows, string expected)
    {
        // META calls publish Only on the first invocation; the second is fresh. A runtime reference of the
        // projection publishes under its target's origin too (OD-E, M4★; formerly a parameterized runtime
        // alias named no publication binding: S[4, 5, 6, 6]). Only.V belongs to F and never reuses either
        // call's local V.
        var owner = "Only(*xs) = {\n    V = k + tock()\n    V\n}\nCapture(meta op) = op\nR = Capture(Only())";
        var oracle = await ObserveAsync(F(owner, rows));
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Ticks(3), oracle.HostCalls);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ReadResources_AgreeAcrossGenericOptimizedAndSuspendingTwins(bool collecting)
    {
        var owner = collecting ? TracedOnly : TracedOnly.Replace("Only(*xs)", "Only", StringComparison.Ordinal);
        var source = F(owner, "[0].map{ n + Only }[0] + Only.V");
        var observations = new List<(string Value, int Emitted, long Steps, long Checkpoints,
            int PeakDepth, int FinalDepth, long Items, long StringChars, int Transient, string Calls)>();
        foreach (var route in new[] { 0, 1, 2 })
        {
            var log = new List<string>();
            var operations = Operations(log, suspending: route == 2);
            var program = Program(source, operations);
            var (result, budget) = route == 2
                ? await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(program,
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: operations))
                : Evaluator.RunCountedObserved(program, enableOptimizations: route == 1, hostOperations: operations);
            Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());
            Assert.Equal(0, budget.CurrentDepth);
            observations.Add((SixRouteAgreement.Neutral(result.Value.Value), result.Value.EmittedCount,
                budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth, budget.CurrentDepth,
                budget.MaterializedItems, budget.MaterializedStringChars, budget.PeakTransientExpansion,
                string.Join(",", log)));
        }
        Assert.Equal("6", observations[0].Value);
        Assert.Equal("trace(3)", observations[0].Calls);
        Assert.True(observations[0].Checkpoints > 0);
        Assert.Equal(observations[0], observations[1]);
        Assert.Equal(observations[0], observations[2]);
    }

    // ── C11, C13, C14, C15: existing rejections and eligibility are unchanged ─────────────────

    [Fact]
    public async Task C11_AStructuralReadNeedingTheCollector_IsStillRejected()
    {
        // V reads xs, so Only.V needs an Only activation the structural read does not have: the ordinary
        // accessibility rejection, not a cache-shared value. The callback's bare read itself is valid.
        const string onlyRows = "Only(*xs) = {\n    V = trace(k) + xs.count\n    V\n}";
        var rejected = await ObserveAsync(F(onlyRows, "[0].map{ n + Only }[0] + Only.V"));
        Assert.Equal("err", rejected.Kind);
        Assert.StartsWith("LocalOnlyProperty: ", Assert.Single(rejected.Errors), StringComparison.Ordinal);
        Assert.Contains("'k', 'xs'", rejected.Errors[0], StringComparison.Ordinal);

        var read = await ObserveAsync(F(onlyRows, "[0].map{ n + Only }[0] + Only"));
        Assert.Equal("ok", read.Kind);
        Assert.Equal("6", read.Value);
        Assert.Equal(Traces(3), read.HostCalls);
    }

    [Theory]
    // C13: a fixed slot before the collector does not accept zero supplied arguments.
    [InlineData("Fix(x, *xs) = {\n    V = trace(k)\n    V\n}", "Fix + 0", "Property 'Fix' expects 1 parameter, but was called with 0 arguments.")]
    // C14: a grouped collecting pattern consumes one slot.
    [InlineData("Grp((*xs)) = {\n    V = trace(k)\n    V\n}", "Grp + 0", "Property 'Grp' expects 1 parameter, but was called with 0 arguments.")]
    public async Task C13_C14_SignaturesThatRefuseTheEmptySupply_KeepTheirArityRejection(string owner, string rows, string message)
    {
        var oracle = await ObserveAsync(F(owner, rows));
        Assert.Equal("err", oracle.Kind);
        var error = Assert.Single(oracle.Errors);
        Assert.StartsWith("ArityMismatch: ", error, StringComparison.Ordinal);
        Assert.Contains(message, error, StringComparison.Ordinal);
        Assert.Empty(oracle.HostCalls);
    }

    [Fact]
    public async Task C14_AGroupedCollectorsWrittenCall_StaysFresh()
    {
        var oracle = await ObserveAsync(F("Grp((*xs)) = {\n    V = trace(k)\n    V\n}", "Grp(()) + Grp.V"));
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal("6", oracle.Value);
        Assert.Equal(Traces(3, 3), oracle.HostCalls);
    }

    [Theory]
    // C15: a clause family cannot declare a collecting clause (the zero-supply family has no surface
    // spelling; ExplicitCallPublicationTests pins the host-built one), and `open` refuses an owner that
    // requires arguments, so neither reaches the new read.
    [InlineData("H(0) = 100\nH(*xs) = {\n    V = trace(k)\n    V\n}", "[0].map{ n + H }[0] + H", "InvalidCollectingBinding: ")]
    [InlineData("open Only\n" + TracedOnly, "V", "UndeclaredIdentifier: ")]
    public async Task C15_FamiliesAndOpenedCollectingOwners_RemainFrontEndErrors(string owner, string rows, string code)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(F(owner, rows));
        Assert.Equal("parse", oracle.Kind);
        Assert.StartsWith(code, oracle.Errors[0], StringComparison.Ordinal);
    }

    // ── C16, C18: aliases, META and every consumer route ─────────────────────────────────────

    [Theory]
    // C16: a static alias's bare read is Only's property read (was two traces).
    [InlineData(TracedOnly + "\nA = Only", "[0].map{ n + A }[0] + Only.V + A", "9", 1)]
    // C16: the alias's explicit call stays fresh.
    [InlineData(TracedOnly + "\nA = Only", "A + A() + A", "9", 2)]
    // C16: META: a captured call reading Only in a helper (was two traces).
    [InlineData(TracedOnly + "\nCapture(meta op) = op\nG(x) = x + Only\nR = Capture(G(1))", "R.Invoke() + Only.V", "7", 1)]
    [InlineData(TracedOnly + "\nCapture(meta op) = op\nG(x) = x + Only\nR = Capture(G(1))", "R.Algorithm(5) + Only.V", "11", 1)]
    [InlineData(TracedOnly + "\nCapture(meta op) = op\nG(x) = x + Only\nR = Capture(G(1))\nA = R.Algorithm", "A(5) + A(6) + Only.V", "20", 1)]
    // C18: every consumer (was two traces each).
    [InlineData(TracedOnly, "Step(s) = s + Only\nrepeat(Step(0), 3) + Only.V", "12", 1)]
    [InlineData(TracedOnly, "Step(s) = s + 1 + Only * 0, s < 3\nwhile(Step(0)) + Only.V", "6", 1)]
    [InlineData(TracedOnly, "Step(s) = s + Only, s < 5\nStep(0).while + Only.V", "9", 1)]
    [InlineData(TracedOnly, "[0, 1].filter{ n + Only > 3 }.count + Only.V", "4", 1)]
    [InlineData(TracedOnly, "[0, 1].filter{ n * 0 + Only > 0 }.count + Only.V", "5", 1)]
    [InlineData(TracedOnly, "Add(e, a) = a + e * Only\nreduce([1, 2], Add, 0) + Only.V", "12", 1)]
    [InlineData(TracedOnly, "Add(e, a) = a + e\nreduce([1, 2], Add, Only) + Only.V", "9", 1)]
    [InlineData(TracedOnly, "sum(Only) + Only.V + if(true, Only, 0)", "9", 1)]
    [InlineData(TracedOnly, "if(k > 0, [0].map{ n + Only }[0], 0) + Only.V", "6", 1)]
    [InlineData(TracedOnly, "G(f) = f + 1\nG(Only) + Only.V", "7", 1)]
    [InlineData(TracedOnly, "Apply(f, x) = f(x)\nApply({ x + Only }, 1) + Only.V", "7", 1)]
    [InlineData(TracedOnly, "H(0) = Only\nH(x) = x\nH(0) + Only.V", "6", 1)]
    public async Task C16_C18_AliasesMetaAndConsumers_ShareTheDeclaringActivationsEntry(string owner, string fRows, string expected, int traces)
    {
        var oracle = await ObserveAsync(F(owner, fRows));
        Assert.True(oracle.Kind == "ok", oracle.ToString());
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Traces([.. Enumerable.Repeat(3, traces)]), oracle.HostCalls);
    }

    [Theory]
    // C18: the collecting owner declared INSIDE a loop step: one V per step activation.
    [InlineData("Step(s) = {\n    Only(*xs) = {\n        V = trace(s)\n        V\n    }\n    s + 1 + Only * 0 + Only.V * 0\n}\nrepeat(Step(0), 3)", "3", new[] { 0, 1, 2 })]
    [InlineData("Step(s) = {\n    Only(*xs) = {\n        V = trace(s)\n        V\n    }\n    s + 1 + [0].map{ n + Only }[0] * 0 + Only.V * 0, s < 2\n}\nwhile(Step(0))", "2", new[] { 0, 1 })]
    public async Task C18_ACollectingOwnerInsideALoopStep_IsReadOncePerStep(string source, string expected, int[] traces)
    {
        var oracle = await ObserveAsync(source);
        Assert.True(oracle.Kind == "ok", oracle.ToString());
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Traces(traces), oracle.HostCalls);
    }

    [Theory]
    [InlineData("Step(s) = s + Only\nrepeat(Step(0), 3) + Only.V", "12", 1, 0)]
    [InlineData("[0, 1].filter{ n * 0 + Only > 0 }.count + Only.V", "5", 0, 1)]
    public void C18_OptimizedConsumers_ActuallyExecuteTheIntendedStrategy(string rows, string expected, int loopHits, int fusionHits)
    {
        var loops = new LoopOptimizationDiagnostics();
        var sequences = new SequencePipelineDiagnostics();
        var cache = new RecordingCache();
        var log = new List<string>();
        var (result, _) = Evaluator.RunCountedObserved(Program(F(TracedOnly, rows)), enableOptimizations: true,
            loopDiagnostics: loops, sequenceDiagnostics: sequences, zeroArgPropertyResultCache: cache,
            hostOperations: Operations(log, suspending: false));
        Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());
        Assert.Equal(expected, SixRouteAgreement.Neutral(result.Value.Value));
        Assert.Equal(loopHits, loops.GetSnapshot().OptimizedLoopHits);
        Assert.Equal(fusionHits, sequences.GetSnapshot().FilterCountFusionHits);
        Assert.Equal(1, cache.Evaluations["V"]);
        Assert.Equal(Traces(3), log);
    }

    // ── Exported members and root owners are unchanged ───────────────────────────────────────

    [Theory]
    // Only declares only an exported E: no local-only key, one evaluation for the run.
    [InlineData("Only(*xs) = {\n    E = trace(7)\n    E + k\n}", "[0].map{ n + Only }[0] + Only.E", "F(3), F(4)", "S[17, 18]", new[] { 7 })]
    public async Task OwnersWithoutLocalOnlyProperties_AreUnchanged(string onlyRows, string fRows, string calls, string expected, int[] traces)
    {
        var oracle = await ObserveAsync(F(onlyRows, fRows, calls));
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Traces(traces), oracle.HostCalls);
    }

    [Theory]
    // A root owner: V is exported, one evaluation.
    [InlineData("Only(*xs) = {\n    V = trace(7)\n    V + 1\n}\n[1, 2].map{ n + Only }[0] + Only.V + Only", "24")]
    // A root owner whose V reads the collector: no activated declaring level, the reader fallback.
    [InlineData("Only(*xs) = {\n    V = trace(7) + xs.count\n    V + 1\n}\n[1, 2].map{ n + Only }[0] + Only", "17")]
    public async Task RootOwners_AreUnchanged(string source, string expected)
    {
        var oracle = await ObserveAsync(source);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(Traces(7), oracle.HostCalls);
    }

    // ── C19: a host-built ownerless ScopeCtx (CACHE-OWNER-D3) ────────────────────────────────

    [Fact]
    public async Task C19_AHostScopeCollectingOwner_KeepsItsReferenceIdentity()
    {
        // The host scope declares Only(*xs) = { V = tock() + xs.count ⏎ V + V } with V marked local-only
        // on the collector. Two opened blocks read Only: Only is ONE entry keyed on the host scope by
        // reference (D3), and its V is evaluated once (the reader fallback: no activated declaring level).
        static Expr Build(ScopeCtx prelude)
        {
            var v = new Property("V", new Algorithm.User(null, [], [], [],
                    new OutputBundle([new Expr.Binary(BinaryOp.Add, new Expr.Call(new Expr.Resolve("tock"), OutputBundle.Empty),
                        new Expr.Call(new Expr.Resolve("count"), new OutputBundle([new Expr.Param("xs")])))])),
                false, PropertyExposure.LocalOnlyCapturedAncestorParameters) { RequiredAncestorParameters = ["xs"] };
            var only = new Algorithm.User(null, [new CaptureParameterPattern("xs", Kind: ParameterKind.Collecting)], [], [v],
                new OutputBundle([new Expr.Binary(BinaryOp.Add, new Expr.Resolve("V"), new Expr.Resolve("V"))]));
            var host = new ScopeCtx(prelude, [], [new Property("Only", only)]);
            Expr Block(string name) => new Expr.AlgorithmExpr(new Algorithm.User(host, [], [],
                [new Property(name, new Algorithm.User(null, [], [], [], new OutputBundle([new Expr.Resolve("Only")])), true)],
                OutputBundle.Empty));
            return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [Block("RunA"), Block("RunB")], [],
                new OutputBundle([new Expr.Binary(BinaryOp.Add, new Expr.Resolve("RunA"), new Expr.Resolve("RunB"))])));
        }

        foreach (var route in new[] { 0, 1, 2 })
        {
            var log = new List<string>();
            var operations = Operations(log, suspending: route == 2);
            var program = Build(new ScopeCtx(null, [], operations.RuntimePreludeAlgorithm.Properties));
            var (result, _) = route == 2
                ? await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                    hostOperations: operations)
                : Evaluator.RunCountedObserved(program, enableOptimizations: route == 1, hostOperations: operations);
            Assert.True(result.IsOk, result.IsOk ? null : result.Error.ToString());
            Assert.Equal("4", SixRouteAgreement.Neutral(result.Value.Value));
            Assert.Equal(Ticks(1), log);
        }
    }

    // ── C20: re-entrant reads, failure and cancellation ──────────────────────────────────────

    [Fact]
    public async Task C20_AReentrantRead_PublishesOnlyTheOutermostOwnersResult()
    {
        // Q-37: Only entered in a callback evaluates V, whose body re-enters V through Only.V. Both
        // spellings are ONE key, so the inner reads are re-entrant and only the outermost result is
        // published and reused. Before the fix the split key published an inner result (22, four ticks).
        var source = F("Only(*xs) = {\n    V = if(tock() < 3, Only.V + 1, k)\n    V\n}", "[0].map{ n + Only }[0] + Only.V", "F(10)");
        var oracle = await ObserveAsync(source);
        Assert.Equal("24", oracle.Value);
        Assert.Equal(Ticks(3), oracle.HostCalls);

        // The same through a re-entrant bare read of the owner itself.
        var owner = await ObserveAsync(source.Replace("Only.V + 1, k", "Only + 1, k", StringComparison.Ordinal));
        Assert.Equal("24", owner.Value);
        Assert.Equal(Ticks(3), owner.HostCalls);
    }

    [Fact]
    public async Task C20_AFailingOutermostOwner_PublishesNothing()
    {
        var source = F("Only(*xs) = {\n    V = if(tock() == 1, 1 / 0, k)\n    V\n}", "[0].map{ n + Only }[0] + Only.V");
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

    [Fact]
    public async Task C20_CancellationInsideTheCollectingRead_PublishesNothingAndReleasesOwners()
    {
        using var cts = new CancellationTokenSource();
        var cache = new RecordingCache();
        var operations = HostOperations.Create(
            HostOperation.CreateAsync("trace", async (args, _) =>
            {
                await Task.Yield();
                cts.Cancel();
                return args[0];
            }, "x"));

        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedObservedAsync(Program(F(TracedOnly, "[0].map{ n + Only }[0] + Only.V"), operations),
                zeroArgPropertyResultCache: cache, hostOperations: operations, cancellationToken: cts.Token));
        Assert.Equal(0, cache.PublishedCount);
        Assert.Equal(0, cache.ActiveOwnerCount);
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
            log.Add($"tock#{++ticks}");
            return new Result.Atom(ticks);
        }

        Result Trace(Result value)
        {
            log.Add($"trace({SixRouteAgreement.Neutral(value)})");
            return value;
        }

        return suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync("tock", async (_, _) => { await Task.Yield(); return Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return Trace(args[0]); }, "x"))
            : HostOperations.Create(
                HostOperation.Create("tock", (_, _) => Tick()),
                HostOperation.Create("trace", (args, _) => Trace(args[0]), "x"));
    }

    private static Expr Program(string source, HostOperations? operations = null)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations ?? Operations([], suspending: false) });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

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
