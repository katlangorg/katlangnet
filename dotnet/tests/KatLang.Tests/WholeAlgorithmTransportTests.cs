using KatLang.Evaluation;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// M4★ WHOLE-ALGORITHM TRANSPORT (ALIAS-UNIFY-1, October 2026): the discriminating regressions of the
/// selected contract. An unbraced <c>A = R</c> is a TRANSPARENT REFERENCE (every observation is R's:
/// structure, members, open provider, invocation, bare VALUE, publication origin); a braced
/// <c>A = { R }</c> is a STRUCTURAL FORWARDING CARRIER (its own structure and members; invocation
/// forwards the exact supply freshly to R's target; bare VALUE delegates to R's bare view). No alias owns
/// a zero-argument cache entry (OD-E). The source cases run on the generic, optimized and asynchronous
/// engines, which must agree on the outcome (the value, or the error's code), the host effects and the step
/// charge — except the root-property observation fact, which reads <see cref="KatLangEngine.Run(string, RunOptions?)"/>
/// alone, and the shared-tree runtime-target fact, which runs one parsed tree on the optimized evaluator; the
/// host-built R11 cases run the optimized evaluator (<see cref="Evaluator.RunCounted(Expr)"/>,
/// <c>RunCountedObserved</c>'s default). Lean: the guards of <c>KatLangArityLaws/WholeAlgorithmTransportGuards.lean</c>.
/// </summary>
public sealed class WholeAlgorithmTransportTests
{
    /// <summary>R1's holder, its reference, member alias and carrier, and the transport helpers.</summary>
    private const string Holder =
        "B = {\n" +
        "    public F(x) = x * x\n" +
        "    public Q = 99\n" +
        "    F\n" +
        "}\n" +
        "A = B\n" +
        "C = B.F\n" +
        "D = { B }\n" +
        "GetQ(f) = f.Q\n" +
        "Apply(f, x) = f(x)\n" +
        "Pick(f, f) = f.Q\n" +
        "Same(x, x) = 0\n";

    // ── R1 — whole algorithm versus output algorithm ──

    [Theory]
    [InlineData("B.Q", "ok 99")]
    [InlineData("GetQ(B)", "ok 99")]
    [InlineData("GetQ(A)", "ok 99")]
    [InlineData("A.Q", "ok 99")]
    [InlineData("Pick(B, B)", "ok 99")]
    [InlineData("Pick(A, B)", "ok 99")]
    [InlineData("Pick(B, A)", "ok 99")]
    public async Task R1_TransportAndMatching_ObserveTheWholeHolder_WithoutItsOutput(string row, string expected)
        => await AssertAllEngines(Holder + row, expected);

    [Theory]
    [InlineData("B(3)", "ok 9")]
    [InlineData("B.F(3)", "ok 9")]
    [InlineData("Apply(B, 3)", "ok 9")]
    [InlineData("A(3)", "ok 9")]
    [InlineData("C(3)", "ok 9")]
    [InlineData("D(3)", "ok 9")]
    [InlineData("Apply(D, 3)", "ok 9")]
    public async Task R1_Invocation_ForwardsTheExactSupply(string row, string expected)
        => await AssertAllEngines(Holder + row, expected);

    [Theory]
    [InlineData("B()")]
    [InlineData("A()")]
    [InlineData("D()")]
    public async Task R1_ZeroSupply_IsTheForwardedTargetsArityRejection(string row)
        => await AssertAllEngines(Holder + row, "err ArityMismatch");

    [Theory]
    // C denotes F (a member alias): it does not acquire B's Q; D is its own structure and inherits nothing.
    [InlineData("GetQ(C)")]
    [InlineData("GetQ(D)")]
    public async Task R1_MemberAliasesAndCarriers_DoNotInheritTheHoldersMembers(string row)
        => await AssertAllEngines(Holder + row, "err UnknownName");

    [Theory]
    [InlineData("Same(B, B.F)")]
    [InlineData("Same(B.F, B)")]
    [InlineData("Same(D, B)")]
    [InlineData("Same(B, D)")]
    [InlineData("Same(C, B)")]
    public async Task R1_DifferentStructures_AreDifferentIdentities_WithoutTheirOutputs(string row)
        => await AssertAllEngines(Holder + row, "err TypeMismatch");

    [Theory]
    [InlineData("Same(A, B)", "ok 0")]
    [InlineData("Same(B, A)", "ok 0")]
    [InlineData("Same(C, B.F)", "ok 0")]
    public async Task R1_AReference_IsItsTargetsIdentity(string row, string expected)
        => await AssertAllEngines(Holder + row, expected);

    // ── R2 — the M4★ boundary and member aliases ──

    private const string Boundary =
        "P = {\n" +
        "    public Q = 5\n" +
        "    6\n" +
        "}\n" +
        "Alias = P\n" +
        "Grouped = (P)\n" +
        "Forward = { P }\n" +
        "WithHelper = {\n" +
        "    public Helper = 0\n" +
        "    P\n" +
        "}\n" +
        "Nested = { { P } }\n" +
        "Box = {\n" +
        "    public C = {\n" +
        "        public Q = 7\n" +
        "        public D = {\n" +
        "            public Q = 70\n" +
        "            71\n" +
        "        }\n" +
        "        8\n" +
        "    }\n" +
        "    1 / 0\n" +
        "}\n" +
        "MemberAlias = Box.C\n" +
        "DeepAlias = Box.C.D\n" +
        "MemberCarrier = { Box.C }\n" +
        "Called = P()\n" +
        "Computed = P + 0\n" +
        "GetQ(f) = f.Q\n";

    [Theory]
    [InlineData("GetQ(Alias)", "ok 5")]
    [InlineData("Alias.Q", "ok 5")]
    [InlineData("GetQ(Grouped)", "ok 5")]
    [InlineData("GetQ(MemberAlias)", "ok 7")]
    [InlineData("MemberAlias.Q", "ok 7")]
    [InlineData("GetQ(DeepAlias)", "ok 70")]
    [InlineData("Box.C.Q", "ok 7")]
    [InlineData("WithHelper.Helper", "ok 0")]
    public async Task R2_References_ExposeTheirTargetsMembers_WithoutEvaluatingUnrelatedOutputs(string row, string expected)
        => await AssertAllEngines(Boundary + row, expected);

    [Theory]
    [InlineData("GetQ(Forward)")]
    [InlineData("GetQ(WithHelper)")]
    [InlineData("GetQ(MemberCarrier)")]
    [InlineData("GetQ({ P })")]
    [InlineData("GetQ(Nested)")]
    public async Task R2_Carriers_DoNotInheritTheTargetsMembers(string row)
        => await AssertAllEngines(Boundary + row, "err UnknownName");

    [Theory]
    // A deliberately supplied lexical fallback takes the miss route exactly as for any receiver.
    [InlineData("Q(x) = 100\nGetQ(Forward)", "ok 100")]
    [InlineData("Q(x) = 100\nGetQ(WithHelper)", "ok 100")]
    [InlineData("Q(x) = 100\nGetQ(Alias)", "ok 5")]
    public async Task R2_AMissingCarrierMember_KeepsTheOrdinaryFallbackRoute(string rows, string expected)
        => await AssertAllEngines(Boundary + rows, expected);

    [Theory]
    [InlineData("Forward()", "ok 6")]
    [InlineData("WithHelper()", "ok 6")]
    [InlineData("MemberCarrier()", "ok 8")]
    [InlineData("MemberAlias()", "ok 8")]
    [InlineData("Alias", "ok 6")]
    [InlineData("Forward", "ok 6")]
    // A block-literal row is no reference: Nested's value is its inner block's value, never flattened.
    [InlineData("Nested", "ok 6")]
    public async Task R2_Invocation_AndBareValues_Forward(string row, string expected)
        => await AssertAllEngines(Boundary + row, expected);

    [Theory]
    // Explicit calls and calculations are not references: their value is P's output, a number.
    [InlineData("GetQ(Called)")]
    [InlineData("GetQ(Computed)")]
    public async Task R2_CallsAndCalculations_AreNoAlgorithmReferences(string row)
        => await AssertAllEngines(Boundary + row, "err UnknownName");

    [Fact]
    public async Task R2_TheHelperDeclaration_KeepsABracedBodyACarrier()
    {
        // Same identity as a carrier of P? No: each braced body is its own structure.
        await AssertAllEngines(Boundary + "Same(x, x) = 0\nSame(Forward, P)", "err TypeMismatch");
        await AssertAllEngines(Boundary + "Same(x, x) = 0\nSame(WithHelper, P)", "err TypeMismatch");
        await AssertAllEngines(Boundary + "Same(x, x) = 0\nSame(Alias, P)", "ok 0");
    }

    // ── R3 — parameter-rooted classification and structural laziness ──

    [Theory]
    [InlineData("Box10 = { C(x) = x * 10 }\nUse(b) = { A = b.C\n A(3) }\nUse(Box10)", "ok 30")]
    // An unrelated lexical C is not needed for the member reference — and does not replace it.
    [InlineData("C(x) = x + 1\nBox10 = { C(x) = x * 10 }\nUse(b) = { A = b.C\n A(3) }\nUse(Box10)", "ok 30")]
    [InlineData("Box10 = { Inner = { C(x) = x * 10 } }\nUse(b) = { A = b.Inner.C\n A(3) }\nUse(Box10)", "ok 30")]
    // A runtime miss keeps the member-first / extension-fallback route: here the value view.
    [InlineData("C(x) = x + 1\nUse(b) = { A = b.C\n A }\nUse(5)", "ok 6")]
    [InlineData("Use(b) = { A = b.C\n A }\nUse(5)", "err UnknownName")]
    public async Task R3_AParameterRootedMemberPath_IsAMemberReference(string source, string expected)
        => await AssertAllEngines(source, expected);

    [Fact]
    public async Task R3_AnOwnMember_IsInspectedWithoutResolvingAFailingForwardingTarget()
    {
        const string source =
            "Boom = trace(1) / 0\n" +
            "B = {\n" +
            "    public Q = 99\n" +
            "    Boom\n" +
            "}\n" +
            "GetQ(f) = f.Q\n";
        await AssertAllEngines(source + "B.Q", "ok 99", traces: "");
        await AssertAllEngines(source + "GetQ(B)", "ok 99", traces: "");
        await AssertAllEngines(source + "B", "err DivisionByZero", traces: "1");
        await AssertAllEngines(source + "B()", "err DivisionByZero", traces: "1");
    }

    // ── R4 — reference and carrier VALUE / publication ──

    [Theory]
    [InlineData("A, P, A", "ok (1, 1, 1)")]
    [InlineData("A(), P", "ok (1, 1)")]
    [InlineData("P, B(), B", "ok (1, 2, 1)")]
    [InlineData("B(), B(), P()", "ok (1, 2, 3)")]
    public async Task R4_AReferenceAndACarrier_ReadAndPublishUnderTheTarget(string rows, string expected)
        => await AssertAllEngines("P = tock()\nA = P\nB = { P }\n" + rows, expected);

    [Fact]
    public async Task R4_TheOwnedHolder_DelegatesItsBareView()
        => await AssertAllEngines(
            "B = {\n    public P = tock()\n    public Q = 99\n    P\n}\nB.P, B(), B, B.P",
            "ok (1, 2, 1, 1)");

    [Theory]
    [InlineData("Only(*xs) = tock()\nA = Only\nA, Only, A", "ok (1, 1, 1)")]
    [InlineData("Only(*xs) = tock()\nA = Only\nA(), Only, A", "ok (1, 1, 1)")]
    [InlineData("P = tock()\nA = P\nB = A\nB, A, P", "ok (1, 1, 1)")]
    [InlineData("P = tock()\nA = P\nB = A\nB(), P", "ok (1, 1)")]
    public async Task R4_CollectorsAndTransitiveReferences_ShareTheTargetsEntry(string source, string expected)
        => await AssertAllEngines(source, expected);

    [Fact]
    public void R4_NoAliasOwnsARootPropertyObservation()
    {
        var result = KatLangEngine.Run("P = tick()\nA = P\nB = { P }\nA, B, P",
            new RunOptions { ObservePropertyValues = true });
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(["P"], success.PropertyObservations!.Select(static observation => observation.Name).ToArray());
    }

    // ── R9 — dynamic target lifetime and META ──

    private const string ComputedTarget =
        "Capture(meta op) = op\n" +
        "Z(y) = tock()\n" +
        "Mk(n) = if(trace(n) == n, Capture(Z(n)), 0)\n";

    [Fact]
    public async Task R9_AComputedTarget_IsEstablishedOncePerDeclaringActivation_AndCalledFreshly()
    {
        // The receiver `Mk(5)` runs ONCE for the alias's binding cell (one trace); every call is fresh.
        await AssertAllEngines(ComputedTarget + "A = Mk(5).Algorithm\nA(1), A(2), A(3)", "ok (1, 2, 3)", traces: "5");
        // A braced carrier of the computed reference resolves its target at ITS declaring activation too.
        await AssertAllEngines(ComputedTarget + "A = Mk(5).Algorithm\nB = { A }\nB(1), A(2), B(3)", "ok (1, 2, 3)", traces: "5");
        // Two outer activations: one binding cell each.
        await AssertAllEngines(
            ComputedTarget + "Outer(k) = {\n    A = Mk(k).Algorithm\n    A(1) + A(1) * 10\n}\nOuter(5), Outer(6)",
            "ok (21, 43)",
            traces: "5,6");
    }

    [Fact]
    public async Task R9_CapturesExposeTheWholeHolderOrTheSelectedMember()
    {
        const string source = Holder + "Capture(meta op) = op\nRB = Capture(B(3))\nRF = Capture(B.F(3))\nRA = Capture(A(3))\n";
        await AssertAllEngines(source + "GetQ(RB.Algorithm)", "ok 99");
        await AssertAllEngines(source + "GetQ(RA.Algorithm)", "ok 99");
        await AssertAllEngines(source + "GetQ(RF.Algorithm)", "err UnknownName");
        await AssertAllEngines(source + "RB.Invoke(), RB.Algorithm(4), RF.Algorithm(5)", "ok (9, 16, 25)");
        await AssertAllEngines(source + "Same(RB.Algorithm, RA.Algorithm)", "ok 0");
    }

    // ── R10 — open through references ──

    private const string Libraries =
        "Lib = {\n    public K = 99\n    public F(x) = x + 1\n}\n" +
        "Other = {\n    public K = 98\n}\n" +
        "Alias = Lib\n" +
        "Forward = {\n    public Own = 5\n    Lib\n}\n";

    [Theory]
    [InlineData("P = {\n    open Alias\n    K\n}\nP", "ok 99")]
    [InlineData("P = {\n    open Alias\n    F(1)\n}\nP", "ok 2")]
    [InlineData("P = {\n    open Alias, Lib\n    K\n}\nP", "ok 99")]
    [InlineData("P = {\n    open Forward\n    Own\n}\nP", "ok 5")]
    public async Task R10_OpenThroughAReference_OpensTheTarget(string rows, string expected)
        => await AssertAllEngines(Libraries + rows, expected);

    [Fact]
    public void R10_DistinctProvidersExportingOneName_StayAmbiguous()
    {
        var parsed = Parser.Parse(Libraries + "P = {\n    open Alias, Other\n    K\n}\nP");
        Assert.Contains(parsed.Diagnostics, static d => d.Code == DiagnosticCode.AmbiguousOpen);
    }

    [Fact]
    public async Task R10_ACarrier_DoesNotInheritItsTargetsProviderSurface()
    {
        // Forward opens only its OWN public member Own: K is no provided name, so the inferring body
        // takes it as P's own parameter (an inherited Lib.K would give P no parameter and K = 99).
        await AssertAllEngines(Libraries + "P = {\n    open Forward\n    K + Own\n}\nP(1)", "ok 6");
        var p = Assert.IsType<Algorithm.User>(Assert.Single(SourceProvenance.ParseValid(
            Libraries + "P = {\n    open Forward\n    K + Own\n}\nP(1)").Root.Properties, static p => p.Name == "P").Value);
        Assert.Equal(["K"], p.Params);
    }

    [Theory]
    // An unused reference cycle stays an ordinary lazy property; a demanded one terminates.
    [InlineData("A = B\nB = A\n1", "ok 1")]
    public async Task R10_ReferenceCycles_AreInertUntilDemanded(string source, string expected)
        => await AssertAllEngines(source, expected);

    // ── R11 — host-built trees and the elaboration boundary ──
    // (Host-object identity under ownerless parents: HostScopePropertyCacheTests and its Nested part.)

    private static readonly Property HostSquare = new(
        "F",
        new Algorithm.User(null, Algorithm.NormalParameters(["x"]), [], [], [new Expr.Binary(BinaryOp.Mul, new Expr.Param("x"), new Expr.Param("x"))]));

    private static readonly Property HostHolder = new(
        "H",
        new Algorithm.User(null, [], [], [new Property("Q", new Algorithm.User(null, [], [], [], [new Expr.Num(5)]), IsPublic: true)], [new Expr.Num(6)]));

    private static string RunHostBuilt(IEnumerable<Property> properties, Expr output)
        => Outcome(Evaluator.RunCounted(new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [.. properties], [output]))));

    [Fact]
    public void R11_ARawHostBuiltReferenceRow_KeepsItsWrittenArity_WhileElaborationMakesItAReference()
    {
        // Elaboration decides what a lone reference row means. A raw host-built User that never went
        // through it is an ordinary zero-parameter algorithm whose row reads F as a value, so the
        // supplied argument is its own arity rejection — it never silently acquires F's arity.
        var call = new Expr.Call(new Expr.Resolve("A"), [new Expr.Num(3)]);
        Assert.Equal("err ArityMismatch", RunHostBuilt([HostSquare, new Property("A", new Algorithm.User(null, [], [], [], [new Expr.Resolve("F")]))], call));

        // A host-built alias of either kind forwards the call, and the parsed source elaborates the same
        // row to the transparent reference.
        foreach (var isReference in new[] { true, false })
            Assert.Equal("ok 9", RunHostBuilt([HostSquare, new Property("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("F")) { IsReference = isReference })], call));
        var parsed = Assert.IsType<Algorithm.Alias>(Assert.Single(SourceProvenance.ParseValid("F(x) = x * x\nA = F\nA(3)").Root.Properties, static p => p.Name == "A").Value);
        Assert.True(parsed.IsReference);
    }

    [Fact]
    public void R11_HostBuiltReferencesAndCarriers_KeepTheirOwnStructures()
    {
        var read = new Expr.DotCall(new Expr.Resolve("A"), "Q", null);
        // A host-built reference IS its target's structure: A.Q is the holder's member.
        Assert.Equal("ok 5", RunHostBuilt([HostHolder, new Property("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("H")))], read));
        // A host-built carrier's members are its own declarations only.
        var ownQ = new Property("Q", new Algorithm.User(null, [], [], [], [new Expr.Num(99)]), IsPublic: true);
        Assert.Equal("ok 99", RunHostBuilt([HostHolder, new Property("A", new Algorithm.Alias(null, [], [ownQ], new Expr.Resolve("H")) { IsReference = false })], read));
        // A carrier without the member never inherits it from its target: the read is a structural miss
        // whose lexical fallback names nothing.
        Assert.Equal("err UnknownName", RunHostBuilt([HostHolder, new Property("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("H")) { IsReference = false })], read));
    }

    [Fact]
    public void R11_ASharedHostBuiltTree_KeepsNoStateAcrossRuns()
    {
        // One host-built tree evaluated twice over ONE tock counter: each run reads its own target entry —
        // one tock per run, the reference sharing it — never the previous run's (a leaked entry would make
        // the second run (1, 1, 1) with no tock).
        var tree = new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [],
            [new Property("P", new Algorithm.User(null, [], [], [], [new Expr.Call(new Expr.Resolve("tock"), [])])),
                new Property("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("P")))],
            [new Expr.Resolve("A"), new Expr.Resolve("P"), new Expr.Resolve("A")]));
        var probe = new Probe();
        var operations = probe.Operations(asynchronous: false);
        foreach (var expected in new[] { "ok (1, 1, 1)", "ok (2, 2, 2)" })
        {
            var (result, _) = Evaluator.RunCountedObserved(tree, limits: null, hostOperations: operations);
            Assert.Equal(expected, Outcome(result));
        }
    }

    [Fact]
    public void R11_ASharedTreesRuntimeTarget_IsEstablishedAfreshInEveryRun()
    {
        // A runtime-target alias's ONE binding cell belongs to its run: the second run of the same tree
        // establishes its target again, and its bare read is that run's own entry of the target (a leaked
        // cell or entry would read the first run's 1).
        var probe = new Probe();
        var operations = probe.Operations(asynchronous: false);
        var parsed = Parser.Parse(
            "Capture(meta c) = c\nZ = tock()\nR = Capture(Z())\nA = R.Algorithm\nA(), A, A()",
            new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
        var tree = new Expr.AlgorithmExpr(parsed.Root);
        foreach (var expected in new[] { "ok (1, 1, 2)", "ok (3, 3, 4)" })
        {
            var (result, _) = Evaluator.RunCountedObserved(tree, limits: null, hostOperations: operations);
            Assert.Equal(expected, Outcome(result));
        }
    }

    // ── Harness ──

    private sealed record Observation(string Outcome, string Traces, long Steps);

    private sealed class Probe
    {
        private readonly List<string> _traces = [];
        private int _ticks;

        public HostOperations Operations(bool asynchronous) => HostOperations.Create(
            HostOperation.Create("trace", (args, _) => { lock (_traces) _traces.Add(Format(args[0])); return args[0]; }, "x"),
            asynchronous
                ? HostOperation.CreateAsync("tock", async (_, _) => { await Task.Yield(); return new Result.Atom(Interlocked.Increment(ref _ticks)); })
                : HostOperation.Create("tock", (_, _) => new Result.Atom(Interlocked.Increment(ref _ticks))));

        public Observation Observe(string outcome, long steps) => new(outcome, string.Join(",", _traces), steps);
    }

    private static string Format(Result value) => value switch
    {
        Result.Atom a => a.Value.ToString(),
        Result.Str s => "'" + s.Value + "'",
        Result.Bool b => b.Value ? "true" : "false",
        Result.SequenceValue q => "(" + string.Join(", ", q.Items.Select(Format)) + ")",
        Result.ListValue l => "[" + string.Join(", ", l.Items.Select(Format)) + "]",
        _ => value.ToString(),
    };

    private static string Outcome(EvalResult<Evaluator.CountedResult> result)
        => result.IsOk ? "ok " + Format(result.Value.Value) : "err " + result.Error.Code;

    private static Observation RunSync(string source, bool optimized)
    {
        var probe = new Probe();
        var operations = probe.Operations(asynchronous: false);
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
        var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), limits: null,
            enableOptimizations: optimized, loopDiagnostics: new LoopOptimizationDiagnostics(), hostOperations: operations);
        return probe.Observe(Outcome(result), budget.ConsumedSteps);
    }

    private static async Task<Observation> RunAsync(string source)
    {
        var probe = new Probe();
        var operations = probe.Operations(asynchronous: true);
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
        var (result, budget) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), limits: null,
            hostOperations: operations);
        return probe.Observe(Outcome(result), budget.ConsumedSteps);
    }

    private static async Task AssertAllEngines(string source, string expected, string? traces = null)
    {
        var generic = RunSync(source, optimized: false);
        var optimized = RunSync(source, optimized: true);
        var asynchronous = await RunAsync(source);
        Assert.Equal(expected, generic.Outcome);
        if (traces is not null)
            Assert.Equal(traces, generic.Traces);
        Assert.Equal(generic, optimized);
        Assert.Equal(generic, asynchronous);
    }
}
