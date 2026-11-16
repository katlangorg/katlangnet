using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// ALIAS-CELL-LIFETIME (owner decision 2026-11-15: PROPERTY LIFETIME; adversarial audit of 2026-11-14,
/// finding §1.7 and SPECS §9/§10): a runtime-target alias's BINDING CELL lives exactly as long as the
/// zero-argument property cache entry of the same row written as a property would.
/// <list type="bullet">
///   <item>An alias whose own property is EXPORTED (its row uses no enclosing input) has ONE cell per
///   declaration and structural declaring scope per RUN: explicit calls of its owner, reads of its owner
///   and reads from outside share it.</item>
///   <item>A LOCAL-ONLY alias has one cell per declaring BINDING IDENTITY: property-style reads inherit
///   their declaring activation's identity and share the cell, every explicit call mints a fresh
///   identity and gets a fresh cell (CACHE-OWNER-D1).</item>
///   <item>A parameter row stays the parameter's own cell.</item>
/// </list>
/// Formerly the cell was keyed by the nearest ACTIVATION of the declaring chain, so a property-style
/// read (which mints an activation that only inherits the binding identity) established a second cell
/// in one declaring activation, and an unrelated local-only sibling — which decides whether a
/// parameterless owner gets an activation at all — changed how explicit calls shared the cell.
/// <para>THE ORACLE: every alias program gives exactly what its PROPERTY TWIN gives — the same row
/// written as an ordinary property (<c>A = Pick(tick()).Algorithm</c> / <c>A(1)</c> becomes
/// <c>P = Pick(tick())</c> / <c>P.Algorithm(1)</c>; a value-only <c>A = b.G</c> / <c>A</c> becomes
/// <c>P = b.G + 0</c> / <c>P</c>). The one deliberate exception is re-entrancy (<c>r1</c>): a binding
/// cell is a need cell, so re-entering its own demand is <c>DemandCycle</c>, where a property's
/// re-entrant read (Q-37) evaluates again; that difference is out of scope and unchanged.</para>
/// <para>Every program runs on the six established routes (<see cref="SixRouteAgreement"/>: the sync
/// and async engines, the suspending async twin, the generic and the optimized evaluator, the forced
/// twin), which must agree on value, errors and the exact host-call log, and on the ORDINARY and the
/// PLANNED invocation route (<see cref="InvocationPlanTestSeam"/>). <see cref="Row.Was"/> records the
/// outcome before the change wherever it differs.</para>
/// </summary>
public sealed class RuntimeAliasCellLifetimeTests(ITestOutputHelper output)
{
    // (10, 10) means one cell and (10, 100) two: the cell's receiver `Pick(tick())` selects by the tick.
    private const string Pick = "Cap(meta r) = r\nTen(x) = x * 10\nHun(x) = x * 100\nPick(n) = if(n == 1, Cap(Ten(0)), Cap(Hun(0)))\n";

    // One `trace(1)` per established cell.
    private const string Pk = "W(x) = x\nCap(meta r) = r\nPk(t) = if(t > 0, Cap(W(0)), Cap(W(0)))\n";

    private const string TraceG = "G(x) = trace(x)\n";
    private const string TickG = "G(x) = tick() + x * 0\n";

    /// <summary>
    /// One row of the decided table: the alias program, its property twin (null where the row has no
    /// property spelling), the expected outcome (<c>err Code</c> for a failure) and host-call log, and
    /// the outcome before ALIAS-CELL-LIFETIME where it changed.
    /// </summary>
    public sealed record Row(string Id, string Alias, string? Twin, string Expected, string[] HostCalls, string? Was = null)
    {
        public override string ToString() => Id;
    }

    private static string[] Traces(params int[] values) => [.. values.Select(static value => $"trace({value})")];

    private static readonly Row[] Table =
    [
        // A property-style read of B after the structural B.A: one declaring activation, one cell.
        new("p6d",
            TraceG + "F(b) = { B = { public A = b.G\nA + 0 }\nB.A, B }\nF(5)",
            TraceG + "F(b) = { B = { public P = b.G + 0\nP + 0 }\nB.P, B }\nF(5)",
            "S[5, 5]", Traces(5), Was: "S[5, 5] with trace [5, 5]"),
        new("spec1",
            TickG + "F(b) = { B = { public A = b.G\nA + 0 }\nB.A, B }\nF(5)",
            TickG + "F(b) = { B = { public P = b.G + 0\nP + 0 }\nB.P, B }\nF(5)",
            "S[1, 1]", [], Was: "S[1, 2]"),
        new("spec2",
            TickG + "F(b) = { B1 = { B2 = { public A = b.G\nA + 0 }\nB2.A + B2 * 10 }\nB1.B2.A, B1 }\nF(5)",
            TickG + "F(b) = { B1 = { B2 = { public P = b.G + 0\nP + 0 }\nB2.P + B2 * 10 }\nB1.B2.P, B1 }\nF(5)",
            "S[1, 11]", [], Was: "S[1, 32]"),
        // Reads share the declaring identity's cell; the explicit B() mints a fresh identity and cell.
        new("spec3",
            TickG + "F(b) = { B = { public A = b.G\nA + 0 }\nB, B, B.A, B.A, B(), B.A }\nF(5)",
            TickG + "F(b) = { B = { public P = b.G + 0\nP + 0 }\nB, B, B.P, B.P, B(), B.P }\nF(5)",
            "S[1, 1, 1, 1, 2, 1]", [], Was: "S[1, 1, 2, 2, 3, 2]"),
        new("open",
            TraceG + "F(b) = { B = { public A = b.G\nA + 0 }\nC = { open B\nA + 0 }\nB, C }\nF(5)",
            TraceG + "F(b) = { B = { public P = b.G + 0\nP + 0 }\nC = { open B\nP + 0 }\nB, C }\nF(5)",
            "S[5, 5]", Traces(5), Was: "S[5, 5] with trace [5, 5]"),
        // An EXPORTED alias: one cell per run, whatever calls or reads its owner.
        new("e2",
            Pick + "F(k) = { Outer = { A = Pick(tick()).Algorithm\nA(1) }\nOuter(), Outer() }\nF(0)",
            Pick + "F(k) = { Outer = { P = Pick(tick())\nP.Algorithm(1) }\nOuter(), Outer() }\nF(0)",
            "S[10, 10]", []),
        // e2 with an unused local-only sibling, which formerly gave Outer an activation per call.
        new("e3",
            Pick + "F(k) = { Outer = { U = k + 0\nA = Pick(tick()).Algorithm\nA(1) }\nOuter(), Outer() }\nF(0)",
            Pick + "F(k) = { Outer = { U = k + 0\nP = Pick(tick())\nP.Algorithm(1) }\nOuter(), Outer() }\nF(0)",
            "S[10, 10]", [], Was: "S[10, 100]"),
        new("e4",
            Pick + "Outer(k) = { A = Pick(tick()).Algorithm\nA(1) }\nOuter(0), Outer(0)",
            Pick + "Outer(k) = { P = Pick(tick())\nP.Algorithm(1) }\nOuter(0), Outer(0)",
            "S[10, 10]", [], Was: "S[10, 100]"),
        // Read from outside after a call.
        new("esc",
            Pick + "Outer(k) = { public A = Pick(tick()).Algorithm\nA(1) }\nOuter(0), Outer.A(1)",
            Pick + "Outer(k) = { public P = Pick(tick())\nP.Algorithm(1) }\nOuter(0), Outer.P.Algorithm(1)",
            "S[10, 10]", [], Was: "S[10, 100]"),
        new("p5d",
            Pick + "F(k) = { B = { U = k + 0\npublic A = Pick(tick()).Algorithm\nA(1) + 0 }\nB.A(1), B }\nF(0)",
            Pick + "F(k) = { B = { U = k + 0\npublic P = Pick(tick())\nP.Algorithm(1) + 0 }\nB.P.Algorithm(1), B }\nF(0)",
            "S[10, 10]", [], Was: "S[10, 100]"),
        // A LOCAL-ONLY row: every explicit call of the owner is a fresh binding identity.
        new("e7",
            Pick + "F(k) = { Outer = { A = Pick(tick() + k).Algorithm\nA(1) }\nOuter(), Outer() }\nF(0)",
            Pick + "F(k) = { Outer = { P = Pick(tick() + k)\nP.Algorithm(1) }\nOuter(), Outer() }\nF(0)",
            "S[10, 100]", []),
        // Reads, no calls.
        new("e9",
            Pick + "F(k) = { Outer = { A = Pick(tick()).Algorithm\nA(1) }\nOuter, Outer }\nF(0)",
            Pick + "F(k) = { Outer = { P = Pick(tick())\nP.Algorithm(1) }\nOuter, Outer }\nF(0)",
            "S[10, 10]", []),
        // The alias one level deeper: the call route and the structural route share the cell.
        new("s0",
            Pk + "F(k) = { Outer = { C = { A = Pk(trace(1)).Algorithm\nA(7) + 0 }\nC + 0 }\nOuter(), Outer.C.A(7) }\nF(0)",
            Pk + "F(k) = { Outer = { C = { P = Pk(trace(1))\nP.Algorithm(7) + 0 }\nC + 0 }\nOuter(), Outer.C.P.Algorithm(7) }\nF(0)",
            "S[7, 7]", Traces(1)),
        new("s1",
            Pk + "F(k) = { Outer = { U = k + 0\nC = { A = Pk(trace(1)).Algorithm\nA(7) + 0 }\nC + 0 }\nOuter(), Outer.C.A(7) }\nF(0)",
            Pk + "F(k) = { Outer = { U = k + 0\nC = { P = Pk(trace(1))\nP.Algorithm(7) + 0 }\nC + 0 }\nOuter(), Outer.C.P.Algorithm(7) }\nF(0)",
            "S[7, 7]", Traces(1), Was: "S[7, 7] with trace [1, 1]"),
        // A collecting-only owner read (COLLECT-CACHE-1) and its member read from outside.
        new("d1",
            Pk + "Only(*xs) = { public A = Pk(trace(1)).Algorithm\nA(7) + 0 }\nOnly, Only.A(7)",
            Pk + "Only(*xs) = { public P = Pk(trace(1))\nP.Algorithm(7) + 0 }\nOnly, Only.P.Algorithm(7)",
            "S[7, 7]", Traces(1), Was: "S[7, 7] with trace [1, 1]"),
        // A local-only alias per loop step: a fresh cell per iteration on every loop route.
        new("x3",
            "G(x) = x * 10\nStep(x) = { A = x.G\nA + 1 }\nStep(0).repeat(3)",
            "G(x) = x * 10\nStep(x) = { P = x.G + 0\nP + 1 }\nStep(0).repeat(3)",
            "111", []),
        new("x4",
            "G(x) = x * 10\nStep(x) = { A = x.G\nB = A + 0\nB + 1 }\nStep(0).repeat(3)",
            "G(x) = x * 10\nStep(x) = { P = x.G + 0\nB = P + 0\nB + 1 }\nStep(0).repeat(3)",
            "111", []),
        // The structural spelling of the re-entrant read: the cell's own demand, re-entered.
        new("r2",
            "F(b) = { B = { public A = b.G\nA + 0 }\nG(x) = if(tick() < 3, B.A + 1, x)\nB }\nF(5)",
            null,
            "err DemandCycle", []),
        // A parameter row is the parameter's own cell.
        new("par",
            "Use(f, x) = { A = f\nA(x) }\nInc(v) = v + 1\nUse(Inc, 1), Use(Inc, 2)",
            null,
            "S[2, 3]", []),
    ];

    public static TheoryData<Row> Rows => new(Table);

    private sealed record Outcome(string Value, IReadOnlyList<string> HostCalls)
    {
        public override string ToString() => $"{Value} host=[{string.Join(",", HostCalls)}]";
    }

    // The outcome of a program all six routes agree on, on the ordinary and the planned invocation route.
    private static async Task<Outcome> OnEveryRouteAsync(string source)
    {
        var ordinary = Describe(await SixRouteAgreement.OnEveryRouteAsync(source));
        Outcome planned;
        using (InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()))
            planned = Describe(await SixRouteAgreement.OnEveryRouteAsync(source));
        Assert.Equal(ordinary.Value, planned.Value);
        Assert.Equal(ordinary.HostCalls, planned.HostCalls);
        return ordinary;
    }

    private static Outcome Describe(SixRouteAgreement.Observation observation) => new(
        observation.Kind == "ok"
            ? observation.Value!
            : $"{observation.Kind} {string.Join(" | ", observation.Errors.Select(static error => error[..error.IndexOf(':')]))}",
        observation.HostCalls);

    [Theory]
    [MemberData(nameof(Rows))]
    public async Task AnAliasProgram_GivesItsPropertyTwinsOutcome_OnEveryRoute(Row row)
    {
        var alias = await OnEveryRouteAsync(row.Alias);
        output.WriteLine($"{row.Id}: alias {alias}{(row.Was is null ? "" : $" (was {row.Was})")}");
        Assert.Equal(row.Expected, alias.Value);
        Assert.Equal(row.HostCalls, alias.HostCalls);

        if (row.Twin is null)
            return;

        // THE ORACLE: the same row written as an ordinary property.
        var twin = await OnEveryRouteAsync(row.Twin);
        output.WriteLine($"{row.Id}: twin  {twin}");
        Assert.Equal(twin.Value, alias.Value);
        Assert.Equal(twin.HostCalls, alias.HostCalls);
    }

    /// <summary>
    /// THE ONE DELIBERATE EXCEPTION to the oracle (out of scope, unchanged): a binding cell is a need
    /// cell. The read of <c>B</c> re-entered through <c>G</c> reaches <c>A</c>'s cell again — the SAME
    /// cell now, since a read shares its declaring identity's cell — while that cell is being demanded:
    /// <c>DemandCycle</c>, the outcome the structural spelling <c>B.A</c> (<c>r2</c>) always had. The
    /// property twin keeps Q-37's re-entrant read. Formerly each re-entrant read of <c>B</c> minted an
    /// activation and with it a fresh cell, and the program gave 7.
    /// </summary>
    [Fact]
    public async Task R1_AReentrantReadOfTheCell_IsADemandCycle_WhereThePropertyTwinReentersQ37()
    {
        const string alias = "F(b) = { B = { public A = b.G\nA + 0 }\nG(x) = if(tick() < 3, B + 1, x)\nB }\nF(5)";
        const string twin = "F(b) = { B = { public P = b.G + 0\nP + 0 }\nG(x) = if(tick() < 3, B + 1, x)\nB }\nF(5)";

        Assert.Equal("err DemandCycle", (await OnEveryRouteAsync(alias)).Value);
        Assert.Equal("7", (await OnEveryRouteAsync(twin)).Value);
    }

    /// <summary>
    /// SPECS §9 as a metamorphic law: an unused local-only sibling <c>U</c> — at the alias's own level
    /// or at any enclosing level — never changes the value or the effect trace of a program with a
    /// runtime alias. (It decides whether a parameterless owner's explicit call records an activation,
    /// which no longer keys anything of the alias.)
    /// </summary>
    [Theory]
    [InlineData("e2/e3",
        Pick + "F(k) = { Outer = { A = Pick(tick()).Algorithm\nA(1) }\nOuter(), Outer() }\nF(0)",
        Pick + "F(k) = { Outer = { U = k + 0\nA = Pick(tick()).Algorithm\nA(1) }\nOuter(), Outer() }\nF(0)")]
    [InlineData("s0/s1",
        Pk + "F(k) = { Outer = { C = { A = Pk(trace(1)).Algorithm\nA(7) + 0 }\nC + 0 }\nOuter(), Outer.C.A(7) }\nF(0)",
        Pk + "F(k) = { Outer = { U = k + 0\nC = { A = Pk(trace(1)).Algorithm\nA(7) + 0 }\nC + 0 }\nOuter(), Outer.C.A(7) }\nF(0)")]
    [InlineData("sibling beside the alias (deep)",
        Pk + "F(k) = { Outer = { C = { A = Pk(trace(1)).Algorithm\nA(7) + 0 }\nC + 0 }\nOuter(), Outer.C.A(7) }\nF(0)",
        Pk + "F(k) = { Outer = { C = { U = k + 0\nA = Pk(trace(1)).Algorithm\nA(7) + 0 }\nC + 0 }\nOuter(), Outer.C.A(7) }\nF(0)")]
    [InlineData("local-only alias, sibling beside it",
        TickG + "F(b) = { B = { public A = b.G\nA + 0 }\nB, B, B.A, B.A, B(), B.A }\nF(5)",
        TickG + "F(b) = { B = { U = b + 0\npublic A = b.G\nA + 0 }\nB, B, B.A, B.A, B(), B.A }\nF(5)")]
    [InlineData("local-only alias, explicit calls",
        Pick + "F(k) = { Outer = { A = Pick(tick() + k).Algorithm\nA(1) }\nOuter(), Outer() }\nF(0)",
        Pick + "F(k) = { Outer = { U = k + 0\nA = Pick(tick() + k).Algorithm\nA(1) }\nOuter(), Outer() }\nF(0)")]
    public async Task AnUnusedLocalOnlySibling_NeverChangesTheOutcome(string id, string plain, string withSibling)
    {
        var expected = await OnEveryRouteAsync(plain);
        var actual = await OnEveryRouteAsync(withSibling);
        output.WriteLine($"{id}: {expected}");
        Assert.Equal(expected.Value, actual.Value);
        Assert.Equal(expected.HostCalls, actual.HostCalls);
    }

    /// <summary>
    /// An exported alias's cell is shared by every route to it in one run — a call of its owner, a read
    /// of its owner, a callback, a helper and a path from outside — and establishes its receiver once.
    /// </summary>
    [Fact]
    public async Task AnExportedAlias_IsEstablishedOncePerRun_ByEveryConsumer()
    {
        const string source = Pk
            + "Outer(k) = { public A = Pk(trace(1)).Algorithm\nA(k) }\n"
            + "Help(v) = Outer(v) + Outer.A(v)\n"
            + "Outer(1), [2, 3].map(Outer), Help(4), Outer.A(5), [6].map{ Outer.A(n) }";
        var outcome = await OnEveryRouteAsync(source);
        Assert.Equal("S[1, L[2, 3], 8, 5, L[6]]", outcome.Value);
        Assert.Equal(Traces(1), outcome.HostCalls);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(40)]
    public async Task SharedPropertyLists_DoNotMergeDistinctDeclaringOwners(int unusedProperties)
    {
        static Expr Program(string source)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            var first = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "First").Value);
            var second = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "Second").Value);
            second = second with { Properties = first.Properties };
            root = root with { Properties = root.Properties.Select(p => p.Name == "Second" ? p with { Value = second } : p).ToArray() };
            return new Expr.AlgorithmExpr(root);
        }

        var padding = string.Join("\n", Enumerable.Range(0, unusedProperties).Select(i => $"Unused{i} = {i}")) + "\n";
        var alias = Program(Pick + "First(k) = { " + padding + "public A = Pick(tick()).Algorithm\nA(1) }\n"
            + "Second(k) = { public A = Pick(tick()).Algorithm\nA(1) }\nFirst(0), Second(0)");
        var twin = Program(Pick + "First(k) = { " + padding + "public P = Pick(tick())\nP.Algorithm(1) }\n"
            + "Second(k) = { public P = Pick(tick())\nP.Algorithm(1) }\nFirst(0), Second(0)");
        foreach (var optimize in new[] { false, true })
        {
            var property = Evaluator.RunCountedObserved(twin, enableOptimizations: optimize).Result;
            Assert.True(property.IsOk, property.IsError ? property.Error.ToString() : "");
            Assert.Equal("S[10, 100]", SixRouteAgreement.Neutral(property.Value.Value));
            var reference = Evaluator.RunCountedObserved(alias, enableOptimizations: optimize).Result;
            Assert.True(reference.IsOk, reference.IsError ? reference.Error.ToString() : "");
            Assert.Equal(SixRouteAgreement.Neutral(property.Value.Value), SixRouteAgreement.Neutral(reference.Value.Value));
        }

        var asynchronous = await Evaluator.RunCountedObservedAsync(
            alias, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.True(asynchronous.Result.IsOk, asynchronous.Result.IsError ? asynchronous.Result.Error.ToString() : "");
        Assert.Equal("S[10, 100]", SixRouteAgreement.Neutral(asynchronous.Result.Value.Value));
    }

    /// <summary>
    /// A local-only alias is one cell per declaring binding identity: each call of <c>F</c> has its own,
    /// and inside one call a callback, a helper, a structural path and an opened name share it.
    /// </summary>
    [Fact]
    public async Task ALocalOnlyAlias_IsEstablishedOncePerDeclaringCall_ByEveryConsumer()
    {
        const string source = TraceG
            + "F(b) = { B = { public A = b.G\nA + 0 }\nC = { open B\nA + 0 }\nHelp(v) = v * 0 + B\n"
            + "[0].map{ n + B }[0] + B.A + Help(1) + C + B }\n"
            + "F(5), F(7)";
        var outcome = await OnEveryRouteAsync(source);
        Assert.Equal("S[25, 35]", outcome.Value);
        Assert.Equal(Traces(5, 7), outcome.HostCalls);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void X3X4_LocalCellsAreFresh_WhenTheLoopActuallyUsesItsPlan(bool throughProperty, bool plannedInvocation)
    {
        using var plans = plannedInvocation ? InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()) : null;
        var source = "G(x) = x * 10\nStep(x) = { A = x.G\n"
            + (throughProperty ? "B = A + 0\nB + 1" : "A + 1")
            + " }\nStep(0).repeat(3)";
        var parsed = SourceProvenance.ParseValid(source);
        var diagnostics = new LoopOptimizationDiagnostics();
        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: true, loopDiagnostics: diagnostics);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal("111", SixRouteAgreement.Neutral(result.Value.Value));
        var loops = diagnostics.GetSnapshot();
        Assert.Equal(1, loops.OptimizedLoopHits);
        Assert.Equal(0, loops.OptimizedLoopFallbacks);
        Assert.Equal(3, loops.LoopIterations);
        Assert.Equal(3, budget.AliasBindingCells.AddedCount);
    }

    [Fact]
    public void APropertylessAlias_KeepsItsExistingStructuralWiringIdentity()
    {
        var ctx = Evaluator.EvalCtx.Empty;
        var alias = new Algorithm.Alias(null, [], [], new Expr.DotCall(new Expr.Resolve("R"), "Algorithm"));
        var firstOwner = new Algorithm.User(null, [], [], [], OutputBundle.Empty);
        var secondOwner = new Algorithm.User(null, [], [], [], OutputBundle.Empty);
        Assert.NotSame(firstOwner.Declaration, secondOwner.Declaration);
        var first = new ScopeCtx(null, [], []) { Owner = firstOwner };
        var second = new ScopeCtx(null, [], []) { Owner = secondOwner };
        // Neither scope declares this alias as a property. There is no property owner to distinguish;
        // preserve the existing inline-literal policy (CoreTests.HostScopeIdentity.literalPair).
        Assert.Same(Evaluator.AliasBindingCell(alias with { Parent = first }, ctx),
            Evaluator.AliasBindingCell(alias with { Parent = second }, ctx));
        Assert.Equal(1, ctx.Budget.AliasBindingCells.AddedCount);
    }

    // ── Storage follows lifetime ────────────────────────────────────────────────────────

    private const int Calls = 20_000;
    private const int MaxLivePartitions = 64;

    /// <summary>
    /// A local-only alias declared per activation in a long loop: every finished iteration's cell is in
    /// the partition of that iteration's binding identity and dies with it, while the run's store still
    /// counts every establishment. (A cell kept in a run-wide dictionary would stay for the run.)
    /// </summary>
    [Theory]
    // An `.Algorithm` row over the step's parameter: called through.
    [InlineData("Cap(meta r) = r\nInc(v) = v + 1\nMk(n) = Cap(Inc(n))\nStep(x) = { A = Mk(x).Algorithm\nA(x) }\nStep(0).repeat(20000)", false)]
    [InlineData("Cap(meta r) = r\nInc(v) = v + 1\nMk(n) = Cap(Inc(n))\nStep(x) = { A = Mk(x).Algorithm\nA(x) }\nStep(0).repeat(20000)", true)]
    // A parameter-rooted member path: a value-only reference, read bare.
    [InlineData("G(v) = v + 1\nStep(x) = { A = x.G\nA + 0 }\nStep(0).repeat(20000)", false)]
    [InlineData("G(v) = v + 1\nStep(x) = { A = x.G\nA + 0 }\nStep(0).repeat(20000)", true)]
    public void ALocalOnlyAliasPerLoopStep_DoesNotRetainFinishedStepsCells(string source, bool enableOptimizations)
    {
        var (value, budget) = Run(source, enableOptimizations);
        ForceFullCollection();
        var live = budget.AliasBindingCells.LivePartitionCount();
        output.WriteLine($"optimizations {enableOptimizations}: cells {budget.AliasBindingCells.AddedCount}, live partitions {live}");
        Assert.Equal("20000", value);
        Assert.Equal(Calls, budget.AliasBindingCells.AddedCount);
        Assert.Empty(budget.AliasBindingCells.RunWideValues);
        Assert.InRange(live, 0, MaxLivePartitions);
        GC.KeepAlive(budget);
    }

    /// <summary>A parameter row records no cell at all: it is the parameter's own.</summary>
    [Fact]
    public void AParameterRowPerLoopStep_RecordsNoCell()
    {
        var (value, budget) = Run(
            "Inc(v) = v + 1\nUse(f, x) = { A = f\nA(x) }\nStep(x) = Use(Inc, x)\nStep(0).repeat(20000)", enableOptimizations: true);
        Assert.Equal("20000", value);
        Assert.Equal(0, budget.AliasBindingCells.AddedCount);
    }

    /// <summary>An exported alias in a long loop is ONE run-wide cell, however many steps call its owner.</summary>
    [Fact]
    public void AnExportedAliasPerLoopStep_IsOneRunWideCell()
    {
        var (value, budget) = Run(
            "Cap(meta r) = r\nInc(v) = v + 1\nStep(x) = { A = Cap(Inc(0)).Algorithm\nA(x) }\nStep(0).repeat(20000)", enableOptimizations: true);
        ForceFullCollection();
        Assert.Equal("20000", value);
        Assert.Equal(1, budget.AliasBindingCells.AddedCount);
        Assert.Single(budget.AliasBindingCells.RunWideValues);
        Assert.Equal(0, budget.AliasBindingCells.LivePartitionCount());
        GC.KeepAlive(budget);
    }

    /// <summary>
    /// The cell of a dead binding identity is collected while the run's store is alive, and the cell of
    /// a live identity is kept: a partition is held weakly by the identity OBJECT.
    /// </summary>
    [Fact]
    public void TheCellOfADeadBindingIdentity_IsCollected_WhileALiveIdentityKeepsItsCell()
    {
        var ctx = Evaluator.EvalCtx.Empty;
        var alias = new Algorithm.Alias(null, [], [], new Expr.DotCall(new Expr.Resolve("R"), "Algorithm"));
        var kept = Activated(ctx);
        var keptCell = Evaluator.AliasBindingCell(alias with { Parent = kept }, ctx);
        var (deadCell, deadIdentity) = EstablishUnderAFreshIdentity(alias, ctx);

        ForceFullCollection();

        Assert.False(deadIdentity.IsAlive);
        Assert.False(deadCell.IsAlive);
        Assert.Equal(2, ctx.Budget.AliasBindingCells.AddedCount);
        Assert.Equal(1, ctx.Budget.AliasBindingCells.LivePartitionCount());
        Assert.Same(keptCell, Evaluator.AliasBindingCell(alias with { Parent = kept }, ctx));
        GC.KeepAlive(kept);
        GC.KeepAlive(ctx.Budget);
    }

    /// <summary>
    /// The store's PROMPT-RECLAIM partition table (the alias cells' form of
    /// <see cref="BindingContextPartitionTable"/>): the same weak association as the property cache's
    /// table — an entry lives while its identity is reachable, although the entry's key refers back to
    /// the identity — but dead entries are freed in place when the table fills, so the table stays as
    /// small as the identities alive between collections instead of waiting for finalizers.
    /// </summary>
    [Fact]
    public void ThePromptReclaimTable_KeepsLiveIdentities_AndFreesDeadOnesInPlace()
    {
        var map = new PartitionedMap<ZeroArgPropertyCacheKey, int>(
            ZeroArgPropertyCacheKeyComparer.Instance, BindingContextPartitions.OfPropertyKey, promptReclaim: true);
        var owner = new object();
        var binding = new object();
        var run = new object();
        var kept = Enumerable.Range(0, 5).Select(static _ => new object()).ToArray();
        for (var index = 0; index < kept.Length; index++)
            Assert.True(map.TryAdd(Key(owner, binding, kept[index], run), index));
        Assert.True(map.TryAdd(Key(owner, binding, ZeroArgPropertyCacheKey.RunWideEnvironmentIdentity, run), -1));

        const int rounds = 50;
        const int perRound = 1_000;
        for (var round = 0; round < rounds; round++)
        {
            AddUnderFreshIdentities(map, owner, binding, run, perRound);
            ForceFullCollection();
        }

        // Every addition counted; only the kept identities' partitions are alive, and the table never
        // grew to hold the dead ones (50,000 identities passed through a table of a few thousand).
        Assert.Equal(kept.Length + 1 + rounds * perRound, map.AddedCount);
        Assert.Equal(kept.Length, map.LivePartitionCount());
        Assert.InRange(map.PromptTableCapacity, 8, 4 * perRound);
        for (var index = 0; index < kept.Length; index++)
        {
            Assert.True(map.TryGetValue(Key(owner, binding, kept[index], run), out var stored));
            Assert.Equal(index, stored);
            Assert.False(map.TryAdd(Key(owner, binding, kept[index], run), 99));
        }

        Assert.True(map.TryGetValue(Key(owner, binding, ZeroArgPropertyCacheKey.RunWideEnvironmentIdentity, run), out var exported));
        Assert.Equal(-1, exported);
        Assert.False(map.ContainsKey(Key(owner, binding, new object(), run)));

        // A chain of identities, each referring to the previous one, is not rooted by the table.
        var last = AddUnderLinkedIdentities(map, owner, binding, run, count: 256);
        ForceFullCollection();
        Assert.False(last.IsAlive);
        Assert.Equal(kept.Length, map.LivePartitionCount());
        GC.KeepAlive(kept);
        GC.KeepAlive(map);
    }

    private static ZeroArgPropertyCacheKey Key(object owner, object binding, object identity, object run)
        => new(owner, binding, identity, run);

    // Separate frames, so no fresh identity stays reachable from the asserting method's locals.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static void AddUnderFreshIdentities(
        PartitionedMap<ZeroArgPropertyCacheKey, int> map, object owner, object binding, object run, int count)
    {
        for (var index = 0; index < count; index++)
            Assert.True(map.TryAdd(Key(owner, binding, new object(), run), index));
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static WeakReference AddUnderLinkedIdentities(
        PartitionedMap<ZeroArgPropertyCacheKey, int> map, object owner, object binding, object run, int count)
    {
        object? previous = null;
        for (var index = 0; index < count; index++)
        {
            var identity = new object?[] { previous };
            Assert.True(map.TryAdd(Key(owner, binding, identity, run), index));
            previous = identity;
        }

        return new WeakReference(previous);
    }

    private static ScopeCtx Activated(Evaluator.EvalCtx ctx)
        => new(null, [], [], ["p"])
        {
            Activation = ParameterActivation.Capture(["p"], ctx, new List<(string Name, Result Value)>()),
        };

    // A separate frame, so neither the fresh identity nor its cell stays reachable from the asserting method's locals.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static (WeakReference Cell, WeakReference Identity) EstablishUnderAFreshIdentity(Algorithm.Alias alias, Evaluator.EvalCtx ctx)
    {
        var scope = Activated(ctx);
        var cell = Evaluator.AliasBindingCell(alias with { Parent = scope }, ctx);
        Assert.Same(cell, Evaluator.AliasBindingCell(alias with { Parent = scope }, ctx));
        return (new WeakReference(cell), new WeakReference(scope.Activation!.ValueEnvironmentIdentity));
    }

    private static (string Value, EvaluationBudget Budget) Run(string source, bool enableOptimizations)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: enableOptimizations);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        return (SixRouteAgreement.Neutral(result.Value.Value), budget);
    }

    private static void ForceFullCollection()
    {
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.WaitForPendingFinalizers();
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
    }
}
