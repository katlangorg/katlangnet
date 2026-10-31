using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// ALIAS-UNIFY-1 (M4★) second independent-review regressions. Source cases run on the six routes of
/// <see cref="SixRouteAgreement"/>; the observation fact reads the engine alone, the cancellation fact the sync and
/// async evaluators, the carrier's step and depth comparison the generic evaluator, and the allocation guard the
/// parser. Evaluator: an alias chase keys what it has passed by the BINDING it
/// followed (declaration, declaring scope and activation), and the structure a step's route decision needs
/// is computed with the structure chase's own context only — so a reference behind a carrier whose row
/// reads it back, a carrier of a parameter across activations, and two same-shape references all resolve.
/// Front end: OD-D is the TARGET chase (references and carriers alike, through opens) read in the lower
/// stratum, in both twins, so the detector and the resolver classify every cycle alike in every declaration
/// order; a reference chase reads its row in its own scope (a prelude-rooted open block, a block receiver);
/// a member miss makes the body its own structure; and every declaration-determined chase stretch is
/// recorded once per operation, so K reads through an L-long reference chain cost O(K + L), while K receivers
/// through a W-member provider stay O(K + W) through the operation's one body level per navigated body
/// (<c>OpenMemberIndexCache.BodyLevel</c>).
/// </summary>
public sealed class AliasUnifySecondReviewRegressionTests
{
    private const string CarrierReadingItsReference = "B = {\n    public F(x) = x * x\n    A.F\n}\n";

    private static async Task<SixRouteAgreement.Observation> OkAsync(string source, string value)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(value, outcome.Value);
        return outcome;
    }

    private static IReadOnlyDictionary<string, Algorithm> Kinds(string source)
        => SourceProvenance.ParseValid(source).Root.Properties.ToDictionary(static p => p.Name, static p => p.Value);

    // ── Evaluator: a chase keys what it passed by binding; a route decision gets the structure context only ──

    [Theory]
    [InlineData("A = B\n" + CarrierReadingItsReference + "A(3)", "9")]
    [InlineData("A = B\n" + CarrierReadingItsReference + "B(3), A(3)", "S[9, 9]")]
    [InlineData("A = B\n" + CarrierReadingItsReference + "B(3)", "9")]
    [InlineData(CarrierReadingItsReference + "A = B\nB(3)", "9")]
    [InlineData("Settings = Config\nConfig = {\n    public Rate = 0.2\n    Default\n}\nDefault = Settings.Rate\nSettings", "0.2")]
    [InlineData("P = C\nC = {\n    public Algorithm = 5\n    A\n}\nA = P.Algorithm\nP", "5")]
    [InlineData("Primary = Config\nBackup = Config\nConfig = {\n    public Rate = 0.2\n    Backup.Rate\n}\nPrimary", "0.2")]
    public async Task AReferenceBehindACarrierThatReadsItBack_Resolves(string source, string value)
    {
        await OkAsync(source, value);
        var kinds = Kinds(source);
        Assert.Contains(kinds.Values, static value => value is Algorithm.Alias { IsReference: true });
        Assert.Contains(kinds.Values, static value => value is Algorithm.Alias { IsReference: false });
    }

    [Theory]
    [InlineData("A = { f }")]
    [InlineData("A = f")]
    public async Task AnAliasOfAParameter_IsItsOwnBindingInEveryActivation(string alias)
        => await OkAsync($"Inc(x) = x + 1\nF(f, n) = {{\n    {alias}\n    if(n == 0, A(5), F(A, n - 1))\n}}\nF(Inc, 1)", "6");

    // ── Front end: OD-D is the target chase, through opens and carriers, in both twins ──

    [Fact]
    public async Task AReferenceCycleClosedThroughAnOpen_IsNoAlias()
    {
        const string source = "open Lib\nLib = { public B = A }\nA = B\nSame(x, x) = 0\nSame(A, A)";
        await OkAsync(source, "0");
        Assert.IsType<Algorithm.User>(Kinds(source)["A"]);
    }

    [Theory]
    [InlineData("A = B\nB = {\n    public X = 1\n    A\n}\n")]
    [InlineData("B = {\n    public X = 1\n    A\n}\nA = B\n")]
    public async Task AReferenceToACarrierWhoseRowLeadsBack_IsNoAlias_InEveryLayerAndOrder(string declarations)
    {
        // Neither body is an alias (OD-D: the target chase A -> B -> A never ends), so A has no member X: the
        // root infers X — reported, as at HEAD, as the certain fallback of A's miss (A is its own structure) — and a
        // closed body reports the certain fallback name.
        var kinds = Kinds(declarations + "A.X");
        Assert.IsType<Algorithm.User>(kinds["A"]);
        Assert.IsType<Algorithm.User>(kinds["B"]);

        var root = await SixRouteAgreement.OnEveryRouteAsync(declarations + "A.X");
        Assert.Equal("err", root.Kind);
        Assert.StartsWith("UnresolvedImplicitParams: Property 'X' was not found on `A`", root.Errors[0], StringComparison.Ordinal);

        var closed = await SixRouteAgreement.OnEveryRouteAsync(declarations + "G(p) = A.X\nG(1)");
        Assert.Equal("parse", closed.Kind);
        Assert.StartsWith("UndeclaredIdentifier: Property 'X' was not found on `A`", closed.Errors[0], StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("A = B.C\nB = Lib\nLib = {\n    public C = { public X = 1 }\n    public D = A\n}\nA.X", "1")]
    [InlineData("Lib = {\n    public C = { public X = 1 }\n    public D = A\n}\nB = Lib\nA = B.C\nA.X", "1")]
    [InlineData("A = B.K\nB = {\n    V(x) = x * 10\n    K = V\n    U = A\n}\nZ = A + 1\nZ(4)", "41")]
    [InlineData("B = {\n    V(x) = x * 10\n    K = V\n    U = A\n}\nA = B.K\nZ = A + 1\nZ(4)", "41")]
    public async Task AReferenceInASiblingCycle_ReadsItsUnprocessedReceiverStatically_InEveryOrder(string source, string value)
    {
        await OkAsync(source, value);
        Assert.IsType<Algorithm.Alias>(Kinds(source)["A"]);
    }

    // ── Front end: a reference chase reads its row in its own scope ──

    [Theory]
    [InlineData("K", "7")]
    [InlineData("K * 2", "14")]
    public async Task AnOpenBlocksMemberReference_OpensItsTarget(string row, string value)
        => await OkAsync("open {\n    public Lib = { public K = 7 }\n    public A = Lib\n}.A\n" + row, value);

    [Fact]
    public async Task ABlockReceiversReferenceMember_IsItsTargetsStructure()
        => await OkAsync("V = { public W = 7 }\nY = { K = V }.K.W + 0\nY", "7");

    [Fact]
    public async Task AMemberMissOnAKnownReceiver_MakesTheBodyItsOwnStructure_SoAClosedBodyChecksTheCertainFallback()
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("B = { Q = 1 }\nA = B.foo\nG(p) = A.bar\nG(1)");
        Assert.Equal("parse", outcome.Kind);
        Assert.StartsWith("UndeclaredIdentifier: Property 'bar' was not found on `A`", outcome.Errors[0], StringComparison.Ordinal);
    }

    // ── Coverage the second review found missing ──

    private const string CapturedPlan = "B(x) = x * 10\nCapture(meta c) = c\nR = Capture(B(tock()))\n";

    [Theory]
    [InlineData("R.Invoke(), { R }.Invoke(), { R }.Arguments == R.Arguments", "S[10, 10, true]")]
    [InlineData("R.Invoke(), { R }.Algorithm(2), { R }.Algorithm(R.Arguments*)", "S[10, 20, 10]")]
    [InlineData("C = { R }\nR.Invoke(), C.Invoke(), C.Arguments == R.Arguments, C.Algorithm(3)", "S[10, 10, true, 30]")]
    [InlineData("A = R\nR.Invoke(), A.Invoke(), A.Arguments == R.Arguments, A.Algorithm(3)", "S[10, 10, true, 30]")]
    public async Task AnAliasReceiverOfACallReferenceIntrinsic_ReadsTheOneCapturedPlan(string rows, string value)
    {
        // Every receiver spelling reads R's ONE cached reference: one plan, one sticky argument cell, one tock.
        var outcome = await OkAsync(CapturedPlan + rows, value);
        Assert.Equal(["tock#1"], outcome.HostCalls);
    }

    [Theory]
    [InlineData("A = G\nA*", "SpreadMissingOutput: while evaluating property G: Cannot spread because the spread operand has no defined output.")]
    [InlineData("A = {\n    G\n}\nA*", "MissingOutput: while evaluating spread operand A: Property 'G' has no defined output.")]
    public async Task ASpreadThroughAReference_IsTheTargetsOwnMissingOutput_WhileACarrierNestsIt(string rows, string expected)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("G = {\n    public X = 1\n}\n" + rows);
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith(expected, outcome.Errors[0], StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("F(x) = {\n    M = 2\n    x\n}\nA = {\n    M = 1\n    F\n}\nM(v) = 9\nNavigate(f) = f.M\nNavigate(A), Navigate(F)", "S[1, 2]")]
    [InlineData("Lib(*xs) = {\n    public K = 99\n    0\n}\nNavigate(f) = f.K\nUse(f) = {\n    A = {\n        public K = 5\n        f\n    }\n    Navigate(A), A.K\n}\nUse(Lib)", "S[5, 5]")]
    public async Task APassedCarrier_KeepsItsOwnStructure(string source, string value)
        => await OkAsync(source, value);

    [Fact]
    public async Task AValueOnlyRuntimeAlias_AnswersEveryZeroSupplyCallWithItsOneValue_AndPassesNoCallable()
    {
        var reads = await OkAsync("Use(f) = {\n    A = f\n    A(), A, A()\n}\nUse(tock())", "S[1, 1, 1]");
        Assert.Equal(["tock#1"], reads.HostCalls);

        var passed = await SixRouteAgreement.OnEveryRouteAsync("Apply(g) = g()\nUse(f) = {\n    A = f\n    Apply(A)\n}\nUse(5)");
        Assert.Equal("err", passed.Kind);
        Assert.StartsWith("NotAnAlgorithm:", passed.Errors[0], StringComparison.Ordinal);
    }

    [Fact]
    public async Task AHostOperationTarget_PublishesNothing_ThroughItsReference()
    {
        // `A()` is a fresh host call that publishes nothing (host targets publish nothing); bare `A` is
        // tock's own prelude read. A synthetic entry for the alias or its call would give (1, 1, 1).
        var outcome = await OkAsync("A = tock\nA(), A, tock", "S[1, 2, 2]");
        Assert.Equal(["tock#1", "tock#2"], outcome.HostCalls);
    }

    [Fact]
    public async Task AnOpenTargetsReference_NeverResolvesThroughAnOpen()
    {
        // The reference's head X is provided only by the sibling open Lib1: an open target's reference never
        // resolves through an open (OD-C stratification), so A is unresolved.
        var stratified = await SixRouteAgreement.OnEveryRouteAsync(
            "Lib1 = {\n    public X = {\n        public X = 1\n        0\n    }\n    0\n}\nG = {\n    open A, Lib1\n    A = X\n    X\n}\nG");
        Assert.Equal("parse", stratified.Kind);
        Assert.StartsWith("UnresolvedOpenTarget: 'A' cannot be opened", stratified.Errors[0], StringComparison.Ordinal);

        // A runtime reference opens only its own (empty) namespace, so D provides V.
        await OkAsync(
            "P = {\n    public V = 7\n    0\n}\nD = {\n    public V = -1\n    0\n}\nF(p) = {\n    A = p\n    G = {\n        open A, D\n        V\n    }\n    G\n}\nF(P)",
            "-1");
    }

    [Fact]
    public async Task ACarriersOwnMember_IsReadWithoutResolvingItsComputedTarget()
    {
        var outcome = await OkAsync(
            "Capture(meta op) = op\nZ = 7\nMk(n) = if(trace(n) == n, Capture(Z()), 0)\nB = {\n    public Q = 99\n    Mk(5).Algorithm\n}\nGetQ(f) = f.Q\nB.Q, GetQ(B)",
            "S[99, 99]");
        Assert.Empty(outcome.HostCalls);
    }

    [Fact]
    public async Task CapturesThroughAHolder_KeepTheirStickySupply_AndMatchByIdentityInertly()
    {
        var sticky = await OkAsync(
            "B = {\n    public F(x) = x * x\n    public Q = 99\n    F\n}\nA = B\nCapture(meta op) = op\nSame(x, x) = 0\n"
            + "RB = Capture(B(trace(3)))\nRA = Capture(A(trace(4)))\nSame(RB.Algorithm, RA.Algorithm), RB.Invoke(), RB.Invoke(), RA.Invoke(), RA.Invoke()",
            "S[0, 9, 9, 16, 16]");
        Assert.Equal(["trace(3)", "trace(4)"], sticky.HostCalls);

        await OkAsync(
            "Capture(meta op) = op\nQ(unused) = -1\nB = {\n    public F(x) = x * x\n    public Q = 99\n    F\n}\nGetQ(f) = f.Q\n"
            + "R = Capture(B(3))\nA = R.Algorithm\nD = { R.Algorithm }\nGetQ(A), GetQ(D), A(4), D(4), R.Invoke()",
            "S[99, -1, 16, 16, 9]");
    }

    [Fact]
    public async Task ACarrierForwardsItsExactSuppliedCells_AddingNoStepOrDepth()
    {
        const string definitions = "F(x, y) = x + x\nD = {\n    public Helper = 0\n    F\n}\n";
        var outcome = await OkAsync(definitions + "D(trace(3), trace(4)), F(trace(5), trace(6))", "S[6, 10]");
        Assert.Equal(["trace(3)", "trace(5)"], outcome.HostCalls);

        static EvaluationBudget Budget(string source)
        {
            var (result, budget) = Evaluator.RunCountedObserved(
                new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), limits: null, enableOptimizations: false);
            Assert.False(result.IsError);
            return budget;
        }

        var throughCarrier = Budget(definitions + "D(3, 4)");
        var direct = Budget(definitions + "F(3, 4)");
        Assert.Equal(direct.ConsumedSteps, throughCarrier.ConsumedSteps);
        Assert.Equal(direct.PeakDepth, throughCarrier.PeakDepth);
    }

    [Fact]
    public async Task AFamilyEndsDispatchOnAnExecutedProjectionFailure()
    {
        // The first clause's CALLABLE projection of the `.Algorithm` link reads Bad and fails: an executed
        // failure ends dispatch (a non-match would select the second clause, 2).
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("Bad = min([])\nSame(x, x) = 1\nSame(x, y) = 2\nSame(Bad.Algorithm, 7)");
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith("IllegalInEval:", outcome.Errors[0], StringComparison.Ordinal);
    }

    [Fact]
    public async Task AnAnchorsOwnFailure_DemandsNoPendingValue()
    {
        // The anchor's counted VALUE fails, so A's pending VALUE (trace(10)) is never demanded.
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("A = trace(10) - 3\nSame(x, x) = 0\nSame(A, trace(7) / 0)");
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith("DivisionByZero:", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Equal(["trace(7)"], outcome.HostCalls);
    }

    [Fact]
    public void AnAliasCall_IsObservedUnderItsTargetOnly()
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "P = tick()\nA = P\nA(), P, tick()", new RunOptions { ObservePropertyValues = true }));
        // The final tick is second: A() ran P once and the bare P reused that value.
        Assert.Equal("S[1, 1, 2]", SixRouteAgreement.Neutral(success.Value));
        var observation = Assert.Single(success.PropertyObservations!);
        Assert.Equal("P", observation.Name);
        Assert.Equal("1", SixRouteAgreement.Neutral(observation.Value!));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationInsideAnAliasCall_ClearsOwnership_AndPublishesNothing(bool asynchronous)
    {
        // `A()` is P's fresh call under P's publication origin, owning P's empty entry when it is cancelled.
        const string source = "P = tock() + tock()\nA = P\nA(), P";
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
        var program = new Expr.AlgorithmExpr((await SourceProvenance.ParseValidAsync(source, new RunOptions { HostOperations = operations })).Root);
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

    // ── Front end: FE-1 for reference chains and wide providers ──

    /// <summary>An L-long reference chain <c>A1 = A2</c>, …, <c>AL = Lib</c> read K times through <c>A1.x</c> (or <c>A{j}.x</c>).</summary>
    private static string ChainReads(int size, bool everyStart)
        => "Lib = { public x = 1 }\n"
            + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"A{i} = A{i + 1}\n")) + $"A{size} = Lib\n"
            + string.Concat(Enumerable.Range(0, size).Select(j => $"R{j} = A{(everyStart ? 1 + j % size : 1)}.x + 0\n"))
            + "R0";

    /// <summary>The same chain opened by K sibling blocks.</summary>
    private static string ChainOpens(int size)
        => "Lib = { public x = 1 }\n"
            + string.Concat(Enumerable.Range(1, size - 1).Select(i => $"A{i} = A{i + 1}\n")) + $"A{size} = Lib\n"
            + string.Concat(Enumerable.Range(0, size).Select(j => $"R{j} = {{\n    open A1\n    x + 0\n}}\n"))
            + "R0";

    /// <summary>K receivers <c>M{j}.x</c> through one opened W-member provider.</summary>
    private static string WideReceivers(int size)
        => "open Lib\nLib = {\n" + string.Concat(Enumerable.Range(0, size).Select(i => $"    public M{i} = {{ public x = {i} }}\n")) + "}\n"
            + string.Concat(Enumerable.Range(0, size).Select(j => $"R{j} = M{j}.x + 0\n"))
            + "R0";

    /// <summary>
    /// A design-independent guard over the public parse: doubling the size of each shape roughly doubles the
    /// allocation. Before the chase memos, K reads through an L-long chain were O(K·L) (3.1x to 3.7x per doubling
    /// at 500 -> 1000: about 1 GB for the 2000-long read chain and 2.3 GB for the 2000-long opened chain).
    /// </summary>
    [Theory]
    [InlineData("chain-head")]
    [InlineData("chain-every-start")]
    [InlineData("chain-opens")]
    [InlineData("wide-receivers")]
    public void StaticChases_AllocationGrowsLinearly(string shape)
    {
        string Source(int size) => shape switch
        {
            "chain-head" => ChainReads(size, everyStart: false),
            "chain-every-start" => ChainReads(size, everyStart: true),
            "chain-opens" => ChainOpens(size),
            _ => WideReceivers(size),
        };

        static long Allocation(string source)
        {
            Assert.False(Parser.Parse(source).HasErrors);
            var before = GC.GetAllocatedBytesForCurrentThread();
            _ = Parser.Parse(source);
            return GC.GetAllocatedBytesForCurrentThread() - before;
        }

        var small = Allocation(Source(400));
        var large = Allocation(Source(800));
        var ratio = (double)large / small;
        Assert.True(ratio < 2.5, $"Doubling {shape} grew the parse allocation {ratio:F2}x ({small} -> {large} bytes).");
    }
}
