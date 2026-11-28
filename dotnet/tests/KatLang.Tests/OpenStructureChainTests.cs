using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// THE STRATIFIED OPEN STRUCTURE OF A LONG REFERENCE CHAIN (OD-C, OD-D; <c>Evaluator.OpenStructure</c>, Lean
/// <c>openStructure</c> / <c>openStructureFuel</c>; November 2026, from the adversarial investigation of
/// 2026-11-21, finding <c>static-structure-aliases-open-structure-fuel-and-rechase</c>).
/// <para>Before: the walk had a FIXED budget of 4096 reference hops (C# <c>OpenStructureFuel</c>, Lean
/// <c>openStructureFuel := 4096</c>) and reported a walk still standing on a reference after it as the alias
/// cycle — but the front end admits an acyclic chain of any length, so <c>open A4097</c> over
/// <c>A0 = Lib</c>, <c>A1 = A0</c>, …, <c>A4097 = A4096</c> was <c>IllegalInEval</c> "callable alias cycle"
/// although no source program forms one (OD-D). And every new level state that opened a chain — the next
/// call of a body that opens it — walked the whole chain again.</para>
/// <para>Now: C# records the walk's CURRENT CHAIN by binding and reports a reference reached twice on it
/// (the accepted traversal of the alias chases and <c>StaticAliasTargets.FindCycle</c>), and Lean bounds the
/// walk by its static world's alias count (a structured bound, like <c>staticAliasCycle</c>), so an admitted
/// acyclic chain of any length opens its target while a host-built cycle through a reference RECEIVER —
/// which the pre-evaluation gate does not see — stays the alias cycle. A run of bare-name references is
/// remembered per declaring chain (on its activation or the run), so a later open of the chain in a stable
/// context jumps to its end, with the same provider identity.</para>
/// </summary>
public class OpenStructureChainTests
{
    /// <summary>Past the former fixed budget of 4096 hops.</summary>
    private const int LongChain = 4_100;

    private static string NameChain(string head, int length, string target)
        => $"{head}0 = {target}\n" + string.Concat(Enumerable.Range(1, length).Select(i => $"{head}{i} = {head}{i - 1}\n"));

    /// <summary>
    /// A chain of <paramref name="length"/> + 1 references to <c>Lib</c>, opened as a dotted target
    /// (<c>open A{n}.Sub</c>: the receiver of <c>ResolveOpenPropAccess</c>) and through a member-path reference
    /// whose receiver is the chain (<c>S = A{n}.Sub</c>: a receiver walk nested in the walk of <c>S</c>).
    /// </summary>
    private static string ChainProgram(int length)
        => "Lib = {\n  public Sub = {\n    public X = 7\n  }\n}\n"
            + NameChain("A", length, "Lib")
            + $"S = A{length}.Sub\n"
            + $"UseDotted = {{\n  open A{length}.Sub\n  X\n}}\n"
            + "UseMember = {\n  open S\n  X + 1\n}\n"
            + "UseDotted, UseMember\n";

    private static Expr Parsed(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static async Task<(EvalResult<Result> Sync, EvalResult<Result> Async)> BothRoutes(Expr program)
    {
        var sync = Evaluator.Run(program);
        var twin = await Evaluator.RunAsync(program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        return (sync, twin);
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext withContext)
            error = withContext.Inner;
        return error;
    }

    private static void AssertAliasCycle(EvalResult<Result> result)
    {
        Assert.True(result.IsError, result.IsError ? null : result.Value.ToString());
        Assert.Equal(Evaluator.AliasCycleMessage, Assert.IsType<EvalError.IllegalInEval>(Innermost(result.Error)).Reason);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(LongChain)]
    public async Task SourceChain_OpensItsTarget_AtAnyLength_OnBothRoutes(int length)
    {
        var (sync, twin) = await BothRoutes(Parsed(ChainProgram(length)));

        Assert.False(sync.IsError, sync.IsError ? sync.Error.ToString() : null);
        Assert.Equal("S[7, 8]", SixRouteAgreement.Neutral(sync.Value));
        Assert.False(twin.IsError, twin.IsError ? twin.Error.ToString() : null);
        Assert.Equal("S[7, 8]", SixRouteAgreement.Neutral(twin.Value));
    }

    // ── Host-built controls: no front end, the pre-evaluation gate admits the chain ──

    private static Algorithm.Alias Ref(string name) => new(null, [], [], new Expr.Resolve(name));

    private static Algorithm.Alias MemberRef(string receiver, string member)
        => new(null, [], [], new Expr.DotCall(new Expr.Resolve(receiver), member, null));

    private static Algorithm.User Lib()
        => new(null, [], [], [new Property("X", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]), IsPublic: true)], []);

    private static IEnumerable<Property> HostChain(string head, int length, Algorithm.Alias first)
        => Enumerable.Range(0, length + 1).Select(i => new Property($"{head}{i}", i == 0 ? first : Ref($"{head}{i - 1}")));

    private static Expr HostRoot(string opened, IEnumerable<Property> properties, Expr output)
        => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [new Expr.Resolve(opened)], [.. properties], [output]));

    [Theory]
    [InlineData(1)]
    [InlineData(5_000)]
    public async Task HostBuiltChain_OpensItsTarget_AtAnyLength_OnBothRoutes(int length)
    {
        var program = HostRoot($"A{length}", [new Property("Lib", Lib()), .. HostChain("A", length, Ref("Lib"))], new Expr.Resolve("X"));

        var (sync, twin) = await BothRoutes(program);

        Assert.False(sync.IsError, sync.IsError ? sync.Error.ToString() : null);
        Assert.Equal(new Result.Atom(7), sync.Value);
        Assert.False(twin.IsError, twin.IsError ? twin.Error.ToString() : null);
        Assert.Equal(sync.Value, twin.Value);
    }

    [Fact]
    public async Task OpenProviderIdentityIncludesTheDeclaringOwnerOfSharedMembers()
    {
        Property[] members = [new("A", Ref("Lib"), IsPublic: true), new("Lib", Lib())];
        var left = new Algorithm.User(null, [], [], members, []);
        var right = new Algorithm.User(null, [], [], members, []);
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [],
            [new Expr.DotCall(new Expr.Resolve("Left"), "A", null), new Expr.DotCall(new Expr.Resolve("Right"), "A", null)],
            [new Property("Left", left), new Property("Right", right)], [new Expr.Resolve("X")]));

        var (sync, twin) = await BothRoutes(program);
        foreach (var result in new[] { sync, twin })
        {
            Assert.True(result.IsError);
            var error = Assert.IsType<EvalError.AmbiguousOpen>(Innermost(result.Error));
            Assert.Equal("X", error.Name);
            Assert.Equal(["Left.A", "Right.A"], error.Providers);
        }
    }

    [Fact]
    public async Task HostAliasViewsWithDifferentTargetsCanOccurInOneAcyclicChain()
    {
        var first = Ref("Second");
        var second = first with { Target = new Expr.Resolve("Lib") };
        var program = HostRoot("First", [new("First", first), new("Second", second), new("Lib", Lib())], new Expr.Resolve("X"));

        var (sync, twin) = await BothRoutes(program);
        foreach (var result in new[] { sync, twin })
        {
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal(new Result.Atom(7), result.Value);
        }
    }

    /// <summary>
    /// A cycle through a reference RECEIVER (<c>A = B.C</c> / <c>B = A</c>, and <c>A = A.F</c>): the static gate
    /// follows declared members only, so it admits the tree, and the open walk meets the cycle — opened at the
    /// member-path alias, at the name alias (whose name run is remembered before the receiver walk jumps
    /// through it), and at the far end of a 5,000-reference chain.
    /// </summary>
    [Theory]
    [InlineData("A", 0)]
    [InlineData("B", 0)]
    [InlineData("Z5000", 5_000)]
    [InlineData("Self", 0)]
    public async Task HostBuiltReceiverCycle_IsStillTheAliasCycle_OnBothRoutes(string opened, int chain)
    {
        Property[] cycle =
        [
            new("A", MemberRef("B", "C")),
            new("B", Ref("A")),
            new("Self", MemberRef("Self", "F")),
        ];
        var properties = chain == 0 ? cycle : [.. cycle, .. HostChain("Z", chain, Ref("A"))];

        // `Y` is declared nowhere, so its lookup consults the root's open.
        var (sync, twin) = await BothRoutes(HostRoot(opened, properties, new Expr.Resolve("Y")));

        AssertAliasCycle(sync);
        AssertAliasCycle(twin);
        Assert.Equal(sync.Error, twin.Error);
    }

    // ── Warm chases: a chain's name run is walked once per stable context ──

    private static string WarmProgram(int length, int calls)
        => "Lib = {\n  public X = 7\n}\n"
            + NameChain("A", length, "Lib")
            + $"F(k) = {{\n  open A{length}, Lib\n  X + k\n}}\n"
            + $"sum(range(1, {calls}).map(F))\n";

    /// <summary>
    /// Every call of <c>F</c> is a new level state that resolves <c>open A{n}, Lib</c>; the chain is declared
    /// outside every activation, so its name run is walked by the first call only (<c>n + 1</c> steps) and every
    /// later call jumps to the remembered end. The provider stays <c>Lib</c>'s own identity: <c>A{n}</c> and
    /// <c>Lib</c> remain ONE provider of <c>X</c> (two would be <c>AmbiguousOpen</c>), cold and warm.
    /// </summary>
    [Theory]
    [InlineData(1)]
    [InlineData(50)]
    public async Task RepeatedOpensOfAChain_WalkItOnce_AndKeepTheProviderIdentity(int calls)
    {
        const int length = 64;
        var program = Parsed(WarmProgram(length, calls));
        var expected = new Result.Atom(7 * calls + calls * (calls + 1) / 2);

        var observations = new EvaluationObservations();
        var sync = Evaluator.RunObserved(program, observations);
        Assert.False(sync.IsError, sync.IsError ? sync.Error.ToString() : null);
        Assert.Equal(expected, sync.Value);
        Assert.Equal(length + 1, observations.OpenStructureStepCount);
        Assert.Equal(calls - 1, observations.OpenStructureRememberedEndCount);

        var twinObservations = new EvaluationObservations();
        var (twin, _) = await Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), observations: twinObservations);
        Assert.False(twin.IsError, twin.IsError ? twin.Error.ToString() : null);
        Assert.Equal(expected, twin.Value.Value);
        Assert.Equal(length + 1, twinObservations.OpenStructureStepCount);
        Assert.Equal(calls - 1, twinObservations.OpenStructureRememberedEndCount);
    }

    /// <summary>
    /// A chain declared INSIDE a call is remembered on that call's activation: each call of <c>G</c> walks its
    /// own chain to its own <c>L</c>, whose <c>X</c> reads that call's <c>k</c> — a run-wide memo would answer
    /// the first call's <c>L</c> for every call. Within one call the second level's open jumps to the end.
    /// </summary>
    [Fact]
    public async Task AChainDeclaredInACall_IsRememberedPerActivation()
    {
        const string source =
            "G(k) = {\n  L = {\n    public X = k\n  }\n  B0 = L\n  B1 = B0\n  B2 = B1\n"
            + "  H = {\n    open B2\n    X\n  }\n  J = {\n    open B2\n    X * 10\n  }\n  H + J\n}\n"
            + "G(1), G(2), G(3)\n";
        var program = Parsed(source);

        var observations = new EvaluationObservations();
        var sync = Evaluator.RunObserved(program, observations);
        Assert.False(sync.IsError, sync.IsError ? sync.Error.ToString() : null);
        Assert.Equal("S[11, 22, 33]", SixRouteAgreement.Neutral(sync.Value));
        // Three references walked per call, and the second open of each call jumps to the remembered end.
        Assert.Equal(9, observations.OpenStructureStepCount);
        Assert.Equal(3, observations.OpenStructureRememberedEndCount);

        var twin = await Evaluator.RunAsync(program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.False(twin.IsError, twin.IsError ? twin.Error.ToString() : null);
        Assert.Equal("S[11, 22, 33]", SixRouteAgreement.Neutral(twin.Value));
    }

    /// <summary>Nothing is remembered across runs: a second run of the same tree walks the chain again.</summary>
    [Fact]
    public void RememberedEnds_AreRunScoped()
    {
        var program = Parsed(WarmProgram(length: 16, calls: 3));
        for (var run = 0; run < 2; run++)
        {
            var observations = new EvaluationObservations();
            var result = Evaluator.RunObserved(program, observations);
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal(17, observations.OpenStructureStepCount);
            Assert.Equal(2, observations.OpenStructureRememberedEndCount);
        }
    }

    [Fact]
    public async Task MemberPathSharedByTwoOpenTargetsIsWalkedOnceAtThatSite()
    {
        var program = Parsed("Lib = { public Sub = { public X = 7 } }\nS = Lib.Sub\nA = S\nB = S\n"
            + "F(k) = {\n  open A, B\n  X + k\n}\nF(1), F(2)\n");
        var observations = new EvaluationObservations();
        var result = Evaluator.RunObserved(program, observations);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal("S[8, 9]", SixRouteAgreement.Neutral(result.Value));
        // First call visits A, S and B. The next call reuses both name runs and walks S in its own context.
        Assert.Equal(4, observations.OpenStructureStepCount);
        Assert.Equal(4, observations.OpenStructureRememberedEndCount);
        var twin = await Evaluator.RunAsync(program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.False(twin.IsError, twin.IsError ? twin.Error.ToString() : null);
        Assert.Equal("S[8, 9]", SixRouteAgreement.Neutral(twin.Value));
    }

    private sealed class CancelDuringLookup(EvaluationObservations observations, CancellationTokenSource source, int cancelAtStep = 1)
        : IReadOnlyList<Property>
    {
        public int Count
        {
            get
            {
                if (observations.OpenStructureStepCount >= cancelAtStep) source.Cancel();
                return 0;
            }
        }

        public Property this[int index] => throw new ArgumentOutOfRangeException(nameof(index));
        public IEnumerator<Property> GetEnumerator() => Enumerable.Empty<Property>().GetEnumerator();
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationDuringAReferenceLookupStopsTheChase(bool asynchronous)
    {
        var observations = new EvaluationObservations();
        using var cancellation = new CancellationTokenSource();
        var middle = Ref("A127") with { Properties = new CancelDuringLookup(observations, cancellation) };
        var chain = HostChain("A", 256, Ref("Lib"))
            .Select(p => p.Name == "A128" ? new Property("A128", middle) : p);
        var program = HostRoot("A256", [new Property("Lib", Lib()), .. chain], new Expr.Resolve("X"));

        OperationCanceledException cancelled;
        if (asynchronous)
        {
            cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), observations: observations,
                cancellationToken: cancellation.Token));
        }
        else
        {
            cancelled = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(
                program, zeroArgPropertyResultCache: new RunScopedZeroArgPropertyResultCache(), observations: observations,
                cancellationToken: cancellation.Token));
        }

        Assert.Equal(cancellation.Token, cancelled.CancellationToken);
        Assert.InRange(observations.OpenStructureStepCount, 128, 129);
    }

    // ── Nested receiver walks: a member path whose receiver is itself such a path ──
    //
    // `C0 = A` and `C{k} = C{k-1}.N` over `A`, whose public `N` is `A` itself: the receiver of each member step is
    // the previous member-path reference, so opening `C{n}` walks n receivers inside one another. The walk keeps
    // them on an explicit stack (`Evaluator.OpenStructure`, `OpenStructureReceiverWait`) — before, each receiver was
    // a host frame, and 800 of them were `EvaluationStackExhausted` on a 1 MiB Release thread. The bounded-stack pin
    // is `EvaluatorOpenChainStackProcessTests.NestedReceiverChain_CompletesOnSmallThreads`; the step and memo counts
    // below are the ones the recursive walk produced, so the explicit stack walks the same references in the same
    // contexts. Lean: `afReceiverChainProvides`, `afReceiverCycleAtDepth` and `afReceiverInaccessibleAtDepth` in
    // `CoreTests/AliasForwarding.lean`.

    /// <summary>Past the receiver depth the recursive walk fitted in the test host's worker thread.</summary>
    private const int LongReceiverChain = 1_000;

    /// <summary>
    /// The receiver chain of <paramref name="length"/> member-path references: <c>member</c> as above, <c>mixed</c>
    /// with a bare-name reference between each pair (<c>D{k} = C{k-1}</c>, <c>C{k} = D{k}.N</c>), and <c>double</c>
    /// with two member steps per reference (<c>C{k} = C{k-1}.N.N</c>).
    /// </summary>
    internal static string ReceiverChain(string shape, int length)
        => "A = {\n  public N = A\n  public V = 7\n}\nC0 = A\n" + string.Concat(Enumerable.Range(1, length).Select(k => shape switch
        {
            "member" => $"C{k} = C{k - 1}.N\n",
            "mixed" => $"D{k} = C{k - 1}\nC{k} = D{k}.N\n",
            "double" => $"C{k} = C{k - 1}.N.N\n",
            _ => throw new ArgumentOutOfRangeException(nameof(shape), shape, null),
        }));

    /// <summary>The receiver chain with a body that opens its last reference and reads <c>V</c> (7) through it.</summary>
    internal static string ReceiverChainProgram(string shape, int length)
        => ReceiverChain(shape, length) + $"B = {{\n  open C{length}\n  V\n}}\nB\n";

    /// <summary>Host-built: <c>Lib</c> with public <c>X = 7</c> and <c>N = Lib</c>, <c>Z0 = first</c>, <c>Z{k} = Z{k-1}.N</c>, the root opening <c>Z{length}</c>.</summary>
    internal static Expr HostReceiverChain(int length, Algorithm.Alias? first = null, IEnumerable<Property>? more = null, Func<int, string>? member = null, string read = "X")
        => HostRoot($"Z{length}",
            [new Property("Lib", ReceiverLib()), .. more ?? [],
             .. Enumerable.Range(0, length + 1).Select(k => new Property($"Z{k}", k == 0 ? first ?? Ref("Lib") : MemberRef($"Z{k - 1}", member?.Invoke(k) ?? "N")))],
            new Expr.Resolve(read));

    private static Algorithm.User ReceiverLib(params Property[] more)
        => new(null, [], [],
            [new Property("X", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]), IsPublic: true), new Property("N", Ref("Lib"), IsPublic: true), .. more], []);

    private static async Task<(EvalResult<Result> Sync, EvaluationObservations SyncObserved, EvalResult<Result> Async, EvaluationObservations AsyncObserved)> ObservedRoutes(Expr program)
    {
        var observations = new EvaluationObservations();
        var sync = Evaluator.RunObserved(program, observations);
        var twinObservations = new EvaluationObservations();
        var (twin, _) = await Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), observations: twinObservations);
        return (sync, observations, twin.IsError ? twin.Error : EvalResult<Result>.Ok(twin.Value.Value), twinObservations);
    }

    /// <summary>
    /// Every reference of the chain is stepped on once and every name run after the first is remembered: a
    /// <c>member</c> chain of n takes its n member steps, <c>C0</c>'s name step and the first wired <c>N</c>'s, and each
    /// later <c>N</c> jumps to the remembered end of that name run; <c>mixed</c> adds one name step per <c>D{k}</c>;
    /// <c>double</c> reads two <c>N</c>s per reference.
    /// </summary>
    [Theory]
    [InlineData("member", 1)]
    [InlineData("member", 64)]
    [InlineData("member", LongReceiverChain)]
    [InlineData("mixed", 1)]
    [InlineData("mixed", 64)]
    [InlineData("mixed", LongReceiverChain)]
    [InlineData("double", 64)]
    [InlineData("double", LongReceiverChain)]
    public async Task NestedReceiverChain_OpensItsTarget_StepsOnEachReferenceOnce_OnBothRoutes(string shape, int length)
    {
        var (sync, observed, twin, twinObserved) = await ObservedRoutes(Parsed(ReceiverChainProgram(shape, length)));

        var (steps, remembered) = shape switch
        {
            "member" => (length + 2, length - 1),
            "mixed" => (2 * length + 2, length - 1),
            _ => (length + 2, 2 * length - 1),
        };
        foreach (var (result, observations) in new[] { (sync, observed), (twin, twinObserved) })
        {
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal(new Result.Atom(7), result.Value);
            Assert.Equal(steps, observations.OpenStructureStepCount);
            Assert.Equal(remembered, observations.OpenStructureRememberedEndCount);
        }
    }

    /// <summary>A host-built chain, with no front end in the way, far past any receiver depth a host frame per receiver allowed.</summary>
    [Fact]
    public async Task HostBuiltNestedReceiverChain_OpensItsTarget_OnBothRoutes()
    {
        const int length = 20_000;
        var (sync, observed, twin, twinObserved) = await ObservedRoutes(HostReceiverChain(length));

        foreach (var (result, observations) in new[] { (sync, observed), (twin, twinObserved) })
        {
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal(new Result.Atom(7), result.Value);
            Assert.Equal(length + 2, observations.OpenStructureStepCount);
            Assert.Equal(length - 1, observations.OpenStructureRememberedEndCount);
        }
    }

    /// <summary>
    /// A GENUINE cycle met inside the innermost receiver walk: <c>Z0 = A</c> with <c>A = B.C</c> / <c>B = A</c>, or
    /// <c>Z0 = Self</c> with <c>Self = Self.F</c>, at the bottom of a receiver chain. Every enclosing walk is still on
    /// the active path when the cycle is met, so it is the alias cycle at any depth — and the same error on both
    /// routes.
    /// </summary>
    [Theory]
    [InlineData("A", 1)]
    [InlineData("A", 64)]
    [InlineData("A", 5_000)]
    [InlineData("Self", 1)]
    [InlineData("Self", 5_000)]
    public async Task CycleThroughTheInnermostReceiver_IsTheAliasCycle_AtAnyDepth_OnBothRoutes(string start, int length)
    {
        Property[] cycle = [new("A", MemberRef("B", "C")), new("B", Ref("A")), new("Self", MemberRef("Self", "F"))];
        var (sync, twin) = await BothRoutes(HostReceiverChain(length, Ref(start), cycle));

        AssertAliasCycle(sync);
        AssertAliasCycle(twin);
        Assert.Equal(sync.Error, twin.Error);
    }

    /// <summary>
    /// An inaccessible member on the path of the innermost receiver walk: <c>C1 = C0.S</c> with <c>C0 = G</c> and
    /// <c>S</c> capturing <c>G</c>'s parameter, opened at the root where <c>G</c> has no activation. The step is refused
    /// with the receiver as written and the step's span, under the frame of the open that reached it — not later at
    /// the read of <c>V</c>. Inside <c>G</c>'s activation the same chain opens.
    /// </summary>
    [Theory]
    [InlineData(2)]
    [InlineData(64)]
    public async Task InaccessibleMemberInTheInnermostReceiver_IsRefusedAtItsStep_OnBothRoutes(int length)
    {
        const string g = "G(p) = {\n  public S = {\n    public N = S\n    public V = 7\n    p\n  }\n";
        var chain = string.Concat(Enumerable.Range(2, length - 1).Select(k => $"C{k} = C{k - 1}.N\n"));
        var refused = Parsed(g + "  p\n}\nC0 = G\nC1 = C0.S\n" + chain + $"B = {{\n  open C{length}\n  V\n}}\nB\n");

        var (sync, twin) = await BothRoutes(refused);
        foreach (var result in new[] { sync, twin })
        {
            Assert.True(result.IsError);
            var frame = Assert.IsType<EvalError.WithContext>(result.Error);
            Assert.Equal($"while resolving open: C{length}", frame.Context);
            var error = Assert.IsType<EvalError.LocalOnlyProperty>(Innermost(result.Error));
            Assert.Equal(("C0", "S", PropertyExposure.LocalOnlyCapturedAncestorParameters), (error.ObjectDesc, error.PropertyName, error.Exposure));
            Assert.Equal(["p"], error.RequiredParameters);
            // `C0.S` in `C1 = C0.S`, line 10.
            Assert.Equal(new SourceSpan(10, 6, 10, 10), error.Span);
        }
        Assert.Equal(sync.Error, twin.Error);

        var inside = Parsed(g + "  C0 = S\n" + string.Concat(Enumerable.Range(1, length).Select(k => $"  C{k} = C{k - 1}.N\n"))
            + $"  B = {{\n    open C{length}\n    V\n  }}\n  B\n}}\nG(5)\n");
        var (insideSync, insideTwin) = await BothRoutes(inside);
        Assert.Equal(EvalResult<Result>.Ok(new Result.Atom(7)).ToString(), insideSync.ToString());
        Assert.Equal(insideSync.ToString(), insideTwin.ToString());
    }

    /// <summary>
    /// A host-built member that is never accessible (a conditional branch's own declaration) as the innermost
    /// receiver's step, the Lean guard's tree: refused as the receiver's <c>LocalOnlyProperty</c> at every depth.
    /// </summary>
    [Theory]
    [InlineData(1)]
    [InlineData(5_000)]
    public async Task NeverAccessibleMemberInTheInnermostReceiver_IsRefused_OnBothRoutes(int length)
    {
        var lib = new Property("Lib", ReceiverLib(new Property("S", Ref("Lib"), IsPublic: true, Exposure: PropertyExposure.LocalOnlyConditionalAlgorithm)));
        var program = HostRoot($"Z{length}",
            [lib, .. Enumerable.Range(0, length + 1).Select(k => new Property($"Z{k}", k == 0 ? MemberRef("Lib", "S") : MemberRef($"Z{k - 1}", "N")))],
            new Expr.Resolve("X"));

        var (sync, twin) = await BothRoutes(program);
        foreach (var result in new[] { sync, twin })
        {
            Assert.True(result.IsError);
            var error = Assert.IsType<EvalError.LocalOnlyProperty>(Innermost(result.Error));
            Assert.Equal(("Lib", "S", PropertyExposure.LocalOnlyConditionalAlgorithm), (error.ObjectDesc, error.PropertyName, error.Exposure));
        }
        Assert.Equal(sync.Error, twin.Error);
    }

    /// <summary>
    /// The <c>.Algorithm</c> intrinsic inside the receiver chain ends the walk that navigates it at its own
    /// reference, a runtime link: as the LAST step, the opened link is its own namespace and provides no <c>X</c>; in
    /// the MIDDLE, the next walk's step reads a member of that link, which has none, so the path is no static path.
    /// </summary>
    [Theory]
    [InlineData(3)]
    [InlineData(64)]
    public async Task AlgorithmIntrinsicInTheReceiverChain_EndsTheWalkThatReachesIt_OnBothRoutes(int length)
    {
        var (lastSync, lastTwin) = await BothRoutes(HostReceiverChain(length, member: k => k == length ? "Algorithm" : "N"));
        foreach (var result in new[] { lastSync, lastTwin })
            Assert.Equal("X", Assert.IsType<EvalError.UnknownName>(Innermost(result.Error)).Name);

        var middle = (length + 1) / 2;
        var (midSync, midTwin) = await BothRoutes(HostReceiverChain(length, member: k => k == middle ? "Algorithm" : "N"));
        foreach (var result in new[] { midSync, midTwin })
        {
            var error = Assert.IsType<EvalError.IllegalInEval>(Innermost(result.Error));
            Assert.Equal(Evaluator.AliasTargetNotStaticPathMessage(MemberRef($"Z{middle}", "N").Target), error.Reason);
        }
        Assert.Equal(midSync.Error, midTwin.Error);
    }

    /// <summary>
    /// REPEATED READERS: every call of <c>F</c> is a new level that opens <c>C{n}</c>, a second reference <c>E</c> to it and
    /// <c>A</c>. The first call walks the chain (n + 3 steps for the <c>member</c> chain, and <c>E</c> jumps to
    /// <c>C{n}</c>'s member end in the same open list); each later call walks only the n member steps again —
    /// member-path ends live for one open list — and jumps over every name run, remembered for the run. All three
    /// targets stay ONE provider of <c>V</c> (two would be <c>AmbiguousOpen</c>).
    /// </summary>
    [Theory]
    [InlineData("member", 1)]
    [InlineData("member", 20)]
    [InlineData("mixed", 20)]
    public async Task RepeatedReadersOfAReceiverChain_RewalkOnlyItsMemberSteps_AndKeepTheProvider(string shape, int calls)
    {
        const int length = 64;
        var program = Parsed(ReceiverChain(shape, length) + $"E = C{length}\nF(k) = {{\n  open C{length}, E, A\n  V + k\n}}\n"
            + $"sum(range(1, {calls}).map(F))\n");

        var (sync, observed, twin, twinObserved) = await ObservedRoutes(program);

        // The mixed chain's D{k} are one name step each on the first call and one remembered name run each later.
        var (firstSteps, laterRemembered) = shape == "mixed" ? (2 * length + 3, 2 * length + 2) : (length + 3, length + 3);
        foreach (var (result, observations) in new[] { (sync, observed), (twin, twinObserved) })
        {
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal(new Result.Atom(7 * calls + calls * (calls + 1) / 2), result.Value);
            Assert.Equal(firstSteps + (calls - 1) * length, observations.OpenStructureStepCount);
            Assert.Equal(length + (calls - 1) * laterRemembered, observations.OpenStructureRememberedEndCount);
        }
    }

    /// <summary>
    /// FAILED PUBLICATION: the innermost receiver's name run fails (<c>Z0 = W</c>, <c>W = Nowhere</c>), so neither of
    /// its references is remembered, nor anything the enclosing walks would have finished; the same chain over
    /// <c>W = Lib</c> remembers <c>Z0</c>, <c>W</c> and the wired <c>N</c>.
    /// </summary>
    [Theory]
    [InlineData(4)]
    [InlineData(5_000)]
    public void FailedInnermostNameRun_RemembersNothing(int length)
    {
        var (failed, failedRun) = Evaluator.RunCountedObserved(
            HostReceiverChain(length, Ref("W"), [new Property("W", Ref("Nowhere"))]), zeroArgPropertyResultCache: new RunScopedZeroArgPropertyResultCache());
        Assert.True(failed.IsError);
        Assert.Equal("Nowhere", Assert.IsType<EvalError.UnknownName>(Innermost(failed.Error)).Name);
        Assert.Empty(failedRun.OpenStructureEnds);

        var (succeeded, succeededRun) = Evaluator.RunCountedObserved(
            HostReceiverChain(length, Ref("W"), [new Property("W", Ref("Lib"))]), zeroArgPropertyResultCache: new RunScopedZeroArgPropertyResultCache());
        Assert.False(succeeded.IsError, succeeded.IsError ? succeeded.Error.ToString() : null);
        Assert.Equal(new Result.Atom(7), succeeded.Value.Value);
        Assert.Equal(3, succeededRun.OpenStructureEnds.Count);
    }

    /// <summary>
    /// CANCELLED PUBLICATION: the host cancels while the innermost receiver's name run looks <c>Lib</c> up, so the
    /// run's own publication observes it first — after all n member steps and that one name step, before any end
    /// is remembered or any enclosing walk resumes. The run ends with the host's token on both routes.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationInTheInnermostReceiver_StopsBeforePublication(bool asynchronous)
    {
        const int length = 256;
        var observations = new EvaluationObservations();
        using var cancellation = new CancellationTokenSource();
        var first = Ref("Lib") with { Properties = new CancelDuringLookup(observations, cancellation, length + 1) };
        // Read a root property before its body consults the root's opens. Its cache access captures the
        // run's budget, which the throwing entry point cannot return.
        var reader = new Property("Reader", new Algorithm.User(null, [], [], [], [new Expr.Resolve("X")]));
        var program = HostReceiverChain(length, first, [reader], read: "Reader");
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();

        OperationCanceledException cancelled;
        if (asynchronous)
        {
            cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: cache, observations: observations,
                cancellationToken: cancellation.Token));
        }
        else
        {
            cancelled = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(
                program, zeroArgPropertyResultCache: cache, observations: observations,
                cancellationToken: cancellation.Token));
        }

        Assert.Equal(cancellation.Token, cancelled.CancellationToken);
        Assert.Equal(length + 1, observations.OpenStructureStepCount);
        var run = Assert.IsType<EvaluationBudget>(cache.ObservedBudget);
        Assert.Equal(asynchronous, run.IsAsynchronousRun);
        Assert.Empty(run.OpenStructureEnds);
    }
}
