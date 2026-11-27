using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

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

    private sealed class CancelDuringLookup(EvaluationObservations observations, CancellationTokenSource source)
        : IReadOnlyList<Property>
    {
        public int Count
        {
            get
            {
                if (observations.OpenStructureStepCount > 0) source.Cancel();
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
}
