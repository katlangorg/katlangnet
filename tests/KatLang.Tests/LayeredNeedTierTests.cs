using System.Reflection;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.TestInfrastructure;
using KatLang.Tests.AsyncEvaluation;
using KatLang.Tests.InvocationRoute;
using NeedEnv = System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Evaluation.NeedCell Cell)>;

namespace KatLang.Tests;

/// <summary>
/// NARROW BOUNDARIES OVER WIDE INHERITED TIERS (2026-11-24, follow-up of the wide-binding report of 2026-11-23). Every
/// binding boundary mints its callee's need tier as Lean's <c>needBindingContext</c>: the callee's own cells, then the
/// inherited tier with the callee's names shadowed out. A narrow call under a wide caller copied that wide tier twice
/// (the shadow filter, then the prepend) and its activation scanned the copy, so a wide loop step whose N rows each
/// call a one-parameter helper allocated about 35 MB per round at N = 1,024. Now a boundary of fewer than
/// <see cref="Evaluator.MinimumIndexedParameterCount"/> cells and names over a wide tier the evaluator made mints a
/// <see cref="Evaluator.LayeredBoundNeedEnv"/>: its cells, the base tier it shares, and the names hidden from it.
/// Implementation-only: these tests pin the layer against the flat list it stands for — lookup for lookup on random
/// boundary chains with repeated, null and shadowed names, its composition and limits, activation captures and
/// shadow filters that never build its flat list — the conditions under which a boundary still copies (narrow tiers,
/// host-built lists and their later edits, wide boundaries), the planner's shadowed step tier, the caller-tier reads
/// per call, the absence of retention chains, and whole programs (direct, same-name, callback, recursive, mutual,
/// chained beyond the limit, clause, zero-argument, captured-ancestor, free host-parameter, looped and handed-over
/// calls, per-invocation inner properties and aliases) on the plain, counted generic, optimized, plan-retaining and
/// async routes.
/// </summary>
public class LayeredNeedTierTests
{
    private const int Wide = Evaluator.MinimumIndexedParameterCount;

    private delegate NeedEnv Minter(NeedEnv bindings, NeedEnv inherited, IReadOnlyList<string> names);

    private delegate NeedCell? NeedLookup(NeedEnv env, string name);

    private delegate Evaluator.EvalCtx WithBindings(Evaluator.EvalCtx ctx, NeedEnv bindings, IReadOnlyList<string> names);

    private static T Private<T>(string name) where T : Delegate
        => typeof(Evaluator).GetMethod(name, BindingFlags.NonPublic | BindingFlags.Static)!.CreateDelegate<T>();

    private static readonly Minter Mint = Private<Minter>("MintNeedBindingContext");
    private static readonly NeedLookup LookupNeed = Private<NeedLookup>("LookupNeed");
    private static readonly WithBindings WithNeedBindings = Private<WithBindings>("WithNeedBindings");

    private static NeedCell Cell(int value) => NeedCell.Ready(new(new Result.Atom(value), 1));

    private static string[] Names(string prefix, int count) => Enumerable.Range(0, count).Select(i => prefix + i).ToArray();

    private static (string Name, NeedCell Cell)[] Bound(IEnumerable<string> names, int seed = 0)
        => names.Select((name, i) => (name, Cell(seed + i))).ToArray();

    private static Evaluator.EvalCtx With(NeedEnv tier) => Evaluator.EvalCtx.Empty.WithNeedEnv(tier);

    // ── The flat list a boundary stands for (Lean needBindingContext) ──────────────────────────────

    private static List<(string Name, NeedCell Cell)> Shadow(IEnumerable<(string Name, NeedCell Cell)> tier, IReadOnlyList<string> names)
        => tier.Where(binding => !names.Contains(binding.Name, StringComparer.Ordinal)).ToList();

    private static List<(string Name, NeedCell Cell)> Boundary(NeedEnv own, IEnumerable<(string Name, NeedCell Cell)> inherited, IReadOnlyList<string> names)
        => [.. own, .. Shadow(inherited, names)];

    private static NeedCell? Linear(IEnumerable<(string Name, NeedCell Cell)> env, string name)
    {
        foreach (var (n, cell) in env)
            if (string.Equals(n, name, StringComparison.Ordinal)) return cell;
        return null;
    }

    private static List<(string Name, NeedCell Cell)> FirstOwned(IEnumerable<(string Name, NeedCell Cell)> env, IReadOnlyList<string> names)
    {
        var kept = new List<(string Name, NeedCell Cell)>();
        foreach (var binding in env)
            if (names.Contains(binding.Name, StringComparer.Ordinal) && !kept.Any(k => string.Equals(k.Name, binding.Name, StringComparison.Ordinal)))
                kept.Add(binding);
        return kept;
    }

    // A wide tier as a wide call mints it: its own cells, then an inherited part with a repeated name and a null.
    private static NeedEnv WideMintedTier(int width)
        => Evaluator.Concat(Bound(Names("p", width)), [("outer", Cell(-1)), ("p1", Cell(-2)), ("outer", Cell(-3)), (null!, Cell(-4)), ("x0", Cell(-5))]);

    // ── The layer against the flat list ─────────────────────────────────────────────────────────────

    public static TheoryData<int> Seeds => new() { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 };

    [Theory]
    [MemberData(nameof(Seeds))]
    public void ALayeredTier_IsTheFlatBoundaryList_ReadForRead_OnRandomBoundaryChains(int seed)
    {
        var random = new Random(7919 * seed);
        var width = new[] { Wide, Wide + 1, 64, 300 }[seed % 4];
        NeedEnv tier = WideMintedTier(width);
        List<(string Name, NeedCell Cell)> oracle = [.. tier];
        string[] pool = ["p0", "p1", "p2", "p" + (width - 1), "outer", "x0", "x1", "x2", "y", "z", null!, ""];
        var layers = 0;
        for (var step = 0; step < 80; step++)
        {
            // A boundary: mostly narrow, sometimes at the limit's edge; its own cells are its distinct names, in order,
            // as a binder binds them — occasionally with one name left unbound, which hides it all the same.
            var count = random.Next(12) == 0 ? random.Next(Wide - 2, Wide + 2) : random.Next(5);
            var names = Enumerable.Range(0, count).Select(_ => random.Next(4) == 0 ? "n" + random.Next(60) : pool[random.Next(pool.Length)]).ToArray();
            var own = names.Distinct(StringComparer.Ordinal).Where(_ => random.Next(8) != 0).Select(n => (n, Cell(1000 * step + random.Next(1000)))).ToArray();
            var parent = tier;
            var minted = Mint(own, parent, names);
            var expected = Boundary(own, oracle, names);
            Assert.NotSame(parent, minted);
            AssertShape(parent, own, names, minted);

            // Reads before anything enumerates the tier: lookups, an activation's capture, the shadow filter.
            var probes = pool.Concat(names).Concat(expected.Select(b => b.Name)).Append("missing").Distinct().ToArray();
            foreach (var probe in probes)
                Assert.Same(Linear(expected, probe), LookupNeed(minted, probe));
            if (names.Length < Wide)
                Assert.Equal(FirstOwned(expected, names), ParameterActivation.Capture(names, With(minted), []).Needs);
            var hidden = random.Next(3) == 0 ? Names("w", Wide + 3).Concat(pool).ToArray() : pool.Where(_ => random.Next(2) == 0).ToArray();
            Assert.Equal(Shadow(expected, hidden), Evaluator.ShadowInheritedParameterEnvironments(With(minted), hidden).NeedEnv);
            Assert.Same(minted, Evaluator.BindingContextIdentity(With(minted), [("v", new Result.Atom(1))]));
            if (minted is Evaluator.LayeredBoundNeedEnv layered)
            {
                layers++;
                Assert.False(layered.IsMaterialized, "lookups, captures and shadow filters read the parts");
                // A capture for other names: a copy of the boundary's names still reads the prefix alone; names the
                // layer does not shadow have their first bindings in the base, so the capture reads the whole tier.
                var copy = names.ToArray();
                if (copy.Length < Wide)
                {
                    Assert.Equal(FirstOwned(expected, copy), ParameterActivation.Capture(copy, With(minted), []).Needs);
                    Assert.False(layered.IsMaterialized);
                }
                string[] other = [.. names.Take(1), "p2", "outer", "x1"];
                Assert.Equal(FirstOwned(expected, other), ParameterActivation.Capture(other, With(minted), []).Needs);
            }

            // The tier IS the flat list.
            Assert.Equal(expected.Count, minted.Count);
            Assert.Equal(expected, minted);
            Assert.Equal(expected, Enumerable.Range(0, minted.Count).Select(i => minted[i]));
            foreach (var probe in probes)
                Assert.Same(Linear(expected, probe), LookupNeed(minted, probe));

            tier = minted;
            oracle = expected;
        }

        Assert.True(layers > 40, $"the chains layered only {layers} of 80 boundaries");
    }

    // The representation a boundary chose: a layer exactly when it is narrow and inherits a layer it can compose with or
    // a wide tier the evaluator made; a layer's base is never a layer and is its parent's base, or its parent.
    private static void AssertShape(NeedEnv parent, NeedEnv own, IReadOnlyList<string> names, NeedEnv minted)
    {
        var narrow = own.Count < Wide && names.Count < Wide;
        switch (parent)
        {
            case Evaluator.LayeredBoundNeedEnv parentLayer when narrow:
            {
                List<(string Name, NeedCell Cell)> prefix = [.. own, .. Shadow(parentLayer.Prefix, names)];
                var shadowed = parentLayer.ShadowedNames;
                var added = new List<string>();
                foreach (var name in names)
                    if (!shadowed.Contains(name, StringComparer.Ordinal) && !added.Contains(name, StringComparer.Ordinal))
                        added.Add(name);
                if (prefix.Count >= Wide || shadowed.Count + added.Count >= Wide)
                {
                    Assert.IsType<Evaluator.BoundNeedEnv>(minted);
                    return;
                }

                var layer = Assert.IsType<Evaluator.LayeredBoundNeedEnv>(minted);
                Assert.Same(parentLayer.Base, layer.Base);
                Assert.Equal(prefix, layer.Prefix);
                Assert.Equal([.. shadowed, .. added], layer.ShadowedNames);
                if (added.Count == 0)
                    Assert.Same(shadowed, layer.ShadowedNames);
                return;
            }
            case Evaluator.BoundNeedEnv or Evaluator.ShadowedNeedEnv when narrow && parent.Count >= Wide:
            {
                var layer = Assert.IsType<Evaluator.LayeredBoundNeedEnv>(minted);
                Assert.Same(parent, layer.Base);
                Assert.Same(own, layer.Prefix);
                Assert.Same(names, layer.ShadowedNames);
                return;
            }
            default:
                Assert.IsAssignableFrom<Evaluator.BoundNeedEnv>(minted);
                Assert.Equal(own.Count >= Wide, minted is Evaluator.WideBoundNeedEnv);
                return;
        }
    }

    [Fact]
    public void ACalleesNames_HideEveryInheritedBindingOfThem_EvenOneItDoesNotBind()
    {
        // The same-name negative control of the structure: the base binds p1 and p5 (p5 twice); the boundary's names
        // are p5 and p1, but it binds only p1. Neither of the base's bindings of p5 may stay visible — the flat list
        // has none — while the base itself keeps them; a nested boundary keeps them hidden, and one that binds p5
        // again answers with its own cell.
        var baseTier = Evaluator.Concat(Bound(Names("p", 40)), [("p5", Cell(-5)), ("q", Cell(-6))]);
        var p1 = Cell(101);
        string[] names = ["p5", "p1"];
        var layer = Assert.IsType<Evaluator.LayeredBoundNeedEnv>(Mint([("p1", p1)], baseTier, names));
        Assert.Null(LookupNeed(layer, "p5"));
        Assert.Same(p1, LookupNeed(layer, "p1"));
        Assert.Same(Linear(baseTier, "p6"), LookupNeed(layer, "p6"));
        Assert.NotNull(LookupNeed(baseTier, "p5"));
        Assert.Equal(Boundary([("p1", p1)], baseTier, names), layer);
        Assert.DoesNotContain(layer, binding => binding.Name == "p5");

        var x = Cell(102);
        var nested = Assert.IsType<Evaluator.LayeredBoundNeedEnv>(Mint([("x", x)], layer, ["x"]));
        Assert.Null(LookupNeed(nested, "p5"));
        Assert.Same(p1, LookupNeed(nested, "p1"));
        Assert.Same(x, LookupNeed(nested, "x"));
        Assert.Equal(Boundary([("x", x)], layer.ToList(), ["x"]), nested);

        var p5 = Cell(103);
        var rebinding = Assert.IsType<Evaluator.LayeredBoundNeedEnv>(Mint([("p5", p5)], nested, ["p5"]));
        Assert.Same(p5, LookupNeed(rebinding, "p5"));
        Assert.Single(rebinding, binding => binding.Name == "p5");
    }

    [Fact]
    public void ALayer_IsMintedOnlyByANarrowBoundary_OverAWideTierTheEvaluatorMade()
    {
        NeedEnv own = [("x", Cell(1))];
        string[] names = ["x"];

        // Narrow tiers are copied as before, from the threshold on a minted tier is layered.
        Assert.IsType<Evaluator.BoundNeedEnv>(Mint(own, Evaluator.Concat(Bound(Names("p", Wide - 1)), []), names));
        Assert.IsType<Evaluator.LayeredBoundNeedEnv>(Mint(own, Evaluator.Concat(Bound(Names("p", Wide)), []), names));
        Assert.IsType<Evaluator.LayeredBoundNeedEnv>(Mint(own, Evaluator.Concat([], Bound(Names("p", Wide))), names));

        // A wide boundary keeps the flat tier: wide by its own cells, or by its names.
        Assert.IsType<Evaluator.WideBoundNeedEnv>(Mint(Bound(Names("q", Wide)), WideMintedTier(64), Names("q", Wide)));
        Assert.IsType<Evaluator.BoundNeedEnv>(Mint(own, WideMintedTier(64), [.. names, .. Names("q", Wide - 1)]));

        // An activation's captured cells and a host-built list are never a base, however wide.
        var captured = ParameterActivation.Capture(Names("p", 64), With(WideMintedTier(64)), []).Needs;
        Assert.IsType<OwnedNeedBindings>(captured);
        Assert.IsType<Evaluator.BoundNeedEnv>(Mint(own, captured, names));
        Assert.IsType<Evaluator.BoundNeedEnv>(Mint(own, Bound(Names("p", 300)), names));

        // HOST-LIST FRESHNESS: a tier minted over a host list is a snapshot, so a later edit of the list cannot reach it.
        var host = new List<(string Name, NeedCell Cell)>(Bound(Names("p", 300)));
        var original = host[3].Cell;
        var minted = Mint(own, host, names);
        var snapshot = minted.ToList();
        host[3] = ("p3", Cell(-99));
        host.Add(("late", Cell(-100)));
        host.RemoveAt(0);
        Assert.Equal(snapshot, minted);
        Assert.Same(original, LookupNeed(minted, "p3"));
        Assert.Null(LookupNeed(minted, "late"));
        Assert.NotNull(LookupNeed(minted, "p0"));

        // The planner's wide shadowed step tier is the evaluator's, so a round's boundary layers over it.
        var shadowed = Evaluator.ShadowInheritedParameterEnvironments(With(WideMintedTier(64)), ["y"]).NeedEnv;
        Assert.IsType<Evaluator.ShadowedNeedEnv>(shadowed);
        Assert.Same(shadowed, Assert.IsType<Evaluator.LayeredBoundNeedEnv>(Mint([("y", Cell(2))], shadowed, ["y"])).Base);
    }

    [Fact]
    public void ThePlannersShadowedStepTier_KeepsItsBindingsAndItsIdentityRule()
    {
        // ShadowInheritedParameterEnvironments is the loop planner's step context: the filtered bindings, held as a
        // ShadowedNeedEnv from the wide threshold on. Its binding identity is the rule every tier below no boundary
        // follows — the tier itself when nonempty, the value environment's identity when empty.
        IReadOnlyList<(string Name, Result Value)> values = [("v", new Result.Atom(1))];
        var wide = WideMintedTier(40);
        var kept = Evaluator.ShadowInheritedParameterEnvironments(With(wide), ["p0", "outer"]).NeedEnv;
        Assert.IsType<Evaluator.ShadowedNeedEnv>(kept);
        Assert.Equal(Shadow(wide, ["p0", "outer"]), kept);
        Assert.Same(kept, Evaluator.BindingContextIdentity(With(kept), values));
        Assert.NotSame(kept, Evaluator.ShadowInheritedParameterEnvironments(With(wide), ["p0", "outer"]).NeedEnv);

        var narrow = Evaluator.Concat(Bound(Names("p", Wide)), []);
        var below = Evaluator.ShadowInheritedParameterEnvironments(With(narrow), ["p0"]).NeedEnv;
        Assert.IsType<(string Name, NeedCell Cell)[]>(below);
        Assert.Equal(Wide - 1, below.Count);

        var none = Evaluator.ShadowInheritedParameterEnvironments(With(Evaluator.Concat(Bound(["y"]), [])), ["y"]).NeedEnv;
        Assert.Empty(none);
        Assert.Same(values, Evaluator.BindingContextIdentity(With(none), values));

        // Over a layer the filter reads the layer's parts, never its flat list.
        var layer = Assert.IsType<Evaluator.LayeredBoundNeedEnv>(Mint([("x", Cell(5))], wide, ["x"]));
        var filtered = Evaluator.ShadowInheritedParameterEnvironments(With(layer), ["p1"]).NeedEnv;
        Assert.False(layer.IsMaterialized);
        Assert.IsType<Evaluator.ShadowedNeedEnv>(filtered);
        Assert.Equal(Shadow(layer.ToList(), ["p1"]), filtered);
    }

    // ── Work and retention ──────────────────────────────────────────────────────────────────────────

    // A minted tier whose reads through the environment interface are counted: every consumer that reads the caller's
    // tier as a NeedEnv — the shadow filter, the prepend, the capture, a lookup — is observed.
    private sealed class CountingTier : Evaluator.BoundNeedEnv, IReadOnlyList<(string Name, NeedCell Cell)>
    {
        public long Reads;

        public CountingTier(NeedEnv own)
            : base(own, [])
        {
        }

        (string Name, NeedCell Cell) IReadOnlyList<(string Name, NeedCell Cell)>.this[int index]
        {
            get
            {
                Reads++;
                return this[index];
            }
        }

        IEnumerator<(string Name, NeedCell Cell)> IEnumerable<(string Name, NeedCell Cell)>.GetEnumerator()
        {
            for (var i = 0; i < Count; i++)
            {
                Reads++;
                yield return this[i];
            }
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator()
            => ((IEnumerable<(string Name, NeedCell Cell)>)this).GetEnumerator();
    }

    public static TheoryData<int> CallerWidths => new() { Wide - 1, Wide, 64, 1024, 4096 };

    [Theory]
    [MemberData(nameof(CallerWidths))]
    public void ANarrowCall_ReadsNoBindingOfItsWideCallersTier_AtAnyWidthOrCallCount(int width)
    {
        // One narrow call H(x) — its boundary, its body entry (the activation's capture) and a read of x — K times under
        // a caller tier of `width` cells, and a chain of five nested narrow calls under it. Before, each call read the
        // caller's tier 3 × width times (two filter passes, one of them twice per kept binding); a tier below the
        // threshold still does, by design. A lookup of a caller name through a layer reads what the caller's own
        // lookup reads.
        var caller = new CountingTier(Bound(Names("p", width)));
        var callee = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Param("x")]);
        foreach (var calls in new[] { 1, 10, 100 })
        {
            caller.Reads = 0;
            for (var call = 0; call < calls; call++)
            {
                var names = callee.Params;
                var x = Cell(call);
                var entered = Evaluator.EnterAlgorithmBody(callee, WithNeedBindings(With(caller), [("x", x)], names), [], names, invoked: true);
                Assert.Same(x, LookupNeed(entered.NeedEnv, "x"));
                Assert.Same(x, Evaluator.ParameterNeedCell("x", entered));
            }

            Assert.Equal(width >= Wide ? 0 : 3L * width * calls, caller.Reads);
        }

        // Five nested calls: only the first one's boundary can read the caller's tier, and only when it copies it.
        caller.Reads = 0;
        NeedEnv tier = caller;
        for (var level = 0; level < 5; level++)
            tier = WithNeedBindings(With(tier), [("a" + level, Cell(level))], ["a" + level]).NeedEnv;
        Assert.Equal(width >= Wide ? 0 : 3L * width, caller.Reads);
        if (width < Wide)
            return;

        var deep = Assert.IsType<Evaluator.LayeredBoundNeedEnv>(tier);
        Assert.Same(caller, deep.Base);
        var last = caller[width - 1].Cell;
        caller.Reads = 0;
        Assert.Same(last, LookupNeed(deep, "p" + (width - 1)));
        Assert.Equal(width, caller.Reads);
    }

    [Fact]
    public void ALayer_RetainsOneBase_AndNoOtherLayer_HoweverDeepItsBoundaries()
    {
        // A recursion re-binding one name and a chain of distinct names, each 200 boundaries deep: every layer shares
        // the one base and references no other layer, so the layers above the deepest are collectable while it lives.
        foreach (var distinct in new[] { false, true })
        {
            var (deepest, baseTier, above) = DeepLayers(distinct);
            GC.Collect();
            GC.WaitForPendingFinalizers();
            GC.Collect();
            Assert.All(above, weak => Assert.False(weak.IsAlive, "a layer kept another layer alive"));
            Assert.IsNotType<Evaluator.LayeredBoundNeedEnv>(deepest.Base);
            Assert.True(baseTier.IsAlive);
            Assert.Same(baseTier.Target, deepest.Base);
            Assert.True(deepest.Prefix.Count < Wide && deepest.ShadowedNames.Count < Wide);
            if (!distinct)
                Assert.Equal(["j"], deepest.ShadowedNames);
            GC.KeepAlive(deepest);
        }
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (Evaluator.LayeredBoundNeedEnv Deepest, WeakReference Base, List<WeakReference> Above) DeepLayers(bool distinct)
    {
        NeedEnv tier = WideMintedTier(64);
        var above = new List<WeakReference>();
        for (var level = 0; level < 200; level++)
        {
            var name = distinct ? "a" + level : "j";
            var minted = Mint([(name, Cell(level))], tier, [name]);
            if (tier is Evaluator.LayeredBoundNeedEnv)
                above.Add(new WeakReference(tier));
            tier = minted;
        }

        var deepest = Assert.IsType<Evaluator.LayeredBoundNeedEnv>(tier);
        return (deepest, new WeakReference(deepest.Base), above);
    }

    // ── Programs on every route ─────────────────────────────────────────────────────────────────────

    private static string Describe((EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) run)
    {
        var (result, budget) = run;
        var outcome = result.IsOk
            ? $"ok {InvocationRouteCorpus.Value(result.Value.Value)} n={result.Value.EmittedCount}"
            : $"err {result.Error.Code} | {KatLangError.FromEvalError(result.Error).Message.Replace("\n", " / ", StringComparison.Ordinal)} @{result.Error.Span}";
        return $"{outcome}\tsteps={budget.ConsumedSteps}\tcheckpoints={budget.ConsumedExpressionCheckpoints}\titems={budget.MaterializedItems}";
    }

    /// <summary>
    /// The plain value entry, the counted generic and optimized routes, the optimized route of a run that retains
    /// invocation plans, and the async twin: they agree on the outcome, steps, checkpoints and materialized items.
    /// </summary>
    private static async Task<string> ObserveAllRoutes(Func<Expr> build)
    {
        var plain = Evaluator.Run(build(), new RunScopedZeroArgPropertyResultCache(), enableLoopOptimization: true, loopDiagnostics: null,
            enableSequencePipelineOptimization: true, sequenceDiagnostics: null);
        var generic = Describe(Evaluator.RunCountedObserved(build(), enableOptimizations: false));
        var optimized = Describe(Evaluator.RunCountedObserved(build(), enableOptimizations: true));
        string planned;
        using (InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()))
            planned = Describe(Evaluator.RunCountedObserved(build(), enableOptimizations: true));
        var twin = Describe(await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            build(), zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache())));
        Assert.Equal(generic, optimized);
        Assert.Equal(generic, planned);
        Assert.Equal(generic, twin);
        Assert.Equal(generic.StartsWith("ok ", StringComparison.Ordinal), plain.IsOk);
        if (plain.IsOk)
            Assert.StartsWith($"ok {InvocationRouteCorpus.Value(plain.Value)} n=", generic, StringComparison.Ordinal);
        return generic;
    }

    private static Task<string> ObserveSource(string source)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        return ObserveAllRoutes(() => new Expr.AlgorithmExpr(root));
    }

    private static string List(string prefix, int from, int to) => string.Join(", ", Enumerable.Range(from, to - from + 1).Select(i => prefix + i));

    private static string Chain(string name, int depth)
        => string.Concat(Enumerable.Range(1, depth - 1).Select(level => $"{name}{level}({name.ToLowerInvariant()}{level}) = {name}{level + 1}({name.ToLowerInvariant()}{level}) + 1\n"))
            + $"{name}{depth}({name.ToLowerInvariant()}{depth}) = {name.ToLowerInvariant()}{depth}\n";

    public static TheoryData<int> ProgramWidths => new() { 4, Wide - 1, Wide, Wide + 1, 64, 300 };

    [Theory]
    [MemberData(nameof(ProgramWidths))]
    public async Task NarrowCallsUnderAWideFrame_KeepTheirValues_OnAllRoutes(int width)
    {
        // Each row of W is a narrow call (or calls) under W's tier of `width` cells: direct, same-name (S's own p1 is
        // not W's), callback, recursion, mutual recursion, a chain of 6 and one of 40 nested callees (which crosses the
        // layer limit), a clause family, zero-argument calls, a loop step planned whole and one the planner cannot
        // plan, a callee declared in W reading W's captured parameter, and the wide control V forwarding W's frame.
        var m = Math.Min(7, width);
        var source = "H(x) = x * 2\n"
            + "S(p1) = p1 * 3\n"
            + "R(j) = if(j == 0, 0, R(j - 1) + 1)\n"
            + "A(a, j) = if(j == 0, a, B(a, j - 1))\n"
            + "B(b, j) = if(j == 0, b, A(b, j - 1))\n"
            + Chain("F", 6)
            + Chain("D", 40)
            + "C(0) = 100\n"
            + "C(x) = x * 5\n"
            + "G(y) = y + 1\n"
            + "K(y) = H(y)\n"
            + "Z = 7\n"
            + $"V({List("q", 1, width)}) = q1 + q{width}\n"
            + $"W({List("p", 1, width)}) = {{\n"
            + $"  I(x) = x + p{m}\n"
            + "  H(p2)\n"
            + $"  S(p{width}) + p1\n"
            + "  range(1, 4).map(H).sum\n"
            + "  R(10)\n"
            + "  A(p1, 7)\n"
            + "  F1(p2)\n"
            + "  D1(p1)\n"
            + "  C(0) + C(p2)\n"
            + "  G(p1).repeat(3)\n"
            + "  K(p1).repeat(3)\n"
            + "  Z() + Z\n"
            + $"  I(p1) + I(p{width})\n"
            + $"  V({List("p", 1, width)})\n"
            + "}\n"
            + $"W({List("", 1, width)})\n";
        var outcome = await ObserveSource(source);
        Assert.StartsWith($"ok (4, {3 * width + 1}, 20, 10, 1, 7, 40, 110, 4, 8, 14, {1 + m + width + m}, {1 + width}) n=", outcome, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(ProgramWidths))]
    public async Task AFreeHostParameterRead_SeesTheNearestUnshadowedBinding_OnAllRoutes(int width)
    {
        // A host-built parameter read that no lexical level owns reads the context's own tiers — the one place a program
        // observes what a boundary's tier holds beyond its own cells. Under W(p1..pN): H(x) reads W's p2 through its
        // boundary; K(p2) reads its own p2, and M(y) under K reads K's p2 (W's is shadowed), N(z) under M reads M's y and
        // K's p2, and U(u) under N reads a name nothing binds.
        static Expr Param(string name) => new Expr.Param(name);
        static Expr Num(int value) => new Expr.Num(value);
        static Expr Add(Expr left, Expr right) => new Expr.Binary(BinaryOp.Add, left, right);
        static Expr Mul(Expr left, Expr right) => new Expr.Binary(BinaryOp.Mul, left, right);
        static Expr Call(string callee, params Expr[] args) => new Expr.Call(new Expr.Resolve(callee), OutputBundle.TakeOwnership(args));
        static Property Def(string name, IReadOnlyList<string> parameters, params Expr[] output)
            => new(name, new Algorithm.User(null, parameters.Select(static p => (ParameterPattern)new CaptureParameterPattern(p)).ToArray(), [], [], output));

        Expr Build() => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
        [
            Def("H", ["x"], Add(Param("p2"), Mul(Param("x"), Num(1000)))),
            Def("K", ["p2"], Add(Param("p2"), Call("M", Num(7)))),
            Def("M", ["y"], Add(Add(Param("p2"), Mul(Param("y"), Num(100))), Call("N", Num(1)))),
            Def("N", ["z"], Add(Param("y"), Param("p2"))),
            Def("U", ["u"], Param("nobody")),
            Def("W", Names("p", width).Select((_, i) => "p" + (i + 1)).ToArray(),
                Call("H", Param("p1")), Call("K", Num(50)), Call("H", Param("p3")), Param("p2")),
        ],
        [Call("W", Enumerable.Range(1, width).Select(Num).ToArray()), Call("W", Enumerable.Range(1, width).Select(Num).ToArray())]));

        var outcome = await ObserveAllRoutes(Build);
        // H(p1) = 2 + 1000; K(50) = 50 + (50 + 700 + (7 + 50)); H(p3) = 2 + 3000; then W's own p2.
        Assert.StartsWith("ok ((1002, 857, 3002, 2), (1002, 857, 3002, 2)) n=", outcome, StringComparison.Ordinal);

        Expr Unbound() => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [Def("U", ["u"], Param("nobody")), Def("W", Names("p", width).Select((_, i) => "p" + (i + 1)).ToArray(), Call("U", Param("p1")))],
            [Call("W", Enumerable.Range(1, width).Select(Num).ToArray())]));
        Assert.StartsWith("err UnknownName ", await ObserveAllRoutes(Unbound), StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(ProgramWidths))]
    public async Task EachNarrowCall_OwnsItsInnerBindingsAndAliasCell_OnAllRoutes(int width)
    {
        // The two calls through A share their invocation's target selection. A fresh selection
        // chooses Hundred on the second and third invocations, even when H receives p1 again.
        var source = "Cap(meta r) = r\nTen(x) = x * 10\nHundred(x) = x * 100\n"
            + "Pick(n) = if(n == 1, Cap(Ten(0)), Cap(Hundred(0)))\n"
            + "H(x) = {\n  L = x * 10 + tick()\n  E = tick()\n  A = Pick(tick()).Algorithm\n  A(x), A(x), L + L, E + E\n}\n"
            + $"W({List("p", 1, width)}) = H(p1), H(p2), H(p1)\n"
            + $"W({List("", 1, width)})\n";
        var outcome = await ObserveSource(source);
        Assert.StartsWith("ok ((10, 10, 24, 6), (200, 200, 50, 12), (100, 100, 36, 18)) n=", outcome, StringComparison.Ordinal);

        // The bindings' keys: one binding context per call, a layer over W's tier from the threshold on, none of them
        // ever enumerated.
        foreach (var optimize in new[] { false, true })
        {
            var cache = new RecordingCache();
            var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root),
                enableOptimizations: optimize, zeroArgPropertyResultCache: cache);
            Assert.True(result.IsOk);
            Assert.Equal(3, budget.AliasBindingCells.AddedCount);
            // Compared by reference: Assert.Equal would compare the tiers as lists, building their flat lists.
            var identities = cache.EnvironmentIdentities("L");
            Assert.Equal(3, identities.Count);
            Assert.True(identities.SequenceEqual(cache.EnvironmentIdentities("E"), ReferenceEqualityComparer.Instance),
                "the exported E of each call is keyed by that call, as its local-only L is");
            AssertLayeredOverOneBase(identities, layered: width >= Wide);
        }
    }

    private static void AssertLayeredOverOneBase(IReadOnlyList<object> identities, bool layered, Type? baseType = null)
    {
        if (!layered)
        {
            Assert.All(identities, identity => Assert.IsAssignableFrom<Evaluator.BoundNeedEnv>(identity));
            return;
        }

        var layers = identities.Select(identity => Assert.IsType<Evaluator.LayeredBoundNeedEnv>(identity)).ToList();
        Assert.Single(layers.Select(layer => layer.Base).Distinct(ReferenceEqualityComparer.Instance));
        Assert.All(layers, layer => Assert.False(layer.IsMaterialized));
        Assert.All(layers, layer => Assert.IsNotType<Evaluator.LayeredBoundNeedEnv>(layer.Base));
        if (baseType is not null)
            Assert.IsType(baseType, layers[0].Base);
    }

    [Theory]
    [InlineData(4)]
    [InlineData(Wide)]
    [InlineData(300)]
    public async Task NarrowRecursionAndLoopRounds_LayerOverOneFlatBase_AndAHandoverChainsNothing(int width)
    {
        // R recurses 30 levels; G and Q loop under W — Q's row is a user call the planner cannot plan, so its planned
        // rounds bind per iteration and its local property is read through the generic cache — and T's planned round
        // emits no state, which hands its loop over to the generic rounds. Each binding's local-only property is keyed
        // by its boundary's tier: one layer per level or round, all over ONE flat base — W's tier, or for planned rounds
        // the planner's shadowed step tier — and never over another layer.
        var source = "R(j) = {\n  LR = j + 0\n  if(j == 0, LR, R(j - 1) + LR)\n}\n"
            + "G(y) = {\n  LG = y + 1\n  LG\n}\n"
            + "H(x) = x * 2\n"
            + "Q(y) = {\n  LQ = y * 2\n  H(LQ)\n}\n"
            + "Zr(x, acc) = ()\n"
            + "T(s) = {\n  LT = [s]\n  reduce(LT, Zr, 0)\n}\n"
            + $"W({List("p", 1, width)}) = R(30), G(p1).repeat(5), Q(p1).repeat(3), T(p1).repeat(3)\n"
            + $"W({List("", 1, width)})\n";
        var outcome = await ObserveSource(source);
        Assert.StartsWith("ok (465, 6, 64, ()) n=", outcome, StringComparison.Ordinal);

        foreach (var optimize in new[] { false, true })
        {
            var cache = new RecordingCache();
            var diagnostics = new LoopOptimizationDiagnostics();
            var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root),
                enableOptimizations: optimize, zeroArgPropertyResultCache: cache, loopDiagnostics: diagnostics);
            Assert.True(result.IsOk);
            var recursion = cache.EnvironmentIdentities("LR");
            Assert.Equal(31, recursion.Count);
            AssertLayeredOverOneBase(recursion, layered: width >= Wide);
            if (width >= Wide)
                Assert.All(recursion, identity => Assert.Equal(["j"], ((Evaluator.LayeredBoundNeedEnv)identity).ShadowedNames));

            // Q's rounds: over W's tier on the generic route, over the planner's shadowed step tier when planned.
            var wBase = width >= Wide ? ((Evaluator.LayeredBoundNeedEnv)recursion[0]).Base : null;
            var rounds = cache.EnvironmentIdentities("LQ");
            Assert.Equal(3, rounds.Count);
            AssertLayeredOverOneBase(rounds, layered: width >= Wide, baseType: optimize && width >= Wide ? typeof(Evaluator.ShadowedNeedEnv) : null);
            if (!optimize && wBase is not null)
                Assert.Same(wBase, ((Evaluator.LayeredBoundNeedEnv)rounds[0]).Base);

            // T's rounds after the handover are generic rounds over W's tier; no round's tier is over another layer.
            var continuation = cache.EnvironmentIdentities("LT");
            Assert.Equal(3, continuation.Count);
            Assert.All(continuation, identity => Assert.False(identity is Evaluator.LayeredBoundNeedEnv { Base: Evaluator.LayeredBoundNeedEnv }));
            if (wBase is not null)
                Assert.Equal(optimize ? 2 : 3, continuation.Count(identity => identity is Evaluator.LayeredBoundNeedEnv layer && ReferenceEquals(layer.Base, wBase)));
            if (optimize)
                Assert.True(diagnostics.FallbackReasons.ContainsKey("loop expression did not emit exactly one state value"));
            else
                Assert.Equal(5, cache.EnvironmentIdentities("LG").Count);
        }
    }

    /// <summary>Records the property executions a run asks for, and serves them from a run-scoped cache.</summary>
    private sealed class RecordingCache : IZeroArgPropertyResultCache
    {
        private readonly RunScopedZeroArgPropertyResultCache _inner = new(collectStatistics: false);
        private readonly List<ZeroArgPropertyExecution> _requests = [];

        public bool ReadObtainsPublishedValue(ZeroArgPropertyCacheKey key) => _inner.ReadObtainsPublishedValue(key);

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            _requests.Add(execution);
            return _inner.GetOrEvaluate(execution, evaluate);
        }

        public EvalResult<ZeroArgPropertyResult> Invoke(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
            => _inner.Invoke(execution, evaluate);

        // The environment components of the keys of the properties named `name`, in request order, each once.
        public IReadOnlyList<object> EnvironmentIdentities(string name)
            => _requests
                .Where(request => request.Binding.Name == name)
                .Select(request => ZeroArgPropertyCacheKey.FromExecution(request).ValueEnvironmentIdentity)
                .Distinct(ReferenceEqualityComparer.Instance)
                .ToList()!;
    }

    // ── Allocation ──────────────────────────────────────────────────────────────────────────────────

    [Fact]
    public void ANarrowCallUnderAWideFrame_AllocatesIndependentlyOfTheFramesWidth()
    {
        // Per narrow call (K-differenced: 150 − 50 calls), at widths 256 and 2,048. Before, a call under the 2,048-wide
        // frame allocated about 66 KB (two copies of the tier); now its boundary is one layer. The bounds leave room for
        // an ArrayPool refill and the counter's 8 KB quantum over the 100 differenced calls.
        long PerCall(int width)
        {
            long Bytes(int calls)
            {
                var source = "H(x) = x * 2\n"
                    + $"W({List("p", 1, width)}) = {string.Join(" + ", Enumerable.Range(0, calls).Select(i => $"H(p{i % width + 1})"))}\n"
                    + $"W({List("", 1, width)})\n";
                var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
                Assert.True(Evaluator.RunCounted(program).IsOk);
                var before = GC.GetAllocatedBytesForCurrentThread();
                var result = Evaluator.RunCounted(program);
                var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
                Assert.True(result.IsOk);
                return bytes;
            }

            return (Bytes(150) - Bytes(50)) / 100;
        }

        var narrowFrame = PerCall(256);
        var wideFrame = PerCall(2048);
        Assert.True(wideFrame < 4096, $"a narrow call under a 2,048-wide frame allocated {wideFrame} B");
        Assert.True(Math.Abs(wideFrame - narrowFrame) < 512, $"per-call bytes moved from {narrowFrame} to {wideFrame} B with the frame's width");
    }

    [Fact]
    public void ANarrowBoundaryOverAWideTier_AllocatesOneLayer_AtEveryWidth_GcIsolatedChild()
    {
        // The boundary mints one layer, whatever the width of the tier below and however deep the recursion above it;
        // a lookup through it allocates nothing, and its activation's capture allocates exactly what the capture of the
        // same cells over a narrow flat tier does.
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var layerSize = InstanceSize.Of(typeof(Evaluator.LayeredBoundNeedEnv));
        string[] names = ["x"];
        NeedEnv own = [("x", Cell(1))];
        NeedEnv rebound = [("x", Cell(2))];
        IReadOnlyList<(string Name, Result Value)> values = [];
        var narrowCtx = With(Evaluator.Concat(own, []));
        _ = ParameterActivation.Capture(names, narrowCtx, values);
        var flatCapture = Bytes(() => ParameterActivation.Capture(names, narrowCtx, values));
        foreach (var width in new[] { Wide, 256, 4096 })
        {
            var tier = WideMintedTier(width);
            _ = Mint(own, tier, names);
            Assert.Equal(layerSize, Bytes(() => Mint(own, tier, names)));
            var layer = (Evaluator.LayeredBoundNeedEnv)Mint(own, tier, names);
            _ = Mint(rebound, layer, names);
            Assert.Equal(layerSize, Bytes(() => Mint(rebound, layer, names)));
            _ = LookupNeed(layer, "x");
            _ = LookupNeed(layer, "p1");
            _ = LookupNeed(layer, "missing");
            Assert.Equal(0, Bytes(() => LookupNeed(layer, "x")));
            Assert.Equal(0, Bytes(() => LookupNeed(layer, "p1")));
            Assert.Equal(0, Bytes(() => LookupNeed(layer, "missing")));
            var layerCtx = With(layer);
            _ = ParameterActivation.Capture(names, layerCtx, values);
            Assert.Equal(flatCapture, Bytes(() => ParameterActivation.Capture(names, layerCtx, values)));
            Assert.False(layer.IsMaterialized);
        }

        GcIsolatedAllocation.Complete();
    }

    private static long Bytes(Func<object?> action)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        var result = action();
        var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
        GC.KeepAlive(result);
        return bytes;
    }
}
