using System.Reflection;
using KatLang.Evaluation;
using KatLang.TestInfrastructure;
using KatLang.Tests.InvocationRoute;

namespace KatLang.Tests;

/// <summary>
/// Brief 2.08b (PERF-ORD-1 follow-ups F0359/F0360): the ONE inspecting binder binds a flat level of
/// two to <see cref="Evaluator.FlatUniqueNameBindingWidth"/> unique plain names directly
/// (<c>FlatUniqueNameBindings</c>), and the call path forms its supply, a builtin's resolved arguments
/// and a callback's supply without an iterator, closure, delegate or LINQ chain. These are
/// implementation-only optimizations: every program keeps its value, error and resource profile on
/// the three engines, every other pattern level (a repeated name, a collecting capture, META, a
/// structural pattern, a literal head) keeps the general path's own rule, and the environment is a
/// fresh array in written order. The strict allocation counts run in isolated child processes.
/// </summary>
public class OrdinaryCallBindingAllocationTests
{
    private delegate ValueTask<EvalResult<IReadOnlyList<(string Name, NeedCell Cell)>?>> BindAccepted(
        IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply, Evaluator.EvalCtx ctx,
        bool asynchronous, bool family, IReadOnlyList<Expr?>? occurrences);

    private delegate ValueTask<EvalResult<IReadOnlyList<Evaluator.ResolvedArgumentAlgorithm>>> ResolveSupply(
        OutputBundle args, Evaluator.EvalCtx ctx, IReadOnlyList<(string Name, Result Value)> values, bool asynchronous);

    private delegate ValueTask<EvalResult<IReadOnlyList<NeedCell>>> FormSupply(
        OutputBundle arguments, Evaluator.EvalCtx caller, IReadOnlyList<(string Name, Result Value)> values, bool asynchronous, List<Expr?>? sources);

    private delegate ValueTask<EvalResult<Evaluator.CountedResult>> CallbackBody(
        Algorithm callee, IReadOnlyList<Evaluator.CountedResult> arguments, Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> values, string name, bool asynchronous);

    private delegate EvalResult<Evaluator.CountedResult> ApplyResolved(
        BuiltinId builtin, IReadOnlyList<Evaluator.ResolvedArgumentAlgorithm> resolvedArgs, Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> valEnv);

    private static T Private<T>(string name) where T : Delegate
        => typeof(Evaluator).GetMethod(name, BindingFlags.NonPublic | BindingFlags.Static)!.CreateDelegate<T>();

    private static readonly BindAccepted Bind = Private<BindAccepted>("BindAcceptedNeedPatterns");

    private static NeedCell Cell(int value) => NeedCell.Ready(new(new Result.Atom(value), 1));

    private static Evaluator.NeedPattern[] Names(params string[] names)
        => names.Select(static name => new Evaluator.NeedPattern(name)).ToArray();

    // These seams select the synchronous route. Assert completion before reading the result so the
    // allocation windows stay on this thread and no test can block on a suspended operation.
    private static T CompleteSynchronously<T>(ValueTask<T> operation)
    {
        Assert.True(operation.IsCompleted, "The synchronous route must complete without suspension.");
        return operation.GetAwaiter().GetResult();
    }

    private static IReadOnlyList<(string Name, NeedCell Cell)> BindSync(IReadOnlyList<Evaluator.NeedPattern> patterns, IReadOnlyList<NeedCell> supply, Evaluator.EvalCtx ctx, bool family = false)
    {
        var bound = CompleteSynchronously(Bind(patterns, supply, ctx, false, family, null));
        Assert.True(bound.IsOk, bound.IsError ? bound.Error.ToString() : null);
        return bound.Value!;
    }

    // ── Binder-level equivalence: written order, transported cells, a fresh array ───────────────────

    public static TheoryData<int> AllWidths
    {
        get
        {
            var data = new TheoryData<int>();
            for (var width = 2; width <= 33; width++) data.Add(width);
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(AllWidths))]
    public void FlatUniqueLevel_BindsEachNameToItsCell_InWrittenOrder_FreshPerCall(int width)
    {
        // Widths up to FlatUniqueNameBindingWidth take the direct path, wider ones the general path:
        // both must return exactly (name_i, supply_i) in written order, as a fresh environment.
        var names = Enumerable.Range(0, width).Select(static i => i % 2 == 0 ? "p" + i : "P" + i).ToArray();
        var patterns = Names(names);
        var supply = Enumerable.Range(0, width).Select(Cell).ToArray();
        var ctx = Evaluator.EvalCtx.Empty;
        foreach (var family in new[] { false, true })
        {
            var first = BindSync(patterns, supply, ctx, family);
            var second = BindSync(patterns, supply, ctx, family);
            Assert.NotSame(first, second);
            Assert.Equal(width, first.Count);
            for (var i = 0; i < width; i++)
            {
                Assert.Equal(names[i], first[i].Name);
                Assert.Same(supply[i], first[i].Cell);
                Assert.Equal(first[i], second[i]);
            }
        }
    }

    [Fact]
    public void FlatUniqueLevel_NamesDifferingOnlyInCase_AreDistinct()
    {
        var supply = new[] { Cell(5), Cell(3) };
        var bound = BindSync(Names("a", "A"), supply, Evaluator.EvalCtx.Empty);
        Assert.Equal(["a", "A"], bound.Select(static b => b.Name));
        Assert.Same(supply[0], bound[0].Cell);
        Assert.Same(supply[1], bound[1].Cell);
    }

    [Fact]
    public void FlatLevel_WithARepeatedName_KeepsTheGroupAwareAgreementRule()
    {
        // A repeated name never takes the direct path: unequal VALUES refuse (Bad arity), equal ones
        // bind ONE representative, and family mode turns the refusal into a non-match.
        var ctx = Evaluator.EvalCtx.Empty;
        var refused = CompleteSynchronously(Bind(Names("x", "x"), [Cell(1), Cell(2)], ctx, false, false, null));
        Assert.True(refused.IsError);
        Assert.Equal("repeated parameter 'x' requires equal arguments: Bad arity", KatLangError.FromEvalError(refused.Error).Message);
        var nonMatch = CompleteSynchronously(Bind(Names("x", "y", "x"), [Cell(1), Cell(2), Cell(3)], ctx, false, true, null));
        Assert.True(nonMatch.IsOk);
        Assert.Null(nonMatch.Value);
        var agreed = BindSync(Names("x", "y", "x"), [Cell(2), Cell(3), Cell(2)], ctx);
        Assert.Equal(["x", "y"], agreed.Select(static b => b.Name));
    }

    // ── Source programs: values, errors and one resource profile on the three engines ──────────────

    private static string Width(int width)
    {
        // W(p1, …, pP) = 1 * p1 + 2 * p2 + … : every position weighs its own argument, so any
        // misbinding changes the value; W(1, …, P) = Σ i².
        var parameters = string.Join(", ", Enumerable.Range(1, width).Select(static i => "p" + i));
        var body = string.Join(" + ", Enumerable.Range(1, width).Select(static i => i + " * p" + i));
        var arguments = string.Join(", ", Enumerable.Range(1, width));
        return $"Wide({parameters}) = {body}\nWide({arguments})";
    }

    public static TheoryData<string, string, bool> Programs
    {
        get
        {
            var data = new TheoryData<string, string, bool>
            {
                // The brief's programs (Add, Inc and Id come from the corpus library).
                { "Add(1, 2)", "ok 3", true },
                { "W(a, b, c, d, e, f, g, h, i) = a + b + c + d + e + f + g + h + i\nW(1, 2, 3, 4, 5, 6, 7, 8, 9)", "ok 45", true },
                { "W(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17) = p1 + p17\nW(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17)", "ok 18", true },
                { "C(a, A) = a - A\nC(5, 3)", "ok 2", true },
                { "Same(x, x) = x\nSame(1, 1)", "ok 1", true },
                { "Same(x, x) = x\nSame(1, 2)", "err ArityMismatch | while evaluating call to Same: repeated parameter 'x' requires equal arguments: Bad arity @[24:1, 24:11)", true },
                { "Tri(x, y, x) = x + y\nTri(2, 3, 2)", "ok 5", true },
                { "Head(a, *rest) = a + rest.count\nHead(5, 6, 7)", "ok 7", true },
                { "Cnt(*xs) = xs.count\nCnt(1, 2, 3)", "ok 3", true },
                { "P((a, b)) = a + b\nP((1, 2))", "ok 3", true },
                { "Pair(meta op, k) = op.Arguments.count + k\nPair(Inc(1), 10)", "ok 11", false },
                { "[1, 2, 3].reduce(Add, 0)", "ok 6", true },
                { "range(1, 5).map(Inc)", "ok [2, 3, 4, 5, 6]", true },
                { "Abs(x) = if(x < 0, -x, x)\nAbs(-3) + Abs(2)", "ok 5", true },
                { "G(0, y) = y\nG(x, y) = x + y\nG(0, 5), G(2, 3)", "ok (5, 5)", true },
                // Order-sensitive two-name bodies: a swap would change every value (reduce passes the
                // item, then the accumulator: Sub(1, 3) = 13, Sub(2, 13) = 33).
                { "Sub(a, b) = a * 10 + b\nSub(1, 2), Sub(2, 1)", "ok (12, 21)", true },
                { "Sub(a, b) = a * 10 + b\n[1, 2].reduce(Sub, 3)", "ok 33", true },
                { LoopWhile, "ok (21, 34)", false },
                { LoopRepeat, "ok (5, 8)", false },
                // A flat unique head whose argument fails keeps the call's failure, demanded by the body.
                { "Sub(a, b) = a * 10 + b\nSub(1, [1][5])", "err BadIndex | while evaluating call to Sub: Bad index @[24:12, 24:13)", true },
            };
            for (var width = 2; width <= 33; width++)
            {
                var expected = Enumerable.Range(1, width).Sum(static i => i * i);
                data.Add(Width(width), "ok " + expected, true);
            }
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task Program_HasThePinnedOutcome_AndOneResourceProfile_OnAllEngines(string source, string expected, bool plainToo)
    {
        foreach (var plain in plainToo ? new[] { true, false } : [false])
        {
            var c = new InvocationRouteCorpus.Case("BIND-ALLOC", source, Plain: plain);
            var generic = await InvocationRouteCorpus.Observe(c, 0);
            Assert.Equal(expected, generic.Outcome);
            var optimized = await InvocationRouteCorpus.Observe(c, 1);
            var asynchronous = await InvocationRouteCorpus.Observe(c, 2);
            Assert.Equal(generic.Semantic, optimized.Semantic);
            Assert.Equal(generic.Semantic, asynchronous.Semantic);
            Assert.Equal(generic.Plans, optimized.Plans);
            Assert.Equal(generic.Plans, asynchronous.Plans);
            Assert.Equal(generic.Formations, optimized.Formations);
            Assert.Equal(generic.Formations, asynchronous.Formations);
            if (source is not (LoopWhile or LoopRepeat))
            {
                Assert.Equal((0L, 0L), (generic.Loops, generic.LoopFallbacks));
                Assert.Equal((0L, 0L), (optimized.Loops, optimized.LoopFallbacks));
                Assert.Equal((0L, 0L), (asynchronous.Loops, asynchronous.LoopFallbacks));
            }
        }
    }

    private const string LoopWhile = "Step2(a, b) = b, a + b, a < 20\nStep2(0, 1).while";
    private const string LoopRepeat = "Step2(a, b) = b, a + b\nStep2(0, 1).repeat(5)";

    // Each engine's own loop counters for a two-parameter step, as measured before the direct path
    // existed: the generic evaluator records one fallback, the optimizer plans the loop once, and
    // the async engine runs no optimizer; every engine charges the same steps and checkpoints.
    [Theory]
    [InlineData(LoopWhile, 0, 9, 113, 0, 1)]
    [InlineData(LoopWhile, 1, 9, 113, 1, 0)]
    [InlineData(LoopWhile, 2, 9, 113, 0, 0)]
    [InlineData(LoopRepeat, 0, 5, 39, 0, 1)]
    [InlineData(LoopRepeat, 1, 5, 39, 1, 0)]
    [InlineData(LoopRepeat, 2, 5, 39, 0, 0)]
    public async Task TwoParameterLoopStep_KeepsItsPinnedCounters(string source, int mode, long steps, long checkpoints, long loops, long fallbacks)
    {
        var observed = await InvocationRouteCorpus.Observe(new InvocationRouteCorpus.Case("BIND-ALLOC", source), mode);
        Assert.Equal((steps, checkpoints, loops, fallbacks, 1L, 1L),
            (observed.Steps, observed.Checkpoints, observed.Loops, observed.LoopFallbacks, observed.Plans, observed.Formations));
    }

    // ── A two-parameter generic loop step: a fresh environment per iteration, written order ─────────

    private sealed class RecordingCache : KatLang.Evaluation.Caching.IZeroArgPropertyResultCache
    {
        private readonly KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache inner = new();

        public bool ReadObtainsPublishedValue(KatLang.Evaluation.Caching.ZeroArgPropertyCacheKey key) => inner.ReadObtainsPublishedValue(key);

        public List<KatLang.Evaluation.Caching.ZeroArgPropertyExecution> Requests { get; } = [];

        public EvalResult<KatLang.Evaluation.Caching.ZeroArgPropertyResult> GetOrEvaluate(
            KatLang.Evaluation.Caching.ZeroArgPropertyExecution execution,
            Func<EvalResult<KatLang.Evaluation.Caching.ZeroArgPropertyResult>> evaluate)
        {
            Requests.Add(execution);
            return inner.GetOrEvaluate(execution, evaluate);
        }

        public EvalResult<KatLang.Evaluation.Caching.ZeroArgPropertyResult> Invoke(
            KatLang.Evaluation.Caching.ZeroArgPropertyExecution execution,
            Func<EvalResult<KatLang.Evaluation.Caching.ZeroArgPropertyResult>> evaluate)
            => inner.Invoke(execution, evaluate);
    }

    [Fact]
    public void GenericRepeat_TwoParameterStep_GetsAFreshEnvironment_EveryIteration_InWrittenOrder()
    {
        // (a, b) → (a * 10 + b, b + 1): a swapped binding would give a different state at once.
        var cache = new RecordingCache();
        var observations = new EvaluationObservations();
        var (result, _) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid("Step(a, b) = { Val = a * 10 + b\nVal, b + 1 }\nStep(0, 1).repeat(3)").Root),
            enableOptimizations: false,
            zeroArgPropertyResultCache: cache,
            observations: observations);

        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([123m, 4m], result.Value.Value.ToAtoms());
        var requests = cache.Requests.Where(static request => request.Binding.Name == "Val").ToList();
        Assert.Equal(3, requests.Count);
        Assert.Equal(3, requests.Select(static request => request.ValueEnvironmentIdentity).Distinct().Count());
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
    }

    // ── Strict allocation counts (isolated child processes) ─────────────────────────────────────────

    private static long Bytes(Action action)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        action();
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    // An async method's own state machine: a struct in an optimized build, which a synchronous
    // completion never boxes, but a heap class in a Debug build (one object per call). Its exact size
    // is measured from an uninitialized instance, so every count below holds in both configurations.
    private static long StateMachineBytes(string method)
    {
        var type = typeof(Evaluator).GetMethod(method, BindingFlags.NonPublic | BindingFlags.Static)!
            .GetCustomAttribute<System.Runtime.CompilerServices.AsyncStateMachineAttribute>()!.StateMachineType;
        if (type.IsValueType) return 0;
        _ = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(type);
        return Bytes(() => _ = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(type));
    }

    [Fact]
    public void FlatUniqueLevel_BindingAllocatesExactlyTheResultArray_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var ctx = Evaluator.EvalCtx.Empty;
        foreach (var width in new[] { 2, 3, 8, Evaluator.FlatUniqueNameBindingWidth })
        {
            var patterns = Names(Enumerable.Range(0, width).Select(static i => "n" + i).ToArray());
            var supply = Enumerable.Range(0, width).Select(Cell).ToArray();
            IReadOnlyList<(string Name, NeedCell Cell)>? bound = null;
            bound = BindSync(patterns, supply, ctx); // warm-up: first-call initialization stays outside the window
            var expected = StateMachineBytes("BindAcceptedNeedPatterns") + Bytes(() => _ = new (string Name, NeedCell Cell)[width]);
            var allocated = Bytes(() => bound = CompleteSynchronously(Bind(patterns, supply, ctx, false, false, null)).Value);
            Assert.Equal(width, bound!.Count);
            Assert.Equal(expected, allocated);
        }
        GcIsolatedAllocation.Complete();
    }

    [Fact]
    public void BuiltinArgumentSupply_AllocatesNoIteratorOrDelegate_GcIsolatedChild()
    {
        // A builtin call forms its supply (FormNeedSupply with sources) and then resolves it: the
        // resolution may add exactly its sources list and ResolvedArgumentAlgorithm array, and the
        // formation exactly its list plus one supply cell per slot — no bundle enumerator, closure,
        // delegate or iterator (beyond each async method's Debug-build state machine).
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var resolve = Private<ResolveSupply>("ResolveNeedSupply");
        var form = Private<FormSupply>("FormNeedSupply");
        var ctx = Evaluator.EvalCtx.Empty;
        IReadOnlyList<(string Name, Result Value)> values = [];
        var flat = OutputBundle.TakeOwnership([new Expr.Num(1), new Expr.Num(2), new Expr.Num(3)]);
        var tailed = OutputBundle.Prepend([new Expr.Num(0)], flat);
        foreach (var args in new[] { flat, tailed })
        {
            var warm = CompleteSynchronously(resolve(args, ctx, values, false));
            Assert.True(warm.IsOk);
            for (var i = 0; i < args.Count; i++)
            {
                Assert.Same(args[i], warm.Value[i].Source);
                Assert.Same(args[i], warm.Value[i].Cell!.Source);
            }
            _ = CompleteSynchronously(form(args, ctx, values, false, new List<Expr?>(args.Count)));
            _ = Evaluator.SupplyCell(args[0], ctx, values);

            var cells = 0L;
            for (var i = 0; i < args.Count; i++)
            {
                var slot = args[i];
                cells += Bytes(() => _ = Evaluator.SupplyCell(slot, ctx, values));
            }
            var list = Bytes(() => _ = new List<NeedCell>(args.Count));
            var sources = Bytes(() => _ = new List<Expr?>(args.Count));
            var resolvedArray = Bytes(() => _ = new Evaluator.ResolvedArgumentAlgorithm[args.Count]);

            var formMachine = StateMachineBytes("FormNeedSupply");
            var resolveMachine = StateMachineBytes("ResolveNeedSupply");

            var formed = Bytes(() => _ = CompleteSynchronously(form(args, ctx, values, false, null)));
            Assert.Equal(formMachine + list + cells, formed);
            var resolved = Bytes(() => _ = CompleteSynchronously(resolve(args, ctx, values, false)));
            Assert.Equal(resolveMachine + sources + formMachine + list + cells + resolvedArray, resolved);
        }
        GcIsolatedAllocation.Complete();
    }

    [Fact]
    public void BuiltinCallback_AllocatesOnlyItsSupplyArrays_GcIsolatedChild()
    {
        // A builtin callback invocation (a builtin passed to map/filter/reduce) allocates its Ready
        // cells, their array, the resolved array and whatever the builtin itself allocates.
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var callback = Private<CallbackBody>("EvalNeedCallbackBody");
        var apply = Private<ApplyResolved>("ApplyBuiltinCountedResolved");
        var ctx = Evaluator.EvalCtx.Empty;
        IReadOnlyList<(string Name, Result Value)> values = [];
        var callee = new Algorithm.Builtin(BuiltinId.range);
        Evaluator.CountedResult[] arguments = [new(new Result.Atom(4), 1), new(new Result.Atom(9), 1)];
        var warm = CompleteSynchronously(callback(callee, arguments, ctx, values, "range", false));
        Assert.True(warm.IsOk, warm.IsError ? warm.Error.ToString() : null);
        Assert.Equal(6, Assert.IsType<Result.ListValue>(warm.Value.Value).Items.Count);
        var prepared = arguments.Select(static argument => new Evaluator.ResolvedArgumentAlgorithm(null) { Cell = NeedCell.Ready(argument) }).ToArray();
        _ = apply(BuiltinId.range, prepared, ctx, values);

        var cells = Bytes(() =>
        {
            _ = NeedCell.Ready(arguments[0]);
            _ = NeedCell.Ready(arguments[1]);
        });
        var cellArray = Bytes(() => _ = new NeedCell[arguments.Length]);
        var resolvedArray = Bytes(() => _ = new Evaluator.ResolvedArgumentAlgorithm[arguments.Length]);
        var builtin = Bytes(() => _ = apply(BuiltinId.range, prepared, ctx, values));
        var machine = StateMachineBytes("EvalNeedCallbackBody");
        var allocated = Bytes(() => _ = CompleteSynchronously(callback(callee, arguments, ctx, values, "range", false)));
        Assert.Equal(machine + cells + cellArray + resolvedArray + builtin, allocated);
        GcIsolatedAllocation.Complete();
    }
}
