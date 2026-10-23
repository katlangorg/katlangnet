using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// CACHE-OWNER-D3 (owner decisions O-2, O-3, O-4, October 23 2026): a property declared in an
/// OWNERLESS host-built <see cref="ScopeCtx"/> level — a host scope kept as the parent of an opened
/// inline block (<c>Evaluator.WireOpenBlockToGlobalScope</c>) — takes part in the ordinary
/// zero-argument property cache, Q-37 outermost publication and CACHE-PUB-1 invocation publication
/// exactly like an evaluator-owned property. Its declaring owner is that host scope OBJECT, by
/// reference (<see cref="PropertyDeclaringOwner"/>): repeated reads through one scope share one entry,
/// and two independently constructed scopes never do — even when they are record-equal, share a
/// property, share a property list, or one is a <c>with</c> copy of the other.
/// <para>Formerly such reads bypassed the cache (<c>owner is null</c> in
/// <c>GetOrEvaluateZeroArgPropertyResultCore</c> and its async twin) and a written <c>P()</c> could not
/// publish (<c>WrittenCalleeBinding</c> refused a null owner): every read re-evaluated, Q-37 and
/// CACHE-PUB-1 did not apply, and C# diverged from Lean, which already caches these properties
/// (<c>lookupInParentsStructuralProperty</c>; guards in <c>lean/CoreTests/ParentScopeValidation.lean</c>).
/// The witnesses H1–H12 are the CACHE-OWNER-F1 research fixtures
/// (<c>experimental/features/cache-owner-f1-research.md</c> §2.4, §13); each host case agrees with its
/// evaluator-owned control on value, effects, steps and publications.</para>
/// </summary>
public class HostScopePropertyCacheTests
{
    // ── Fixtures ─────────────────────────────────────────────────────────────────────────────

    private sealed class Log
    {
        internal int Ticks;
        internal readonly List<string> Effects = [];
    }

    private static HostOperations Ops(Log log, bool withAsync = false)
    {
        var tick = HostOperation.Create("tick", (_, _) =>
        {
            log.Ticks++;
            log.Effects.Add("tick" + log.Ticks);
            return new Result.Atom(log.Ticks);
        });
        var boom = HostOperation.Create("boom", (_, _) => throw new InvalidOperationException("boom"));
        return withAsync
            ? HostOperations.Create(tick, boom,
                // Genuine suspension: the evaluation spine really awaits an incomplete task.
                HostOperation.CreateAsync("atrace", async (args, _) =>
                {
                    await Task.Yield();
                    log.Effects.Add("a" + ((Result.Atom)args[0]).Value);
                    return args[1];
                }, "tag", "value"))
            : HostOperations.Create(tick, boom);
    }

    /// <summary>A prelude-backed host chain root, so host operations and builtins resolve by name (itself an ownerless host level).</summary>
    private static ScopeCtx Prelude(HostOperations ops) => new(null, [], ops.RuntimePreludeAlgorithm.Properties);

    private static Expr R(string name) => new Expr.Resolve(name);
    private static Expr N(int value) => new Expr.Num(value);
    private static Expr X(string name) => new Expr.Param(name);
    private static Expr Add(Expr a, Expr b) => new Expr.Binary(BinaryOp.Add, a, b);
    private static Expr Call(string name, params Expr[] args) => new Expr.Call(R(name), new OutputBundle(args));
    private static Expr Tick() => Call("tick");
    private static Expr Seq(params Expr[] items) => items.Skip(1).Aggregate(items[0], (left, right) => new Expr.SequenceConstruct(left, right));
    private static Algorithm.User Body(params Expr[] rows) => new(null, [], [], [], new OutputBundle(rows));
    private static Algorithm.User Fn(string param, params Expr[] rows)
        => new(null, [new CaptureParameterPattern(param)], [], [], new OutputBundle(rows));

    private static Property Prop(string name, Algorithm value, bool isPublic = false,
        PropertyExposure exposure = PropertyExposure.Exported, string[]? required = null)
        => new(name, value, isPublic, exposure) { RequiredAncestorParameters = required ?? [] };

    /// <summary>Q-37 witness body: <c>if(tick() &lt; 3, P + 1, 0)</c> (or <c>P() + 1</c>).</summary>
    private static Algorithm.User Reentrant(Expr self) => Body(Call("if",
        new Expr.Comparison(Tick(), [new ComparisonLink(ComparisonOp.Lt, N(3))]), Add(self, N(1)), N(0)));

    /// <summary>The established host pattern: the root opens <c>{ public Run = row }</c> whose PARENT is <paramref name="scope"/>; output <c>Run</c>.</summary>
    private static Expr OpenedThrough(ScopeCtx scope, Expr row, params Property[] blockMembers)
        => OpenedThroughRows(scope, [row], blockMembers);

    private static Expr OpenedThroughRows(ScopeCtx scope, Expr[] rows, params Property[] blockMembers)
        => new Expr.AlgorithmExpr(new Algorithm.User(null, [],
            [new Expr.AlgorithmExpr(new Algorithm.User(scope, [], [],
                [Prop("Run", Body(rows), isPublic: true), .. blockMembers], OutputBundle.Empty))],
            [], new OutputBundle([R("Run")])));

    /// <summary>Two opened blocks with their own parents; output <c>RunA + RunB</c>.</summary>
    private static Expr OpenedTwo(ScopeCtx a, Expr rowA, ScopeCtx b, Expr rowB)
        => new Expr.AlgorithmExpr(new Algorithm.User(null, [],
            [new Expr.AlgorithmExpr(new Algorithm.User(a, [], [], [Prop("RunA", Body(rowA), isPublic: true)], OutputBundle.Empty)),
             new Expr.AlgorithmExpr(new Algorithm.User(b, [], [], [Prop("RunB", Body(rowB), isPublic: true)], OutputBundle.Empty))],
            [], new OutputBundle([Add(R("RunA"), R("RunB"))])));

    /// <summary>Records every cache request's key (sync seam) around the ordinary run-scoped law.</summary>
    private sealed class RecordingCache : IZeroArgPropertyResultCache
    {
        internal RunScopedZeroArgPropertyResultCache Inner { get; }
        internal List<ZeroArgPropertyCacheKey> Reads { get; } = [];
        internal List<ZeroArgPropertyCacheKey> Invocations { get; } = [];

        internal RecordingCache(RootPropertyObservationSink? sink = null) => Inner = new(sink);

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Reads.Add(ZeroArgPropertyCacheKey.FromExecution(execution));
            return Inner.GetOrEvaluate(execution, evaluate);
        }

        public EvalResult<ZeroArgPropertyResult> Invoke(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Invocations.Add(ZeroArgPropertyCacheKey.FromExecution(execution));
            return Inner.Invoke(execution, evaluate);
        }

        internal int DistinctKeys(Property binding)
            => Reads.Concat(Invocations).Where(k => ReferenceEquals(k.BindingIdentity, binding))
                .Distinct(ZeroArgPropertyCacheKeyComparer.Instance).Count();
    }

    /// <summary>The async law, genuinely suspending before every access; records keys and counts.</summary>
    private sealed class SuspendingRecordingCache : IAsyncZeroArgPropertyResultCache
    {
        private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();
        internal List<ZeroArgPropertyCacheKey> Keys { get; } = [];
        internal int SyncAccesses { get; private set; }
        internal int Suspensions { get; private set; }
        internal int PublishedCount => _inner.PublishedCount;
        internal int ActiveOwnerCount => _inner.ActiveOwnerCount;

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            SyncAccesses++;
            return _inner.GetOrEvaluate(execution, evaluate);
        }

        public EvalResult<ZeroArgPropertyResult> Invoke(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            SyncAccesses++;
            return _inner.Invoke(execution, evaluate);
        }

        public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(ZeroArgPropertyExecution execution, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            Keys.Add(ZeroArgPropertyCacheKey.FromExecution(execution));
            Suspensions++;
            await Task.Yield();
            return await _inner.GetOrEvaluateAsync(execution, evaluateAsync);
        }

        public async ValueTask<EvalResult<ZeroArgPropertyResult>> InvokeAsync(ZeroArgPropertyExecution execution, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            Keys.Add(ZeroArgPropertyCacheKey.FromExecution(execution));
            Suspensions++;
            await Task.Yield();
            return await _inner.InvokeAsync(execution, evaluateAsync);
        }
    }

    private sealed record Outcome(string Value, string Effects, long Steps, long Checkpoints, int PeakDepth, int Published);

    private static string Render(Result result) => result switch
    {
        Result.Atom atom => atom.Value.ToString(),
        Result.SequenceValue sequence => "(" + string.Join(", ", sequence.Items.Select(Render)) + ")",
        Result.ListValue list => "[" + string.Join(", ", list.Items.Select(Render)) + "]",
        _ => result.ToString() ?? "?",
    };

    private static Outcome RunSync(Func<ScopeCtx, Expr> build, bool optimized)
    {
        var log = new Log();
        var ops = Ops(log);
        var cache = new RunScopedZeroArgPropertyResultCache();
        var (result, budget) = Evaluator.RunCountedObserved(build(Prelude(ops)), enableOptimizations: optimized,
            zeroArgPropertyResultCache: cache, hostOperations: ops);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal(0, cache.ActiveOwnerCount);
        var snapshot = cache.GetSnapshot();
        return new(Render(result.Value.Value), string.Join(",", log.Effects), budget.ConsumedSteps,
            budget.ConsumedExpressionCheckpoints, budget.PeakDepth, snapshot.Stores);
    }

    private static async Task<Outcome> RunSuspendingAsync(Func<ScopeCtx, Expr> build)
    {
        var log = new Log();
        var ops = Ops(log, withAsync: true);
        var cache = new SuspendingRecordingCache();
        var (result, budget) = await Evaluator.RunCountedObservedAsync(build(Prelude(ops)),
            zeroArgPropertyResultCache: cache, hostOperations: ops);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal(0, cache.SyncAccesses);
        Assert.True(cache.Suspensions > 0);
        Assert.Equal(0, cache.ActiveOwnerCount);
        return new(Render(result.Value.Value), string.Join(",", log.Effects), budget.ConsumedSteps,
            budget.ConsumedExpressionCheckpoints, budget.PeakDepth, cache.PublishedCount);
    }

    /// <summary>
    /// The three execution routes — generic sync, optimized sync, genuinely suspending async — must
    /// agree exactly. A program using the asynchronous host operation runs on the async route only.
    /// </summary>
    private static async Task<Outcome> OnEveryRouteAsync(Func<ScopeCtx, Expr> build, bool asyncOnly = false)
    {
        if (asyncOnly)
            return await RunSuspendingAsync(build);
        var generic = RunSync(build, optimized: false);
        Assert.Equal(generic, RunSync(build, optimized: true));
        Assert.Equal(generic, await RunSuspendingAsync(build));
        return generic;
    }

    // ── 1. H1–H12: host scopes cache like evaluator-owned properties ─────────────────────────

    /// <summary>
    /// A host case and its evaluator-owned control: the same members, declared once in the host
    /// scope and once in the opened block itself.
    /// </summary>
    public static TheoryData<string, string, string> HostWitnesses => new()
    {
        // id, expected value, expected effects
        { "H1 P + P", "2", "tick1" },
        { "H7 P() + P", "2", "tick1" },
        { "H7b P, P()", "(1, 2)", "tick1,tick2" },
        { "H7c P(), P", "(1, 1)", "tick1" },
        { "H7d P(), P, P(), P", "(1, 1, 2, 1)", "tick1,tick2" },
        { "H7e P(E*), P with an empty spread", "(1, 1)", "tick1" },
        { "H7f nonempty supply F(1), F(1), F", "(1, 2, 3)", "tick1,tick2,tick3" },
        { "H8 Q-37 P + P", "4", "tick1,tick2,tick3" },
        { "H8i Q-37 through P(): P(), P", "(2, 2)", "tick1,tick2,tick3" },
        { "H11 Q = P + P; Q + Q", "4", "tick1" },
        { "H12 map callback reads P", "[2, 3, 4]", "tick1" },
        { "alias A = P: A(), A, P", "(1, 1, 2)", "tick1,tick2" },
        { "forwarded P: Apply(P), P", "(1, 1)", "tick1" },
        { "META Invoke: Apply(P()), P", "(1, 1)", "tick1" },
        { "META Algorithm: Apply(P()), P", "(1, 1)", "tick1" },
        { "two bindings P, Q in one scope", "(1, 2, 1, 2)", "tick1,tick2" },
        { "H9 async P = atrace(1, 7); P + P", "14", "a1" },
    };

    private static (Property[] Members, Expr Row) Witness(string id) => id switch
    {
        "H1 P + P" => ([Prop("P", Body(Tick()))], Add(R("P"), R("P"))),
        "H7 P() + P" => ([Prop("P", Body(Tick()))], Add(Call("P"), R("P"))),
        "H7b P, P()" => ([Prop("P", Body(Tick()))], Seq(R("P"), Call("P"))),
        "H7c P(), P" => ([Prop("P", Body(Tick()))], Seq(Call("P"), R("P"))),
        "H7d P(), P, P(), P" => ([Prop("P", Body(Tick()))], Seq(Call("P"), R("P"), Call("P"), R("P"))),
        "H7e P(E*), P with an empty spread" => ([Prop("P", Body(Tick()))],
            Seq(Call("P", new Expr.SequenceSpread(new Expr.ListLiteral(OutputBundle.Empty))), R("P"))),
        "H7f nonempty supply F(1), F(1), F" => ([Prop("F", new Algorithm.User(null,
                [new CaptureParameterPattern("xs", Kind: ParameterKind.Collecting)], [], [], new OutputBundle([Tick()])))],
            Seq(Call("F", N(1)), Call("F", N(1)), R("F"))),
        "H8 Q-37 P + P" => ([Prop("P", Reentrant(R("P")))], Add(R("P"), R("P"))),
        "H8i Q-37 through P(): P(), P" => ([Prop("P", Reentrant(Call("P")))], Seq(Call("P"), R("P"))),
        "H11 Q = P + P; Q + Q" => ([Prop("P", Body(Tick())), Prop("Q", Body(Add(R("P"), R("P"))))], Add(R("Q"), R("Q"))),
        "H12 map callback reads P" => ([Prop("P", Body(Tick())), Prop("Cb", Fn("n", Add(R("P"), X("n"))))],
            Call("map", new Expr.ListLiteral(new OutputBundle([N(1), N(2), N(3)])), R("Cb"))),
        "alias A = P: A(), A, P" => ([Prop("P", Body(Tick())), Prop("A", new Algorithm.Alias(null, [], [], R("P")))],
            Seq(Call("A"), R("A"), R("P"))),
        "forwarded P: Apply(P), P" => ([Prop("P", Body(Tick())), Prop("Apply", Fn("f", new Expr.Call(X("f"), OutputBundle.Empty)))],
            Seq(Call("Apply", R("P")), R("P"))),
        "META Invoke: Apply(P()), P" => ([Prop("P", Body(Tick())), Prop("Apply", new Algorithm.User(null,
                [new CaptureParameterPattern("op", Kind: ParameterKind.Meta)], [], [],
                [new Expr.DotCall(X("op"), "Invoke", OutputBundle.Empty)]))],
            Seq(Call("Apply", Call("P")), R("P"))),
        "META Algorithm: Apply(P()), P" => ([Prop("P", Body(Tick())), Prop("Apply", new Algorithm.User(null,
                [new CaptureParameterPattern("op", Kind: ParameterKind.Meta)], [], [],
                [new Expr.DotCall(X("op"), "Algorithm", OutputBundle.Empty)]))],
            Seq(Call("Apply", Call("P")), R("P"))),
        "two bindings P, Q in one scope" => ([Prop("P", Body(Tick())), Prop("Q", Body(Tick()))],
            Seq(R("P"), R("Q"), R("P"), R("Q"))),
        "H9 async P = atrace(1, 7); P + P" => ([Prop("P", Body(Call("atrace", N(1), N(7))))], Add(R("P"), R("P"))),
        _ => throw new ArgumentOutOfRangeException(nameof(id)),
    };

    [Theory]
    [MemberData(nameof(HostWitnesses))]
    public async Task HostScopeProperty_CachesExactlyLikeItsOwnedControl_OnEveryRoute(string id, string value, string effects)
    {
        var asyncOnly = id.StartsWith("H9 ", StringComparison.Ordinal);
        var host = await OnEveryRouteAsync(pre =>
        {
            var (members, row) = Witness(id);
            return OpenedThrough(new ScopeCtx(pre, [], members), row);
        }, asyncOnly);
        var owned = await OnEveryRouteAsync(pre =>
        {
            var (members, row) = Witness(id);
            return OpenedThrough(new ScopeCtx(pre, [], []), row, members);
        }, asyncOnly);

        Assert.Equal(value, host.Value);
        Assert.Equal(effects, host.Effects);
        // Value, effects, the step charge and the publications all equal the owned control's.
        Assert.Equal(owned, host);
    }

    [Fact]
    public async Task H1_StepsEqualTheOwnedControl()
    {
        // Formerly 5 steps and two ticks (the bypass re-evaluated P); the owned control is 4.
        var host = await OnEveryRouteAsync(pre => OpenedThrough(new ScopeCtx(pre, [], [Prop("P", Body(Tick()))]), Add(R("P"), R("P"))));
        Assert.Equal(4, host.Steps);
        Assert.Equal("tick1", host.Effects);
    }

    [Fact]
    public async Task H1g_AHostGrandparentsPropertyIsCached_UnderTheGrandparentScope()
    {
        var outcome = await OnEveryRouteAsync(pre => OpenedThrough(
            new ScopeCtx(new ScopeCtx(pre, [], [Prop("P", Body(Tick()))]), [], [Prop("Q", Body(N(5)))]),
            Add(R("P"), R("P"))));
        Assert.Equal(("2", "tick1"), (outcome.Value, outcome.Effects));

        // The owner identity is the DECLARING (grandparent) level object, not the level the lookup started at.
        var log = new Log();
        var ops = Ops(log);
        var p = Prop("P", Body(Tick()));
        var grandparent = new ScopeCtx(Prelude(ops), [], [p]);
        var parent = new ScopeCtx(grandparent, [], [Prop("Q", Body(N(5)))]);
        var cache = new RecordingCache();
        Assert.False(Evaluator.RunCountedObserved(OpenedThrough(parent, Add(R("P"), R("P"))),
            zeroArgPropertyResultCache: cache, hostOperations: ops).Result.IsError);
        var keys = cache.Reads.Where(k => ReferenceEquals(k.BindingIdentity, p)).ToList();
        Assert.Equal(2, keys.Count);
        Assert.All(keys, key => Assert.Same(grandparent, key.OwnerIdentity));
    }

    [Fact]
    public async Task H6e_AnExportedHostProperty_IsRunCached_AsAnOwnedExportedPropertyIs()
    {
        // O-4: the evaluator trusts host exposure metadata. P reads the caller's x but is marked
        // Exported, so — exactly as for the owned control — its first value is reused: G(1) + G(2)
        // is 1 + 1. (The former bypass printed 3.)
        Expr Build(ScopeCtx scope, params Property[] block)
            => OpenedThrough(scope, Add(Call("G", N(1)), Call("G", N(2))),
                [Prop("G", Fn("x", R("P")), isPublic: true), .. block]);
        var host = await OnEveryRouteAsync(pre => Build(new ScopeCtx(pre, [], [Prop("P", Body(X("x")))])));
        var owned = await OnEveryRouteAsync(pre => Build(new ScopeCtx(pre, [], []), Prop("P", Body(X("x")))));
        Assert.Equal("2", host.Value);
        Assert.Equal(owned.Value, host.Value);
    }

    [Fact]
    public async Task H6l_ALocalOnlyHostProperty_KeepsTheAccessEnvironmentFallback()
    {
        // A local-only host property has no declaring activation (host levels never carry one), so
        // its key keeps the access binding context: each G activation evaluates its own P.
        var outcome = await OnEveryRouteAsync(pre => OpenedThrough(
            new ScopeCtx(pre, [], [Prop("P", Body(X("x")), exposure: PropertyExposure.LocalOnlyCapturedAncestorParameters, required: ["x"])], ["x"]),
            Add(Call("G", N(1)), Call("G", N(2))),
            Prop("G", Fn("x", R("P")), isPublic: true)));
        Assert.Equal("3", outcome.Value);
        // Run once, and P once per G activation.
        Assert.Equal(3, outcome.Published);
    }

    [Fact]
    public async Task LocalOnlyHostProperty_IsSharedWithinOneActivation_AndSeparateAcrossActivations()
    {
        // F(x) = Q + Q with local-only host Q = x + tick() * 0: one evaluation per F activation.
        var outcome = await OnEveryRouteAsync(pre => OpenedThrough(
            new ScopeCtx(pre, [], [Prop("Q", Body(Add(X("x"), new Expr.Binary(BinaryOp.Mul, Tick(), N(0)))),
                exposure: PropertyExposure.LocalOnlyCapturedAncestorParameters, required: ["x"])], ["x"]),
            Seq(Call("F", N(1)), Call("F", N(2)), Call("F", N(1))),
            Prop("F", Fn("x", Add(R("Q"), R("Q"))), isPublic: true)));
        Assert.Equal(("(2, 4, 2)", "tick1,tick2,tick3"), (outcome.Value, outcome.Effects));
    }

    [Fact]
    public async Task LocalOnlyInvocations_PublishUnderTheReadsKey_WithoutCrossingActivations()
    {
        Expr Build(ScopeCtx pre, bool host)
        {
            var p = Prop("P", Body(Add(X("x"), Tick())),
                exposure: PropertyExposure.LocalOnlyCapturedAncestorParameters, required: ["x"]);
            var g = Prop("G", Fn("x", Seq(Call("P"), R("P"), Call("P"), R("P"))), isPublic: true);
            return OpenedThrough(new ScopeCtx(pre, [], host ? [p] : [], ["x"]),
                Seq(Call("G", N(10)), Call("G", N(20))), host ? [g] : [g, p]);
        }

        var host = await OnEveryRouteAsync(pre => Build(pre, host: true));
        var owned = await OnEveryRouteAsync(pre => Build(pre, host: false));
        Assert.Equal("((11, 11, 12, 11), (23, 23, 24, 23))", host.Value);
        Assert.Equal("tick1,tick2,tick3,tick4", host.Effects);
        Assert.Equal(owned, host);
    }

    [Fact]
    public async Task H9_AGenuinelySuspendingHostProperty_EvaluatesOnce()
    {
        var host = await RunSuspendingAsync(pre => OpenedThrough(
            new ScopeCtx(pre, [], [Prop("P", Body(Call("atrace", N(1), N(7))))]), Add(R("P"), R("P"))));
        // Two publications: Run, and P exactly once.
        Assert.Equal(("14", "a1", 2), (host.Value, host.Effects, host.Published));
    }

    [Fact]
    public async Task H10_AnOpenedProviderInsideAHostScope_KeepsItsProviderOwner()
    {
        var lib = new Algorithm.User(null, [], [], [Prop("V", Body(Tick()), isPublic: true)], OutputBundle.Empty);
        var outcome = await OnEveryRouteAsync(pre => OpenedThrough(
            new ScopeCtx(pre, [new Expr.AlgorithmExpr(lib)], []), Add(R("V"), R("V"))));
        Assert.Equal(("2", "tick1"), (outcome.Value, outcome.Effects));
    }

    [Theory]
    [InlineData(false, "(1, 1, 1, 1)", "tick1")]
    [InlineData(true, "(1, 2, 3, 2)", "tick1,tick2,tick3")]
    public async Task RuntimeAliasInAHostScope_PreservesTerminalPublication_AndParameterizedFreshness(
        bool collectingTarget, string value, string effects)
    {
        Expr Build(ScopeCtx pre, bool host)
        {
            var target = collectingTarget
                ? new Algorithm.User(null, [new CaptureParameterPattern("xs", Kind: ParameterKind.Collecting)], [], [], [Tick()])
                : Body(Tick());
            Property[] members =
            [
                Prop("F", target),
                Prop("Capture", new Algorithm.User(null, [new CaptureParameterPattern("op", Kind: ParameterKind.Meta)], [], [], [X("op")])),
                Prop("R", Body(Call("Capture", Call("F")))),
                Prop("A", new Algorithm.Alias(null, [], [], new Expr.DotCall(R("R"), "Algorithm")) { HasRuntimeTarget = true }),
            ];
            return OpenedThrough(new ScopeCtx(pre, [], host ? members : []),
                Seq(Call("A"), R("A"), Call("A"), R("A")), host ? [] : members);
        }

        var host = await OnEveryRouteAsync(pre => Build(pre, host: true));
        var owned = await OnEveryRouteAsync(pre => Build(pre, host: false));
        Assert.Equal((value, effects), (host.Value, host.Effects));
        Assert.Equal(owned, host);
    }

    // ── 2. Identity: the host scope OBJECT, by reference ─────────────────────────────────────

    /// <summary>Runs <paramref name="build"/> with a recording cache: the value, the ticks, and the cache.</summary>
    private static (string Value, int Ticks, RecordingCache Cache) Recorded(Func<ScopeCtx, Property, Expr> build, bool optimized = true)
    {
        var log = new Log();
        var ops = Ops(log);
        var p = Prop("P", Body(Tick()));
        var cache = new RecordingCache();
        var (result, _) = Evaluator.RunCountedObserved(build(Prelude(ops), p), enableOptimizations: optimized,
            zeroArgPropertyResultCache: cache, hostOperations: ops);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        return (Render(result.Value.Value), log.Ticks, cache);
    }

    [Fact]
    public void RepeatedReadsThroughOneHostScope_ShareOneKey()
    {
        ScopeCtx? scope = null;
        var (value, ticks, cache) = Recorded((pre, p) =>
            OpenedThrough(scope = new ScopeCtx(pre, [], [p]), Seq(R("P"), R("P"), R("P"))));
        Assert.Equal(("(1, 1, 1)", 1), (value, ticks));
        var keys = cache.Reads.Where(k => k.BindingIdentity is Property { Name: "P" }).ToList();
        Assert.Equal(3, keys.Count);
        Assert.All(keys, key => Assert.Same(scope, key.OwnerIdentity));
        Assert.Single(keys.Distinct(ZeroArgPropertyCacheKeyComparer.Instance));
    }

    [Fact]
    public void TheSameHostScopeObject_OpenedByTwoBlocks_IsOneOwner()
    {
        var (value, ticks, _) = Recorded((pre, p) =>
        {
            var scope = new ScopeCtx(pre, [], [p]);
            return OpenedTwo(scope, Add(R("P"), R("P")), scope, Add(R("P"), R("P")));
        });
        Assert.Equal(("4", 1), (value, ticks));
    }

    /// <summary>
    /// Two DISTINCT host scope objects that are record-EQUAL (the same parent, opens and property-list
    /// references) remain two owners: the test first proves the scopes are structurally equal, so it
    /// fails if the key ever compares host owners with <see cref="ScopeCtx"/>'s record equality.
    /// </summary>
    [Theory]
    [InlineData("shared properties list")]
    [InlineData("record with-copy")]
    [InlineData("shared Property, distinct lists")]
    [InlineData("equal but separately built")]
    public void DistinctHostScopeObjects_NeverShareAnOwner_EvenWhenRecordEqual(string shape)
    {
        foreach (var optimized in new[] { false, true })
        {
            ScopeCtx? first = null, second = null;
            var (value, ticks, cache) = Recorded((pre, p) =>
            {
                IReadOnlyList<Expr> noOpens = [];
                IReadOnlyList<Property> list = [p];
                (first, second) = shape switch
                {
                    "shared properties list" => (new ScopeCtx(pre, noOpens, list), new ScopeCtx(pre, noOpens, list)),
                    "record with-copy" => (new ScopeCtx(pre, noOpens, list), null),
                    "shared Property, distinct lists" => (new ScopeCtx(pre, noOpens, [p]), new ScopeCtx(pre, noOpens, [p])),
                    _ => (new ScopeCtx(pre, noOpens, [Prop("P", Body(Tick()))]), new ScopeCtx(pre, noOpens, [Prop("P", Body(Tick()))])),
                };
                second ??= first with { };
                return OpenedTwo(first, Add(R("P"), R("P")), second, Add(R("P"), R("P")));
            }, optimized);

            Assert.NotSame(first, second);
            if (shape is "shared properties list" or "record with-copy")
            {
                Assert.Equal(first, second); // record equality holds …
                Assert.Equal(first!.GetHashCode(), second!.GetHashCode());
            }

            // … yet each scope evaluates its own P once: 1 + 1 + 2 + 2.
            Assert.Equal(("6", 2), (value, ticks));
            var owners = cache.Reads.Where(k => k.BindingIdentity is Property { Name: "P" })
                .Select(k => k.OwnerIdentity).Distinct(ReferenceEqualityComparer.Instance).ToList();
            Assert.Equal(2, owners.Count);
            Assert.Contains(first!, owners);
            Assert.Contains(second!, owners);
        }
    }

    [Fact]
    public void TheKeyComparer_ComparesHostOwnersByReference_NeverByRecordEquality()
    {
        var p = Prop("P", Body(N(1)));
        IReadOnlyList<Expr> noOpens = [];
        IReadOnlyList<Property> list = [p];
        var first = new ScopeCtx(null, noOpens, list);
        var copy = first with { };
        Assert.Equal(first, copy);
        var run = new object();
        ZeroArgPropertyCacheKey Key(ScopeCtx scope) => ZeroArgPropertyCacheKey.FromExecution(new ZeroArgPropertyExecution(
            PropertyDeclaringOwner.OfLevel(scope), p, ZeroArgPropertyAccessKind.CountedLexical, new object(), run));

        var comparer = ZeroArgPropertyCacheKeyComparer.Instance;
        Assert.True(comparer.Equals(Key(first), Key(first)));
        Assert.Equal(comparer.GetHashCode(Key(first)), comparer.GetHashCode(Key(first)));
        Assert.False(comparer.Equals(Key(first), Key(copy)));
        Assert.False(ZeroArgPropertyCacheKeyComparer.OwnerIdentityEquals(first, copy));

        // A host owner never equals a structural (evaluator-owned) identity over the same lists.
        var owned = new Algorithm.User(null, [], noOpens, list, OutputBundle.Empty);
        var ownedKey = ZeroArgPropertyCacheKey.FromExecution(new ZeroArgPropertyExecution(
            owned, p, ZeroArgPropertyAccessKind.CountedLexical, new object(), run));
        Assert.IsType<StructuralOwnerIdentity>(ownedKey.OwnerIdentity);
        Assert.False(comparer.Equals(Key(first), ownedKey));
        Assert.False(comparer.Equals(ownedKey, Key(first)));

        // The declaring-owner value itself is reference-equal only to itself.
        Assert.Equal(PropertyDeclaringOwner.OfLevel(first), PropertyDeclaringOwner.OfLevel(first));
        Assert.NotEqual(PropertyDeclaringOwner.OfLevel(first), PropertyDeclaringOwner.OfLevel(copy));
        Assert.Same(first, PropertyDeclaringOwner.OfLevel(first).HostScope);
        Assert.Null(PropertyDeclaringOwner.OfLevel(first).Algorithm);
    }

    [Fact]
    public void TwoBindingsInOneHostScope_HaveSeparateEntries()
    {
        var log = new Log();
        var ops = Ops(log);
        var p = Prop("P", Body(Tick()));
        var q = Prop("Q", Body(Tick()));
        var cache = new RecordingCache();
        var (result, _) = Evaluator.RunCountedObserved(OpenedThrough(new ScopeCtx(Prelude(ops), [], [p, q]), Seq(R("P"), R("Q"), R("P"), R("Q"))),
            zeroArgPropertyResultCache: cache, hostOperations: ops);
        Assert.Equal("(1, 2, 1, 2)", Render(result.Value.Value));
        Assert.Equal((1, 1), (cache.DistinctKeys(p), cache.DistinctKeys(q)));
        Assert.Equal(3, cache.Inner.GetSnapshot().Stores); // Run, P, Q
    }

    [Fact]
    public void AReusedHostAst_NeverSharesEntriesAcrossRuns_EvenOnOneSharedCache()
    {
        var log = new Log();
        var ops = Ops(log);
        var p = Prop("P", Body(Tick()));
        var expr = OpenedThrough(new ScopeCtx(Prelude(ops), [], [p]), Add(R("P"), R("P")));

        // Separate caches: each run evaluates P once.
        Assert.Equal("2", Render(Evaluator.RunCountedObserved(expr, hostOperations: ops).Result.Value.Value));
        Assert.Equal("4", Render(Evaluator.RunCountedObserved(expr, hostOperations: ops).Result.Value.Value));
        Assert.Equal(2, log.Ticks);

        // One cache instance shared by two runs: the run identity still separates them.
        var shared = new RecordingCache();
        Assert.Equal("6", Render(Evaluator.RunCountedObserved(expr, zeroArgPropertyResultCache: shared, hostOperations: ops).Result.Value.Value));
        Assert.Equal("8", Render(Evaluator.RunCountedObserved(expr, zeroArgPropertyResultCache: shared, hostOperations: ops).Result.Value.Value));
        Assert.Equal(4, log.Ticks);
        Assert.Equal(2, shared.DistinctKeys(p));
        var snapshot = shared.Inner.GetSnapshot();
        // Per run: Run and P are stored once each, and P's second read hits.
        Assert.Equal((2, 4), (snapshot.Hits, snapshot.Stores));
    }

    [Fact]
    public void TenThousandReads_CreateOneEntry_AndOneEvaluation()
    {
        // The refuted synthetic-owner prototype minted a fresh owner per read: 0 hits and one entry per read.
        const int reads = 10_000;
        var (value, ticks, cache) = Recorded((pre, p) =>
            OpenedThroughRows(new ScopeCtx(pre, [], [p]), [.. Enumerable.Repeat(R("P"), reads)]));
        Assert.Equal(1, ticks);
        Assert.StartsWith("(1, 1, 1", value);
        var snapshot = cache.Inner.GetSnapshot();
        var pReads = cache.Reads.Where(k => k.BindingIdentity is Property { Name: "P" }).ToList();
        Assert.Equal(reads, pReads.Count);
        Assert.Single(pReads.Select(k => k.OwnerIdentity).Distinct(ReferenceEqualityComparer.Instance));
        Assert.Single(pReads.Distinct(ZeroArgPropertyCacheKeyComparer.Instance));
        Assert.Equal(reads - 1, snapshot.GetAccessKind(ZeroArgPropertyAccessKind.CountedLexical).Hits);
        Assert.True(snapshot.MaxCacheSize <= 2, $"max cache size {snapshot.MaxCacheSize}");
    }

    // ── 3. Publication safety: failure, cancellation, root observations ──────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ReentrantSuccessThenOrdinaryOwnerFailure_KeepsOtherEntries_AndItsOriginalSpan(bool invocation)
    {
        var divisionSpan = new SourceSpan(4, 9, 4, 14);

        async Task<(EvalError Error, long Steps, long Checkpoints, int PeakDepth)> Run(bool host, int route)
        {
            var log = new Log();
            var ops = Ops(log);
            var division = new Expr.Binary(BinaryOp.Div, N(1), N(0)) { Span = divisionSpan };
            var p = Prop("P", Body(Call("if",
                new Expr.Comparison(Tick(), [new ComparisonLink(ComparisonOp.Lt, N(2))]),
                Add(Add(R("S"), Call("P")), division), N(5))));
            var s = Prop("S", Body(new Expr.Binary(BinaryOp.Mul, Tick(), N(100))));
            var row = Seq(invocation ? Call("P") : R("P"), Tick());
            var pre = Prelude(ops);
            var program = host
                ? OpenedThrough(new ScopeCtx(pre, [], [p, s]), row)
                : OpenedThrough(new ScopeCtx(pre, [], []), row, p, s);
            var syncCache = new RecordingCache();
            var asyncCache = new SuspendingRecordingCache();
            var (result, budget) = route == 2
                ? await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: asyncCache, hostOperations: ops)
                : Evaluator.RunCountedObserved(program, enableOptimizations: route == 1,
                    zeroArgPropertyResultCache: syncCache, hostOperations: ops);

            Assert.True(result.IsError);
            Assert.Equal(KatLangErrorCode.DivisionByZero, result.Error.Code);
            Assert.Equal(divisionSpan, KatLangError.FromEvalError(result.Error).Span);
            Assert.Equal("tick1,tick2,tick3", string.Join(",", log.Effects));
            // The inner P() succeeded, but cannot publish for its failing owner. S keeps its entry.
            Assert.Equal(1, route == 2 ? asyncCache.PublishedCount : syncCache.Inner.GetSnapshot().Stores);
            Assert.Equal(0, route == 2 ? asyncCache.ActiveOwnerCount : syncCache.Inner.ActiveOwnerCount);
            if (route == 2)
            {
                Assert.True(asyncCache.Suspensions > 0);
                Assert.Equal(0, asyncCache.SyncAccesses);
            }
            return (result.Error, budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth);
        }

        var expected = await Run(host: false, route: 0);
        for (var route = 0; route < 3; route++)
            Assert.Equal(expected, await Run(host: true, route));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AFailedOwningEvaluation_PublishesNothing(bool invocation)
    {
        var log = new Log();
        var ops = Ops(log);
        var p = Prop("P", Body(Add(Tick(), Call("boom"))));
        var cache = new RecordingCache();
        var row = invocation ? Seq(Call("P"), R("P")) : Seq(R("P"), R("P"));
        Assert.Throws<InvalidOperationException>(() => Evaluator.RunCountedObserved(
            OpenedThrough(new ScopeCtx(Prelude(ops), [], [p]), row), zeroArgPropertyResultCache: cache, hostOperations: ops));
        Assert.Equal(1, log.Ticks);
        Assert.Equal(0, cache.Inner.ActiveOwnerCount);
        Assert.Equal(0, cache.Inner.GetSnapshot().Stores);
        Assert.Equal(1, cache.DistinctKeys(p));
    }

    [Fact]
    public async Task CancellationDuringAnOwningHostEvaluation_IsTerminal_AndPublishesNothing()
    {
        using var cts = new CancellationTokenSource();
        var ops = HostOperations.Create(HostOperation.Create("tick", (_, _) => { cts.Cancel(); return new Result.Atom(1); }));
        // P's owning evaluation is still running when the next charged boundary (the read of Q) observes the token.
        Expr Build() => OpenedThrough(new ScopeCtx(Prelude(ops), [], [Prop("P", Body(Add(Tick(), R("Q")))), Prop("Q", Body(N(1)))]),
            Add(R("P"), R("P")));

        var cache = new RunScopedZeroArgPropertyResultCache();
        Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(Build(),
            zeroArgPropertyResultCache: cache, hostOperations: ops, cancellationToken: cts.Token));
        Assert.Equal(0, cache.ActiveOwnerCount);

        using var asyncCts = new CancellationTokenSource();
        var asyncOps = HostOperations.Create(HostOperation.CreateAsync("tick", async (_, _) =>
        {
            await Task.Yield();
            asyncCts.Cancel();
            return new Result.Atom(1);
        }));
        var asyncCache = new SuspendingRecordingCache();
        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(
            OpenedThrough(new ScopeCtx(Prelude(asyncOps), [], [Prop("P", Body(Add(Tick(), R("Q")))), Prop("Q", Body(N(1)))]),
                Add(R("P"), R("P"))),
            zeroArgPropertyResultCache: asyncCache, hostOperations: asyncOps, cancellationToken: asyncCts.Token));
        Assert.Equal(0, asyncCache.ActiveOwnerCount);
        Assert.Equal(0, asyncCache.PublishedCount);
        Assert.Equal(0, cache.GetSnapshot().Stores);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void HostScopePublications_NeverMasqueradeAsRootObservations(bool invocation)
    {
        // The sink's root shares the host scope's very property list and declares spanned members,
        // so only the owner kind (a host scope, not the root's structural identity) excludes it.
        var log = new Log();
        var ops = Ops(log);
        IReadOnlyList<Property> list = [new Property("P", Body(Tick())) { DeclarationSpans = [new SourceSpan(1, 1, 1, 2)] }];
        var root = new Algorithm.User(null, [], [], list, [N(0)]);
        var sink = new RootPropertyObservationSink(root);
        var cache = new RunScopedZeroArgPropertyResultCache(sink);
        var row = invocation ? Seq(Call("P"), R("P")) : Seq(R("P"), R("P"));
        var result = Evaluator.RunCountedObserved(OpenedThrough(new ScopeCtx(Prelude(ops), [], list), row),
            zeroArgPropertyResultCache: cache, hostOperations: ops).Result;
        Assert.Equal("(1, 1)", Render(result.Value.Value));
        Assert.True(cache.GetSnapshot().Stores >= 1);
        Assert.Empty(sink.Complete());
        Assert.Equal(0, sink.DuplicateBindingPublications);
    }
}
