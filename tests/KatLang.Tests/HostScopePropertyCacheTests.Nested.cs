using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// HOST-NESTED-1 (owner decision OD-1(a) of the HOST-LEAN-O6 research, October 24 2026): EVERY
/// ownerless host <see cref="ScopeCtx"/> on a resolving chain contributes its original object, by
/// reference, to the owner identity of the property cache and to the scope identity of the
/// runtime-alias memos — not only a host DECLARING level. An evaluator-owned declaration nested under
/// two distinct host objects (a shared property list, or a record <c>with</c> copy) formerly kept a
/// structural chain identity, so host <c>{ S = tock(); P = { public Q = S } }</c> read as
/// <c>(S, P.Q)</c> through two such objects gave <c>((1, 1), (2, 1))</c>: the second <c>P.Q</c> returned
/// the first object's <c>S</c>. Equivalent rebuilt evaluator-owned levels keep their structural identity.
/// </summary>
public partial class HostScopePropertyCacheTests
{
    // ── 4. HOST-NESTED-1: host ancestors by reference ────────────────────────────────────────

    /// <summary>Host level members <c>S = tock(); P = { public Q = S }</c> (fresh objects on every call).</summary>
    private static Property[] NestedMembers() =>
    [
        Prop("S", Body(Tick())),
        Prop("P", new Algorithm.User(null, [], [], [Prop("Q", Body(R("S")), isPublic: true)], OutputBundle.Empty)),
    ];

    /// <summary>Host level members <c>S = tock(); M = { public P = { public Q = S } }</c>: the host level is TWO levels above <c>Q</c>'s owner.</summary>
    private static Property[] DeepNestedMembers() =>
    [
        Prop("S", Body(Tick())),
        Prop("M", new Algorithm.User(null, [], [], [Prop("P", new Algorithm.User(null, [], [],
            [Prop("Q", Body(R("S")), isPublic: true)], OutputBundle.Empty), isPublic: true)], OutputBundle.Empty)),
    ];

    private static Expr Dot(Expr target, string name, params Expr[] args)
        => new Expr.DotCall(target, name, args.Length == 0 ? null : new OutputBundle(args));

    /// <summary>The second host scope of a pair, built from <paramref name="first"/>'s construction.</summary>
    private static (ScopeCtx First, ScopeCtx Second) HostPair(string shape, ScopeCtx? parent, Func<Property[]> members)
    {
        IReadOnlyList<Property> list = members();
        var first = new ScopeCtx(parent, [], list);
        return (first, shape switch
        {
            "same object" => first,
            "fresh equal scopes" => new ScopeCtx(parent, [], members()),
            "shared Property, distinct lists" => new ScopeCtx(parent, [], [.. list]),
            "shared properties list" => new ScopeCtx(parent, [], list),
            "record with-copy" => first with { },
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        });
    }

    [Theory]
    [InlineData("same object", false, "((1, 1), (1, 1))", "tock1")]
    [InlineData("fresh equal scopes", false, "((1, 1), (2, 2))", "tock1,tock2")]
    [InlineData("shared Property, distinct lists", false, "((1, 1), (2, 2))", "tock1,tock2")]
    [InlineData("shared properties list", false, "((1, 1), (2, 2))", "tock1,tock2")]
    [InlineData("record with-copy", false, "((1, 1), (2, 2))", "tock1,tock2")]
    // The second scope reads P.Q BEFORE S: no stale first-scope value, and both rows agree within a scope.
    [InlineData("same object", true, "((1, 1), (1, 1))", "tock1")]
    [InlineData("shared properties list", true, "((1, 1), (2, 2))", "tock1,tock2")]
    [InlineData("record with-copy", true, "((1, 1), (2, 2))", "tock1,tock2")]
    public async Task NestedOwnedProperty_UnderDistinctHostObjects_KeepsOneEntryPerHostObject(
        string shape, bool secondReadsNestedFirst, string value, string effects)
    {
        ScopeCtx? first = null, second = null;
        Expr Build(ScopeCtx pre)
        {
            (first, second) = HostPair(shape, pre, NestedMembers);
            var nested = Dot(R("P"), "Q");
            return OpenedTwo(first, Seq(R("S"), nested),
                second, secondReadsNestedFirst ? Seq(nested, R("S")) : Seq(R("S"), nested), sequence: true);
        }

        // Generic sync, optimized sync and genuinely suspending async agree on value, effects, steps and stores.
        var outcome = await OnEveryRouteAsync(Build);
        Assert.Equal((value, effects), (outcome.Value, outcome.Effects));

        // Key-level: Q has one entry per host OBJECT — reuse for one object reached twice, never across objects.
        var (_, ticks, cache) = Recorded((pre, _) => Build(pre));
        Assert.Equal(ReferenceEquals(first, second) ? 1 : 2, ticks);
        var q = cache.Reads.Where(k => k.BindingIdentity is Property { Name: "Q" }).ToList();
        Assert.Equal(2, q.Count);
        Assert.All(q, key => Assert.IsType<StructuralOwnerIdentity>(key.OwnerIdentity));
        Assert.Equal(ReferenceEquals(first, second) ? 1 : 2, q.Distinct(ZeroArgPropertyCacheKeyComparer.Instance).Count());
    }

    /// <summary>
    /// The host level sits two levels above <c>Q</c>'s owner (an evaluator-owned <c>M</c> in between), so
    /// an identity that compared only the owner's immediate parent by reference would still merge.
    /// </summary>
    [Theory]
    [InlineData("same object", "((1, 1), (1, 1))", 1)]
    [InlineData("shared properties list", "((1, 1), (2, 2))", 2)]
    [InlineData("record with-copy", "((1, 1), (2, 2))", 2)]
    public async Task NestedOwnedProperty_BeyondTheImmediateParent_KeepsItsHostAncestorByReference(string shape, string value, int qKeys)
    {
        Expr Build(ScopeCtx pre)
        {
            var (first, second) = HostPair(shape, pre, DeepNestedMembers);
            var row = Seq(R("S"), Dot(Dot(R("M"), "P"), "Q"));
            return OpenedTwo(first, row, second, row, sequence: true);
        }

        var outcome = await OnEveryRouteAsync(Build);
        Assert.Equal(value, outcome.Value);
        var (_, _, cache) = Recorded((pre, _) => Build(pre));
        Assert.Equal(qKeys, cache.Reads.Where(k => k.BindingIdentity is Property { Name: "Q" })
            .Distinct(ZeroArgPropertyCacheKeyComparer.Instance).Count());
    }

    /// <summary>
    /// Several host ancestors: the block opens through an EMPTY host level whose parent is the host
    /// level declaring <c>S</c> and <c>P</c>; those declaring levels are a record <c>with</c> copy pair.
    /// </summary>
    [Fact]
    public async Task NestedOwnedProperty_ThroughAnEmptyHostLevel_OverDistinctHostObjects_StaysSeparate()
    {
        var outcome = await OnEveryRouteAsync(pre =>
        {
            var (first, second) = HostPair("record with-copy", pre, NestedMembers);
            var row = Seq(R("S"), Dot(R("P"), "Q"));
            return OpenedTwo(new ScopeCtx(first, [], []), row, new ScopeCtx(second, [], []), row, sequence: true);
        });
        Assert.Equal(("((1, 1), (2, 2))", "tock1,tock2"), (outcome.Value, outcome.Effects));
    }

    [Fact]
    public void NestedOwnedProperty_OnOneSharedCache_StillSeparatesRuns()
    {
        var log = new Log();
        var ops = Ops(log);
        var (first, second) = HostPair("record with-copy", Prelude(ops), NestedMembers);
        var row = Seq(R("S"), Dot(R("P"), "Q"));
        var expr = OpenedTwo(first, row, second, row, sequence: true);
        var shared = new RecordingCache();
        Assert.Equal("((1, 1), (2, 2))", Render(Evaluator.RunCountedObserved(expr, zeroArgPropertyResultCache: shared, hostOperations: ops).Result.Value.Value));
        Assert.Equal("((3, 3), (4, 4))", Render(Evaluator.RunCountedObserved(expr, zeroArgPropertyResultCache: shared, hostOperations: ops).Result.Value.Value));
        Assert.Equal(4, shared.Reads.Where(k => k.BindingIdentity is Property { Name: "Q" })
            .Distinct(ZeroArgPropertyCacheKeyComparer.Instance).Count());
    }

    /// <summary>The nested witness with <c>S</c> waiting on a deterministic gate: the async route really suspends inside the host callback.</summary>
    [Fact]
    public async Task NestedOwnedProperty_WithAGatedSuspension_KeepsOneEntryPerHostObject()
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var ops = HostOperations.Create(HostOperation.CreateAsync("gate", async (_, token) =>
        {
            var call = ++calls;
            entered.TrySetResult();
            await release.Task.WaitAsync(token);
            return new Result.Atom(call);
        }));
        var (first, second) = HostPair("record with-copy", Prelude(ops), () =>
        [
            Prop("S", Body(Call("gate"))),
            Prop("P", new Algorithm.User(null, [], [], [Prop("Q", Body(R("S")), isPublic: true)], OutputBundle.Empty)),
        ]);
        var row = Seq(R("S"), Dot(R("P"), "Q"));
        var cache = new SuspendingRecordingCache();
        var pending = Evaluator.RunCountedObservedAsync(OpenedTwo(first, row, second, row, sequence: true),
            zeroArgPropertyResultCache: cache, hostOperations: ops).AsTask();
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(30));
        Assert.False(pending.IsCompleted); // suspended inside the first S
        release.SetResult();
        var (result, _) = await pending.WaitAsync(TimeSpan.FromSeconds(30));

        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal("((1, 1), (2, 2))", Render(result.Value.Value));
        Assert.Equal(2, calls);
        Assert.Equal(0, cache.ActiveOwnerCount);
        Assert.Equal(2, cache.Keys.Where(k => k.BindingIdentity is Property { Name: "Q" })
            .Distinct(ZeroArgPropertyCacheKeyComparer.Instance).Count());
    }

    /// <summary>
    /// The identity relation itself (property owners and alias scopes alike): host levels anywhere on
    /// the chain by reference — including EMPTY host levels, which have no list to tell them apart —
    /// while rebuilt evaluator-owned levels over the same host ancestry stay equal, with equal hashes.
    /// A host level never equals an evaluator-owned level with the same (empty) lists. Building the
    /// identity evaluates nothing.
    /// </summary>
    [Fact]
    public void OwnerIdentity_ComparesEveryHostAncestorByReference_AndRebuiltOwnedLevelsStructurally()
    {
        IReadOnlyList<Expr> noOpens = [];
        IReadOnlyList<Property> hostList = [Prop("S", Body(Tick()))];
        var host = new ScopeCtx(null, noOpens, hostList);
        var copy = host with { };
        var emptyHost = new ScopeCtx(null, [], []);
        var otherEmptyHost = new ScopeCtx(null, [], []);
        Assert.Equal(host, copy);
        Assert.Equal(emptyHost, otherEmptyHost);

        IReadOnlyList<Property> pList = [Prop("Q", Body(R("S")), isPublic: true)];
        var p = new Algorithm.User(null, [], noOpens, pList, OutputBundle.Empty);
        IReadOnlyList<Property> mList = [Prop("P", p, isPublic: true)];
        var m = new Algorithm.User(null, [], noOpens, mList, OutputBundle.Empty);
        // Rebuilt evaluator-owned levels: fresh records every time, as structural access mints them.
        ScopeCtx MLevel(ScopeCtx? parent) => new(parent, noOpens, mList) { Owner = m };
        ScopeCtx PLevel(ScopeCtx? parent) => new(parent, noOpens, pList) { Owner = p };
        StructuralOwnerIdentity Owner(ScopeCtx? parent) => StructuralOwnerIdentity.FromPropertyOwner(p with { Parent = parent });

        void Same(StructuralOwnerIdentity x, StructuralOwnerIdentity y)
        {
            Assert.Equal(x, y);
            Assert.Equal(x.GetHashCode(), y.GetHashCode());
        }

        // Immediate host parent, host two levels up, and an EMPTY host level two levels up.
        Same(Owner(host), Owner(host));
        Assert.NotEqual(Owner(host), Owner(copy));
        Same(Owner(MLevel(host)), Owner(MLevel(host)));
        Assert.NotEqual(Owner(MLevel(host)), Owner(MLevel(copy)));
        Same(Owner(MLevel(emptyHost)), Owner(MLevel(emptyHost)));
        Assert.NotEqual(Owner(MLevel(emptyHost)), Owner(MLevel(otherEmptyHost)));
        // Owner kinds: an empty host level is not an empty evaluator-owned level.
        Assert.NotEqual(Owner(MLevel(emptyHost)), Owner(MLevel(new ScopeCtx(null, [], []) { Owner = m })));
        // Evaluator-owned empty levels keep their resolution-equivalence.
        Same(Owner(new ScopeCtx(host, [], []) { Owner = m }), Owner(new ScopeCtx(host, [], []) { Owner = m }));

        // The alias scope identity applies the same rule at the declaring level and above it.
        Same(StructuralOwnerIdentity.FromScope(PLevel(MLevel(host))), StructuralOwnerIdentity.FromScope(PLevel(MLevel(host))));
        Assert.NotEqual(StructuralOwnerIdentity.FromScope(PLevel(MLevel(host))), StructuralOwnerIdentity.FromScope(PLevel(MLevel(copy))));
        Assert.NotEqual(StructuralOwnerIdentity.FromScope(PLevel(emptyHost)), StructuralOwnerIdentity.FromScope(PLevel(otherEmptyHost)));
        Assert.NotEqual(StructuralOwnerIdentity.FromScope(emptyHost), StructuralOwnerIdentity.FromScope(otherEmptyHost));
        Same(StructuralOwnerIdentity.FromScope(emptyHost), StructuralOwnerIdentity.FromScope(emptyHost));

        // Whole keys: owner equivalence is one component; binding, environment and run still separate.
        var run = new object();
        var q = pList[0];
        ZeroArgPropertyCacheKey Key(ScopeCtx parent, object runIdentity) => ZeroArgPropertyCacheKey.FromExecution(
            new ZeroArgPropertyExecution(p with { Parent = MLevel(parent) }, q, ZeroArgPropertyAccessKind.CountedStructural, new object(), runIdentity));
        var comparer = ZeroArgPropertyCacheKeyComparer.Instance;
        Assert.True(comparer.Equals(Key(host, run), Key(host, run)));
        Assert.Equal(comparer.GetHashCode(Key(host, run)), comparer.GetHashCode(Key(host, run)));
        Assert.False(comparer.Equals(Key(host, run), Key(copy, run)));
        Assert.False(comparer.Equals(Key(host, run), Key(host, new object())));
    }

    // No declaration is attached to the intermediate host level. Its provenance must still be
    // present in the actual Q key, even though S resolves at the SAME farther host object.
    [Theory]
    [InlineData(false, false, 2)]
    [InlineData(false, true, 1)]
    [InlineData(true, false, 2)]
    [InlineData(true, true, 1)]
    public async Task NestedOwnedProperty_EmptyOrOpensOnlyHostAncestor_ContributesItsOwnIdentity(
        bool opensOnly, bool sameHost, int qKeys)
    {
        Expr Build(ScopeCtx pre)
        {
            var outerHost = new ScopeCtx(pre, [], [Prop("S", Body(Tick()))]);
            IReadOnlyList<Expr> opens = opensOnly ? [new Expr.AlgorithmExpr(Body(N(0)))] : [];
            var host = new ScopeCtx(outerHost, opens, []);
            var provider = new Algorithm.User(host, [], [], [Prop("Q", Body(R("S")), isPublic: true)], OutputBundle.Empty);
            Expr ReadThrough(ScopeCtx parent) => new Expr.AlgorithmExpr(new Algorithm.User(null, [],
                [new Expr.AlgorithmExpr(provider with { Parent = parent })], [], new OutputBundle([R("Q")])));
            return new Expr.AlgorithmExpr(Body(Seq(ReadThrough(host), ReadThrough(sameHost ? host : host with { }))));
        }

        var outcome = await OnEveryRouteAsync(Build);
        Assert.Equal(("(1, 1)", "tock1"), (outcome.Value, outcome.Effects));
        var (_, ticks, cache) = Recorded((pre, _) => Build(pre));
        Assert.Equal(1, ticks);
        Assert.Equal(qKeys, cache.Reads.Where(k => k.BindingIdentity is Property { Name: "Q" })
            .Distinct(ZeroArgPropertyCacheKeyComparer.Instance).Count());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void OwnerAndAliasIdentity_KeepMultipleHostLevels_AcrossRebuiltOwnedLevels(bool opensOnly)
    {
        IReadOnlyList<Expr> opens = opensOnly ? [new Expr.AlgorithmExpr(Body(N(0)))] : [];
        var farHost = new ScopeCtx(null, opens, []);
        var middleOwner = Body(N(0));
        ScopeCtx RebuildMiddle(ScopeCtx parent) => new(parent, [], []) { Owner = middleOwner };
        var nearHost = new ScopeCtx(RebuildMiddle(farHost), opens, []);
        var owner = Body(N(0));
        StructuralOwnerIdentity[] Identities(ScopeCtx parent) =>
        [
            StructuralOwnerIdentity.FromOwner(owner with { Parent = parent }),
            StructuralOwnerIdentity.FromPropertyOwner(owner with { Parent = parent }),
            StructuralOwnerIdentity.FromScope(new ScopeCtx(parent, [], []) { Owner = owner }),
        ];

        var first = Identities(RebuildMiddle(nearHost));
        var rebuilt = Identities(RebuildMiddle(nearHost));
        var nearCopy = Identities(RebuildMiddle(nearHost with { }));
        // Change only the farther host, with evaluator-owned wrappers rebuilt around it.
        var farFirst = Identities(RebuildMiddle(farHost));
        var farCopy = Identities(RebuildMiddle(farHost with { }));
        for (var i = 0; i < first.Length; i++)
        {
            Assert.Equal(first[i], rebuilt[i]);
            Assert.Equal(first[i].GetHashCode(), rebuilt[i].GetHashCode());
            Assert.NotEqual(first[i], nearCopy[i]);
            Assert.NotEqual(farFirst[i], farCopy[i]);
        }
    }

    /// <summary>
    /// Runtime-target alias binding cells of an alias declared in an evaluator-owned level BENEATH a host
    /// level: one cell per host object (never shared with a record-equal copy), the same cell for one
    /// host object reached twice and for rebuilt owned levels over it — and retrieving a cell neither
    /// demands its receiver nor projects its target.
    /// </summary>
    [Fact]
    public void NestedRuntimeAliasCells_FollowTheHostAncestor_WithoutDemandingEitherChannel()
    {
        var ctx = Evaluator.EvalCtx.Empty;
        IReadOnlyList<Property> members = RuntimeAliasMembers(collectingTarget: true);
        var p = new Algorithm.User(null, [], [], members, OutputBundle.Empty);
        var alias = Assert.IsType<Algorithm.Alias>(members.Single(x => x.Name == "A").Value);
        var host = new ScopeCtx(null, [], [Prop("P", p)]);
        var copy = host with { };
        ScopeCtx PLevel(ScopeCtx parent) => new(parent, [], members) { Owner = p };

        var first = Evaluator.AliasBindingCell(alias with { Parent = PLevel(host) }, ctx);
        Assert.Same(first, Evaluator.AliasBindingCell(alias with { Parent = PLevel(host) }, ctx));
        var second = Evaluator.AliasBindingCell(alias with { Parent = PLevel(copy) }, ctx);
        Assert.NotSame(first, second);
        Assert.Same(second, Evaluator.AliasBindingCell(alias with { Parent = PLevel(copy) }, ctx));
        Assert.Equal(2, ctx.Budget.AliasBindingCells.Count);
        Assert.All(new[] { first, second }, cell =>
        {
            Assert.False(cell.HasCompletedValue);
            Assert.Equal(0, cell.ProjectionComputations);
        });
    }


    /// <summary>
    /// End to end: <c>P = { F; Capture; R = Capture(F()); A = R.Algorithm; public V(x) = (A, A(), A, A(…)) }</c>
    /// in a host level, <c>P.V(0)</c> read through two host objects. <c>V</c> is parameterized (never
    /// cached). With the property cache DISABLED only the alias binding cell can carry a value from one
    /// block to the other — a user-visible alias observation, not only a key-level one: two distinct
    /// host objects (sharing a list, or a <c>with</c> copy) behave exactly like two independently built
    /// ones (the control), while one object reached twice reuses its cell and every call stays fresh
    /// (M4★: whatever the target's arity, so the cached value equals the uncached one). With the
    /// ordinary cache, every route agrees as well.
    /// </summary>
    [Theory]
    [InlineData(false, "same object", "((1, 2, 1, 3), (1, 4, 1, 5))", "((1, 2, 1, 3), (1, 4, 1, 5))")]
    [InlineData(false, "shared properties list", "((1, 2, 1, 3), (4, 5, 4, 6))", "((1, 2, 1, 3), (4, 5, 4, 6))")]
    [InlineData(false, "record with-copy", "((1, 2, 1, 3), (4, 5, 4, 6))", "((1, 2, 1, 3), (4, 5, 4, 6))")]
    [InlineData(true, "same object", "((1, 2, 1, 3), (1, 4, 1, 5))", "((1, 2, 1, 3), (1, 4, 1, 5))")]
    [InlineData(true, "shared properties list", "((1, 2, 1, 3), (4, 5, 4, 6))", "((1, 2, 1, 3), (4, 5, 4, 6))")]
    [InlineData(true, "record with-copy", "((1, 2, 1, 3), (4, 5, 4, 6))", "((1, 2, 1, 3), (4, 5, 4, 6))")]
    public async Task NestedRuntimeAlias_UnderDistinctHostObjects_KeepsOneBindingCellPerHostObject(
        bool collectingTarget, string shape, string uncachedValue, string cachedValue)
    {
        Func<ScopeCtx, Expr> Build(string pairShape) => pre =>
        {
            var (first, second) = HostPair(pairShape, pre, () =>
            [
                Prop("P", new Algorithm.User(null, [], [],
                [
                    .. RuntimeAliasMembers(collectingTarget),
                    Prop("V", Fn("x", Seq(R("A"), Call("A"), R("A"), collectingTarget ? Call("A", N(5)) : Call("A"))), isPublic: true),
                ], OutputBundle.Empty)),
            ]);
            var row = Dot(R("P"), "V", N(0));
            return OpenedTwo(first, row, second, row, sequence: true);
        };

        static (string Value, string Effects) Uncached(Func<ScopeCtx, Expr> build, bool optimized)
        {
            var log = new Log();
            var ops = Ops(log);
            var (result, _) = Evaluator.RunCountedObserved(build(Prelude(ops)), enableOptimizations: optimized,
                zeroArgPropertyResultCache: UncachedZeroArgPropertyResultCache.Instance, hostOperations: ops);
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            return (Render(result.Value.Value), string.Join(",", log.Effects));
        }

        foreach (var optimized in new[] { false, true })
        {
            var observed = Uncached(Build(shape), optimized);
            Assert.Equal(uncachedValue, observed.Value);
            if (shape != "same object")
                Assert.Equal(Uncached(Build("fresh equal scopes"), optimized), observed);
        }

        var outcome = await OnEveryRouteAsync(Build(shape));
        Assert.Equal(cachedValue, outcome.Value);
        if (shape != "same object")
            Assert.Equal(await OnEveryRouteAsync(Build("fresh equal scopes")), outcome);
    }
}
