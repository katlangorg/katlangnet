using System.Collections;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// KEY FACTS PER SCOPE LEVEL (implementation-only optimization, 2026-11-22; finding
/// <c>caching-retention-key-depth-per-read</c> of the 2026-11-21 adversarial investigation, baseline
/// <c>8947d21e</c>; C#-only, no Lean change). Every zero-argument property request builds its cache key, and
/// before this change each request copied its owner's whole parent chain into a fresh array, hashed it,
/// compared it level by level with the stored key and walked the declaring chain again for the owning
/// invocation or binding identity: about 16 B and 17 ns per lexical level per read, hits included (an alias
/// read paid about 140 B per level for its memo key as well). A level's facts — its structural chain identity
/// and the nearest invocation-owning and nearest activation of its chain (<see cref="ScopeKeyFacts"/>) — are now
/// memoized on the evaluator-owned level itself, and keys share the parent's chain identity.
/// <para>Pinned here: (1) the identity is still the former flat-chain comparison, and the declaring
/// identities still the former walks, on random chains with host levels, activations, empty and shared lists
/// and <c>with</c> copies; (2) the work of a read does not grow with lexical depth or repeat count (level
/// computations independent of the repeat count, allocation per read independent of the depth); (3) the
/// cache law is unchanged at depth — per owning call, per activation, distinct owners, aliases, runtime
/// alias cells, deconstruction, failed publication, cancellation, Result identity, detached evaluation and the
/// alias memos' detachment test — on every route; and (4) retention: no key or memo keeps an activation, a finished call or a finished run
/// alive, and no host-built level (a shared blueprint) carries a memo.</para>
/// </summary>
public sealed class PropertyKeyDepthTests(ITestOutputHelper output)
{
    // ── 1. The identity is the former flat chain comparison ───────────────────────────────────

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(4)]
    public void Identities_AgreeWithTheFlatChainComparison_OnRandomChains(int seed)
    {
        var world = new ChainWorld(seed);
        var built = new List<(StructuralOwnerIdentity Actual, Flat Oracle)>();
        for (var step = 0; step < 900; step++)
        {
            switch (world.Next(6))
            {
                case 0:
                    world.NewLevel();
                    break;
                case 1:
                    world.NewTwin();
                    break;
                case 2:
                    world.NewCopy();
                    break;
                case 3:
                    world.CheckDeclaringIdentities();
                    break;
                default:
                    built.Add(world.Construct());
                    break;
            }
        }

        Assert.True(built.Count > 200, $"only {built.Count} identities");
        var equalPairs = 0;
        for (var i = 0; i < built.Count; i++)
        {
            for (var j = 0; j < built.Count; j++)
            {
                var expected = FlatEquals(built[i].Oracle, built[j].Oracle);
                Assert.True(expected == built[i].Actual.Equals(built[j].Actual), $"pair {i}, {j}: expected {expected}");
                Assert.Equal(expected, ZeroArgPropertyCacheKeyComparer.OwnerIdentityEquals(built[i].Actual, built[j].Actual));
                if (expected)
                {
                    Assert.Equal(built[i].Actual.GetHashCode(), built[j].Actual.GetHashCode());
                    if (i != j)
                        equalPairs++;
                }
            }
        }

        // Equal pairs over distinct objects exist (twins, copies, rebuilt owners, separately allocated empty lists).
        Assert.True(equalPairs > 0, "no equal pair of distinct constructions");
    }

    [Fact]
    public void AWithCopyOfAMemoizedLevel_ComputesItsOwnFacts_AndTheOriginalKeepsItsOwn()
    {
        var ctx = Evaluator.EvalCtx.Empty;
        var p1 = new ScopeCtx(null, [], [NewProperty("a")]) { Owner = NewAlgorithm() };
        var p2 = new ScopeCtx(null, [], [NewProperty("b")], ["x"])
        {
            Owner = NewAlgorithm(),
            Activation = ParameterActivation.Capture(["x"], ctx, [], invoked: true),
        };
        var level = new ScopeCtx(p1, [], [NewProperty("c")]) { Owner = NewAlgorithm() };

        var original = StructuralOwnerIdentity.FromScope(level);
        Assert.Null(Evaluator.DeclaringInvocationIdentity(level));
        Assert.Same(original, StructuralOwnerIdentity.FromScope(level));
        Assert.NotNull(level.StaticKeyFacts);

        // The copy carries the original's runtime slot, and with it the original's memo, until it computes its own.
        var copy = level with { Parent = p2 };
        Assert.Same(level.StaticKeyFacts, copy.StaticKeyFacts);
        var copied = StructuralOwnerIdentity.FromScope(copy);
        Assert.NotEqual(original, copied);
        Assert.Equal(StructuralOwnerIdentity.FromScope(new ScopeCtx(p2, level.Opens, level.Properties) { Owner = level.Owner }), copied);
        Assert.Same(p2.Activation!.ValueEnvironmentIdentity, Evaluator.DeclaringInvocationIdentity(copy));
        Assert.Same(p2.Activation, Evaluator.DeclaringActivation(copy));
        Assert.NotSame(level.StaticKeyFacts, copy.StaticKeyFacts);

        // The original still answers with its own facts.
        Assert.Same(original, StructuralOwnerIdentity.FromScope(level));
        Assert.Null(Evaluator.DeclaringInvocationIdentity(level));
        Assert.Null(Evaluator.DeclaringActivation(level));

        // A copy of an ACTIVATED level shares the activation (and the memo on it) but not its parent chain.
        var activated = new ScopeCtx(p1, [], [NewProperty("d")], ["y"])
        {
            Owner = NewAlgorithm(),
            Activation = ParameterActivation.Capture(["y"], ctx, [], invoked: false),
        };
        var activatedIdentity = StructuralOwnerIdentity.FromScope(activated);
        Assert.Null(Evaluator.DeclaringInvocationIdentity(activated));
        var activatedCopy = activated with { Parent = p2 };
        Assert.Same(p2.Activation.ValueEnvironmentIdentity, Evaluator.DeclaringInvocationIdentity(activatedCopy));
        Assert.Same(activated.Activation, Evaluator.DeclaringActivation(activatedCopy));
        Assert.NotEqual(activatedIdentity, StructuralOwnerIdentity.FromScope(activatedCopy));
        Assert.Equal(activatedIdentity, StructuralOwnerIdentity.FromScope(activated));
        Assert.Null(Evaluator.DeclaringInvocationIdentity(activated));
    }

    [Fact]
    public void AnOwnerIdentity_IsReusedOverOneLevel_OnlyForTheSameDeclarationAndLists()
    {
        var parent = new ScopeCtx(null, [], [NewProperty("a")]) { Owner = NewAlgorithm() };
        var owner = NewAlgorithm() with { Properties = [NewProperty("p")], Parent = parent };

        var first = StructuralOwnerIdentity.FromPropertyOwner(owner);
        // A rebuilt owner over the same lists and declaration: the identity built over the level is reused.
        Assert.Same(first, StructuralOwnerIdentity.FromPropertyOwner(owner with { Output = [] }));
        // Another list, or the declaration left out: a new identity, never the reused one.
        var otherList = StructuralOwnerIdentity.FromPropertyOwner(owner with { Properties = [NewProperty("p")] });
        Assert.NotEqual(first, otherList);
        var undeclared = StructuralOwnerIdentity.FromOwner(owner);
        Assert.NotEqual(first, undeclared);
        Assert.NotEqual(first, StructuralOwnerIdentity.FromPropertyOwner(NewAlgorithm() with { Properties = owner.Properties, Parent = parent }));
        // A rebuilt owner over a distinct but structurally equal parent compares equal.
        var twin = new ScopeCtx(null, parent.Opens, parent.Properties) { Owner = parent.Owner };
        Assert.Equal(first, StructuralOwnerIdentity.FromPropertyOwner(owner with { Parent = twin }));
    }

    [Fact]
    public void ActivationLookups_CrossHostLevelsWithoutBuildingStructuralKeys()
    {
        var activation = ParameterActivation.Capture(["x"], Evaluator.EvalCtx.Empty, [], invoked: true);
        var parent = new ScopeCtx(null, [], []) { Owner = NewAlgorithm(), Activation = activation };
        _ = ScopeKeyFacts.Describe(parent);
        for (int i = 0; i < 128; i++)
            parent = new ScopeCtx(parent, [], []);

        ScopeKeyFacts.CountComputations();
        long computations;
        try
        {
            Assert.Same(activation.ValueEnvironmentIdentity, Evaluator.DeclaringInvocationIdentity(parent));
            Assert.Same(activation, Evaluator.DeclaringActivation(parent));
            Assert.Equal(activation.Serial, ScopeKeyFacts.ForActivationLookup(parent).OldestActivationSerial);
        }
        finally
        {
            computations = ScopeKeyFacts.StopCountingComputations();
        }
        Assert.Equal(0, computations);
    }

    [Fact]
    public async Task ConcurrentFirstPublications_KeepBothStaticLevelMemos()
    {
        var levels = Enumerable.Range(0, 256)
            .Select(_ => new ScopeCtx(null, [], []) { Owner = NewAlgorithm() })
            .ToArray();
        var run = Evaluator.EvalCtx.Empty.Budget;
        await Task.WhenAll(
            Task.Run(() =>
            {
                foreach (var level in levels)
                    level.PublishStaticOpenLevel(new Evaluator.ResolvedOpenLevel(level, run, []));
            }),
            Task.Run(() =>
            {
                foreach (var level in levels)
                    _ = ScopeKeyFacts.Of(level);
            }));
        foreach (var level in levels)
        {
            Assert.Same(level, level.StaticKeyFacts?.Level);
            Assert.Same(level, level.StaticOpenLevel?.Level);
        }
    }

    // ── 2. Work against lexical depth and repeat count ────────────────────────────────────────

    public static TheoryData<string> Workloads() => ["exported", "underCall", "localOnly", "alias", "deconstruction", "invocation"];

    /// <summary>
    /// The number of level computations a run makes (<see cref="ScopeKeyFacts.CountComputations"/>) does not
    /// depend on how often the deep property is read: each level of the chain is described once, however
    /// many reads build keys over it. It grows linearly with the depth (one per lexical level, plus the
    /// levels the run itself wires). Formerly every read rebuilt the whole chain.
    /// </summary>
    [Theory]
    [MemberData(nameof(Workloads))]
    public void LevelComputations_DoNotDependOnTheRepeatCount_AndAreLinearInDepth(string workload)
    {
        foreach (var optimized in new[] { true, false })
        {
            foreach (var depth in new[] { 1, 8, 32 })
            {
                var few = Computations(workload, depth, repeats: 16, optimized);
                var many = Computations(workload, depth, repeats: 512, optimized);
                output.WriteLine($"{workload} depth {depth} optimized {optimized}: {few} computations for 16 reads, {many} for 512");
                Assert.Equal(few, many);
                // One per lexical level plus the root and the prelude levels (measured: depth + 1 or depth + 2).
                Assert.InRange(few, depth, (2 * depth) + 8);
            }
        }
    }

    /// <summary>
    /// The bytes a read allocates do not grow with the depth of its declaration: the per-read slope (the
    /// difference of two runs that differ only in the repeat count, so one-time work per level cancels) at depth
    /// 32 is within 32 B of the slope at depth 1. Formerly it grew by about 16 B per level for every read and by
    /// about 140 B per level for an alias read — 500 B and 4.3 KB per read at depth 32. The time per read is
    /// printed for information only (wall-clock ratios are not asserted in the shared suite).
    /// </summary>
    [Theory]
    [MemberData(nameof(Workloads))]
    public void BytesPerRead_DoNotGrowWithTheDepthOfTheDeclaration(string workload)
    {
        var shallow = PerRead(workload, depth: 1);
        var deep = PerRead(workload, depth: 32);
        output.WriteLine($"{workload}: depth 1 {shallow.Bytes:F1} B/read {shallow.Nanoseconds:F0} ns/read; depth 32 {deep.Bytes:F1} B/read {deep.Nanoseconds:F0} ns/read");
        Assert.True(deep.Bytes - shallow.Bytes < 32, $"{workload}: {deep.Bytes:F1} B/read at depth 32 against {shallow.Bytes:F1} at depth 1");
    }

    // ── 3. The cache law at depth, on every route ──────────────────────────────────────────────

    private const int Depth = 24;

    [Fact]
    public async Task ADeepRunScopedProperty_IsEvaluatedOnce_ForEveryRead()
    {
        var observed = await SixRouteAgreement.OnEveryRouteAsync(
            Nested(Depth, "X = tock()\nStep(i, acc) = acc + X\nreduce(range(1, 8), Step, 0) + X"));

        Assert.Equal("ok", observed.Kind);
        Assert.Equal("9", observed.Value);
        Assert.Equal(["tock#1"], observed.HostCalls);
    }

    [Fact]
    public async Task ADeepExportedProperty_IsFreshPerOwningCall_AndSharedWithinIt()
    {
        var observed = await SixRouteAgreement.OnEveryRouteAsync(
            UnderCall(Nested(Depth, "X = tock()\nStep(i, acc) = acc + X\nreduce(range(1, 8), Step, 0)", "L1 + n")) + "G(10), G(20)\n");

        // Each call of G has its own X (8 reads of tock#1, then 8 of tock#2); reads within a call share it.
        Assert.Equal("S[18, 36]", observed.Value);
        Assert.Equal(["tock#1", "tock#2"], observed.HostCalls);
    }

    [Fact]
    public async Task ADeepLocalOnlyProperty_IsPerActivation()
    {
        var observed = await SixRouteAgreement.OnEveryRouteAsync(
            UnderCall(Nested(Depth, "X = n + tock()\nStep(i, acc) = acc + X\nreduce(range(1, 8), Step, 0)", "L1 + n")) + "G(10), G(20)\n");

        Assert.Equal("S[98, 196]", observed.Value);
        Assert.Equal(["tock#1", "tock#2"], observed.HostCalls);
    }

    [Fact]
    public async Task TwoStructurallyIdenticalDeepOwners_KeepTheirOwnEntries()
    {
        var nest = Nested(Depth, "X = tock()\nStep(i, acc) = acc + X\nreduce(range(1, 8), Step, 0)");
        var observed = await SixRouteAgreement.OnEveryRouteAsync(
            $"P1 = {{\n{Indent(nest)}\n}}\nP2 = {{\n{Indent(nest)}\n}}\nP1, P2, P1\n");

        Assert.Equal("S[8, 16, 8]", observed.Value);
        Assert.Equal(["tock#1", "tock#2"], observed.HostCalls);
    }

    [Fact]
    public async Task ADeepAlias_ReadsItsTargetsOneEntry()
    {
        var observed = await SixRouteAgreement.OnEveryRouteAsync(
            Nested(Depth, "X = tock()\nA = X\nStep(i, acc) = acc + A\nreduce(range(1, 8), Step, 0) + A"));

        Assert.Equal("9", observed.Value);
        Assert.Equal(["tock#1"], observed.HostCalls);
    }

    [Fact]
    public async Task ADeepRuntimeAliasCell_IsFreshPerOwningCall_AndSharedWithinIt()
    {
        const string prefix = "Cap(meta r) = if(tock() > 0, r, r)\nInc(x) = x + 1\n";
        var observed = await SixRouteAgreement.OnEveryRouteAsync(prefix + "F(y) = {\n" + Indent(Nested(
            Depth, "A = Cap(Inc(5)).Algorithm\nStep(i, acc) = acc + A(1)\nreduce(range(1, 4), Step, 0) * 100 + tock()", "L1 + y")) + "\n}\nF(1), F(2)\n");

        // Per call: the receiver ticks once for the call's cell (shared by the four A(1)), then the row ticks.
        Assert.Equal("S[803, 806]", observed.Value);
        Assert.Equal(["tock#1", "tock#2", "tock#3", "tock#4"], observed.HostCalls);
    }

    [Fact]
    public void ADeepDeconstruction_BindsItsGroupOnce()
    {
        var source = Nested(Depth, "a, b = (tock(), 8)\nStep(i, acc) = acc + a + b\nreduce(range(1, 8), Step, 0)");
        foreach (var optimized in new[] { true, false })
        {
            var ticks = 0;
            var operations = HostOperations.Create(HostOperation.Create("tock", (_, _) => new Result.Atom(++ticks)));
            var observations = new EvaluationObservations();
            var (result, _) = Evaluator.RunCountedObserved(
                Program(source, operations), enableOptimizations: optimized, observations: observations, hostOperations: operations);

            Assert.Equal("ok raw=72 n=1", AsyncEvaluationHarness.NeutralOf(result));
            Assert.Equal(1, ticks);
            Assert.Equal(1, observations.DeconstructionFullBindCount);
        }
    }

    [Fact]
    public async Task ADeepFailingOwner_PublishesNothing_WhileEarlierEntriesStay()
    {
        var source = "Ok = tock()\n" + Nested(Depth, "X = if(tock() == 2, 1 / 0, 5)\nStep(i, acc) = acc + X\nreduce(range(1, 4), Step, 0)", "Ok + L1");
        Assert.StartsWith("DivisionByZero: ", Assert.Single((await SixRouteAgreement.OnEveryRouteAsync(source)).Errors), StringComparison.Ordinal);

        var ticks = 0;
        var operations = HostOperations.Create(HostOperation.Create("tock", (_, _) => new Result.Atom(++ticks)));
        var cache = new RunScopedZeroArgPropertyResultCache(collectStatistics: false);
        Assert.True(Evaluator.RunCountedObserved(Program(source, operations), zeroArgPropertyResultCache: cache, hostOperations: operations).Result.IsError);
        Assert.Equal(1, cache.PublishedCount);
        Assert.Equal(0, cache.ActiveOwnerCount);

        ticks = 0;
        var asyncCache = new RunScopedAsyncZeroArgPropertyResultCache();
        var asyncResult = (await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            Program(source, operations), zeroArgPropertyResultCache: asyncCache, hostOperations: operations))).Result;
        Assert.True(asyncResult.IsError);
        Assert.Equal(1, asyncCache.PublishedCount);
        Assert.Equal(0, asyncCache.ActiveOwnerCount);
    }

    [Fact]
    public async Task CancellationInsideADeepRead_PublishesNothingForIt_AndTheNextRunIsFresh()
    {
        // The call Id(7) enters a dynamic invocation after stop() returns, so the cancellation is observed while
        // X's evaluation is still running.
        var source = Nested(Depth, "Id(v) = v\nX = stop() + Id(7)\nStep(i, acc) = acc + X\nreduce(range(1, 4), Step, 0)");
        foreach (var asynchronous in new[] { false, true })
        {
            using var cts = new CancellationTokenSource();
            var cancel = true;
            var operations = HostOperations.Create(HostOperation.Create("stop", (_, _) =>
            {
                if (cancel)
                    cts.Cancel();
                return new Result.Atom(0);
            }));
            var program = Program(source, operations);
            if (asynchronous)
            {
                var cache = new RunScopedAsyncZeroArgPropertyResultCache();
                await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(
                    program, zeroArgPropertyResultCache: cache, hostOperations: operations, cancellationToken: cts.Token));
                Assert.Equal(0, cache.PublishedCount);
                Assert.Equal(0, cache.ActiveOwnerCount);
            }
            else
            {
                var cache = new RunScopedZeroArgPropertyResultCache(collectStatistics: false);
                Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(
                    program, zeroArgPropertyResultCache: cache, hostOperations: operations, cancellationToken: cts.Token));
                Assert.Equal(0, cache.PublishedCount);
                Assert.Equal(0, cache.ActiveOwnerCount);
            }

            // The same program, run again: nothing of the cancelled run is reused.
            cancel = false;
            Assert.Equal("ok raw=28 n=1", AsyncEvaluationHarness.NeutralOf(
                Evaluator.RunCountedObserved(program, hostOperations: operations).Result));
        }
    }

    [Fact]
    public async Task ReadsOfADeepEntry_HandOnOneResultObject()
    {
        var source = Nested(Depth, "X = [tock(), 2]\nStep(i, acc) = if(Same(X, X), acc + 1, 1 / 0)\nreduce(range(1, 4), Step, 0)");
        var ticks = 0;
        var operations = HostOperations.Create(
            HostOperation.Create("tock", (_, _) => new Result.Atom(++ticks)),
            HostOperation.Create("Same", (args, _) => new Result.Bool(ReferenceEquals(args[0], args[1])), "a", "b"));
        var program = Program(source, operations);

        foreach (var optimized in new[] { true, false })
            Assert.Equal("ok raw=4 n=1", AsyncEvaluationHarness.NeutralOf(
                Evaluator.RunCountedObserved(program, enableOptimizations: optimized, hostOperations: operations).Result));
        Assert.Equal("ok raw=4 n=1", AsyncEvaluationHarness.NeutralOf((await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: operations))).Result));
    }

    [Fact]
    public async Task ADeepExportedEvaluation_ReadsTheLocalPropertiesOfCallsItMakes()
    {
        var observed = await SixRouteAgreement.OnEveryRouteAsync(UnderCall(Nested(
            Depth, "H(z) = {\n  W = z + 1\n  W * 2\n}\nX = H(3) + 0\nStep(i, acc) = acc + X\nreduce(range(1, 4), Step, 0)", "L1 + n")) + "G(1)\n");

        Assert.Equal("33", observed.Value);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task AMisExposedDeepProperty_IsRefusedItsLocalRead(int route)
    {
        // P reads the call's L at the deepest level; forced exported, its detached evaluation must refuse it.
        string[] parts = ["F", .. Enumerable.Range(1, Depth).Select(static k => "L" + k), "P"];
        var path = string.Join('.', parts);
        var program = MisExposed("F(y) = {\n" + Indent(Nested(Depth, "L = y * 10\nP = L + 1\nP + 0")) + "\n}\nF(1)\n", path);

        var result = await RunOnRoute(program, route);

        Assert.True(result.IsError);
        var refused = Assert.IsType<EvalError.LocalOnlyProperty>(EvaluatorTestSupport.Innermost(result.Error));
        Assert.Equal("L", refused.PropertyName);
    }

    /// <summary>
    /// The alias memos' detachment test reads the chain's facts (<c>AliasMemoDetached</c>: the chain's oldest
    /// activation against the watermark). <c>A(1)</c> first runs attached and memoizes A's chase through the
    /// local-only member <c>B.G</c>; <c>P</c>, forced exported, calls <c>A(1)</c> again inside its detached
    /// evaluation, where <c>B.G</c> is not accessible. The memo is out of reach there, so the chase runs again and
    /// refuses the selection (<see cref="EvalError.LocalOnlyProperty"/>). Reusing it would skip that check and reach
    /// the call, which then fails on the captured <c>y</c> instead (<see cref="EvalError.UnknownName"/>).
    /// </summary>
    [Theory]
    [InlineData(0, 0)]
    [InlineData(0, 1)]
    [InlineData(0, 2)]
    [InlineData(Depth, 0)]
    [InlineData(Depth, 1)]
    [InlineData(Depth, 2)]
    public async Task AnAliasChasedOutsideAnExportedEvaluation_IsChasedAgainInsideIt(int depth, int route)
    {
        const string inner = "B = {\n  G(z) = z + y\n  G(0)\n}\nA = B.G\nP = A(1) + 0\nA(1) + P";
        string[] parts = ["F", .. Enumerable.Range(1, depth).Select(static k => "L" + k), "P"];
        var program = MisExposed("F(y) = {\n" + Indent(depth == 0 ? inner : Nested(depth, inner)) + "\n}\nF(5)\n", string.Join('.', parts));

        var result = await RunOnRoute(program, route);

        Assert.True(result.IsError);
        var refused = Assert.IsType<EvalError.LocalOnlyProperty>(EvaluatorTestSupport.Innermost(result.Error));
        Assert.Equal("G", refused.PropertyName);
        Assert.Equal("B", refused.ObjectDesc);
    }

    private static async Task<EvalResult<Evaluator.CountedResult>> RunOnRoute(Expr program, int route)
        => route switch
        {
            0 => Evaluator.RunCountedObserved(program).Result,
            1 => Evaluator.RunCountedObserved(program, enableOptimizations: false).Result,
            _ => (await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache()))).Result,
        };

    // ── 4. Retention: no key or memo outlives what it describes ───────────────────────────────

    [Fact]
    public void KeysOverAnActivatedLevel_DoNotKeepItsActivationAlive()
    {
        var (keys, activation) = KeysOverAFreshActivation();
        ForceFullCollection();

        Assert.False(activation.IsAlive, "a key or a memo kept the activation alive");
        GC.KeepAlive(keys);
    }

    [Fact]
    public void ARunScopedKeyOverAFinishedReadsActivation_DoesNotKeepTheActivationAlive()
    {
        // Only's property-style read records an activation; Inner's Z is run-scoped (no call owns the chain) and
        // its key is built over that activated level. The probe runs after Only's read has finished.
        const string source = """
            Only(*xs) = {
              W = count(xs)
              Inner = {
                Z = 7
                Z + 0
              }
              Inner + W
            }
            Only + probe() * 0
            """;
        var (recorded, alive, value) = RunWithActivationProbe(source, "Z", keepStrong: false);
        Assert.Equal("7", value);
        Assert.True(recorded >= 1, $"recorded {recorded}");
        Assert.Equal(0, alive);
    }

    [Fact]
    public void FinishedCalls_WhoseLevelsHeldKeyFacts_AreNotRetained_AndTheProbeSeesRetention()
    {
        const string source = """
            F(x) = {
              Inner = {
                Q = x + 1
                Q * 2
              }
              Inner + 0
            }
            Sum(x, acc) = acc + F(x)
            reduce(range(1, 2000), Sum, 0) + probe() * 0
            """;
        var (recorded, alive, value) = RunWithActivationProbe(source, "Q", keepStrong: false);
        output.WriteLine($"recorded {recorded} activations, {alive} alive at the probe");
        Assert.Equal("4006000", value);
        Assert.True(recorded >= 2000, $"recorded {recorded}");
        Assert.InRange(alive, 0, 8);

        // Control: the probe does see activations that something keeps.
        var (controlRecorded, controlAlive, _) = RunWithActivationProbe(source, "Q", keepStrong: true);
        Assert.Equal(controlRecorded, controlAlive);
    }

    [Fact]
    public void SharedHostBlueprintAndFinishedRuns_CanBeCollectedIndependently()
    {
        var ticks = 0;
        var operations = HostOperations.Create(HostOperation.Create("tock", (_, _) => new Result.Atom(++ticks)));
        var prelude = new ScopeCtx(null, [], operations.RuntimePreludeAlgorithm.Properties);
        var (host, members) = RunSharedBlueprint(operations, prelude);
        Assert.Equal(2, ticks);
        ForceFullCollection();
        Assert.False(host.IsAlive, "the shared host level survived its last program and run");
        Assert.False(members.IsAlive, "the shared declaration list survived its last program and run");
        GC.KeepAlive(prelude);
        GC.KeepAlive(operations);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (WeakReference Host, WeakReference Members) RunSharedBlueprint(HostOperations operations, ScopeCtx prelude)
    {
        var host = new ScopeCtx(prelude, [], [new Property("Q", Body(Call("tock")), false, PropertyExposure.Exported)]);
        // The root opens a block whose PARENT is the host level; the block's member reads the host's Q twice and
        // through a nested owner, so keys are built over both host levels.
        var nested = new Algorithm.User(null, [], [], [new Property("Deep", Body(new Expr.Resolve("Q")), false, PropertyExposure.Exported)],
            new OutputBundle([new Expr.Resolve("Deep")]));
        var block = new Algorithm.User(host, [], [], [
                new Property("Run", Body(Add(new Expr.Resolve("Q"), Add(new Expr.Resolve("Q"), new Expr.Resolve("Inner")))), true, PropertyExposure.Exported),
                new Property("Inner", nested, false, PropertyExposure.Exported),
            ], OutputBundle.Empty);
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [new Expr.AlgorithmExpr(block)], [], new OutputBundle([new Expr.Resolve("Run")])));

        var first = RunAndForget(program, operations);
        var second = RunAndForget(program, operations);

        Assert.Equal("ok raw=3 n=1", first.Outcome);
        Assert.Equal("ok raw=6 n=1", second.Outcome);
        Assert.Null(host.StaticKeyFacts);
        Assert.Null(prelude.StaticKeyFacts);
        Assert.Null(host.Activation);
        ForceFullCollection();
        Assert.False(first.Run.IsAlive, "the program kept its first run alive");
        Assert.False(second.Run.IsAlive, "the program kept its second run alive");
        GC.KeepAlive(program);
        return (new WeakReference(host), new WeakReference(host.Properties));
    }

    // ── Programs ───────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// <paramref name="inner"/> at lexical depth <paramref name="depth"/>: <c>L1 = { L2 = { … Ldepth = { inner } … } }</c>,
    /// each level reading the next once (<c>L{k+1} + 0</c>), then <paramref name="rootOutput"/>.
    /// </summary>
    internal static string Nested(int depth, string inner, string rootOutput = "L1 + 0")
    {
        var body = inner;
        for (var k = depth - 1; k >= 1; k--)
            body = $"L{k + 1} = {{\n{Indent(body)}\n}}\nL{k + 1} + 0";
        return $"L1 = {{\n{Indent(body)}\n}}\n{rootOutput}";
    }

    private static string UnderCall(string body) => $"G(n) = {{\n{Indent(body)}\n}}\n";

    private static string Indent(string text) => "  " + text.Replace("\n", "\n  ", StringComparison.Ordinal);

    private static string Workload(string workload, int depth, int repeats)
    {
        var reads = $"reduce(range(1, {repeats}), Step, 0)";
        return workload switch
        {
            "exported" => Nested(depth, $"X = 7\nStep(i, acc) = acc + X\n{reads}"),
            "underCall" => UnderCall(Nested(depth, $"X = 7\nStep(i, acc) = acc + X\n{reads}", "L1 + n")) + "G(1)\n",
            "localOnly" => UnderCall(Nested(depth, $"X = n + 7\nStep(i, acc) = acc + X\n{reads}", "L1 + n")) + "G(1)\n",
            "alias" => Nested(depth, $"X = 7\nA = X\nStep(i, acc) = acc + A\n{reads}"),
            "deconstruction" => Nested(depth, $"a, b = (7, 8)\nStep(i, acc) = acc + a + b\n{reads}"),
            "invocation" => Nested(depth, $"X = 7\nStep(i, acc) = acc + X()\n{reads}"),
            _ => throw new ArgumentOutOfRangeException(nameof(workload), workload, null),
        };
    }

    private static string WorkloadValue(string workload, int repeats) => workload switch
    {
        "underCall" => (7 * repeats + 1).ToString(System.Globalization.CultureInfo.InvariantCulture),
        "localOnly" => (8 * repeats + 1).ToString(System.Globalization.CultureInfo.InvariantCulture),
        "deconstruction" => (15 * repeats).ToString(System.Globalization.CultureInfo.InvariantCulture),
        _ => (7 * repeats).ToString(System.Globalization.CultureInfo.InvariantCulture),
    };

    private static long Computations(string workload, int depth, int repeats, bool optimized)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(Workload(workload, depth, repeats)).Root);
        ScopeKeyFacts.CountComputations();
        EvalResult<Evaluator.CountedResult> result;
        long computations;
        try
        {
            result = Evaluator.RunCountedObserved(program, enableOptimizations: optimized).Result;
        }
        finally
        {
            computations = ScopeKeyFacts.StopCountingComputations();
        }

        Assert.Equal($"ok raw={WorkloadValue(workload, repeats)} n=1", AsyncEvaluationHarness.NeutralOf(result));
        return computations;
    }

    private static (double Bytes, double Nanoseconds) PerRead(string workload, int depth)
    {
        const int Base = 256;
        const int Extra = 8192;
        var (baseBytes, baseTime) = Measure(workload, depth, Base);
        var (moreBytes, moreTime) = Measure(workload, depth, Base + Extra);
        return ((double)(moreBytes - baseBytes) / Extra, (moreTime - baseTime).TotalNanoseconds / Extra);
    }

    // The least of three runs after a warm-up, on the synchronous optimized route.
    private static (long Bytes, TimeSpan Time) Measure(string workload, int depth, int repeats)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(Workload(workload, depth, repeats)).Root);
        var expected = $"ok raw={WorkloadValue(workload, repeats)} n=1";
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(Evaluator.RunCountedObserved(program).Result));
        var bytes = long.MaxValue;
        var time = TimeSpan.MaxValue;
        for (var run = 0; run < 3; run++)
        {
            var before = GC.GetAllocatedBytesForCurrentThread();
            var watch = System.Diagnostics.Stopwatch.StartNew();
            var result = Evaluator.RunCountedObserved(program).Result;
            watch.Stop();
            var after = GC.GetAllocatedBytesForCurrentThread();
            Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(result));
            bytes = Math.Min(bytes, after - before);
            time = watch.Elapsed < time ? watch.Elapsed : time;
        }

        return (bytes, time);
    }

    private static Expr Program(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    /// <summary>
    /// Parses <paramref name="source"/> cleanly and forces the property at the dotted declaration
    /// <paramref name="path"/> to <see cref="PropertyExposure.Exported"/>; the front end's own verdict must be
    /// local-only (the test breaks a correct classification).
    /// </summary>
    private static Expr MisExposed(string source, string path)
        => new Expr.AlgorithmExpr(Export(SourceProvenance.ParseValid(source).Root, path.Split('.'), 0));

    private static Algorithm Export(Algorithm algorithm, string[] path, int depth)
    {
        var owner = Assert.IsType<Algorithm.User>(algorithm);
        var properties = owner.Properties.ToList();
        var index = properties.FindIndex(property => property.Name == path[depth]);
        Assert.True(index >= 0, $"No property '{path[depth]}' on the path {string.Join('.', path)}.");
        var selected = properties[index];
        if (depth < path.Length - 1)
        {
            properties[index] = selected with { Value = Export(selected.Value, path, depth + 1) };
        }
        else
        {
            Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, selected.Exposure);
            properties[index] = selected with { Exposure = PropertyExposure.Exported, RequiredAncestorParameters = [], CaptureRequirements = null };
        }

        return owner with { Properties = properties };
    }

    private static Algorithm.User Body(params Expr[] rows) => new(null, [], [], [], new OutputBundle(rows));

    private static Expr Call(string name, params Expr[] args) => new Expr.Call(new Expr.Resolve(name), new OutputBundle(args));

    private static Expr Add(Expr left, Expr right) => new Expr.Binary(BinaryOp.Add, left, right);

    // ── Retention probes ───────────────────────────────────────────────────────────────────────

    // A separate frame, so nothing of the level stays reachable from the asserting method's locals.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (object[] Keys, WeakReference Activation) KeysOverAFreshActivation()
    {
        var ctx = Evaluator.EvalCtx.Empty;
        var root = new ScopeCtx(null, [], [NewProperty("r")]) { Owner = NewAlgorithm() };
        var activation = ParameterActivation.Capture(["x"], ctx, [("x", new Result.ListValue([new Result.Atom(1)]))], invoked: true);
        var level = new ScopeCtx(root, [], [NewProperty("a")], ["x"]) { Owner = NewAlgorithm(), Activation = activation };
        var child = NewAlgorithm() with { Properties = [NewProperty("p")], Parent = level };
        var inner = new ScopeCtx(level, [], child.Properties) { Owner = child };
        var keys = new object[]
        {
            StructuralOwnerIdentity.FromPropertyOwner(child),
            StructuralOwnerIdentity.FromScope(level),
            StructuralOwnerIdentity.FromPropertyScope(level),
            StructuralOwnerIdentity.FromScope(inner),
            StructuralOwnerIdentity.FromPropertyOwner(NewAlgorithm() with { Parent = inner }),
        };
        Assert.Same(activation.ValueEnvironmentIdentity, Evaluator.DeclaringInvocationIdentity(inner));
        return (keys, new WeakReference(activation));
    }

    private static (int Recorded, int Alive, string Value) RunWithActivationProbe(string source, string bindingName, bool keepStrong)
    {
        var cache = new ActivationRecordingCache(bindingName, keepStrong);
        var alive = -1;
        var operations = HostOperations.Create(HostOperation.Create("probe", (_, _) =>
        {
            ForceFullCollection();
            alive = cache.Alive();
            return new Result.Atom(0);
        }));
        var (result, _) = Evaluator.RunCountedObserved(Program(source, operations), zeroArgPropertyResultCache: cache, hostOperations: operations);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        return (cache.Recorded, alive, SixRouteAgreement.Neutral(result.Value.Value));
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (string Outcome, WeakReference Run) RunAndForget(Expr program, HostOperations operations)
    {
        var (result, budget) = Evaluator.RunCountedObserved(program, hostOperations: operations);
        return (AsyncEvaluationHarness.NeutralOf(result), new WeakReference(budget));
    }

    private static void ForceFullCollection()
    {
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.WaitForPendingFinalizers();
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
    }

    /// <summary>
    /// Records a weak reference to every activation on the declaring chain of each read of one binding,
    /// around the ordinary run-scoped law; <paramref name="keepStrong"/> also keeps them (the control).
    /// </summary>
    private sealed class ActivationRecordingCache(string bindingName, bool keepStrong) : IZeroArgPropertyResultCache
    {
        private readonly RunScopedZeroArgPropertyResultCache _inner = new(collectStatistics: false);
        private readonly List<WeakReference> _weak = [];
        private readonly List<object> _strong = [];

        internal int Recorded => _weak.Count;

        internal int Alive() => _weak.Count(static reference => reference.IsAlive);

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            if (execution.Binding.Name == bindingName)
            {
                for (var scope = execution.DeclaringScope; scope is not null; scope = scope.Parent)
                {
                    if (scope.Activation is not { } activation)
                        continue;
                    _weak.Add(new WeakReference(activation));
                    if (keepStrong)
                        _strong.Add(activation);
                }
            }

            return _inner.GetOrEvaluate(execution, evaluate);
        }

        public EvalResult<ZeroArgPropertyResult> Invoke(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
            => _inner.Invoke(execution, evaluate);

        public bool ReadObtainsPublishedValue(ZeroArgPropertyCacheKey key) => _inner.ReadObtainsPublishedValue(key);
    }

    // ── The flat-chain oracle and its random world ─────────────────────────────────────────────

    private static Algorithm.User NewAlgorithm() => new(Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: [new Expr.Num(0)]);

    private static Property NewProperty(string name) => new(name, NewAlgorithm(), IsPublic: true);

    /// <summary>The former identity: the declaration and, from the first level outward, each level's host object (or none) and lists.</summary>
    private sealed record Flat(object? Declaration, (ScopeCtx? Host, ICollection Opens, ICollection Properties)[] Levels);

    private static IEnumerable<(ScopeCtx? Host, ICollection Opens, ICollection Properties)> Up(ScopeCtx? scope)
    {
        for (var level = scope; level is not null; level = level.Parent)
            yield return (level.Owner is null ? level : null, (ICollection)level.Opens, (ICollection)level.Properties);
    }

    private static bool FlatEquals(Flat x, Flat y)
        => ReferenceEquals(x.Declaration, y.Declaration)
            && x.Levels.Length == y.Levels.Length
            && x.Levels.Zip(y.Levels).All(static pair =>
                ReferenceEquals(pair.First.Host, pair.Second.Host)
                && SameComponent(pair.First.Opens, pair.Second.Opens)
                && SameComponent(pair.First.Properties, pair.Second.Properties));

    private static bool SameComponent(ICollection x, ICollection y) => ReferenceEquals(x, y) || (x.Count == 0 && y.Count == 0);

    private static ParameterActivation? WalkActivation(ScopeCtx? scope, bool invocation)
    {
        for (var level = scope; level is not null; level = level.Parent)
        {
            if (level.Activation is { } activation && (!invocation || activation.OwnsInvocation))
                return activation;
        }

        return null;
    }

    /// <summary>
    /// Random scope chains: host levels, static and activated evaluator levels (the activation owning an
    /// invocation or not), distinct empty lists and shared non-empty ones, structural twins (distinct level
    /// objects over the same lists and parent) and <c>with</c> copies of levels that may already carry facts.
    /// </summary>
    private sealed class ChainWorld(int seed)
    {
        private readonly Random _random = new(seed);
        private readonly Evaluator.EvalCtx _ctx = Evaluator.EvalCtx.Empty;
        private readonly List<ScopeCtx?> _levels = [null];
        private readonly List<Algorithm.User> _owners = [NewAlgorithm(), NewAlgorithm(), NewAlgorithm()];

        private readonly List<List<Expr>> _opens =
            [new List<Expr>(), new List<Expr>(), new List<Expr> { new Expr.Num(1) }, new List<Expr> { new Expr.Num(2) }];

        private readonly List<List<Property>> _properties =
            [new List<Property>(), new List<Property>(), [NewProperty("a")], [NewProperty("b")], [NewProperty("c")]];

        internal int Next(int bound) => _random.Next(bound);

        private T Pick<T>(IReadOnlyList<T> items) => items[_random.Next(items.Count)];

        internal void NewLevel()
        {
            var parent = Pick(_levels);
            var opens = Pick(_opens);
            var properties = Pick(_properties);
            _levels.Add(_random.Next(5) switch
            {
                0 => new ScopeCtx(parent, opens, properties),
                1 or 2 => new ScopeCtx(parent, opens, properties) { Owner = Pick(_owners) },
                var kind => new ScopeCtx(parent, opens, properties, ["x"])
                {
                    Owner = Pick(_owners),
                    Activation = ParameterActivation.Capture(["x"], _ctx, [], invoked: kind == 3),
                },
            });
        }

        // A distinct level object over the same lists and the same parent (a rebuilt wiring); an activated
        // level's twin gets an activation of its own, a host level's twin is another host object.
        internal void NewTwin()
        {
            if (Pick(_levels) is not { } level)
                return;
            _levels.Add(level.Activation is { } activation
                ? new ScopeCtx(level.Parent, level.Opens, level.Properties, ["x"])
                {
                    Owner = level.Owner,
                    Activation = ParameterActivation.Capture(["x"], _ctx, [], invoked: activation.OwnsInvocation),
                }
                : new ScopeCtx(level.Parent, level.Opens, level.Properties) { Owner = level.Owner });
        }

        // A record copy over another parent: it carries the original's runtime slot (activation and memos).
        internal void NewCopy()
        {
            if (Pick(_levels) is not { } level)
                return;
            _levels.Add(level with { Parent = Pick(_levels) });
        }

        internal void CheckDeclaringIdentities()
        {
            var level = Pick(_levels);
            Assert.Same(WalkActivation(level, invocation: true)?.ValueEnvironmentIdentity, Evaluator.DeclaringInvocationIdentity(level));
            Assert.Same(WalkActivation(level, invocation: false)?.ValueEnvironmentIdentity, Evaluator.DeclaringBindingIdentity(level));
            Assert.Same(WalkActivation(level, invocation: false), Evaluator.DeclaringActivation(level));
            var oldest = long.MaxValue;
            for (var current = level; current is not null; current = current.Parent)
            {
                if (current.Activation is { } activation)
                    oldest = Math.Min(oldest, activation.Serial);
            }

            var facts = ScopeKeyFacts.Describe(level);
            Assert.Equal(oldest, facts.OldestActivationSerial);
            Assert.Same(WalkActivation(level, invocation: true), facts.InvocationActivation);
            Assert.Same(WalkActivation(level, invocation: false), facts.BindingActivation);
        }

        internal (StructuralOwnerIdentity Actual, Flat Oracle) Construct()
        {
            switch (_random.Next(4))
            {
                case 0:
                {
                    var level = Pick(_levels);
                    return (StructuralOwnerIdentity.FromScope(level), new Flat(null, [.. Up(level)]));
                }
                case 1:
                case 2:
                {
                    var owner = Pick(_owners) with { Opens = Pick(_opens), Properties = Pick(_properties), Parent = Pick(_levels) };
                    var declared = _random.Next(2) == 0;
                    var actual = declared ? StructuralOwnerIdentity.FromPropertyOwner(owner) : StructuralOwnerIdentity.FromOwner(owner);
                    return (actual, new Flat(declared ? owner.Declaration : null,
                        [(null, (ICollection)owner.Opens, (ICollection)owner.Properties), .. Up(owner.Parent)]));
                }
                default:
                {
                    if (Pick(_levels) is not { Owner: not null } level)
                        return Construct();
                    return (StructuralOwnerIdentity.FromPropertyScope(level), new Flat(level.Declaration,
                        [(null, (ICollection)level.Opens, (ICollection)level.Properties), .. Up(level.Parent)]));
                }
            }
        }
    }
}
