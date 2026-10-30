using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// Q-37 (owner decision, October 11 2026): THE OUTERMOST PROPERTY-STYLE EVALUATION OWNS THE CACHE
/// ENTRY. A zero-parameter property read that misses the cache while NO evaluation of the same
/// cache key is active becomes that key's OWNER; a read of the same key while its owner is still
/// evaluating — directly (<c>A → A</c>) or indirectly (<c>A → B → A</c>) — is RE-ENTRANT: it
/// evaluates the body normally and returns its own (possibly intermediate) result, but publishes
/// nothing. Only the owner's successful completion is published, and every later ordinary read
/// reuses it. A failed owner publishes nothing for its key; other keys' owners that completed
/// keep their entries. An explicit call <c>A()</c> never reads A's entry; since CACHE-PUB-1 (owner
/// decision, October 22 2026) a qualifying zero-supply <c>A()</c> takes part in the SAME ownership
/// domain: on an empty, inactive key it is the owner, and its success publishes. Formerly
/// (October 11–22 2026) an explicit call owned and published nothing.
///
/// <para>This supersedes the first-successful-completion rule (PROP-09 until October 11 2026),
/// under which the INNERMOST re-entrant read completed first, stored its result, and the
/// outermost result never replaced it: the seeded reproduction printed <c>2, 0</c>; it now prints
/// <c>2, 2</c>. The evidence is deterministic — the seeded random stream (its exact draw count
/// observed on the run's own budget), the counting <c>tick</c> host operation and the logging
/// <c>trace</c> — on all six execution routes (<see cref="SixRouteAgreement"/>), plus internal
/// publication recording for the failure, resource-limit, and cancellation boundaries, which the
/// surface cannot observe after a terminal error. Lean: <c>evalZeroArgPropertyAccessCounted</c>
/// over <c>EvalState.activeZeroArgProperties</c>, <c>CoreTests/PropertyCachePublication.lean</c>.</para>
/// </summary>
public class OutermostPropertyCachePublicationTests
{
    /// <summary>The authoritative Q-37 reproduction (run with random seed 7).</summary>
    private const string SeededReproduction = """
        Classify(r) = if(r == 796, 1, if(r == 339, 2, 3))

        tick = Classify(randomInt(0, 1000))

        A = if(tick() < 3, A + 1, 0)

        A, A
        """;

    private const long ReproductionSeed = 7;

    // ── 1. The authoritative seeded reproduction ─────────────────────────────────────────────

    [Fact]
    public async Task SeededReproduction_PublishesTheOutermostEvaluation_OnEveryRoute()
    {
        // `tick` is the program's own zero-parameter property: `tick()` is an explicit, fresh
        // evaluation drawing 796, 339, 489 (classified 1, 2, 3). The innermost read returns 0,
        // the middle 1, the outermost 2 — and the outermost 2 is what the second row reads.
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(SeededReproduction, randomSeed: ReproductionSeed);

        Assert.Equal("ok", oracle.Kind);
        Assert.Equal("S[2, 2]", oracle.Value);
        Assert.Empty(oracle.HostCalls);
    }

    [Fact]
    public void SeededReproduction_DrawsExactlyTheFirstThreeIntegersOfTheSeededStream()
    {
        // The draws themselves, independently of the cache: 796, 339, 489.
        var draws = Evaluator.RunCountedObserved(Program(
            "randomInt(0, 1000), randomInt(0, 1000), randomInt(0, 1000)"), randomSeed: ReproductionSeed).Result;
        Assert.False(draws.IsError);
        Assert.Equal([796m, 339m, 489m], draws.Value.Value.ToAtoms());
    }

    [Fact]
    public async Task SeededReproduction_ConsumesExactlyThreeRandomDraws()
    {
        // After the run, the run's own stream must stand exactly where a stream stands after
        // three `randomInt(0, 1000)` draws: the next raw word of both agrees. The two- and
        // four-draw references disagree with it, so the probe discriminates the count.
        var three = NextRawWordAfter("randomInt(0, 1000), randomInt(0, 1000), randomInt(0, 1000)");
        Assert.NotEqual(NextRawWordAfter("randomInt(0, 1000), randomInt(0, 1000)"), three);
        Assert.NotEqual(NextRawWordAfter("randomInt(0, 1000), randomInt(0, 1000), randomInt(0, 1000), randomInt(0, 1000)"), three);

        foreach (var optimized in new[] { false, true })
        {
            var (result, budget) = Evaluator.RunCountedObserved(
                Program(SeededReproduction), enableOptimizations: optimized, randomSeed: ReproductionSeed);
            Assert.False(result.IsError, result.ToString());
            Assert.Equal([2m, 2m], result.Value.Value.ToAtoms());
            Assert.Equal(three, budget.RandomSource.NextUInt64());
        }

        var (twinResult, twinBudget) = await Evaluator.RunCountedObservedAsync(
            Program(SeededReproduction),
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
            randomSeed: ReproductionSeed);
        Assert.False(twinResult.IsError, twinResult.ToString());
        Assert.Equal([2m, 2m], twinResult.Value.Value.ToAtoms());
        Assert.Equal(three, twinBudget.RandomSource.NextUInt64());
    }

    // ── 2. Deterministic host-counter evidence ───────────────────────────────────────────────

    [Fact]
    public async Task HostCounterReproduction_PublishesTheOutermostEvaluation_OnEveryRoute()
    {
        // The same shape over the counting host operation (1, 2, 3), independent of the random
        // generator's constants.
        var oracle = await SixRouteAgreement.OnEveryRouteAsync("A = if(tick() < 3, A + 1, 0)\nA, A");

        Assert.Equal("ok", oracle.Kind);
        Assert.Equal("S[2, 2]", oracle.Value);
        Assert.Equal(["tick#1", "tick#2", "tick#3"], oracle.HostCalls);
    }

    // ── 3. The law on every route ────────────────────────────────────────────────────────────

    public static TheoryData<string, string, string[]> RecursivePrograms => new()
    {
        // Deeper recursion: five re-entrant levels below the owner; every row reads the owner's 5.
        { "A = if(tick() < 6, A + 1, 0)\nA, A, A", "S[5, 5, 5]", Ticks(6) },

        // Re-entrant evaluations RETURN their intermediate values (traced 0, then 1) — only the
        // owner's 2 is published.
        { "A = if(tick() < 3, trace(A) + 1, 0)\nA, A", "S[2, 2]", [.. Ticks(3), "trace(0)", "trace(1)"] },

        // Indirect recursion A → B → A: the inner A read is re-entrant through B. B's own owner
        // publishes 3 (computed from A's intermediate 2), A's owner publishes 4.
        { "A = if(tick() < 3, B + 1, 0)\nB = A + 1\nA, A, B, B", "S[4, 4, 3, 3]", Ticks(3) },

        // The same pair entered through B: B's owner publishes 5, A's owner (nested) publishes 4.
        { "A = if(tick() < 3, B + 1, 0)\nB = A + 1\nB, A", "S[5, 4]", Ticks(3) },

        // Sibling re-entrant reads: neither publishes, so EACH evaluates (five ticks) and the
        // owner's 3 is published. This row separates the law from both alternatives: under
        // first-completion-wins the second sibling hit the innermost 1 (`S[3, 1]`, three ticks);
        // under a last-writer-wins publication it hit an intermediate entry (`S[4, 4]`, three).
        { "A = if(tick() < 3, A + A, 1)\nA, A", "S[3, 3]", Ticks(5) },

        // A local-only property of a RECURSIVE owner: each activation of F is its own key, so
        // the nested F(0)'s P is that key's owner (not a re-entrant read of F(1)'s P) and
        // publishes 1 for its second read — one tick in all.
        { "F(x) = {\n    P = if(x == 0, tick(), F(x - 1) + 10)\n    P + P\n}\nF(1)", "24", Ticks(1) },

        // An exported binding read from inside calls: one key per run, owned by its first read.
        { "A = if(tick() < 3, A + 1, 0)\nG(y) = A + y\nG(10), G(20), A", "S[12, 22, 2]", Ticks(3) },

        // A local-only binding: each owner activation is its own key with its own owner.
        { "F(x) = {\n    A = if(tick() < x, A + 1, 0)\n    A, A\n}\nF(3), F(5)", "S[S[2, 2], S[1, 1]]", Ticks(5) },

        // Structural self-reference: `Box.A` inside Box's own member is the same binding.
        { "Box = {\n    public A = if(tick() < 3, Box.A + 1, 0)\n}\nBox.A, Box.A", "S[2, 2]", Ticks(3) },

        // A shadowing local A is a different binding with its own entry.
        { "A = if(tick() < 3, A + 1, 0)\nH = {\n    A = tick() * 100\n    A, A\n}\nA, H, A", "S[2, S[400, 400], 2]", Ticks(4) },

        // CACHE-PUB-1: the explicit A() is A's OWNER (empty, inactive key), so the property-style
        // read inside it is re-entrant (returns 1, publishes nothing) and A()'s own 2 is published
        // and reused. Formerly A() owned nothing, the inner read published 1, and this was S[2, 1].
        { "A = if(tick() < 3, A + 1, 0)\nA(), A", "S[2, 2]", Ticks(3) },

        // CACHE-PUB-1: an explicit call owning an inner explicit call of the same key — the inner
        // A() is re-entrant; the owner's 2 is published (formerly nothing was, and the bare read
        // evaluated a fourth time: S[2, 0]).
        { "A = if(tick() < 3, A() + 1, 0)\nA(), A", "S[2, 2]", Ticks(3) },

        // CACHE-PUB-1: a property read owning an inner explicit call: the inner A() is re-entrant.
        { "A = if(tick() < 3, A() + 1, 0)\nA, A, A()", "S[2, 2, 0]", Ticks(4) },

        // CACHE-PUB-1: indirect re-entry through another property's explicit call: A() owns A, B()
        // owns B, and both inner requests are re-entrant; each owner publishes once.
        { "A = if(tick() < 3, B() + 1, 0)\nB = A + 0\nA(), A, B", "S[2, 2, 1]", Ticks(3) },

        // M4★ (OD-E): `B = A` is a transparent alias owning no entry, so B() is the fresh A() — re-entrant
        // under A()'s ownership, never an owner of its own — and the bare B reads A's one entry (formerly
        // B's own entry held 1: S[2, 2, 1]).
        { "A = if(tick() < 3, B() + 1, 0)\nB = A\nA(), A, B", "S[2, 2, 2]", Ticks(3) },

        // An explicit call after publication evaluates afresh (0) and replaces nothing.
        { "A = if(tick() < 3, A + 1, 0)\nA, A(), A", "S[2, 0, 2]", Ticks(4) },

        // Re-entrance is detected THROUGH an explicit-call frame: B's read inside A() inside B's
        // owner is re-entrant (returns 0, publishes nothing); B's owner publishes 1.
        { "A = if(tick() < 3, B + 1, 0)\nB = A()\nA, A, B", "S[2, 2, 1]", Ticks(3) },

        // Loop steps: an exported step property is one run-wide key, owned at the first
        // iteration (2 + 2 + 2); a local-only one reads the step's state (A * 10 + A over 7).
        { "Step(n) = {\n    A = if(tick() < 3, A + 1, 0)\n    n + A\n}\nStep(0).repeat(3)", "6", Ticks(3) },
        { "Step(n) = {\n    A = if(tick() < 3, A + 1, n)\n    A * 10 + A\n}\nStep(5).repeat(1)", "77", Ticks(3) },

        // Assignment deconstruction: the targets are ordinary properties over the hoisted source, so a
        // re-entrant target read re-reads the source re-entrantly and a target's owner publishes its own
        // result. The C#-only shared-bind memo must not serve a bind computed from an intermediate
        // (re-entrant) source evaluation: these mirror the sibling row above and the reference semantics
        // (one independent bind per target read, as Lean models it).
        { "a, b = if(tick() < 3, (a + a, 0), (1, 1))\na, a", "S[3, 3]", Ticks(5) },
        { "a, b = if(tick() < 3, (a + 1, b), (0, tick()))\na, b", "S[2, 6]", Ticks(6) },

        // Ordinary (non-recursive) caching is unchanged.
        { "P = tick()\nP, P, P", "S[1, 1, 1]", Ticks(1) },
        { "P = tick()\nQ = P + P\nQ, Q, P", "S[2, 2, 1]", Ticks(1) },
    };

    [Theory]
    [MemberData(nameof(RecursivePrograms))]
    public async Task RecursivePrograms_PublishTheOutermostEvaluation_OnEveryRoute(
        string source, string expected, string[] hostCalls)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);

        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(expected, oracle.Value);
        Assert.Equal(hostCalls, oracle.HostCalls);
    }

    // ── 4. Failure, resource limits and cancellation publish nothing for the owner's key ─────

    [Fact]
    public async Task FailedOwner_PublishesNothingForItsKey_AndKeepsAnotherOwnersEntry()
    {
        // A's owner reads B (B's owner completes: published) and then A re-entrantly (completes
        // with 0: NOT published), then fails. Before Q-37 the inner A's 0 was stored.
        const string source = "B = tick() * 10\nA = if(tick() < 3, B + A + 1 / 0, 0)\nA";
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", oracle.Kind);
        Assert.StartsWith(nameof(KatLangErrorCode.DivisionByZero) + ":", Assert.Single(oracle.Errors), StringComparison.Ordinal);
        Assert.Equal(Ticks(3), oracle.HostCalls);

        foreach (var observation in await ObservePublicationsAsync(source))
        {
            Assert.True(observation.Failed, observation.ToString());
            Assert.Equal(["B"], observation.Published);
            Assert.Equal(0, observation.ActiveOwners);
        }
    }

    [Fact]
    public async Task FailedOwnerWithoutNestedSuccess_PublishesNothing()
    {
        const string source = "A = if(tick() < 3, A + 1 / 0, 7)\nA";
        foreach (var observation in await ObservePublicationsAsync(source))
        {
            Assert.True(observation.Failed, observation.ToString());
            Assert.Empty(observation.Published);
            Assert.Equal(0, observation.ActiveOwners);
        }
    }

    [Fact]
    public async Task ResourceLimit_AfterAnInnerSameKeySuccess_PublishesNothing()
    {
        // The innermost A completes with 0; its caller then reaches the step limit inside Heavy.
        const string source = "S(x) = x + 1\nHeavy = repeat(S(0), 1000)\nA = if(tick() < 3, A + Heavy, 0)\nA";
        var limits = new EvaluationLimits { MaxSteps = 300 };
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source, limits: limits);
        Assert.Equal("err", oracle.Kind);
        Assert.StartsWith(nameof(KatLangErrorCode.EvaluationStepLimitExceeded) + ":", Assert.Single(oracle.Errors), StringComparison.Ordinal);

        foreach (var observation in await ObservePublicationsAsync(source, limits))
        {
            Assert.True(observation.Failed, observation.ToString());
            Assert.Empty(observation.Published);
            Assert.Equal(0, observation.ActiveOwners);
        }
    }

    [Fact]
    public async Task Cancellation_DuringReentrantEvaluation_PublishesNothing_AndLeavesNoActiveOwner()
    {
        const string source = "A = if(tick() < 3, A + 1, 0)\nA";

        // Synchronous generic evaluator.
        {
            using var cancellation = new CancellationTokenSource();
            var cache = new PublicationRecordingCache();
            var operations = CancellingTicks(cancellation, cancelAt: 3, asynchronous: false);
            var program = await ProgramAsync(source, operations);
            Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(
                program, enableOptimizations: false, zeroArgPropertyResultCache: cache,
                hostOperations: operations, cancellationToken: cancellation.Token));
            Assert.Empty(cache.Published);
            Assert.Equal(0, cache.ActiveOwners);
        }

        // Async twin with a genuinely suspending host operation.
        {
            using var cancellation = new CancellationTokenSource();
            var cache = new PublicationRecordingCache();
            var operations = CancellingTicks(cancellation, cancelAt: 3, asynchronous: true);
            var program = await ProgramAsync(source, operations);
            await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: cache,
                hostOperations: operations, cancellationToken: cancellation.Token));
            Assert.Empty(cache.Published);
            Assert.Equal(0, cache.ActiveOwners);
        }
    }

    // ── 5. Async: genuine suspension at every access neither deadlocks nor misattributes ─────

    [Theory]
    [InlineData(3, "S[2, 2]")]
    [InlineData(60, "S[59, 59]")]
    public async Task SuspendingAsyncCache_RecursiveReentry_CompletesWithTheOwnersResult(int depth, string expected)
    {
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var operations = CountingTicks(asynchronous: true);
        var observed = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            await ProgramAsync($"A = if(tick() < {depth}, A + 1, 0)\nA, A", operations),
            zeroArgPropertyResultCache: cache,
            hostOperations: operations));

        Assert.False(observed.Result.IsError, observed.Result.ToString());
        Assert.Equal(expected, SixRouteAgreement.Neutral(observed.Result.Value.Value));
        Assert.Equal(0, cache.SyncAccesses);
        Assert.True(cache.ObservedThreadHop);
    }

    [Fact]
    public async Task OwnerPublication_StoresOncePerBinding_AndLeavesNoActiveOwner()
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        var operations = CountingTicks(asynchronous: false);
        var result = Evaluator.RunCountedObserved(
            await ProgramAsync("A = if(tick() < 3, A + 1, 0)\nB = A * 10\nA, B, A, B", operations),
            zeroArgPropertyResultCache: cache, hostOperations: operations).Result;

        Assert.False(result.IsError, result.ToString());
        Assert.Equal([2m, 20m, 2m, 20m], result.Value.Value.ToAtoms());
        var snapshot = cache.GetSnapshot();
        Assert.Equal(2, snapshot.Stores);
        Assert.Equal(2, snapshot.MaxCacheSize);
        Assert.Equal(0, cache.ActiveOwnerCount);
    }

    // ── 6. The Lean guards' hand-built trees, evaluated by C# (identical-program parity) ────

    // Lean has no host operations or randomness, so `CoreTests/PropertyCachePublication.lean`
    // makes a same-key re-entrant read terminate with a host-built tree: P is a parameterless
    // EXPORTED property whose body reads `x` dynamically from its caller, so every read of P has
    // ONE key while successive re-entrant reads see different `x`. The same trees here must give
    // the same values and the same published entries on the C# routes.

    public static TheoryData<string, string, string[]> LeanGuardTrees => new()
    {
        { "pubOutermostOwnsTheEntry", "S[101, 101]", ["P"] },
        { "pubDeeperRecursion", "S[301, 301, 301]", ["P"] },
        { "pubExplicitCallOwnsTheEntry", "S[101, 101]", ["P"] },
        { "pubReentranceThroughExplicitCall", "S[101, 101]", ["M", "R"] },
        { "pubExplicitOwnerInnerExplicitCall", "S[101, 101]", ["PC"] },
        { "pubReadOwnerInnerExplicitCall", "S[101, 1, 101]", ["PR"] },
        { "pubEstablishedEntryUnchangedByFreshCall", "S[101, 1, 101]", ["P"] },
        { "pubFailedExplicitOwnerPublishesNothing", "DivisionByZero", [] },
        { "pubFailedExplicitOwnerKeepsOtherEntries", "DivisionByZero", ["Seven"] },
        { "pubIndirectRecursion", "S[101, 101, 1]", ["IB", "IA"] },
        { "pubSiblingReentrantReadsEachEvaluate", "S[29, 29]", ["PB"] },
        { "pubFailedOwnerPublishesNothing", "DivisionByZero", [] },
        { "pubFailedOwnerKeepsOtherEntries", "DivisionByZero", ["Seven"] },
    };

    [Theory]
    [MemberData(nameof(LeanGuardTrees))]
    public async Task LeanGuardTrees_AgreeWithTheLeanGuards(string guard, string expected, string[] published)
    {
        var program = LeanGuardTree(guard);
        var routes = new List<(string Route, EvalResult<Evaluator.CountedResult> Result, PublicationRecordingCache Cache)>();
        foreach (var optimized in new[] { false, true })
        {
            var cache = new PublicationRecordingCache();
            routes.Add((optimized ? "Optimized" : "Generic",
                Evaluator.RunCountedObserved(program, enableOptimizations: optimized, zeroArgPropertyResultCache: cache).Result,
                cache));
        }

        var twinCache = new PublicationRecordingCache();
        routes.Add(("ForcedTwin",
            (await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: twinCache)).Result,
            twinCache));

        foreach (var (route, result, cache) in routes)
        {
            var observed = result.IsError
                ? KatLangError.FromEvalError(result.Error).Code.ToString()
                : SixRouteAgreement.Neutral(result.Value.Value);
            Assert.True(expected == observed, $"{guard} on {route}: expected {expected}, got {observed}");
            Assert.Equal(published, cache.Published);
            Assert.Equal(0, cache.ActiveOwners);
        }
    }

    /// <summary>
    /// The tree of the named Lean guard (<c>pubRoot</c> with that guard's output rows):
    /// <c>P = if(x == 0, 1, G(x - 1) + 100)</c>, <c>G(x) = P</c>, <c>H(x) = P()</c>, the explicit-call
    /// relay <c>R</c>/<c>L</c>/<c>M</c>/<c>LR</c>, the indirect pair <c>IA</c>/<c>IB</c>/<c>IG</c>/<c>IGB</c>,
    /// the failing <c>PF</c>/<c>GF</c> and <c>PS</c>/<c>GS</c> over <c>Seven = 3 + 4</c>, the sibling shape
    /// <c>PB = if(x &lt;= 0, x + 10, GB(x - 1) + GB(x - 2))</c>, <c>GB(x) = PB</c>, and the CACHE-PUB-1
    /// explicit-call shapes <c>PC</c>/<c>HC</c>/<c>GC</c>, <c>PR</c>/<c>HR</c>/<c>GR</c>, <c>PFC</c>/<c>HFC</c> and
    /// <c>PSC</c>/<c>HSC</c> (each <c>Hn(x) = Pn()</c>).
    /// </summary>
    private static Expr LeanGuardTree(string guard)
    {
        static Expr N(int value) => new Expr.Num(value);
        static Expr X() => new Expr.Param("x");
        static Expr Read(string name) => new Expr.Resolve(name);
        static Expr Add(Expr left, Expr right) => new Expr.Binary(BinaryOp.Add, left, right);
        static Expr CallX(string name, int value) => new Expr.Call(new Expr.Resolve(name), [N(value)]);
        static Expr CallPrevious(string name) => new Expr.Call(new Expr.Resolve(name), [new Expr.Binary(BinaryOp.Sub, X(), N(1))]);
        static Expr Invoke(string name) => new Expr.Call(new Expr.Resolve(name), OutputBundle.Empty);
        static Expr If(Expr whenZero, Expr otherwise) => new Expr.Call(new Expr.Resolve("if"),
            [new Expr.Comparison(X(), [new ComparisonLink(ComparisonOp.Eq, N(0))]), whenZero, otherwise]);
        static Algorithm.User Alg(bool takesX, params Expr[] output)
            => new(Parent: null, ParameterPatterns: takesX ? [new CaptureParameterPattern("x")] : [], Opens: [],
                Properties: [], Output: [.. output]);
        static Property Prop(string name, Algorithm.User value) => new(name, value);

        var oneOverZero = new Expr.Binary(BinaryOp.Div, N(1), N(0));
        IReadOnlyList<Property> properties =
        [
            Prop("P", Alg(false, If(N(1), Add(CallPrevious("G"), N(100))))),
            Prop("G", Alg(true, Read("P"))),
            Prop("H", Alg(true, new Expr.Call(new Expr.Resolve("P"), OutputBundle.Empty))),
            Prop("R", Alg(false, If(N(1), Add(CallPrevious("L"), N(100))))),
            Prop("L", Alg(true, new Expr.Call(new Expr.Resolve("M"), OutputBundle.Empty))),
            Prop("M", Alg(false, Read("R"))),
            Prop("LR", Alg(true, Read("R"))),
            Prop("IA", Alg(false, If(N(1), Add(Read("IB"), N(100))))),
            Prop("IB", Alg(false, CallPrevious("IG"))),
            Prop("IG", Alg(true, Read("IA"))),
            Prop("IGB", Alg(true, Read("IB"))),
            Prop("PF", Alg(false, If(N(1), Add(CallPrevious("GF"), oneOverZero)))),
            Prop("GF", Alg(true, Read("PF"))),
            Prop("Seven", Alg(false, Add(N(3), N(4)))),
            Prop("PS", Alg(false, If(N(1), Add(Add(Read("Seven"), CallPrevious("GS")), oneOverZero)))),
            Prop("GS", Alg(true, Read("PS"))),
            Prop("PB", Alg(false, new Expr.Call(new Expr.Resolve("if"),
                [new Expr.Comparison(X(), [new ComparisonLink(ComparisonOp.Le, N(0))]),
                 Add(X(), N(10)),
                 Add(CallPrevious("GB"), new Expr.Call(new Expr.Resolve("GB"), [new Expr.Binary(BinaryOp.Sub, X(), N(2))]))]))),
            Prop("GB", Alg(true, Read("PB"))),
            Prop("PC", Alg(false, If(N(1), Add(CallPrevious("HC"), N(100))))),
            Prop("HC", Alg(true, Invoke("PC"))),
            Prop("GC", Alg(true, Read("PC"))),
            Prop("PR", Alg(false, If(N(1), Add(CallPrevious("HR"), N(100))))),
            Prop("HR", Alg(true, Invoke("PR"))),
            Prop("GR", Alg(true, Read("PR"))),
            Prop("PFC", Alg(false, If(N(1), Add(CallPrevious("HFC"), oneOverZero)))),
            Prop("HFC", Alg(true, Invoke("PFC"))),
            Prop("PSC", Alg(false, If(N(1), Add(Add(Read("Seven"), CallPrevious("HSC")), oneOverZero)))),
            Prop("HSC", Alg(true, Invoke("PSC"))),
        ];

        Expr[] output = guard switch
        {
            "pubOutermostOwnsTheEntry" => [CallX("G", 1), CallX("G", 5)],
            "pubDeeperRecursion" => [CallX("G", 3), CallX("G", 9), CallX("G", 0)],
            "pubExplicitCallOwnsTheEntry" => [CallX("H", 1), CallX("G", 5)],
            "pubExplicitOwnerInnerExplicitCall" => [CallX("HC", 1), CallX("GC", 5)],
            "pubReadOwnerInnerExplicitCall" => [CallX("GR", 1), CallX("HR", 0), CallX("GR", 5)],
            "pubEstablishedEntryUnchangedByFreshCall" => [CallX("G", 1), CallX("H", 0), CallX("G", 5)],
            "pubFailedExplicitOwnerPublishesNothing" => [CallX("HFC", 1)],
            "pubFailedExplicitOwnerKeepsOtherEntries" => [CallX("HSC", 1)],
            "pubReentranceThroughExplicitCall" => [CallX("LR", 1), CallX("LR", 5)],
            "pubIndirectRecursion" => [CallX("IG", 1), CallX("IG", 5), CallX("IGB", 9)],
            "pubFailedOwnerPublishesNothing" => [CallX("GF", 1)],
            "pubFailedOwnerKeepsOtherEntries" => [CallX("GS", 1)],
            "pubSiblingReentrantReadsEachEvaluate" => [CallX("GB", 2), CallX("GB", 7)],
            _ => throw new ArgumentOutOfRangeException(nameof(guard), guard, null),
        };

        return new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null, ParameterPatterns: [], Opens: [], Properties: properties, Output: output));
    }

    // ── Harness ──────────────────────────────────────────────────────────────────────────────

    private static string[] Ticks(int count)
        => [.. Enumerable.Range(1, count).Select(static i => $"tick#{i}")];

    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    /// <summary>Parses with the host operations the program names (<c>tick</c>) in scope.</summary>
    private static async Task<Expr> ProgramAsync(string source, HostOperations operations)
        => new Expr.AlgorithmExpr((await SourceProvenance.ParseValidAsync(source, new RunOptions { HostOperations = operations })).Root);

    private static ulong NextRawWordAfter(string source)
    {
        var (result, budget) = Evaluator.RunCountedObserved(Program(source), randomSeed: ReproductionSeed);
        Assert.False(result.IsError, result.ToString());
        return budget.RandomSource.NextUInt64();
    }

    private static HostOperations CountingTicks(bool asynchronous)
    {
        var ticks = 0;
        return HostOperations.Create(asynchronous
            ? HostOperation.CreateAsync("tick", async (_, _) =>
            {
                await Task.Yield();
                return new Result.Atom((Decimal128)Interlocked.Increment(ref ticks));
            })
            : HostOperation.Create("tick", (_, _) => new Result.Atom((Decimal128)Interlocked.Increment(ref ticks))));
    }

    private static HostOperations CancellingTicks(CancellationTokenSource cancellation, int cancelAt, bool asynchronous)
    {
        var ticks = 0;
        Result Tick()
        {
            var tick = Interlocked.Increment(ref ticks);
            if (tick == cancelAt)
                cancellation.Cancel();
            return new Result.Atom((Decimal128)tick);
        }

        return HostOperations.Create(asynchronous
            ? HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return Tick(); })
            : HostOperation.Create("tick", (_, _) => Tick()));
    }

    private sealed record PublicationObservation(string Route, bool Failed, IReadOnlyList<string> Published, int ActiveOwners)
    {
        public override string ToString()
            => $"{Route}: failed={Failed} published=[{string.Join(",", Published)}] active={ActiveOwners}";
    }

    /// <summary>
    /// Runs <paramref name="source"/> on the generic, optimized, and forced-async evaluator routes
    /// over a <see cref="PublicationRecordingCache"/>, reporting which bindings were published
    /// (in publication order) and how many keys were still active afterwards.
    /// </summary>
    private static async Task<IReadOnlyList<PublicationObservation>> ObservePublicationsAsync(
        string source, EvaluationLimits? limits = null)
    {
        var observations = new List<PublicationObservation>();
        foreach (var optimized in new[] { false, true })
        {
            var cache = new PublicationRecordingCache();
            var operations = CountingTicks(asynchronous: false);
            var result = Evaluator.RunCountedObserved(await ProgramAsync(source, operations), limits: limits,
                enableOptimizations: optimized, zeroArgPropertyResultCache: cache, hostOperations: operations).Result;
            observations.Add(new(optimized ? "Optimized" : "Generic", result.IsError, [.. cache.Published], cache.ActiveOwners));
        }

        var twinCache = new PublicationRecordingCache();
        var twinOperations = CountingTicks(asynchronous: true);
        var twin = (await Evaluator.RunCountedObservedAsync(await ProgramAsync(source, twinOperations), limits: limits,
            zeroArgPropertyResultCache: twinCache, hostOperations: twinOperations)).Result;
        observations.Add(new("ForcedTwin", twin.IsError, [.. twinCache.Published], twinCache.ActiveOwners));
        return observations;
    }

    /// <summary>
    /// Delegates to the production run-scoped caches (the synchronous member to
    /// <see cref="RunScopedZeroArgPropertyResultCache"/>, the asynchronous member to
    /// <see cref="RunScopedAsyncZeroArgPropertyResultCache"/>) and attributes each publication to the
    /// access that made it: an access published exactly when the store count grew by more than the
    /// publications its nested accesses already recorded.
    /// </summary>
    private sealed class PublicationRecordingCache : IAsyncZeroArgPropertyResultCache
    {
        private readonly RunScopedZeroArgPropertyResultCache _sync = new();
        private readonly RunScopedAsyncZeroArgPropertyResultCache _async = new();

        public List<string> Published { get; } = [];

        public int ActiveOwners => _sync.ActiveOwnerCount + _async.ActiveOwnerCount;

        private int Stores => _sync.GetSnapshot().Stores + _async.PublishedCount;

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            var (stores, recorded) = (Stores, Published.Count);
            try
            {
                return _sync.GetOrEvaluate(execution, evaluate);
            }
            finally
            {
                Attribute(execution, stores, recorded);
            }
        }

        public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
            ZeroArgPropertyExecution execution,
            Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            var (stores, recorded) = (Stores, Published.Count);
            try
            {
                return await _async.GetOrEvaluateAsync(execution, evaluateAsync);
            }
            finally
            {
                Attribute(execution, stores, recorded);
            }
        }

        private void Attribute(ZeroArgPropertyExecution execution, int storesBefore, int recordedBefore)
        {
            var nested = Published.Count - recordedBefore;
            var own = Stores - storesBefore - nested;
            Assert.InRange(own, 0, 1);
            if (own == 1)
                Published.Add(execution.Binding.Name);
        }

        // CACHE-PUB-1: an owning explicit zero-supply invocation publishes under the same law, so it is
        // attributed exactly like a read.
        public EvalResult<ZeroArgPropertyResult> Invoke(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            var (stores, recorded) = (Stores, Published.Count);
            try
            {
                return _sync.Invoke(execution, evaluate);
            }
            finally
            {
                Attribute(execution, stores, recorded);
            }
        }

        public async ValueTask<EvalResult<ZeroArgPropertyResult>> InvokeAsync(
            ZeroArgPropertyExecution execution,
            Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            var (stores, recorded) = (Stores, Published.Count);
            try
            {
                return await _async.InvokeAsync(execution, evaluateAsync);
            }
            finally
            {
                Attribute(execution, stores, recorded);
            }
        }
    }
}
