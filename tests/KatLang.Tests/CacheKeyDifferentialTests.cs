using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// Cache-key completeness differentials for the evaluator's two semantic result caches — the
/// zero-argument property cache and the assignment-deconstruction binding cache. The audited
/// invariant: every semantic determinant of a cached computation is either represented in the
/// cache key or invariant over the cache's lifetime. Each test isolates ONE dimension: populate
/// under context A, reuse under context B differing in that dimension only, and compare against
/// fresh (or generic-path) execution of B; warm hits are proven through cache statistics or the
/// run-scoped <see cref="EvaluationObservations.DeconstructionFullBindCount"/> so no test is
/// vacuous.
///
/// <para>The sharpest dimension is the OPTIMIZED LOOP's mutable value environment:
/// <see cref="LoopValueEnvironment"/> keeps one list object whose state slots mutate in place
/// across iterations, so the owner reference, algorithm environment, counted environment, and
/// run identity are all CONSTANT across iterations — the per-iteration
/// <see cref="LoopValueEnvironment.CacheIdentity"/> token (refreshed by
/// <c>LoopRunFrame.BeginIteration</c> when the plan contains a generic fallback) is the ONLY key
/// component separating iteration N from iteration N+1 for both caches. The loop tests fail
/// against a stale token with observably wrong values, not just different counters.</para>
/// </summary>
public class CacheKeyDifferentialTests
{
    // ── shared helpers ──────────────────────────────────────────────────────

    private static Expr ParseValidProgram(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private sealed class RecordingZeroArgPropertyResultCache : IZeroArgPropertyResultCache
    {
        private readonly IZeroArgPropertyResultCache _inner;
        private readonly List<ZeroArgPropertyExecution> _requests = [];

        public RecordingZeroArgPropertyResultCache(IZeroArgPropertyResultCache inner)
        {
            _inner = inner;
        }

        public IReadOnlyList<ZeroArgPropertyExecution> Requests => _requests;

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            _requests.Add(execution);
            return _inner.GetOrEvaluate(execution, evaluate);
        }
    }

    private static Algorithm.User NewAlgorithm()
        => new(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.Num(0)]);

    private static Property NewProperty(string name)
        => new(name, NewAlgorithm(), IsPublic: true);

    /// <summary>Sums the plain and counted variants of one access-shape family.</summary>
    private static (int Requests, int Hits, int Misses, int Stores) AccessShapeCounts(
        RunScopedZeroArgPropertyResultCache cache,
        params ZeroArgPropertyAccessKind[] kinds)
    {
        var snapshot = cache.GetSnapshot();
        int requests = 0, hits = 0, misses = 0, stores = 0;
        foreach (var kind in kinds)
        {
            var access = snapshot.GetAccessKind(kind);
            requests += access.Requests;
            hits += access.Hits;
            misses += access.Misses;
            stores += access.Stores;
        }

        return (requests, hits, misses, stores);
    }

    private static (int Requests, int Hits, int Misses, int Stores) StructuralCounts(
        RunScopedZeroArgPropertyResultCache cache)
        => AccessShapeCounts(
            cache,
            ZeroArgPropertyAccessKind.Structural,
            ZeroArgPropertyAccessKind.CountedStructural);

    private static (int Requests, int Hits, int Misses, int Stores) LexicalCounts(
        RunScopedZeroArgPropertyResultCache cache)
        => AccessShapeCounts(
            cache,
            ZeroArgPropertyAccessKind.Lexical,
            ZeroArgPropertyAccessKind.CountedLexical);

    // ── key comparer one-dimension matrices ─────────────────────────────────

    /// <summary>
    /// The direct §one-dimension-at-a-time matrix at the key-comparer level: starting from one
    /// execution, changing exactly one semantic key dimension must MISS (keys unequal), changing
    /// none must HIT (keys equal, hashes equal). This is the regression that catches a field
    /// dropped from <see cref="ZeroArgPropertyCacheKeyComparer"/>'s Equals — including the
    /// dimensions (algorithm environment, counted environment) that today are additionally
    /// shadowed by per-call owner/value-environment freshness on every source-reachable path and
    /// therefore cannot be pinned behaviorally.
    /// </summary>
    [Fact]
    public void ZeroArgPropertyKey_ChangingExactlyOneDimension_MissesForEveryKeyDimension()
    {
        var comparer = ZeroArgPropertyCacheKeyComparer.Instance;
        var baseline = new ZeroArgPropertyExecution(
            NewAlgorithm(),
            NewProperty("Value"),
            ZeroArgPropertyAccessKind.Lexical,
            new object(),
            new object(),
            new object(),
            new object());
        var baselineKey = ZeroArgPropertyCacheKey.FromExecution(baseline);

        // Unchanged context: HIT (equal keys, equal hashes).
        var sameKey = ZeroArgPropertyCacheKey.FromExecution(baseline);
        Assert.True(comparer.Equals(baselineKey, sameKey));
        Assert.Equal(comparer.GetHashCode(baselineKey), comparer.GetHashCode(sameKey));

        // The plain/counted split of ONE access shape shares entries by design: the stored
        // (value, emitted count) pair serves both channels.
        var countedKey = ZeroArgPropertyCacheKey.FromExecution(
            baseline with { AccessKind = ZeroArgPropertyAccessKind.CountedLexical });
        Assert.True(comparer.Equals(baselineKey, countedKey));
        Assert.Equal(comparer.GetHashCode(baselineKey), comparer.GetHashCode(countedKey));

        // Each single changed semantic dimension: MISS.
        var changed = new[]
        {
            ("access shape", ZeroArgPropertyCacheKey.FromExecution(
                baseline with { AccessKind = ZeroArgPropertyAccessKind.Structural })),
            ("owner", ZeroArgPropertyCacheKey.FromExecution(
                baseline with { Owner = NewAlgorithm() })),
            ("binding", ZeroArgPropertyCacheKey.FromExecution(
                baseline with { Binding = NewProperty("Value") })),
            ("value environment", ZeroArgPropertyCacheKey.FromExecution(
                baseline with { ValueEnvironmentIdentity = new object() })),
            ("algorithm environment", ZeroArgPropertyCacheKey.FromExecution(
                baseline with { AlgorithmEnvironmentIdentity = new object() })),
            ("counted environment", ZeroArgPropertyCacheKey.FromExecution(
                baseline with { CountedParamEnvironmentIdentity = new object() })),
            ("run identity", ZeroArgPropertyCacheKey.FromExecution(
                baseline with { RunIdentity = new object() })),
        };

        foreach (var (dimension, key) in changed)
            Assert.False(comparer.Equals(baselineKey, key), $"changed {dimension} must miss");
    }

    /// <summary>Deconstruction-cache twin of the one-dimension key matrix.</summary>
    [Fact]
    public void DeconstructionKey_ChangingExactlyOneDimension_MissesForEveryKeyDimension()
    {
        var comparer = DeconstructionBindingCacheKeyComparer.Instance;
        var baseline = new DeconstructionBindingCacheKey(
            new object(),
            new object(),
            new object(),
            new object(),
            new object());

        var same = baseline with { };
        Assert.True(comparer.Equals(baseline, same));
        Assert.Equal(comparer.GetHashCode(baseline), comparer.GetHashCode(same));

        var changed = new[]
        {
            ("group", baseline with { GroupIdentity = new object() }),
            ("owner", baseline with { OwnerIdentity = new object() }),
            ("value environment", baseline with { ValueEnvironmentIdentity = new object() }),
            ("algorithm environment", baseline with { AlgorithmEnvironmentIdentity = new object() }),
            ("counted environment", baseline with { CountedParamEnvironmentIdentity = new object() }),
        };

        foreach (var (dimension, key) in changed)
            Assert.False(comparer.Equals(baseline, key), $"changed {dimension} must miss");

        // A rebuilt-but-resolution-equivalent structural owner still HITS: the deconstruction
        // owner rule is shared with the zero-arg property cache's structural owner identity.
        var opens = new List<Expr> { new Expr.Num(1m) };
        var properties = new List<Property> { NewProperty("P") };
        Algorithm.User RebuildOwner() => NewAlgorithm() with { Opens = opens, Properties = properties };
        var structural = baseline with { OwnerIdentity = StructuralOwnerIdentity.FromOwner(RebuildOwner()) };
        var rebuiltStructural = baseline with { OwnerIdentity = StructuralOwnerIdentity.FromOwner(RebuildOwner()) };
        Assert.True(comparer.Equals(structural, rebuiltStructural));
        Assert.Equal(comparer.GetHashCode(structural), comparer.GetHashCode(rebuiltStructural));
    }

    /// <summary>
    /// Scope-chain adversaries for <see cref="StructuralOwnerIdentity"/>: rebuilt owners over the
    /// same resolving scope are equivalent (including separately allocated EMPTY components); a
    /// changed chain length, or a reference-distinct non-empty component at any level, is a
    /// different owner even when its contents look alike (the live declaration lists ARE the
    /// scope).
    /// </summary>
    [Fact]
    public void StructuralOwnerIdentity_DistinguishesResolutionRelevantChains()
    {
        var parentOpens = new List<Expr> { new Expr.Num(1m) };
        var parentProperties = new List<Property> { NewProperty("Parent") };
        var ownerOpens = new List<Expr> { new Expr.Num(2m) };
        var ownerProperties = new List<Property> { NewProperty("Value") };

        Algorithm.User BuildOwner(
            IReadOnlyList<Expr> opens,
            IReadOnlyList<Property> properties,
            ScopeCtx? parent)
            => NewAlgorithm() with { Opens = opens, Properties = properties, Parent = parent };

        ScopeCtx ParentScope() => new(null, parentOpens, parentProperties);

        var baseline = StructuralOwnerIdentity.FromOwner(BuildOwner(ownerOpens, ownerProperties, ParentScope()));

        // Rebuilt owner and rebuilt intermediate scope records over the SAME lists: equivalent.
        var rebuilt = StructuralOwnerIdentity.FromOwner(BuildOwner(ownerOpens, ownerProperties, ParentScope()));
        Assert.True(baseline.Equals(rebuilt));
        Assert.Equal(baseline.GetHashCode(), rebuilt.GetHashCode());

        // Separately allocated EMPTY components resolve identically: equivalent.
        var emptyA = StructuralOwnerIdentity.FromOwner(BuildOwner(new List<Expr>(), new List<Property>(), null));
        var emptyB = StructuralOwnerIdentity.FromOwner(BuildOwner(new List<Expr>(), new List<Property>(), null));
        Assert.True(emptyA.Equals(emptyB));
        Assert.Equal(emptyA.GetHashCode(), emptyB.GetHashCode());

        // Chain length changed (parent level dropped): different owner.
        var chainless = StructuralOwnerIdentity.FromOwner(BuildOwner(ownerOpens, ownerProperties, null));
        Assert.False(baseline.Equals(chainless));

        // Reference-distinct non-empty property list with lookalike contents: different owner.
        var lookalikeProperties = new List<Property> { NewProperty("Value") };
        var lookalike = StructuralOwnerIdentity.FromOwner(BuildOwner(ownerOpens, lookalikeProperties, ParentScope()));
        Assert.False(baseline.Equals(lookalike));

        // Reference-distinct non-empty component at the PARENT level only: different owner.
        var otherParentProperties = new List<Property> { NewProperty("Parent") };
        var otherParent = StructuralOwnerIdentity.FromOwner(
            BuildOwner(ownerOpens, ownerProperties, new ScopeCtx(null, parentOpens, otherParentProperties)));
        Assert.False(baseline.Equals(otherParent));
    }

    // ── optimized-loop mutable environment differentials ────────────────────

    /// <summary>
    /// A state-dependent local-only zero-arg property (<c>Val = x * 2</c> captures the ancestor
    /// step parameter) demanded from an unplannable step expression: the fallback evaluates
    /// generically against the loop's MUTABLE value environment, so the per-iteration cache
    /// identity token is the only key dimension separating iterations. Wrong reuse produces 13
    /// instead of 125.
    /// </summary>
    [Fact]
    public void OptimizedRepeat_StateDependentPropertyInFallback_RebindsPerIterationAndReusesWithinIteration()
    {
        const string source = """
            Step(x) = {
                Val = x * 2
                x + Val + Val + [0]:0
            }
            repeat(Step, 3, 1)
            """;
        var expr = ParseValidProgram(source);

        var generic = Evaluator.Run(expr, new RunScopedZeroArgPropertyResultCache(), enableLoopOptimization: false);
        Assert.False(generic.IsError);
        Assert.Equal([125m], generic.Value.ToAtoms());

        var runScoped = new RunScopedZeroArgPropertyResultCache();
        var recording = new RecordingZeroArgPropertyResultCache(runScoped);
        var diagnostics = new LoopOptimizationDiagnostics();
        var optimized = Evaluator.Run(expr, recording, enableLoopOptimization: true, diagnostics);

        Assert.False(optimized.IsError);
        Assert.Equal([125m], optimized.Value.ToAtoms());
        // Non-vacuity: the optimized loop path actually ran (with a planned template whose
        // output expression fell back to generic evaluation).
        Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);

        // Two demands per iteration across three iterations: each iteration misses once and
        // reuses once, under three DISTINCT per-iteration value-environment identities.
        var valRequests = recording.Requests.Where(static r => r.Binding.Name == "Val").ToList();
        Assert.Equal(6, valRequests.Count);
        Assert.Equal(3, valRequests.Select(static r => r.ValueEnvironmentIdentity).Distinct().Count());
        var lexical = LexicalCounts(runScoped);
        Assert.Equal(3, lexical.Hits);
        Assert.Equal(3, lexical.Misses);
        Assert.Equal(3, lexical.Stores);
    }

    /// <summary>While twin of the repeat differential (planned continuation, fallback state row).</summary>
    [Fact]
    public void OptimizedWhile_StateDependentPropertyInFallback_RebindsPerIteration()
    {
        const string source = """
            Step(x) = {
                Val = x * 2
                x + Val + Val + [0]:0,
                x < 20
            }
            while(Step, 1)
            """;
        var expr = ParseValidProgram(source);

        var generic = Evaluator.Run(expr, new RunScopedZeroArgPropertyResultCache(), enableLoopOptimization: false);
        Assert.False(generic.IsError);
        Assert.Equal([25m], generic.Value.ToAtoms());

        var runScoped = new RunScopedZeroArgPropertyResultCache();
        var recording = new RecordingZeroArgPropertyResultCache(runScoped);
        var diagnostics = new LoopOptimizationDiagnostics();
        var optimized = Evaluator.Run(expr, recording, enableLoopOptimization: true, diagnostics);

        Assert.False(optimized.IsError);
        Assert.Equal([25m], optimized.Value.ToAtoms());
        Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);

        var valRequests = recording.Requests.Where(static r => r.Binding.Name == "Val").ToList();
        Assert.Equal(6, valRequests.Count);
        Assert.Equal(3, valRequests.Select(static r => r.ValueEnvironmentIdentity).Distinct().Count());
    }

    /// <summary>
    /// The deconstruction-cache twin of the loop differential: a state-dependent deconstruction
    /// inside the step must rebind once per iteration (stale reuse would freeze the state at 4),
    /// while the two targets of one iteration share a single bind. The optimized loop and the
    /// generic loop must agree on both the value and the bind count.
    /// </summary>
    [Fact]
    public void OptimizedRepeat_StateDependentDeconstruction_RebindsPerIterationSharedWithinIteration()
    {
        const string source = """
            StepD(x) = {
                a, b = (x + 1, x * 2)
                a + b
            }
            repeat(StepD, 3, 1)
            """;
        var expr = ParseValidProgram(source);

        var genericObservations = new EvaluationObservations();
        var (generic, _) = Evaluator.RunCountedObserved(
            expr,
            enableOptimizations: false,
            observations: genericObservations);
        Assert.False(generic.IsError);
        Assert.Equal([40m], generic.Value.Value.ToAtoms());
        Assert.Equal(3, genericObservations.DeconstructionFullBindCount);

        var optimizedObservations = new EvaluationObservations();
        var diagnostics = new LoopOptimizationDiagnostics();
        var (optimized, _) = Evaluator.RunCountedObserved(
            expr,
            loopDiagnostics: diagnostics,
            observations: optimizedObservations);
        Assert.False(optimized.IsError);
        Assert.Equal([40m], optimized.Value.Value.ToAtoms());
        Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);
        Assert.Equal(3, optimizedObservations.DeconstructionFullBindCount);
    }

    /// <summary>While twin of the deconstruction loop differential.</summary>
    [Fact]
    public void OptimizedWhile_StateDependentDeconstruction_RebindsPerIteration()
    {
        const string source = """
            StepD(x) = {
                a, b = (x + 1, x * 2)
                a * b + x,
                x < 20
            }
            while(StepD, 1)
            """;
        var expr = ParseValidProgram(source);

        var genericObservations = new EvaluationObservations();
        var (generic, _) = Evaluator.RunCountedObserved(
            expr,
            enableOptimizations: false,
            observations: genericObservations);
        Assert.False(generic.IsError);
        Assert.Equal([65m], generic.Value.Value.ToAtoms());
        Assert.Equal(3, genericObservations.DeconstructionFullBindCount);

        var optimizedObservations = new EvaluationObservations();
        var diagnostics = new LoopOptimizationDiagnostics();
        var (optimized, _) = Evaluator.RunCountedObserved(
            expr,
            loopDiagnostics: diagnostics,
            observations: optimizedObservations);
        Assert.False(optimized.IsError);
        Assert.Equal([65m], optimized.Value.Value.ToAtoms());
        Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);
        Assert.Equal(3, optimizedObservations.DeconstructionFullBindCount);
    }

    // ── binding identity within one owner ───────────────────────────────────

    /// <summary>
    /// Sibling properties of ONE owner share every key dimension except the property binding —
    /// same structural owner identity, same root value environment, same run — so the binding
    /// reference is the component that keeps <c>X.B</c> from serving <c>X.A</c>'s value, while
    /// the repeated <c>X.A</c> access still reuses its entry.
    /// </summary>
    [Fact]
    public void StructuralAccess_SiblingPropertiesOfOneOwner_DoNotAliasAndStillReuse()
    {
        const string source = """
            X = {
                A = 1
                B = 2
            }
            X.A, X.B, X.A
            """;
        var expr = ParseValidProgram(source);

        var cache = new RunScopedZeroArgPropertyResultCache();
        var result = Evaluator.Run(expr, cache);

        Assert.False(result.IsError);
        Assert.Equal([1m, 2m, 1m], result.Value.ToAtoms());
        var structural = StructuralCounts(cache);
        Assert.Equal(3, structural.Requests);
        Assert.Equal(1, structural.Hits);
        Assert.Equal(2, structural.Misses);
        Assert.Equal(2, structural.Stores);
    }

    // ── cross-run lifetime differentials on one shared cache instance ───────

    /// <summary>
    /// Reverse direction of the warm-generous/strict-rerun regression: a strict-limit run FAILS
    /// (structural resource failure), and because errors are never stored, a later generous run
    /// sharing the same cache instance re-evaluates and succeeds exactly like a fresh run.
    /// </summary>
    [Fact]
    public void SharedCacheAcrossRuns_StrictLimitFailureIsNotCached_GenerousRerunSucceeds()
    {
        const string source = """
            X = {
                P = range(1, 200)
            }
            X.P.count
            """;
        var expr = ParseValidProgram(source);
        var sharedCache = new RunScopedZeroArgPropertyResultCache();

        var strict = Evaluator.Run(
            expr,
            sharedCache,
            enableLoopOptimization: true,
            new EvaluationLimits { MaxCollectionItems = 10 });
        Assert.True(strict.IsError);

        var generous = Evaluator.Run(expr, sharedCache);
        Assert.False(generous.IsError);
        Assert.Equal([200m], generous.Value.ToAtoms());

        var fresh = Evaluator.Run(expr, new RunScopedZeroArgPropertyResultCache());
        Assert.False(fresh.IsError);
        Assert.Equal(fresh.Value.ToAtoms(), generous.Value.ToAtoms());
    }

    /// <summary>
    /// Structural entries share every key dimension across runs of the SAME program tree (same
    /// scope-chain lists, the same process-wide empty environment singletons) EXCEPT run
    /// identity, so this pins that a plain run and a counted run on one shared cache instance
    /// stay isolated per run: each run misses then reuses within itself, and neither serves the
    /// other's entry.
    /// </summary>
    [Fact]
    public void SharedCacheAcrossRuns_PlainThenCountedRun_EachRunMissesOnceAndReusesWithinItself()
    {
        const string source = """
            X = {
                A = 1 + 1
            }
            X.A + X.A
            """;
        var expr = ParseValidProgram(source);
        var sharedCache = new RunScopedZeroArgPropertyResultCache();

        var plain = Evaluator.Run(expr, sharedCache);
        Assert.False(plain.IsError);
        Assert.Equal([4m], plain.Value.ToAtoms());

        var counted = Evaluator.RunCounted(expr, sharedCache);
        Assert.False(counted.IsError);
        Assert.Equal([4m], counted.Value.Value.ToAtoms());
        Assert.Equal(1, counted.Value.EmittedCount);

        var freshCounted = Evaluator.RunCounted(expr, new RunScopedZeroArgPropertyResultCache());
        Assert.False(freshCounted.IsError);
        Assert.Equal(freshCounted.Value.Value.ToAtoms(), counted.Value.Value.ToAtoms());
        Assert.Equal(freshCounted.Value.EmittedCount, counted.Value.EmittedCount);

        // Two accesses per run: one miss + one within-run reuse each. A run-identity failure
        // would let the second run hit the first run's entry (3 hits / 1 miss).
        var structural = StructuralCounts(sharedCache);
        Assert.Equal(4, structural.Requests);
        Assert.Equal(2, structural.Hits);
        Assert.Equal(2, structural.Misses);
        Assert.Equal(2, structural.Stores);
    }

    /// <summary>
    /// Configuring an (otherwise non-binding) cumulative materialization budget switches the
    /// sequence execution strategy for the whole run. One shared cache instance across the
    /// strategy change must serve nothing across runs: the configured-strategy run matches its
    /// fresh oracle, and per-run hit/miss accounting stays symmetric.
    /// </summary>
    [Fact]
    public void SharedCacheAcrossRuns_ConfiguredMaterializationStrategyRun_IsIsolatedFromWarmDefaultRun()
    {
        const string source = """
            X = {
                Data = range(1, 20)
            }
            X.Data.filter({v > 5}).count + X.Data.count
            """;
        var expr = ParseValidProgram(source);
        var sharedCache = new RunScopedZeroArgPropertyResultCache();

        var defaultStrategy = Evaluator.Run(expr, sharedCache);
        Assert.False(defaultStrategy.IsError);
        Assert.Equal([35m], defaultStrategy.Value.ToAtoms());

        var configuredLimits = new EvaluationLimits { MaxMaterializedItems = 10_000 };
        var configuredStrategy = Evaluator.Run(
            expr,
            sharedCache,
            enableLoopOptimization: true,
            configuredLimits);
        Assert.False(configuredStrategy.IsError);
        Assert.Equal([35m], configuredStrategy.Value.ToAtoms());

        var freshConfigured = Evaluator.Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            configuredLimits);
        Assert.False(freshConfigured.IsError);
        Assert.Equal(freshConfigured.Value.ToAtoms(), configuredStrategy.Value.ToAtoms());

        var structural = StructuralCounts(sharedCache);
        Assert.Equal(4, structural.Requests);
        Assert.Equal(2, structural.Hits);
        Assert.Equal(2, structural.Misses);
        Assert.Equal(2, structural.Stores);
    }

    // ── deconstruction environment differentials ────────────────────────────

    /// <summary>
    /// Algorithm-environment differential: the same deconstruction group bound under two
    /// different higher-order bindings of <c>f</c> must produce per-call values (two full binds,
    /// no reuse of the first call's bound slots).
    /// </summary>
    [Fact]
    public void Deconstruction_SameGroupUnderDifferentAlgorithmBindings_BindsPerContext()
    {
        const string source = """
            Inc(v) = v + 1
            Dec(v) = v - 1
            Apply(f) = {
                p, q = (f(1), f(10))
                p + q
            }
            Apply(Inc), Apply(Dec)
            """;

        var observations = new EvaluationObservations();
        var (result, _) = Evaluator.RunCountedObserved(ParseValidProgram(source), observations: observations);

        Assert.False(result.IsError);
        Assert.Equal([13m, 9m], result.Value.Value.ToAtoms());
        Assert.Equal(2, observations.DeconstructionFullBindCount);
    }

    /// <summary>
    /// The deconstruction cache carries NO run identity: its correctness against cross-run reuse
    /// is pure lifetime scoping (one <c>RunScopedDeconstructionBindingCache</c> is constructed
    /// per root context and is never host-suppliable). Two runs of the SAME parsed tree share
    /// every key dimension — group token, scope-chain owner identity, and the process-wide empty
    /// root environment singletons — so a lifetime broadening (e.g. a shared cache instance)
    /// would serve run 1's bind to run 2. Each run must perform its own full bind.
    /// </summary>
    [Fact]
    public void Deconstruction_SameTreeAcrossTwoRuns_EachRunBindsFreshly()
    {
        const string source = """
            a, b = (1, 2)
            a + b
            """;
        var expr = ParseValidProgram(source);

        var firstObservations = new EvaluationObservations();
        var (first, _) = Evaluator.RunCountedObserved(expr, observations: firstObservations);
        Assert.False(first.IsError);
        Assert.Equal([3m], first.Value.Value.ToAtoms());
        Assert.Equal(1, firstObservations.DeconstructionFullBindCount);

        var secondObservations = new EvaluationObservations();
        var (second, _) = Evaluator.RunCountedObserved(expr, observations: secondObservations);
        Assert.False(second.IsError);
        Assert.Equal([3m], second.Value.Value.ToAtoms());
        Assert.Equal(1, secondObservations.DeconstructionFullBindCount);
    }

    /// <summary>
    /// Counted-callback differential: one deconstruction group demanded per mapped element must
    /// bind per element (per counted/value callback binding context), never reuse the first
    /// element's slots.
    /// </summary>
    [Fact]
    public void Deconstruction_SameGroupPerMappedElement_BindsPerElement()
    {
        const string source = """
            F(e) = {
                p, q = (e, e * 10)
                p + q
            }
            sum([1, 2].map(F))
            """;

        var observations = new EvaluationObservations();
        var (result, _) = Evaluator.RunCountedObserved(ParseValidProgram(source), observations: observations);

        Assert.False(result.IsError);
        Assert.Equal([33m], result.Value.Value.ToAtoms());
        Assert.Equal(2, observations.DeconstructionFullBindCount);
    }
}
