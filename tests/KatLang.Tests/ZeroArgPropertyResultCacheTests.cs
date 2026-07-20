using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

public class ZeroArgPropertyResultCacheTests
{
    private readonly record struct CacheKeyComponentComparison(
        bool OwnerIdentityMatches,
        bool BindingIdentityMatches,
        bool ValueEnvironmentIdentityMatches,
        bool AlgorithmEnvironmentIdentityMatches,
        bool CountedParamEnvironmentIdentityMatches)
    {
        public bool AllComponentsMatch
            => OwnerIdentityMatches
                && BindingIdentityMatches
                && ValueEnvironmentIdentityMatches
                && AlgorithmEnvironmentIdentityMatches
                && CountedParamEnvironmentIdentityMatches;
    }

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

    [Fact]
    public void RunScopedZeroArgPropertyResultCache_TracksHitMissAndStoreCounters_ForIdenticalExecution()
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        var owner = NewAlgorithm();
        var binding = NewProperty("Value");
        var execution = new ZeroArgPropertyExecution(
            owner,
            binding,
            ZeroArgPropertyAccessKind.Lexical,
            new object(),
            new object(),
            new object());

        var first = cache.GetOrEvaluate(
            execution,
            () => EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(new Result.Atom(1m), 1)));

        var second = cache.GetOrEvaluate(
            execution,
            () => EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(new Result.Atom(2m), 1)));

        var snapshot = cache.GetSnapshot();
        var lexical = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Lexical);

        Assert.Equal(1m, Assert.IsType<Result.Atom>(first.Value.Value).Value);
        Assert.Equal(1m, Assert.IsType<Result.Atom>(second.Value.Value).Value);
        Assert.Equal(2, snapshot.TotalRequests);
        Assert.Equal(1, snapshot.Hits);
        Assert.Equal(1, snapshot.Misses);
        Assert.Equal(1, snapshot.Stores);
        Assert.Equal(1, snapshot.DistinctKeysCreated);
        Assert.Equal(0, snapshot.RepeatedMissRequests);
        Assert.Equal(1, snapshot.MaxCacheSize);
        Assert.Equal(2, lexical.Requests);
        Assert.Equal(1, lexical.Hits);
        Assert.Equal(1, lexical.Misses);
        Assert.Equal(1, lexical.Stores);
    }

    [Fact]
    public void RunScopedZeroArgPropertyResultCache_TracksMissOnlyCounters_ForDistinctExecutions()
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        var binding = NewProperty("Value");
        var first = new ZeroArgPropertyExecution(
            NewAlgorithm(),
            binding,
            ZeroArgPropertyAccessKind.Structural,
            new object(),
            new object(),
            new object());
        var second = new ZeroArgPropertyExecution(
            NewAlgorithm(),
            binding,
            ZeroArgPropertyAccessKind.Structural,
            new object(),
            new object(),
            new object());

        Assert.False(cache.GetOrEvaluate(first, () => EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(new Result.Atom(1m), 1))).IsError);
        Assert.False(cache.GetOrEvaluate(second, () => EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(new Result.Atom(2m), 1))).IsError);

        var snapshot = cache.GetSnapshot();
        var structural = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Structural);

        Assert.Equal(2, snapshot.TotalRequests);
        Assert.Equal(0, snapshot.Hits);
        Assert.Equal(2, snapshot.Misses);
        Assert.Equal(2, snapshot.Stores);
        Assert.Equal(2, snapshot.DistinctKeysCreated);
        Assert.Equal(0, snapshot.RepeatedMissRequests);
        Assert.Equal(2, snapshot.MaxCacheSize);
        Assert.Equal(2, structural.Requests);
        Assert.Equal(0, structural.Hits);
        Assert.Equal(2, structural.Misses);
        Assert.Equal(2, structural.Stores);
    }

    [Fact]
    public void RunScopedZeroArgPropertyResultCache_ReusesStructuralExecutions_AcrossRebuiltOwnerIdentity()
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        var binding = NewProperty("Value");
        var valueEnv = new object();
        var algorithmEnv = new object();
        var countedParamEnv = new object();
        var first = new ZeroArgPropertyExecution(
            NewAlgorithm(),
            binding,
            ZeroArgPropertyAccessKind.Structural,
            valueEnv,
            algorithmEnv,
            countedParamEnv);
        var second = new ZeroArgPropertyExecution(
            NewAlgorithm(),
            binding,
            ZeroArgPropertyAccessKind.Structural,
            valueEnv,
            algorithmEnv,
            countedParamEnv);

        var firstResult = cache.GetOrEvaluate(
            first,
            () => EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(new Result.Atom(1m), 1)));
        var secondResult = cache.GetOrEvaluate(
            second,
            () => EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(new Result.Atom(2m), 1)));

        var snapshot = cache.GetSnapshot();
        var structural = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Structural);
        var comparison = CompareKeyComponents(first, second);

        Assert.Equal(1m, Assert.IsType<Result.Atom>(firstResult.Value.Value).Value);
        Assert.Equal(1m, Assert.IsType<Result.Atom>(secondResult.Value.Value).Value);
        Assert.False(ReferenceEquals(first.Owner, second.Owner));
        Assert.True(comparison.AllComponentsMatch);
        Assert.True(comparison.OwnerIdentityMatches);
        Assert.True(comparison.BindingIdentityMatches);
        Assert.True(comparison.ValueEnvironmentIdentityMatches);
        Assert.True(comparison.AlgorithmEnvironmentIdentityMatches);
        Assert.True(comparison.CountedParamEnvironmentIdentityMatches);
        Assert.Equal(2, snapshot.TotalRequests);
        Assert.Equal(1, snapshot.Hits);
        Assert.Equal(1, snapshot.Misses);
        Assert.Equal(1, snapshot.Stores);
        Assert.Equal(1, snapshot.DistinctKeysCreated);
        Assert.Equal(0, snapshot.RepeatedMissRequests);
        Assert.Equal(1, snapshot.MaxCacheSize);
        Assert.Equal(2, structural.Requests);
        Assert.Equal(1, structural.Hits);
        Assert.Equal(1, structural.Misses);
        Assert.Equal(1, structural.Stores);
    }

    [Fact]
    public void RunScopedZeroArgPropertyResultCache_TracksRepeatedMissRequests_WhenEvaluationNeverStores()
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        var execution = new ZeroArgPropertyExecution(
            NewAlgorithm(),
            NewProperty("Value"),
            ZeroArgPropertyAccessKind.CountedStructural,
            new object(),
            new object(),
            new object());

        Assert.True(cache.GetOrEvaluate(execution, static () => new EvalError.UnknownName("missing")).IsError);
        Assert.True(cache.GetOrEvaluate(execution, static () => new EvalError.UnknownName("missing")).IsError);

        var snapshot = cache.GetSnapshot();
        var countedStructural = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.CountedStructural);

        Assert.Equal(2, snapshot.TotalRequests);
        Assert.Equal(0, snapshot.Hits);
        Assert.Equal(2, snapshot.Misses);
        Assert.Equal(0, snapshot.Stores);
        Assert.Equal(1, snapshot.DistinctKeysCreated);
        Assert.Equal(1, snapshot.RepeatedMissRequests);
        Assert.Equal(0, snapshot.MaxCacheSize);
        Assert.Equal(2, countedStructural.Requests);
        Assert.Equal(0, countedStructural.Hits);
        Assert.Equal(2, countedStructural.Misses);
        Assert.Equal(0, countedStructural.Stores);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_MatchesUncachedBehavior()
    {
        var source = """
            Values = range(1, 5)
            Values.count + Values.count
            """;
        var expr = new Expr.Block(Parser.Parse(source).Root);

        var uncached = Evaluator.Run(expr, UncachedZeroArgPropertyResultCache.Instance);
        var cached = Evaluator.Run(expr, new RunScopedZeroArgPropertyResultCache());

        Assert.False(uncached.IsError);
        Assert.False(cached.IsError);
        Assert.Equal(uncached.Value.ToAtoms(), cached.Value.ToAtoms());
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_PropertyStyleAccessReusesRandomPropertyResult()
    {
        var source = """
            Fun = Math.Random(0, 1)
            Fun + Fun
            """;
        var cache = new RunScopedZeroArgPropertyResultCache();

        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root), cache);
        var snapshot = cache.GetSnapshot();
        var lexical = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Lexical);

        Assert.False(result.IsError);
        var atoms = result.Value.ToAtoms();
        Assert.Single(atoms);
        Assert.True(atoms[0] >= 0m && atoms[0] < 2m);
        Assert.Equal(2, lexical.Requests);
        Assert.Equal(1, lexical.Hits);
        Assert.Equal(1, lexical.Misses);
        Assert.Equal(1, lexical.Stores);
    }

    [Fact]
    public void Evaluator_RunCountedWithTopLevelProperty_ReusesOutputCacheEntryForTopLevelProperty()
    {
        var source = """
            Source = Math.RandomInt(0, 10)
            DisplayDecimals = Source

            DisplayDecimals
            """;
        var innerCache = new RunScopedZeroArgPropertyResultCache();
        var cache = new RecordingZeroArgPropertyResultCache(innerCache);

        var result = Evaluator.RunCountedWithTopLevelProperty(
            new Expr.Block(Parser.Parse(source).Root),
            "DisplayDecimals",
            cache);
        var snapshot = innerCache.GetSnapshot();
        var countedLexical = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.CountedLexical);

        Assert.False(result.IsError);
        Assert.NotNull(result.Value.TopLevelProperty);
        Assert.Equal(result.Value.Output.Value, result.Value.TopLevelProperty.Value.Value);
        Assert.Equal(["DisplayDecimals", "Source", "DisplayDecimals"], cache.Requests.Select(request => request.Binding.Name));
        Assert.All(cache.Requests, request =>
            Assert.Equal(ZeroArgPropertyAccessKind.CountedLexical, request.AccessKind));
        Assert.Equal(3, snapshot.TotalRequests);
        Assert.Equal(1, snapshot.Hits);
        Assert.Equal(2, snapshot.Misses);
        Assert.Equal(2, snapshot.Stores);
        Assert.Equal(3, countedLexical.Requests);
        Assert.Equal(1, countedLexical.Hits);
        Assert.Equal(2, countedLexical.Misses);
        Assert.Equal(2, countedLexical.Stores);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_PurePropertyStyleAccessStillUsesCache()
    {
        var source = """
            Heavy = 1 + 2
            Heavy + Heavy
            """;
        var cache = new RunScopedZeroArgPropertyResultCache();

        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root), cache);
        var snapshot = cache.GetSnapshot();
        var lexical = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Lexical);

        Assert.False(result.IsError);
        Assert.Equal([6m], result.Value.ToAtoms());
        Assert.Equal(2, lexical.Requests);
        Assert.Equal(1, lexical.Hits);
        Assert.Equal(1, lexical.Misses);
        Assert.Equal(1, lexical.Stores);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_ConstantLikeMathMembersStillUseCache()
    {
        var source = "Math.Pi + Math.Pi";
        var cache = new RunScopedZeroArgPropertyResultCache();

        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root), cache);
        var snapshot = cache.GetSnapshot();
        var structural = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Structural);

        Assert.False(result.IsError);
        Assert.Single(result.Value.ToAtoms());
        Assert.Equal(2, structural.Requests);
        Assert.Equal(1, structural.Hits);
        Assert.Equal(1, structural.Misses);
        Assert.Equal(1, structural.Stores);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_ExplicitZeroArgCallBypassesCache()
    {
        var source = """
            Heavy = 1 + 2
            Heavy(), Heavy()
            """;
        var innerCache = new RunScopedZeroArgPropertyResultCache();
        var cache = new RecordingZeroArgPropertyResultCache(innerCache);

        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root), cache);
        var snapshot = innerCache.GetSnapshot();

        Assert.False(result.IsError);
        Assert.Equal([3m, 3m], result.Value.ToAtoms());
        Assert.Empty(cache.Requests);
        Assert.Equal(0, snapshot.TotalRequests);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_ExplicitZeroArgCallKeepsNestedPropertyStyleAccessCached()
    {
        var source = """
            A = Math.RandomInt(0, 10)
            B = A, A
            B()
            """;
        var innerCache = new RunScopedZeroArgPropertyResultCache();
        var cache = new RecordingZeroArgPropertyResultCache(innerCache);

        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root), cache);
        var snapshot = innerCache.GetSnapshot();
        var countedLexical = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.CountedLexical);

        Assert.False(result.IsError);
        var atoms = result.Value.ToAtoms();
        Assert.Equal(2, atoms.Count);
        Assert.All(atoms, value => Assert.True(value >= 0m && value < 10m));
        Assert.Equal(atoms[0], atoms[1]);
        Assert.Equal(2, cache.Requests.Count);
        Assert.All(cache.Requests, request =>
        {
            Assert.Equal("A", request.Binding.Name);
            Assert.Equal(ZeroArgPropertyAccessKind.CountedLexical, request.AccessKind);
        });
        Assert.Equal(2, snapshot.TotalRequests);
        Assert.Equal(1, snapshot.Hits);
        Assert.Equal(1, snapshot.Misses);
        Assert.Equal(1, snapshot.Stores);
        Assert.Equal(2, countedLexical.Requests);
        Assert.Equal(1, countedLexical.Hits);
        Assert.Equal(1, countedLexical.Misses);
        Assert.Equal(1, countedLexical.Stores);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_OuterFreshCallsDoNotForceNestedPropertyFreshness()
    {
        var source = """
            A = Math.RandomInt(0, 10)
            B = A, A
            B(), B()
            """;
        var innerCache = new RunScopedZeroArgPropertyResultCache();
        var cache = new RecordingZeroArgPropertyResultCache(innerCache);

        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root), cache);
        var snapshot = innerCache.GetSnapshot();
        var countedLexical = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.CountedLexical);

        Assert.False(result.IsError);
        var atoms = result.Value.ToAtoms();
        Assert.Equal(4, atoms.Count);
        Assert.All(atoms, value => Assert.True(value >= 0m && value < 10m));
        Assert.Equal(atoms[0], atoms[1]);
        Assert.Equal(atoms[2], atoms[3]);
        Assert.Equal(4, cache.Requests.Count);
        Assert.All(cache.Requests, request =>
        {
            Assert.Equal("A", request.Binding.Name);
            Assert.Equal(ZeroArgPropertyAccessKind.CountedLexical, request.AccessKind);
        });
        Assert.Equal(4, snapshot.TotalRequests);
        Assert.Equal(2, snapshot.Hits);
        Assert.Equal(2, snapshot.Misses);
        Assert.Equal(2, snapshot.Stores);
        Assert.Equal(4, countedLexical.Requests);
        Assert.Equal(2, countedLexical.Hits);
        Assert.Equal(2, countedLexical.Misses);
        Assert.Equal(2, countedLexical.Stores);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_ExplicitNestedZeroArgCallsBypassDirectCache()
    {
        var source = """
            A = Math.RandomInt(0, 10)
            C = A(), A()
            C()
            """;
        var innerCache = new RunScopedZeroArgPropertyResultCache();
        var cache = new RecordingZeroArgPropertyResultCache(innerCache);

        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root), cache);
        var snapshot = innerCache.GetSnapshot();

        Assert.False(result.IsError);
        var atoms = result.Value.ToAtoms();
        Assert.Equal(2, atoms.Count);
        Assert.All(atoms, value => Assert.True(value >= 0m && value < 10m));
        Assert.Empty(cache.Requests);
        Assert.Equal(0, snapshot.TotalRequests);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_DotReceiverUsesLexicalAccessKind()
    {
        var source = """
            Values = range(1, 5)
            Values.count + Values.count
            """;
        var cache = new RunScopedZeroArgPropertyResultCache();

        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root), cache);
        var snapshot = cache.GetSnapshot();
        var lexical = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Lexical);

        Assert.False(result.IsError);
        Assert.Equal([10m], result.Value.ToAtoms());
        Assert.Equal(2, snapshot.TotalRequests);
        Assert.Equal(1, snapshot.Hits);
        Assert.Equal(1, snapshot.Misses);
        Assert.Equal(1, snapshot.Stores);
        Assert.Equal(2, lexical.Requests);
        Assert.Equal(1, lexical.Hits);
        Assert.Equal(1, lexical.Misses);
        Assert.Equal(1, lexical.Stores);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_TracksStructuralAccessKindRequests()
    {
        var source = """
            Left = {
                Value = 1
            }
            Left.Value + Left.Value
            """;
        var innerCache = new RunScopedZeroArgPropertyResultCache();
        var cache = new RecordingZeroArgPropertyResultCache(innerCache);

        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root), cache);
        var snapshot = innerCache.GetSnapshot();
        var structural = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Structural);
        var structuralRequests = cache.Requests
            .Where(request => request.AccessKind == ZeroArgPropertyAccessKind.Structural)
            .ToList();
        var comparison = CompareKeyComponents(structuralRequests[0], structuralRequests[1]);

        Assert.False(result.IsError);
        Assert.Equal([2m], result.Value.ToAtoms());
        Assert.Equal(2, snapshot.TotalRequests);
    Assert.Equal(1, snapshot.Hits);
    Assert.Equal(1, snapshot.Misses);
    Assert.Equal(1, snapshot.Stores);
    Assert.Equal(1, snapshot.DistinctKeysCreated);
    Assert.Equal(0, snapshot.RepeatedMissRequests);
        Assert.Equal(2, structural.Requests);
    Assert.Equal(1, structural.Hits);
    Assert.Equal(1, structural.Misses);
    Assert.Equal(1, structural.Stores);

    // The evaluator still rebuilds distinct structural owners here, but the
    // effective Stage 1 key no longer splits the cache on that difference.
        Assert.Equal(2, structuralRequests.Count);
    Assert.False(ReferenceEquals(structuralRequests[0].Owner, structuralRequests[1].Owner));
    Assert.True(comparison.AllComponentsMatch);
    Assert.True(comparison.OwnerIdentityMatches);
        Assert.True(comparison.BindingIdentityMatches);
        Assert.True(comparison.ValueEnvironmentIdentityMatches);
        Assert.True(comparison.AlgorithmEnvironmentIdentityMatches);
        Assert.True(comparison.CountedParamEnvironmentIdentityMatches);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_PreservesBehaviorAcrossDifferentValueEnvironments()
    {
        var source = """
            Measure(values) = {
                Count = values.count
                Count + Count
            }
            Measure((1, 2)) + Measure((3, 4, 5))
            """;
        var cache = new RunScopedZeroArgPropertyResultCache();

        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root), cache);

        Assert.False(result.IsError);
        Assert.Equal([10m], result.Value.ToAtoms());
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_PreservesBehaviorAcrossDifferentOwnerIdentities()
    {
        var sharedClosedBinding = new Property(
            "Shared",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Resolve("Base")])) ;

        var localBaseBinding = new Property(
            "Base",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(1)]));

        var openBaseBinding = new Property(
            "Base",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(2)]),
            IsPublic: true);

        var libraryBinding = new Property(
            "Lib",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [openBaseBinding],
                Output: []),
            IsPublic: true);

        var structuralWrapperBinding = new Property(
            "StructuralWrapper",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [localBaseBinding, sharedClosedBinding],
                Output:
                [
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("Shared"),
                        new Expr.Resolve("Shared"))
                ]));

        var openWrapperBinding = new Property(
            "OpenWrapper",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [new Expr.Resolve("Lib")],
                Properties: [sharedClosedBinding],
                Output:
                [
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("Shared"),
                        new Expr.Resolve("Shared"))
                ]));

        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [libraryBinding, structuralWrapperBinding, openWrapperBinding],
            Output:
            [
                new Expr.Binary(
                    BinaryOp.Add,
                    new Expr.Resolve("StructuralWrapper"),
                    new Expr.Resolve("OpenWrapper"))
            ]);

        var cache = new RunScopedZeroArgPropertyResultCache();
        var result = Evaluator.Run(new Expr.Block(root), cache);

        Assert.False(result.IsError);
        Assert.Equal([6m], result.Value.ToAtoms());
    }

    [Fact]
    public void LoopOptimizer_MultiEmissionHandoff_DoesNotReplayCompletedIterationPropertyAccess()
    {
        var repeatSource = """
            Tick = 42
            S = ((1, 2), (3, 4))
            repeat({a + b + Tick, S:0}, 1, 0, 0)
            """;
        var whileSource = """
            Tick = 42
            S = ((1, 0), (2, 2))
            while({a + Tick, S:0}, 9)
            """;

        foreach (var source in new[] { repeatSource, whileSource })
        {
            var parsed = Parser.Parse(source);
            Assert.False(
                parsed.HasErrors,
                string.Join(Environment.NewLine, parsed.Diagnostics.Select(static diagnostic => diagnostic.Message)));
            var cache = new RecordingZeroArgPropertyResultCache(UncachedZeroArgPropertyResultCache.Instance);
            var diagnostics = new LoopOptimizationDiagnostics();

            var result = Evaluator.Run(
                new Expr.Block(parsed.Root),
                cache,
                enableLoopOptimization: true,
                diagnostics);

            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Single(cache.Requests, static request => request.Binding.Name == "Tick");
            Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);
            Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopFallbacks);
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
        => new(
            name,
            NewAlgorithm(),
            IsPublic: true);

    private static CacheKeyComponentComparison CompareKeyComponents(
        ZeroArgPropertyExecution first,
        ZeroArgPropertyExecution second)
    {
        var firstKey = ZeroArgPropertyCacheKey.FromExecution(first);
        var secondKey = ZeroArgPropertyCacheKey.FromExecution(second);

        return new CacheKeyComponentComparison(
            ReferenceEquals(firstKey.OwnerIdentity, secondKey.OwnerIdentity),
            ReferenceEquals(firstKey.BindingIdentity, secondKey.BindingIdentity),
            ReferenceEquals(firstKey.ValueEnvironmentIdentity, secondKey.ValueEnvironmentIdentity),
            ReferenceEquals(firstKey.AlgorithmEnvironmentIdentity, secondKey.AlgorithmEnvironmentIdentity),
            ReferenceEquals(firstKey.CountedParamEnvironmentIdentity, secondKey.CountedParamEnvironmentIdentity));
    }
}
