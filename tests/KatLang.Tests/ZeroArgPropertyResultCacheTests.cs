using System.Runtime.CompilerServices;
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
        bool CountedParamEnvironmentIdentityMatches,
        bool RunIdentityMatches)
    {
        public bool AllComponentsMatch
            => OwnerIdentityMatches
                && BindingIdentityMatches
                && ValueEnvironmentIdentityMatches
                && AlgorithmEnvironmentIdentityMatches
                && CountedParamEnvironmentIdentityMatches
                && RunIdentityMatches;
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
        var runIdentity = new object();
        var first = new ZeroArgPropertyExecution(
            NewAlgorithm(),
            binding,
            ZeroArgPropertyAccessKind.Structural,
            new object(),
            new object(),
            new object(),
            runIdentity);
        var second = new ZeroArgPropertyExecution(
            NewAlgorithm(),
            binding,
            ZeroArgPropertyAccessKind.Structural,
            new object(),
            new object(),
            new object(),
            runIdentity);

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
        var runIdentity = new object();
        var first = new ZeroArgPropertyExecution(
            NewAlgorithm(),
            binding,
            ZeroArgPropertyAccessKind.Structural,
            valueEnv,
            algorithmEnv,
            countedParamEnv,
            runIdentity);
        var second = new ZeroArgPropertyExecution(
            NewAlgorithm(),
            binding,
            ZeroArgPropertyAccessKind.Structural,
            valueEnv,
            algorithmEnv,
            countedParamEnv,
            runIdentity);

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
        Assert.True(comparison.RunIdentityMatches);
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
    public void RunScopedZeroArgPropertyResultCache_ReusesStructuralExecutions_AcrossRecursivelyRebuiltScopeChains()
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        var binding = NewProperty("Value");
        var valueEnv = new object();
        var algorithmEnv = new object();
        var countedParamEnv = new object();
        var runIdentity = new object();
        IReadOnlyList<Expr> grandparentOpens = [new Expr.Num(1m)];
        IReadOnlyList<Property> grandparentProperties = [NewProperty("Grandparent")];
        IReadOnlyList<Expr> parentOpens = [new Expr.Num(2m)];
        IReadOnlyList<Property> parentProperties = [NewProperty("Parent")];
        IReadOnlyList<Expr> ownerOpens = [new Expr.Num(3m)];
        IReadOnlyList<Property> ownerProperties = [binding];

        Algorithm.User RebuildOwner()
            => NewAlgorithm() with
            {
                Parent = new ScopeCtx(
                    new ScopeCtx(null, grandparentOpens, grandparentProperties),
                    parentOpens,
                    parentProperties),
                Opens = ownerOpens,
                Properties = ownerProperties,
            };

        var first = new ZeroArgPropertyExecution(
            RebuildOwner(),
            binding,
            ZeroArgPropertyAccessKind.Structural,
            valueEnv,
            algorithmEnv,
            countedParamEnv,
            runIdentity);
        var second = first with { Owner = RebuildOwner() };

        var firstResult = cache.GetOrEvaluate(
            first,
            () => EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(new Result.Atom(1m), 1)));
        var secondResult = cache.GetOrEvaluate(
            second,
            () => EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(new Result.Atom(2m), 1)));

        Assert.False(ReferenceEquals(first.Owner.Parent, second.Owner.Parent));
        Assert.False(ReferenceEquals(first.Owner.Parent?.Parent, second.Owner.Parent?.Parent));
        Assert.True(CompareKeyComponents(first, second).AllComponentsMatch);
        Assert.Equal(1m, Assert.IsType<Result.Atom>(firstResult.Value.Value).Value);
        Assert.Equal(1m, Assert.IsType<Result.Atom>(secondResult.Value.Value).Value);
        Assert.Equal(1, cache.GetSnapshot().Hits);
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
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

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

        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache);
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
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root),
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

        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache);
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

        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache);
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

        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache);
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

        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache);
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

        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache);
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

        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache);
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

        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache);
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

        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache);
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
        Assert.True(comparison.RunIdentityMatches);
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

        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache);

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
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root), cache);

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
                new Expr.AlgorithmExpr(parsed.Root),
                cache,
                enableLoopOptimization: true,
                diagnostics);

            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Single(cache.Requests, static request => request.Binding.Name == "Tick");
            Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);
            Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopFallbacks);
        }
    }

    /// <summary>
    /// ONE shared <see cref="Property"/> object placed under TWO owners whose
    /// lexical resolution of <c>Base</c> differs, demanded STRUCTURALLY via
    /// <see cref="Expr.DotCall"/>. This is the structural twin of the tree in
    /// <see cref="Evaluator_ZeroArgPropertyCaching_PreservesBehaviorAcrossDifferentOwnerIdentities"/>:
    /// shared acyclic subtrees are a supported host-AST input class, and an
    /// owner-blind structural cache key served <c>Lib1</c>'s value for
    /// <c>Lib2.Shared</c>. The third output row repeats <c>Lib1.Shared</c> so the
    /// same tree also pins that structural reuse across rebuilt owner records
    /// still works. Expected output: <c>(1, 2, 1)</c>.
    /// </summary>
    private static Expr NewSharedStructuralPropertyProgram()
    {
        var sharedBinding = new Property(
            "Shared",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Resolve("Base")]),
            IsPublic: true);

        var lib1Binding = new Property(
            "Lib1",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties:
                [
                    new Property(
                        "Base",
                        new Algorithm.User(
                            Parent: null,
                            Parameters: [],
                            Opens: [],
                            Properties: [],
                            Output: [new Expr.Num(1)])),
                    sharedBinding,
                ],
                Output: []),
            IsPublic: true);

        var lib2Binding = new Property(
            "Lib2",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties:
                [
                    new Property(
                        "Base",
                        new Algorithm.User(
                            Parent: null,
                            Parameters: [],
                            Opens: [],
                            Properties: [],
                            Output: [new Expr.Num(2)])),
                    sharedBinding,
                ],
                Output: []),
            IsPublic: true);

        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [lib1Binding, lib2Binding],
            Output:
            [
                new Expr.DotCall(new Expr.Resolve("Lib1"), "Shared", null),
                new Expr.DotCall(new Expr.Resolve("Lib2"), "Shared", null),
                new Expr.DotCall(new Expr.Resolve("Lib1"), "Shared", null),
            ]);

        return new Expr.AlgorithmExpr(root);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_StructuralAccess_PreservesBehaviorAcrossDifferentOwnerIdentities()
    {
        var expr = NewSharedStructuralPropertyProgram();

        var cache = new RunScopedZeroArgPropertyResultCache();
        var plain = Evaluator.Run(expr, cache);

        Assert.False(plain.IsError);
        Assert.Equal([1m, 2m, 1m], plain.Value.ToAtoms());
        // Distinct owners never alias; the rebuilt Lib1 owner still reuses its entry.
        AssertStructuralAccessCounts(cache, requests: 3, hits: 1, misses: 2, stores: 2);

        var countedCache = new RunScopedZeroArgPropertyResultCache();
        var counted = Evaluator.RunCounted(expr, countedCache);

        Assert.False(counted.IsError);
        Assert.Equal([1m, 2m, 1m], counted.Value.Value.ToAtoms());
        AssertStructuralAccessCounts(countedCache, requests: 3, hits: 1, misses: 2, stores: 2);
    }

    /// <summary>
    /// Sums the plain and counted structural access kinds: the cache key merges
    /// them by design, and which evaluator core serves a given surface entry
    /// point (root output rows evaluate through the counted core even under
    /// plain <c>Run</c>) is not what these tests pin.
    /// </summary>
    private static void AssertStructuralAccessCounts(
        RunScopedZeroArgPropertyResultCache cache,
        int requests,
        int hits,
        int misses,
        int stores)
    {
        var snapshot = cache.GetSnapshot();
        var plain = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Structural);
        var counted = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.CountedStructural);

        Assert.Equal(requests, plain.Requests + counted.Requests);
        Assert.Equal(hits, plain.Hits + counted.Hits);
        Assert.Equal(misses, plain.Misses + counted.Misses);
        Assert.Equal(stores, plain.Stores + counted.Stores);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_StructuralAccess_MatchesUncachedBehavior()
    {
        var expr = NewSharedStructuralPropertyProgram();

        var uncachedPlain = Evaluator.Run(expr, UncachedZeroArgPropertyResultCache.CreateForRun());
        var cachedPlain = Evaluator.Run(expr, new RunScopedZeroArgPropertyResultCache());

        Assert.False(uncachedPlain.IsError);
        Assert.False(cachedPlain.IsError);
        Assert.Equal(uncachedPlain.Value.ToAtoms(), cachedPlain.Value.ToAtoms());

        var uncachedCounted = Evaluator.RunCounted(expr, UncachedZeroArgPropertyResultCache.CreateForRun());
        var cachedCounted = Evaluator.RunCounted(expr, new RunScopedZeroArgPropertyResultCache());

        Assert.False(uncachedCounted.IsError);
        Assert.False(cachedCounted.IsError);
        Assert.Equal(uncachedCounted.Value.Value.ToAtoms(), cachedCounted.Value.Value.ToAtoms());
        Assert.Equal(uncachedCounted.Value.EmittedCount, cachedCounted.Value.EmittedCount);
    }

    [Fact]
    public void Evaluator_ZeroArgPropertyCaching_StructuralEntries_DoNotCarryAcrossRunsOnASharedCache()
    {
        // The cache contract is run-scoped. A host that (incorrectly) shares one
        // instance across runs must still never be served another run's structural
        // entry: a warmed permissive run must not let a tight-limit rerun bypass
        // its own materialization ceiling.
        var source = """
            X = {
                P = range(1, 200)
            }
            X.P.count
            """;
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var sharedCache = new RunScopedZeroArgPropertyResultCache();

        var warm = Evaluator.Run(expr, sharedCache);
        Assert.False(warm.IsError);
        Assert.Equal([200m], warm.Value.ToAtoms());

        var tight = Evaluator.Run(
            expr,
            sharedCache,
            enableLoopOptimization: true,
            new EvaluationLimits { MaxCollectionItems = 10 });
        Assert.True(tight.IsError);

        var error = tight.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(error);
    }

    [Fact]
    public void UncachedInstance_SharedAcrossConcurrentEvaluations_IsSafeAndStateless()
    {
        // The shared singleton is used concurrently by independent evaluations
        // (thread safety is by per-run isolation everywhere else), so it must
        // record nothing: no thrown collection-corruption exceptions, and no
        // process-lifetime bookkeeping growth.
        const int programCount = 200;
        var programs = Enumerable.Range(0, programCount)
            .Select(index => new Expr.AlgorithmExpr(
                SourceProvenance.ParseValid($"A = {index} + 1\nA + A").Root))
            .ToArray();

        var failures = new System.Collections.Concurrent.ConcurrentBag<string>();
        Parallel.For(0, programCount, index =>
        {
            try
            {
                var result = Evaluator.Run(programs[index], UncachedZeroArgPropertyResultCache.Instance);
                if (result.IsError)
                    failures.Add(result.Error.ToString() ?? "unknown error");
                else if (result.Value.ToAtoms() is not [var atom] || atom != 2m * (index + 1))
                    failures.Add($"wrong value for program {index}");
            }
            catch (Exception exception)
            {
                failures.Add(exception.ToString());
            }
        });

        Assert.Empty(failures);

        var snapshot = UncachedZeroArgPropertyResultCache.Instance.GetSnapshot();
        Assert.Equal(0, snapshot.TotalRequests);
        Assert.Equal(0, snapshot.DistinctKeysCreated);
        Assert.Equal(0, snapshot.RepeatedMissRequests);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static WeakReference EvaluateThroughSharedUncachedInstance()
    {
        var root = SourceProvenance.ParseValid("A = 41 + 1\nA + A").Root;
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root), UncachedZeroArgPropertyResultCache.Instance);
        Assert.False(result.IsError);
        return new WeakReference(root.Properties[0]);
    }

    [Fact]
    public void UncachedInstance_DoesNotRetainEvaluatedPrograms()
    {
        // The former seen-key tracking held strong references to the run's
        // property bindings (and through them the program AST) for process
        // lifetime. The stateless singleton must not pin anything it evaluated.
        var weak = EvaluateThroughSharedUncachedInstance();

        for (var attempt = 0; attempt < 5 && weak.IsAlive; attempt++)
        {
            GC.Collect();
            GC.WaitForPendingFinalizers();
        }

        Assert.False(weak.IsAlive);
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
            // Structural owner identity is a computed scope-chain value, so it is
            // compared through the comparer's owner rule, not raw reference identity.
            ZeroArgPropertyCacheKeyComparer.OwnerIdentityEquals(firstKey.OwnerIdentity, secondKey.OwnerIdentity),
            ReferenceEquals(firstKey.BindingIdentity, secondKey.BindingIdentity),
            ReferenceEquals(firstKey.ValueEnvironmentIdentity, secondKey.ValueEnvironmentIdentity),
            ReferenceEquals(firstKey.AlgorithmEnvironmentIdentity, secondKey.AlgorithmEnvironmentIdentity),
            ReferenceEquals(firstKey.CountedParamEnvironmentIdentity, secondKey.CountedParamEnvironmentIdentity),
            ReferenceEquals(firstKey.RunIdentity, secondKey.RunIdentity));
    }
}
