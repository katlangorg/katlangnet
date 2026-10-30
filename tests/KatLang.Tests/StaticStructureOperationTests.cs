using System.Runtime.CompilerServices;

namespace KatLang.Tests;

public sealed class StaticStructureOperationTests
{
    private static readonly StaticQueryLimits Limits = new(1_000_000, 4, 200_000, 4_000_000);
    private static Algorithm.User Parse(string source) => (Algorithm.User)SourceProvenance.ParseSyntaxValidRoot(source);
    private static Algorithm Property(Algorithm body, string name) => body.Properties.Single(p => p.Name == name).Value;
    private static string[] Inputs(StaticStructureOperation operation, StaticScopeKey scope)
        => Assert.IsType<string[]>(operation.Read(StaticQueryKey.Inputs(scope)).Data);

    [Fact]
    public void PassPublicationsKeepRawQueryDefinitionsAndContextIdentity()
    {
        var root = Parse("P = x + y\n0");
        var operation = new StaticStructureOperation(root, Limits);
        var raw = Assert.IsType<Algorithm.User>(Property(root, "P"));
        var p = operation.ContextOf(operation.Root, raw);
        Assert.Equal(new[] { "x", "y" }, Inputs(operation, p));
        var detected = Assert.IsType<Algorithm.User>(raw.WithParams(new[] { "x", "y" }));
        operation.Publish(p, StaticPublicationStage.Detected, detected);
        var resolved = detected with { Output = new Expr[] { new Expr.Num(0) } };
        operation.Publish(p, StaticPublicationStage.Resolved, resolved);
        Assert.Same(p, operation.ContextOf(operation.Root, detected));
        Assert.Same(p, operation.ContextOf(operation.Root, resolved));
        Assert.Same(raw, operation.SourceOf(p));
        Assert.Same(resolved, operation.Published(p, StaticPublicationStage.Resolved));
        Assert.Equal(new[] { "x", "y" }, Inputs(operation, p));
    }

    [Fact]
    public void Q8InputDeclarationRemainsDetectedAfterSignaturePublication()
    {
        var root = Parse("F(x)=x\nP=F+0\n0");
        var operation = new StaticStructureOperation(root, Limits);
        var raw = Assert.IsType<Algorithm.User>(Property(root, "P"));
        var p = operation.ContextOf(operation.Root, raw);
        var detected = raw with { Output = raw.Output.ToArray() };
        operation.Publish(p, StaticPublicationStage.Detected, detected);
        var map = ImplicitArgumentResolver.SignatureMap.Empty(null);
        var before = operation.Declaration(p, current: false, map);
        var resolved = Assert.IsType<Algorithm.User>(detected.WithParams(new[] { "x" }));
        operation.Publish(p, StaticPublicationStage.Resolved, resolved);
        var after = operation.Declaration(p, current: false, map);
        Assert.Same(detected, before.Target);
        Assert.Same(before.Target, after.Target);
        Assert.True(before.Raw && after.Raw);
        var signature = operation.Declaration(p, current: true, map);
        Assert.Same(resolved, signature.Target);
        Assert.False(signature.Raw);
    }

    [Fact]
    public void ReplacedNavigationLevelsAlsoReleaseTheirOperation()
    {
        var operation = new StaticStructureOperation(Parse("0"), Limits);
        var navigated = operation.ResolverLevel(operation.Root)!;
        var walked = new ImplicitArgumentResolver.ResolverLevel(operation.OwnersOf(operation.Root), null,
            staticContext: operation.Context(operation.Root));
        operation.RegisterResolverLevel(walked);
        operation.ReleaseResolverLevels();
        Assert.Null(navigated.StaticContext);
        Assert.Null(walked.StaticContext);
    }

    [Fact]
    public void ChangedDefinitionCannotReuseAnAlreadyCompletedContext()
    {
        var root = Parse("P = x + y\n0");
        var operation = new StaticStructureOperation(root, Limits);
        var raw = Assert.IsType<Algorithm.User>(Property(root, "P"));
        var p = operation.ContextOf(operation.Root, raw);
        Assert.Equal(new[] { "x", "y" }, Inputs(operation, p));
        Assert.Throws<InvalidOperationException>(() => operation.ContextOf(operation.Root, raw with { Output = [] }));
    }

    [Fact]
    public void PublicationsRequireTheSameDeclarationAndOneViewPerStage()
    {
        var root = Parse("P = x\n0");
        var operation = new StaticStructureOperation(root, Limits);
        var raw = Assert.IsType<Algorithm.User>(Property(root, "P"));
        var p = operation.ContextOf(operation.Root, raw);
        Assert.Throws<InvalidOperationException>(() => operation.Publish(p, StaticPublicationStage.Resolved, raw));
        Assert.Throws<InvalidOperationException>(() => operation.Publish(p, StaticPublicationStage.Detected, Parse("0")));
        operation.Publish(p, StaticPublicationStage.Detected, raw);
        operation.Publish(p, StaticPublicationStage.Detected, raw);
        Assert.Throws<InvalidOperationException>(() => operation.Publish(p, StaticPublicationStage.Detected, raw with { Output = [] }));
    }

    [Fact]
    public void ReferencesShareTerminalPublicationWhileCarriersKeepTheirOwnCell()
    {
        var root = Parse("Lib = { public V = 42\n0 }\nA = Lib\nC = { Lib }\n0");
        var operation = new StaticStructureOperation(root, Limits);
        var lib = operation.ContextOf(operation.Root, Property(root, "Lib"));
        var a = operation.ContextOf(operation.Root, Property(root, "A"));
        var c = operation.ContextOf(operation.Root, Property(root, "C"));
        var cell = Assert.IsType<AliasStructureCell>(operation.StructureCell(a));
        Assert.Same(cell, operation.StructureCell(lib));
        Assert.NotSame(cell, operation.StructureCell(c));
        Assert.True(cell.IsPending);
        var raw = Assert.IsType<Algorithm.User>(Property(root, "Lib"));
        var detected = raw with { Output = new Expr[] { new Expr.Num(1) } };
        var resolved = detected with { Output = new Expr[] { new Expr.Num(2) } };
        operation.Publish(lib, StaticPublicationStage.Detected, detected);
        Assert.True(cell.IsPending);
        operation.Publish(lib, StaticPublicationStage.Resolved, resolved);
        Assert.False(cell.IsPending);
        Assert.Same(resolved, cell.Structure);
        Assert.Same(cell, operation.StructureCell(a));
        var continuation = Freeze(operation);
        var fork = continuation.Materialize(operation.Root, Parse("0"), new Pattern.Bind("x"), Limits);
        Assert.Same(cell, fork.StructureCell(a));
        Assert.Same(resolved, fork.Published(lib, StaticPublicationStage.Resolved));
    }

    [Fact]
    public void UnfinishedUnitCannotProduceAContinuation()
    {
        var operation = new StaticStructureOperation(Parse("0"), Limits);
        Assert.Throws<InvalidOperationException>(() => operation.Freeze());
        operation.Publish(operation.Root, StaticPublicationStage.Detected, operation.SourceOf(operation.Root));
        Assert.Throws<InvalidOperationException>(() => operation.Freeze());
    }

    [Fact]
    public void RealPassLevelsShareContextKeys_AndRebuiltOwnersKeepTheirBindings()
    {
        var root = Parse("P(x) = { N = x\nN }\n0");
        var operation = new StaticStructureOperation(root, Limits);
        var prelude = operation.CreatePreludeScope();
        var rootLevel = ElaboratedScopeLookup.CreateScope(root, prelude);
        Assert.Same(operation.Root, rootLevel.StaticContext!.Key);
        var raw = Assert.IsType<Algorithm.User>(Property(root, "P"));
        var pLevel = ElaboratedScopeLookup.CreateScope(raw, rootLevel);
        var key = pLevel.StaticContext!.Key;
        var copied = raw with { Opens = [] };
        operation.RegisterView(key, copied);
        var rebuilt = ElaboratedScopeLookup.CreateScope(copied, rootLevel);
        var bindings = ParameterOwnership.Empty.Extend(pLevel, new[] { "x" });
        Assert.True(bindings.DeclaresParameter(rebuilt, "x"));
        var resolverRoot = new ImplicitArgumentResolver.ResolverLevel(DeclaringOwners.Root, null, staticContext: operation.Context(operation.Root));
        var resolverP = new ImplicitArgumentResolver.ResolverLevel(copied, DeclaringOwners.Root.Inside(raw), resolverRoot);
        Assert.Same(key, operation.Queries.Keys.ScopeOf(pLevel));
        Assert.Same(key, operation.Queries.Keys.ScopeOf(rebuilt));
        Assert.Same(key, operation.Queries.Keys.ScopeOf(resolverP));
        Assert.Throws<InvalidOperationException>(() => new StaticKeyTable().ScopeOf(pLevel));
    }

    [Fact]
    public void RealPassAdaptersPreserveBranchRegionsAndModuleHygiene()
    {
        var root = Parse("Shared = { N = x\n0 }\nM = { public V = 42\n0 }\n0");
        var operation = new StaticStructureOperation(root, Limits);
        var rootLevel = ElaboratedScopeLookup.CreateScope(root, operation.CreatePreludeScope());
        var shared = Property(root, "Shared");
        var xContext = rootLevel.StaticContext!.Inside(shared, new Pattern.Bind("x"));
        var yContext = rootLevel.StaticContext.Inside(shared, new Pattern.Bind("y"));
        var xLevel = ElaboratedScopeLookup.CreateScope(shared, rootLevel, staticContext: xContext);
        var yLevel = ElaboratedScopeLookup.CreateScope(shared, rootLevel, staticContext: yContext);
        Assert.NotSame(operation.Queries.Keys.ScopeOf(xLevel), operation.Queries.Keys.ScopeOf(yLevel));
        var module = Assert.IsType<Algorithm.User>(Property(root, "M")) with { IsModuleElaborated = true };
        var inX = ElaboratedScopeLookup.CreateScope(module, xLevel);
        var inY = ElaboratedScopeLookup.CreateScope(module, yLevel);
        Assert.Same(operation.Queries.Keys.ScopeOf(inX), operation.Queries.Keys.ScopeOf(inY));
        Assert.Same(rootLevel.Root, inX.Parent);
    }

    [Fact]
    public void BranchContextsIncludeTheWrittenPatternRegion()
    {
        var root = Parse("Template = { x + 0 }\n0");
        var operation = new StaticStructureOperation(root, Limits);
        var body = Property(root, "Template");
        var x = operation.ContextOf(operation.Root, body, new Pattern.Bind("x"));
        var y = operation.ContextOf(operation.Root, body, new Pattern.Bind("y"));
        Assert.NotSame(x, y);
        Assert.Equal(StaticFactKind.Parameter, operation.Read(StaticQueryKey.Binding(x, "x", StaticCycleCheck.Formation)).Kind);
        Assert.Equal(StaticFactKind.Missing, operation.Read(StaticQueryKey.Binding(y, "x", StaticCycleCheck.Formation)).Kind);
    }

    [Fact]
    public void LoaderExpandedModuleStillInfersAndSharesItsHygienicContext()
    {
        var root = Parse("P(k) = k\nQ(k) = k\n0");
        var module = Parse("a + b") with { IsModuleElaborated = true };
        var operation = new StaticStructureOperation(root, Limits);
        var p = operation.ContextOf(operation.Root, Property(root, "P"));
        var q = operation.ContextOf(operation.Root, Property(root, "Q"));
        var first = operation.ContextOf(p, module);
        Assert.Same(first, operation.ContextOf(q, module));
        Assert.Same(operation.Queries.Keys.Root, first.Parent);
        Assert.Equal(new[] { "a", "b" }, Inputs(operation, first));
    }

    [Fact]
    public void DeferredMaterializationGetsFreshDefinitionAndClosedBinders()
    {
        var root = Parse("Lib = { public V = 42\n0 }\nF(x) = x\n0");
        var operation = new StaticStructureOperation(root, Limits);
        var branch = Assert.IsType<Algorithm.User>(Property(root, "F"));
        var pattern = new Pattern.Bind("x");
        var eager = operation.ContextOf(operation.Root, branch, pattern);
        Assert.Empty(Inputs(operation, eager));
        var external = operation.ContextOf(operation.Root, Property(root, "Lib"));
        Assert.Same(external, operation.Read(StaticQueryKey.TargetWalk(external, StaticCycleCheck.Formation)).Scope);
        var continuation = Freeze(operation);
        var loaded = branch with { Output = new Expr[] { new Expr.Resolve("V") }, Opens = new Expr[] { new Expr.Resolve("Lib") } };
        var fork = continuation.Materialize(operation.Root, loaded, pattern, Limits);
        Assert.NotSame(eager, fork.Root);
        Assert.Same(fork.Root, fork.ContextOf(operation.Root, loaded, pattern));
        Assert.Same(operation.Root, fork.Queries.Root);
        Assert.Same(loaded, fork.SourceOf(fork.Root));
        Assert.Empty(Inputs(fork, fork.Root));
        var binding = fork.Read(StaticQueryKey.Binding(fork.Root, "V", StaticCycleCheck.Formation));
        Assert.Equal(StaticFactKind.Declaration, binding.Kind);
        Assert.Same(external, binding.Scope);
        Assert.Same(external, fork.Read(StaticQueryKey.TargetWalk(external, StaticCycleCheck.Formation)).Scope);
    }

    [Fact]
    public void DeferredForkDoesNotUseTheEagerCancellationTokenForLazySyntax()
    {
        using var eagerToken = new CancellationTokenSource();
        var root = Parse("P = a + b\nF(x) = x\n0");
        var operation = new StaticStructureOperation(root, Limits, cancellationToken: eagerToken.Token);
        var p = operation.ContextOf(operation.Root, Property(root, "P"));
        var continuation = Freeze(operation); // P's occurrence graph has deliberately not been built.
        eagerToken.Cancel();
        var fork = continuation.Materialize(operation.Root, Property(root, "F"), new Pattern.Bind("x"), Limits);
        Assert.Equal(new[] { "a", "b" }, Inputs(fork, p));
        using var forkToken = new CancellationTokenSource();
        forkToken.Cancel();
        Assert.Throws<OperationCanceledException>(() => continuation.Materialize(operation.Root, Property(root, "F"),
            new Pattern.Bind("x"), Limits, forkToken.Token));
    }

    [Fact]
    public void FailedSolverCannotPublishAFrozenContinuation()
    {
        var operation = new StaticStructureOperation(Parse("P = x\n0"), new(1_000_000, 4, MaxEntries: 0));
        CompleteUnit(operation);
        Assert.Throws<StaticQueryLimitExceededException>(() => operation.Read(StaticQueryKey.Inputs(operation.Root)));
        Assert.Throws<InvalidOperationException>(() => Freeze(operation));
        Assert.Throws<InvalidOperationException>(() => operation.Published(operation.Root, StaticPublicationStage.Resolved));
        Assert.Throws<InvalidOperationException>(() => operation.Publish(operation.Root, StaticPublicationStage.Detected, Parse("0")));
    }

    [Fact]
    public void FrozenContinuationDoesNotRetainTheEagerEngineOrCancellationSource()
    {
        var (continuation, weakOperation, weakCancellation) = FreezeAndRelease();
        GC.Collect(); GC.WaitForPendingFinalizers(); GC.Collect();
        Assert.False(weakOperation.IsAlive);
        Assert.False(weakCancellation.IsAlive);
        GC.KeepAlive(continuation);
    }

    [Fact]
    public void AttachedOwnershipMapsDoNotRetainTheEagerPhysicalScopeOrOperation()
    {
        var (bindings, weakOperation, weakScope) = BindAndRelease();
        GC.Collect(); GC.WaitForPendingFinalizers(); GC.Collect();
        Assert.False(weakOperation.IsAlive);
        Assert.False(weakScope.IsAlive);
        Assert.True(bindings.Contains("x"));
        GC.KeepAlive(bindings);
    }

    [Fact]
    public void ARebuiltNeverCalledOwnerKeepsTheCallableBindingExemption()
    {
        var root = Parse("x + 0");
        var operation = new StaticStructureOperation(root, Limits);
        var prelude = operation.CreatePreludeScope();
        var first = ElaboratedScopeLookup.CreateScope(root, prelude);
        var bindings = ParameterOwnership.Empty.Extend(first, new[] { "x" }, ownerIsNeverCalled: true);
        var second = ElaboratedScopeLookup.CreateScope(root, prelude);
        Assert.True(bindings.DeclaresParameter(second, "x"));
        Assert.False(bindings.CallableBindings.DeclaresParameter(second, "x"));
    }

    [Fact]
    public void CancellationRefusesPublicationAndDoesNotBecomeAnUnknownClassification()
    {
        using var token = new CancellationTokenSource();
        var root = Parse("P = x\n0");
        var operation = new StaticStructureOperation(root, Limits, cancellationToken: token.Token);
        token.Cancel();
        Assert.Throws<OperationCanceledException>(() => operation.Read(StaticQueryKey.Inputs(operation.Root)));
        Assert.Throws<OperationCanceledException>(() => operation.Publish(operation.Root, StaticPublicationStage.Detected, root));
        Assert.Throws<OperationCanceledException>(() => operation.Freeze());
    }

    [Fact]
    public void SnapshotsExcludeUnfinishedInferenceFacts_AndRecomputeThemFromImmutableSource()
    {
        var root = Parse(StaticStructureWitnessSources.Cases["A.3.1"]);
        var queries = new StaticStructureQueries(root, Limits);
        var p = queries.BodyIn(queries.Root, Property(root, "P"));
        var key = StaticQueryKey.Inputs(p);
        Assert.Equal(StaticFactKind.Unknown, queries.Get(key).Kind);
        var snapshot = queries.Freeze();
        Assert.DoesNotContain(key, snapshot.Facts.Keys);
        Assert.All(snapshot.Facts.Values, value =>
        {
            Assert.False(value.HasUnknownSelection);
            Assert.False(value.Data is StaticOpenMatch { Pending: true });
        });
        var fork = new StaticStructureQueries(snapshot, Limits);
        Assert.Equal(StaticFactKind.Unknown, fork.Get(key).Kind);
    }

    [Fact]
    public void CancellationOfAnEmptyExportDoesNotFaultTheOriginalSolver()
    {
        var queries = new StaticStructureQueries(Parse("0"), Limits);
        using var token = new CancellationTokenSource();
        token.Cancel();
        Assert.Throws<OperationCanceledException>(() => queries.Freeze(token.Token));
        Assert.Equal(StaticFactKind.Inputs, queries.Get(StaticQueryKey.Inputs(queries.Root)).Kind);
    }

    [Fact]
    public void ACancelledSourceCannotExportPreviouslyFinalFacts()
    {
        using var token = new CancellationTokenSource();
        var queries = new StaticStructureQueries(Parse("0"), Limits, cancellationToken: token.Token);
        queries.Get(StaticQueryKey.Inputs(queries.Root));
        token.Cancel();
        Assert.Throws<OperationCanceledException>(() => queries.Freeze());
    }

    [Fact]
    public void EagerAndDeferredDemandPermutationsKeepTheSameContextualSelections()
    {
        var raw = Parse("Lib = { public V = 42\n0 }\nA = Lib\nR = S\nS = { public X = 1\nR }\n0");
        var unit = Parse("open A\nN = p + V\nA.V");
        var pattern = new Pattern.Bind("p");
        for (var seed = 0; seed < 32; seed++)
        {
            var random = new Random(seed);
            var operation = new StaticStructureOperation(raw, Limits);
            var lib = operation.ContextOf(operation.Root, Property(raw, "Lib"));
            var a = operation.ContextOf(operation.Root, Property(raw, "A"));
            var r = operation.ContextOf(operation.Root, Property(raw, "R"));
            var eager = new[] { StaticQueryKey.Inputs(a), StaticQueryKey.TargetWalk(a, StaticCycleCheck.Formation),
                StaticQueryKey.TargetWalk(r, StaticCycleCheck.Formation), StaticQueryKey.Members(lib) };
            random.Shuffle(eager);
            foreach (var key in eager.Take(seed % 5)) operation.Read(key);
            var fork = Freeze(operation).Materialize(operation.Root, unit, pattern, Limits);
            var n = fork.ContextOf(fork.Root, Property(unit, "N"));
            var edge = Assert.IsType<Expr.DotCall>(unit.Output[0]);
            var requests = new[] { StaticQueryKey.Binding(fork.Root, "V", StaticCycleCheck.Formation),
                StaticQueryKey.Binding(n, "p", StaticCycleCheck.Formation), StaticQueryKey.Inputs(n),
                StaticQueryKey.MissSelection(fork.Root, edge), StaticQueryKey.TargetWalk(a, StaticCycleCheck.Formation),
                StaticQueryKey.TargetWalk(r, StaticCycleCheck.Formation) };
            random.Shuffle(requests);
            foreach (var key in requests) fork.Read(key);
            Assert.Same(lib, fork.Read(StaticQueryKey.Binding(fork.Root, "V", StaticCycleCheck.Formation)).Scope);
            Assert.Same(fork.Root, fork.Read(StaticQueryKey.Binding(n, "p", StaticCycleCheck.Formation)).Scope);
            Assert.Empty(Inputs(fork, n));
            Assert.Equal(StaticFactKind.Never, fork.Read(StaticQueryKey.MissSelection(fork.Root, edge)).Kind);
            Assert.Same(lib, fork.Read(StaticQueryKey.TargetWalk(a, StaticCycleCheck.Formation)).Scope);
            Assert.Same(r, fork.Read(StaticQueryKey.TargetWalk(r, StaticCycleCheck.Formation)).Scope);
        }
    }

    [Fact]
    public void AFaultedMaterializationDoesNotPoisonItsContinuationOrAnotherFork()
    {
        var operation = new StaticStructureOperation(Parse("0"), Limits);
        var continuation = Freeze(operation);
        var unit = Parse("0");
        var pattern = new Pattern.Bind("x");
        var bad = continuation.Materialize(operation.Root, unit, pattern, new(1_000_000, 4, MaxEntries: 0));
        Assert.Throws<StaticQueryLimitExceededException>(() => bad.Read(StaticQueryKey.Inputs(bad.Root)));
        Assert.Throws<InvalidOperationException>(() => bad.Published(bad.Root, StaticPublicationStage.Resolved));
        var good = continuation.Materialize(operation.Root, unit, pattern, Limits);
        Assert.Empty(Inputs(good, good.Root));
        Assert.Equal(StaticFactKind.Inputs, operation.Read(StaticQueryKey.Inputs(operation.Root)).Kind);
    }

    private static void CompleteUnit(StaticStructureOperation operation)
    {
        var source = operation.SourceOf(operation.Root);
        operation.Publish(operation.Root, StaticPublicationStage.Detected, source);
        operation.Publish(operation.Root, StaticPublicationStage.Resolved, source);
    }

    private static StaticStructureOperation.Continuation Freeze(StaticStructureOperation operation)
    {
        CompleteUnit(operation);
        return operation.Freeze();
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (ParameterOwnership, WeakReference, WeakReference) BindAndRelease()
    {
        var root = Parse("P(x) = x\n0");
        var operation = new StaticStructureOperation(root, Limits);
        var rootScope = ElaboratedScopeLookup.CreateScope(root, operation.CreatePreludeScope());
        var scope = ElaboratedScopeLookup.CreateScope(Property(root, "P"), rootScope);
        return (ParameterOwnership.Empty.Extend(scope, new[] { "x" }), new(operation), new(scope));
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (StaticStructureOperation.Continuation, WeakReference, WeakReference) FreezeAndRelease()
    {
        var cancellation = new CancellationTokenSource();
        var operation = new StaticStructureOperation(Parse("P = a + b\n0"), Limits, cancellationToken: cancellation.Token);
        operation.Read(StaticQueryKey.Inputs(operation.Root));
        return (Freeze(operation), new(operation), new(cancellation));
    }
}
