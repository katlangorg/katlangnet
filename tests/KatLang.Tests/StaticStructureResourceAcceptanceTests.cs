namespace KatLang.Tests;

public sealed class StaticStructureResourceAcceptanceTests
{
    [Fact]
    public void SharedMemberBearingReferenceTailStaysWithinTheExistingWorkBudget()
    {
        const int length = 32, names = 8;
        var source = "open A0\nLib={" + string.Join('\n', Enumerable.Range(0, names).Select(i => $"public N{i}={i}"))
            + "\n0}\n" + string.Join('\n', Enumerable.Range(0, length).Select(i => $"A{i}=" + (i + 1 == length ? "Lib" : $"A{i + 1}")))
            + "\n(" + string.Join(',', Enumerable.Range(0, names).Select(i => $"N{i}")) + ")";
        var compiled = FrontEndPipeline.Process(source);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(compiled.ElaboratedRoot));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(Enumerable.Range(0, names).Select(i => (System.Numerics.Decimal128)i), result.Value);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AnObserverCanUnlockOrdinaryWorkWithoutChangingTheFixedPoint(bool deferred)
    {
        var engine = new StaticQueryEngine<int, int>(new ObserverCycle(deferred), limits: new(100, 4, 20, 100));
        Assert.Equal(1, engine.Get(0));
        Assert.Equal(1, engine.Get(1));
        Assert.Equal(1, engine.Get(2));
    }

    [Fact]
    public void FailureRejectsPublishedFactsAndPreviouslyCachedProviderReads()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("open Lib\nLib={public K=7\n0}\nK");
        var (operation, _) = StaticStructureAdmission.Create(raw);
        var diagnostics = new DiagnosticBag();
        var modules = new ModuleUnits();
        var detectedInput = ParameterDetector.DetectPrevalidated(raw, diagnostics: diagnostics, modules: modules, structuralOperation: operation);
        var (detected, _) = detectedInput;
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics, modules: modules, structuralOperation: operation);
        Assert.Empty(diagnostics);
        var publication = resolved.CompletedStructure!;
        var graph = publication.Facts;
        var prelude = ElaboratedScopeLookup.CreateScope(graph.Prelude, memberIndexes: new OpenMemberIndexCache(),
            completedContext: graph.Context(graph.PreludeKey));
        var scope = ElaboratedScopeLookup.CreateScope(resolved, prelude);
        Assert.Single(scope.GetResolvedOpenProviders());
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var failure = Assert.Throws<OperationCanceledException>(() => PropertyExposureResolver.Resolve(resolved,
            observations: null, modules: modules, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, failure.CancellationToken);
        Assert.True(graph.IsFailed);
        Assert.Throws<InvalidOperationException>(() => graph.Facts(publication.Entry!));
        Assert.Throws<InvalidOperationException>(() => scope.GetResolvedOpenProviders());
        Assert.Throws<InvalidOperationException>(() => operation.Freeze());
    }

    [Fact]
    public void FanInStorageIsReservedBeforeSubscriptionAndCannotBeSwallowed()
    {
        var engine = new StaticQueryEngine<int, int>(new SwallowedStorageFault(), limits: new(100, 4, 20, 100, 10));
        Assert.Throws<StaticQueryLimitExceededException>(() => engine.Get(0));
        Assert.Equal(0, engine.Statistics.Dependencies);
        Assert.Equal(10, engine.Statistics.PeakStorageUnits);
        Assert.Throws<InvalidOperationException>(() => engine.TryGetFinal(0, out _));
    }

    [Fact]
    public void MetadataAndTemporaryStorageShareOneOverflowSafeStickyEnvelope()
    {
        var budget = new StaticQueryResourceBudget(new(long.MaxValue, 4, MaxStorageUnits: long.MaxValue));
        budget.Metadata(long.MaxValue - 1, 0);
        using var lease = budget.Temporary();
        lease.Add(1);
        Assert.Throws<StaticQueryLimitExceededException>(() => budget.Metadata(1, 0));
        Assert.Equal(long.MaxValue, budget.PeakStorageUnits);
        Assert.True(budget.IsFailed);
        Assert.Throws<InvalidOperationException>(() => budget.Work(0));
    }

    [Fact]
    public void AdapterWorkAndCancellationFaultCompletedPublication()
    {
        var key = new StaticKeyTable().Root;
        var budget = new StaticQueryResourceBudget(new(1, 4, MaxStorageUnits: 100));
        var graph = new CompletedStaticStructures(key, resources: budget);
        graph.Add(key, new(null, new(), new(), new Dictionary<string, StaticScopeKey>(), new HashSet<string>(), []));
        budget.Metadata(1);
        Assert.Throws<StaticQueryLimitExceededException>(() => graph.Seal());
        Assert.True(graph.IsFailed);
        Assert.Throws<InvalidOperationException>(() => graph.Facts(key));
        var cancelled = new StaticQueryResourceBudget(new(100, 4, MaxStorageUnits: 100));
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        Assert.Throws<OperationCanceledException>(() => cancelled.Metadata(1, cancellationToken: cts.Token));
        Assert.True(cancelled.IsFailed);
    }

    [Fact]
    public void CancelledProducerCannotExportOrExposeUnsealedFacts()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("A=7\nA");
        using var cts = new CancellationTokenSource();
        var (op, _) = StaticStructureAdmission.Create(raw, cancellationToken: cts.Token);
        var bag = new DiagnosticBag();
        var modules = new ModuleUnits();
        var detectedInput = ParameterDetector.DetectPrevalidated(raw, diagnostics: bag, modules: modules, structuralOperation: op);
        var (detected, _) = detectedInput;
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: bag, modules: modules, structuralOperation: op);
        Assert.Empty(bag);
        cts.Cancel();
        Assert.Throws<OperationCanceledException>(() => op.Freeze(cts.Token));
        Assert.True(resolved.CompletedStructure!.Facts.IsFailed);
        Assert.Throws<OperationCanceledException>(() => op.Freeze());
    }

    [Fact]
    public void AnIndependentCancelledExportDoesNotInvalidateACompletedUnit()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("A=7\nA");
        var (op, _) = StaticStructureAdmission.Create(raw);
        var bag = new DiagnosticBag();
        var modules = new ModuleUnits();
        var detectedInput = ParameterDetector.DetectPrevalidated(raw, diagnostics: bag, modules: modules, structuralOperation: op);
        var (detected, _) = detectedInput;
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: bag, modules: modules, structuralOperation: op);
        var exposed = PropertyExposureResolver.Resolve(resolved, observations: null, modules: modules);
        Assert.Empty(bag);
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        Assert.Throws<OperationCanceledException>(() => op.Freeze(cts.Token));
        var facts = exposed.CompletedStructure!.Facts;
        Assert.False(facts.IsFailed);
        Assert.NotNull(facts.Facts(op.Root));
        Assert.NotNull(op.Freeze());
    }

    private sealed class SwallowedStorageFault : IStaticQueryDefinition<int, int>
    {
        public int Initial(int key) => 0;
        public int PathCycleValue => 1;
        public bool ValueEquals(int left, int right) => left == right;
        public bool IsRefinement(int before, int after) => after >= before;
        public StaticQueryStep<int> Compute(int key, StaticQueryReader<int, int> reader)
        {
            try { _ = reader.Read(1); } catch (StaticQueryLimitExceededException) { }
            return StaticQueryStep.Complete(1);
        }
    }

    private sealed class ObserverCycle(bool deferred) : IStaticQueryDefinition<int, int>
    {
        public bool IsClosureObserver(int key) => deferred && key == 2;
        public int Initial(int key) => 0;
        public int PathCycleValue => 1;
        public bool ValueEquals(int left, int right) => left == right;
        public bool IsRefinement(int before, int after) => after >= before;
        public StaticQueryStep<int> Compute(int key, StaticQueryReader<int, int> reader)
        {
            if (key == 2)
            {
                _ = reader.Read(0);
                return StaticQueryStep.Complete(1);
            }
            if (key == 0) _ = reader.Read(1);
            return StaticQueryStep.Complete(reader.Read(2));
        }
    }
}
