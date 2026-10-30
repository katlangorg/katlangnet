using KatLang.Semantics;
using System.Numerics;

namespace KatLang.Tests;

public sealed class CompletedStaticStructureTests
{
    [Fact]
    public void PublicationMetadataPreservesAstEqualityAndIsIndependentAcrossCopies()
    {
        var compiled = FrontEndPipeline.Process("Lib={public K=7\n0}\nLib.K");
        Assert.False(compiled.HasErrors);
        var root = compiled.ElaboratedRoot;
        var original = root.CompletedStructure;
        var copy = root with { };
        var print = root.ToString();
        var hash = root.GetHashCode();
        CompletedStaticStructures.Attach(copy, new(original!.Facts));
        Assert.Equal(root, copy);
        Assert.Equal(hash, copy.GetHashCode());
        Assert.Equal(print, copy.ToString());
        Assert.Same(original, root.CompletedStructure);
        Assert.NotSame(original, copy.CompletedStructure);
    }

    [Theory]
    [InlineData("Lib={public K=p+1\n0}\nA=Lib\nReader={open A\nK}")]
    [InlineData("Lib={public K=p+1\n0}\nA=Lib\nReader={A.K}")]
    [InlineData("Lib={public Sub={public K=p+1\n0}\n0}\nA=Lib\nReader={open A.Sub\nK}")]
    [InlineData("Lib={public K=p+1\n0}\nA=Lib\nReader={Nested={open A\nK}\nNested}")]
    public void PublishedNamespaceSelectionsPreserveCapturedRequirements(string definitions)
    {
        var compiled = FrontEndPipeline.Process("Owner(p)={" + definitions + "\n0}\nOwner(1)");
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        var owner = compiled.ElaboratedRoot.Properties.Single(p => p.Name == "Owner").Value;
        var reader = owner.Properties.Single(p => p.Name == "Reader");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, reader.Exposure);
        Assert.Equal(new[] { "p" }, reader.RequiredAncestorParameters);
    }

    private const string OpenReference = "open Lib\nLib={public N={public K=7\n0}\n0}\nA=N\n";

    [Fact]
    public void PublishedRequirementsDoNotExportABranchsSuppliedBinder()
    {
        const string source = "Outer(q)={F(p)={open A\nLib={public K=p+1\n0}\nA=Lib\nK}\nF(0)=0\nReader={F(1)}\n0}\nOuter(9)";
        var compiled = FrontEndPipeline.Process(source);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        var outer = compiled.ElaboratedRoot.Properties.Single(p => p.Name == "Outer").Value;
        Assert.All(outer.Properties, p => Assert.Empty(p.RequiredAncestorParameters));
    }

    [Fact]
    public void PublishedAliasRequirementsKeepTheActualOwnerAcrossShadowing()
    {
        const string source = "Outer(p)={Lib={public K=p+1\n0}\nInner(p)={A=Lib\nReader={A.K}\n0}\n0}\nOuter(1)";
        var compiled = FrontEndPipeline.Process(source);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        var outer = compiled.ElaboratedRoot.Properties.Single(p => p.Name == "Outer").Value;
        var inner = outer.Properties.Single(p => p.Name == "Inner").Value;
        var reader = inner.Properties.Single(p => p.Name == "Reader");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, reader.Exposure);
        Assert.Equal(new[] { "p" }, reader.RequiredAncestorParameters);
        Assert.Equal(new[] { 1 }, reader.CaptureRequirements!.Select(r => r.OwnerDepth));
    }

    private static (Algorithm Root, StaticStructureOperation Operation, ModuleUnits Modules, DiagnosticBag Diagnostics)
        Resolve(Algorithm raw, FrontEndTraversalObservations? observations = null, CancellationToken cancellationToken = default)
    {
        var (operation, _) = StaticStructureAdmission.Create(raw, cancellationToken: cancellationToken);
        var diagnostics = new DiagnosticBag();
        var modules = new ModuleUnits();
        var detectedInput = ParameterDetector.DetectPrevalidated(raw, observations: observations, diagnostics: diagnostics,
            modules: modules, structuralOperation: operation);
        var (detected, _) = detectedInput;
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations, diagnostics, modules: modules, structuralOperation: operation);
        return (resolved, operation, modules, diagnostics);
    }

    private static ElaboratedPropertyScope Scope(Algorithm root, FrontEndTraversalObservations? observations = null)
    {
        var graph = root.CompletedStructure!.Facts;
        var prelude = ElaboratedScopeLookup.CreateScope(graph.Prelude, observations: observations,
            memberIndexes: new OpenMemberIndexCache(observations), completedContext: graph.Context(graph.PreludeKey));
        return ElaboratedScopeLookup.CreateScope(root, prelude);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ReceiverSuccessDoesNotProveOpenEligibility(bool openAlias)
    {
        var compiled = FrontEndPipeline.Process(openAlias
            ? OpenReference.Replace("open Lib\n", "open Lib, A\n", StringComparison.Ordinal) + "K"
            : OpenReference + "A.K");
        Assert.Equal(openAlias, compiled.HasErrors);
        if (openAlias) Assert.Contains(compiled.Diagnostics, d => d.Code == DiagnosticCode.UnresolvedOpenTarget);
        var root = compiled.ElaboratedRoot;
        var graph = root.CompletedStructure!.Facts;
        var alias = root.Properties.Single(p => p.Name == "A").Value;
        var key = graph.Child(root.CompletedStructure.Entry!, alias)!;
        var facts = graph.Facts(key)!;
        Assert.Equal(StaticFactKind.Structure, facts.Receiver.Kind);
        Assert.Equal(StaticFactKind.Missing, facts.Open.Kind);
        Assert.True(graph.IsSealed);
        var scope = Scope(root);
        var selected = ElaboratedScopeLookup.StaticStructureWithScopeAt(alias, scope);
        Assert.NotNull(selected);
        var lib = root.Properties.Single(p => p.Name == "Lib").Value;
        Assert.Same(lib.Properties.Single(p => p.Name == "N").Value, selected.Value.Structure);
        if (!openAlias)
        {
            var value = Evaluator.RunFlat(new Expr.AlgorithmExpr(root));
            Assert.False(value.IsError, value.IsError ? value.Error.ToString() : "");
            Assert.Equal(new[] { (Decimal128)7 }, value.Value);
        }
    }

    [Fact]
    public void ProviderIdentityAndEndpointViewsSurviveExposure()
    {
        const string source = "open A, B\nLib={public K=7\n0}\nA=Lib\nB=Lib\nK";
        var compiled = FrontEndPipeline.Process(source);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        var scope = Scope(compiled.ElaboratedRoot);
        var provider = Assert.Single(scope.GetResolvedOpenProviders());
        Assert.Same(compiled.ElaboratedRoot.Properties.Single(p => p.Name == "Lib").Value, provider.Target);
        var first = ElaboratedScopeLookup.ResolveOpenProvider(scope, scope.Opens[0]);
        var second = ElaboratedScopeLookup.ResolveOpenProvider(scope, scope.Opens[1]);
        Assert.NotNull(first);
        Assert.NotNull(second);
        Assert.Equal(first.Value.Identity, second.Value.Identity);
    }

    [Theory]
    [InlineData("open Lib.Hidden\nLib={Hidden={public K=7\n0}\n0}\n0", "not public")]
    [InlineData("open F.Hidden\nF(0)={public Hidden=1\n0}\nF(x)=0\n0", "conditional branch")]
    public void RecoveryDiagnosticsUseTheSamePublishedOpenBoundary(string source, string reason)
    {
        var previous = FrontEndPipeline.Process(source);
        var candidate = FrontEndPipeline.Process(source);
        Assert.True(candidate.HasErrors);
        Assert.Equal(previous.Diagnostics.Select(d => (d.Code, d.Message, d.Span)), candidate.Diagnostics.Select(d => (d.Code, d.Message, d.Span)));
        Assert.Contains(candidate.Diagnostics, d => d.Code == DiagnosticCode.UnresolvedOpenTarget && d.Message.Contains(reason, StringComparison.Ordinal));
        Assert.NotNull(SemanticModelBuilder.Build(candidate.ToParseResult(null)));
    }

    [Theory]
    [InlineData("editor")]
    [InlineData("exposure")]
    [InlineData("validator")]
    [InlineData("provenance")]
    public void EveryPostResolutionConsumerReadsCompletedFactsWithoutRawChasing(string consumer)
    {
        const string source = "open A\nLib={public K=7\n0}\nA=Lib\nF=A.Absent\nK";
        var observations = new FrontEndTraversalObservations();
        var processed = Resolve(SourceProvenance.ParseSyntaxValidRoot(source), observations);
        Assert.Empty(processed.Diagnostics);
        var beforeReads = observations.CompletedStaticStructureReads;
        switch (consumer)
        {
            case "editor": SemanticModelBuilder.Build(processed.Root, observations); break;
            case "exposure": PropertyExposureResolver.Resolve(processed.Root, observations, modules: processed.Modules); break;
            case "validator": OpenProviderValidator.Validate(processed.Root, processed.Diagnostics, hostOperations: null, observations); break;
            case "provenance": new DotMemberProvenanceFinalizer(Scope(processed.Root, observations)) { TraversalObservations = observations }.VisitAlgorithm(processed.Root); break;
        }
        Assert.True(observations.CompletedStaticStructureReads > beforeReads, consumer);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SharedBranchBodiesKeepDistinctPatternPublicationContexts(bool binders)
    {
        var raw = Assert.IsType<Algorithm.User>(SourceProvenance.ParseSyntaxValidRoot("Lib={public K=7\n0}\n0"));
        var body = SourceProvenance.ParseSyntaxValidRoot("open Lib\nK");
        Pattern first = binders ? new Pattern.Bind("x") : new Pattern.LitInt(0);
        Pattern second = binders ? new Pattern.Bind("y") : new Pattern.LitInt(1);
        var family = new Algorithm.Conditional(null, [], [new(first, body), new(second, body)]);
        raw = raw with { Properties = [..raw.Properties, new Property("F", family)] };
        var processed = Resolve(raw);
        Assert.Empty(processed.Diagnostics);
        var exposed = PropertyExposureResolver.Resolve(processed.Root, observations: null, modules: processed.Modules);
        var graph = exposed.CompletedStructure!.Facts;
        var exposedFamily = Assert.IsType<Algorithm.Conditional>(exposed.Properties.Single(p => p.Name == "F").Value);
        var a = graph.Child(exposed.CompletedStructure!.Entry!, exposedFamily.Branches[0].Body, first)!;
        var b = graph.Child(exposed.CompletedStructure!.Entry!, exposedFamily.Branches[1].Body, second)!;
        Assert.NotSame(a, b);
        Assert.NotNull(graph.Facts(a)?.Body);
        Assert.NotNull(graph.Facts(b)?.Body);
        Assert.Same(exposedFamily.Branches[0].Body, graph.Facts(a)!.Body);
        Assert.Same(exposedFamily.Branches[1].Body, graph.Facts(b)!.Body);
        var observations = new FrontEndTraversalObservations();
        Assert.NotNull(SemanticModelBuilder.Build(exposed, observations));
    }

    [Fact]
    public void CompletedInspectionIsIndependentOfTheProducingOperationsToken()
    {
        using var source = new CancellationTokenSource();
        var processed = Resolve(SourceProvenance.ParseSyntaxValidRoot(OpenReference + "A.K"), cancellationToken: source.Token);
        var exposed = PropertyExposureResolver.Resolve(processed.Root, observations: null, modules: processed.Modules);
        source.Cancel();
        Assert.Throws<OperationCanceledException>(() => processed.Operation.Queries.EnsureUsable());
        var observations = new FrontEndTraversalObservations();
        Assert.NotNull(SemanticModelBuilder.Build(exposed, observations));
        Assert.True(observations.CompletedStaticStructureReads > 0);
    }

    [Fact]
    public void RetainedLookupScopesObserveTheFinalExposureViews()
    {
        const string source = "Owner(p)={open A\nLib={public K=p+1\n0}\nA=Lib\nReader={open A\nK}\n0}\nOwner(1)";
        var processed = Resolve(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(processed.Diagnostics);
        var rootScope = Scope(processed.Root);
        var owner = processed.Root.Properties.Single(p => p.Name == "Owner").Value;
        var ownerScope = ElaboratedScopeLookup.CreateScope(owner, rootScope);
        var reader = owner.Properties.Single(p => p.Name == "Reader").Value;
        var readerScope = ElaboratedScopeLookup.CreateScope(reader, ownerScope);
        _ = readerScope.GetResolvedOpenProviders();
        var exposed = PropertyExposureResolver.Resolve(processed.Root, observations: null, modules: processed.Modules);
        var finalOwner = exposed.Properties.Single(p => p.Name == "Owner").Value;
        var finalLib = finalOwner.Properties.Single(p => p.Name == "Lib").Value;
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, finalLib.Properties.Single(p => p.Name == "K").Exposure);
        Assert.Same(finalLib, Assert.Single(readerScope.GetResolvedOpenProviders()).Target);
        Assert.Same(finalLib, ownerScope.TryLookupOwnProperty("Lib")!.Value.Property.Value);
    }

    [Fact]
    public void ChainedSelectionConsumesPublishedMemberIdentities()
    {
        const string source = "Lib={public Sub={public V=9\n0}\n0}\nA=Lib\nA.Sub.V";
        var compiled = FrontEndPipeline.Process(source);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        var root = compiled.ElaboratedRoot;
        var selected = ElaboratedScopeLookup.CompletedReceiver(root.Output[0], Scope(root));
        Assert.Equal(StaticStructuralMemberProviderKind.KnownAlgorithm, selected.Kind);
        var lib = root.Properties.Single(p => p.Name == "Lib").Value;
        var sub = lib.Properties.Single(p => p.Name == "Sub").Value;
        Assert.Same(sub.Properties.Single(p => p.Name == "V").Value, selected.Algorithm);
        var graph = root.CompletedStructure!.Facts;
        var libKey = graph.Child(root.CompletedStructure.Entry!, lib)!;
        var subKey = graph.Member(libKey, "Sub")!;
        Assert.Same(graph.Member(subKey, "V"), selected.Scope!.BodyKey);
    }

    [Fact]
    public void AForeignCompletedRootKeepsItsOwnOpenContext()
    {
        var first = FrontEndPipeline.Process("public K=7\n0");
        var second = FrontEndPipeline.Process("0");
        var observations = new FrontEndTraversalObservations();
        var scope = Scope(second.ElaboratedRoot, observations);
        var selected = ElaboratedScopeLookup.ResolveOpenProvider(scope, new Expr.AlgorithmExpr(first.ElaboratedRoot));
        Assert.NotNull(selected);
        Assert.Same(first.ElaboratedRoot, selected.Value.Target);
        Assert.True(observations.CompletedStaticStructureReads > 0);
    }

    [Fact]
    public void ExposureRetargetingVisitsSharedExpressionsByContextRatherThanByPath()
    {
        const int depth = 24;
        Expr expression = new Expr.Num(1);
        for (var i = 0; i < depth; i++) expression = new Expr.Binary(BinaryOp.Add, expression, expression);
        var raw = Assert.IsType<Algorithm.User>(SourceProvenance.ParseSyntaxValidRoot("0")) with
        { Output = OutputBundle.From([expression]) };
        var processed = Resolve(raw);
        Assert.Empty(processed.Diagnostics);
        var exposed = PropertyExposureResolver.Resolve(processed.Root, observations: null, modules: processed.Modules);
        var graph = exposed.CompletedStructure!.Facts;
        Assert.InRange(graph.RetargetNodeVisits, depth, 4 * depth);
        Assert.True(graph.IsSealed);
    }

    [Fact]
    public void CancelledExposureCannotSealOrShareItsPublication()
    {
        var processed = Resolve(SourceProvenance.ParseSyntaxValidRoot(OpenReference + "A.K"));
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var error = Assert.Throws<OperationCanceledException>(() => PropertyExposureResolver.Resolve(processed.Root,
            observations: null, modules: processed.Modules, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        var graph = processed.Root.CompletedStructure!.Facts;
        Assert.True(graph.IsFailed);
        Assert.False(graph.IsSealed);
        Assert.Throws<InvalidOperationException>(() => processed.Operation.Freeze());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task DeferredPublicationIsSharedOnlyAfterACompleteSuccessfulUnit(bool invalidModule)
    {
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = async (_, token) =>
            {
                Interlocked.Increment(ref downloads);
                await Task.Yield();
                token.ThrowIfCancellationRequested();
                return invalidModule ? "open Missing\npublic V=42\n0" : "public V=42\n0";
            },
        };
        const string source = "F(0)=0\nF(n)={open 'https://mods.test/a.kat'\nV}\nF(1)";
        var compiled = await FrontEndPipeline.ProcessAsync(source, options);
        Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(d => d.Message)));
        Assert.Equal(0, downloads);
        Assert.NotNull(SemanticModelBuilder.Build(compiled.ToParseResult(null)));
        Assert.Equal(0, downloads);
        var family = Assert.IsType<Algorithm.Conditional>(compiled.ElaboratedRoot.Properties.Single(p => p.Name == "F").Value);
        var registry = family.Branches[1].Body.DeferredRegion!.Structure!.Registry;
        var previous = registry.StructuralContinuation;
        var values = await Task.WhenAll(Enumerable.Range(0, 2).Select(_ => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(compiled.ElaboratedRoot))));
        Assert.Equal(1, downloads);
        Assert.All(values, result => Assert.Equal(invalidModule, result.IsError));
        if (invalidModule) Assert.Same(previous, registry.StructuralContinuation);
        else
        {
            Assert.NotSame(previous, registry.StructuralContinuation);
            Assert.All(values, result => Assert.Equal(new[] { (Decimal128)42 }, result.Value));
        }
        Assert.NotNull(SemanticModelBuilder.Build(compiled.ToParseResult(null)));
        Assert.Equal(1, downloads);
    }

    [Fact]
    public void ParameterizedProviderRefusalSurvivesCompletedPublication()
    {
        const string source = "open Lib\nLib(x)={public K=7\n0}\n0";
        var candidate = FrontEndPipeline.Process(source);
        var previous = FrontEndPipeline.Process(source);
        Assert.True(candidate.HasErrors);
        Assert.Contains(candidate.Diagnostics, d => d.Code == DiagnosticCode.IllegalInOpen);
        Assert.Equal(previous.Diagnostics.Select(d => (d.Code, d.Message, d.Span)), candidate.Diagnostics.Select(d => (d.Code, d.Message, d.Span)));
    }

    [Fact]
    public void PendingAliasCellsAreNotCompletedLookupFacts()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("A=Lib\nLib={public K=7\n0}\n0");
        var (operation, _) = StaticStructureAdmission.Create(raw);
        var body = Assert.IsType<Algorithm.User>(raw.Properties.Single(p => p.Name == "A").Value);
        var lib = raw.Properties.Single(p => p.Name == "Lib").Value;
        var alias = new Algorithm.Alias(body, body.Output[0]) { ResolvedStructureCell = AliasStructureCell.PendingOn(lib) };
        var a = operation.ContextOf(operation.Root, body);
        var l = operation.ContextOf(operation.Root, lib);
        operation.Publish(operation.Root, StaticPublicationStage.Detected, raw);
        operation.Publish(a, StaticPublicationStage.Detected, body);
        operation.Publish(l, StaticPublicationStage.Detected, lib);
        operation.Publish(a, StaticPublicationStage.Resolved, alias);
        operation.Publish(l, StaticPublicationStage.Resolved, lib);
        var resolved = raw with { Properties = raw.Properties.Select(p => p.Name == "A" ? p with { Value = alias } : p).ToArray() };
        operation.Publish(operation.Root, StaticPublicationStage.Resolved, resolved);
        operation.CompleteLookups(resolved);
        var facts = resolved.CompletedStructure!.Facts.Facts(a)!;
        Assert.Null(facts.Body);
        Assert.Equal(StaticFactKind.Unknown, facts.Receiver.Kind);
        Assert.Equal(StaticFactKind.Unknown, facts.Open.Kind);
    }

    [Fact]
    public void A1RecoveryInspectionDoesNotReactivateInference()
    {
        var compiled = FrontEndPipeline.Process(StaticStructureWitnessSources.Cases["A.3.1"]);
        Assert.True(compiled.HasErrors);
        Assert.Contains(compiled.Diagnostics, d => d.Code == DiagnosticCode.SelfDependentInferredParameters);
        var publication = compiled.ElaboratedRoot.CompletedStructure!;
        Assert.Null(publication.Facts.Facts(publication.Entry!)!.Body);
        var observations = new FrontEndTraversalObservations();
        Assert.NotNull(SemanticModelBuilder.Build(compiled.ToParseResult(null), observations));
    }
}
