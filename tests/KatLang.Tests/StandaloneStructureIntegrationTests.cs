using KatLang.Semantics;
using KatLang.TestInfrastructure;
using System.Numerics;
using System.Runtime.CompilerServices;
using Xunit.Abstractions;

namespace KatLang.Tests;

public sealed class StandaloneStructureIntegrationTests(ITestOutputHelper output)
{
    [Theory]
    [InlineData("F=x+1\nF(41)", 42)]
    [InlineData("open A\nLib={public K=7\n0}\nA=Lib\nK", 7)]
    [InlineData("Lib={public K=7\n0}\nA=Lib\nA.K", 7)]
    [InlineData("Lib={public K=7\n0}\nA={C=Lib}.C\nA.K", 7)]
    public void StandaloneCompositionRetainsTheOriginalAdmission(string source, int expected)
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot(source);
        var detected = ParameterDetector.Detect(raw);
        Assert.Empty(detected.Diagnostics);
        Assert.Same(raw, detected.Operation!.SourceOf(detected.Operation.Root));
        var resolved = ImplicitArgumentResolver.Resolve(detected);
        Assert.Same(raw, detected.Operation.SourceOf(detected.Operation.Root));
        var exposed = PropertyExposureResolver.Resolve(resolved);
        Assert.NotNull(exposed.CompletedStructure);
        AssertValue(exposed, expected);
    }

    [Fact]
    public void MissingStaleAndMismatchedAdmissionsCannotReconstructDetection()
    {
        var first = ParameterDetector.Detect(SourceProvenance.ParseSyntaxValidRoot("F=x+1\nF(41)"));
        var second = ParameterDetector.Detect(SourceProvenance.ParseSyntaxValidRoot("0"));
        Assert.Throws<ArgumentNullException>(() => ImplicitArgumentResolver.ResolvePrevalidated(first.Root));
        Assert.Throws<ArgumentException>(() => ImplicitArgumentResolver.ResolvePrevalidated(first.Root, structuralOperation: second.Operation));
        var copied = Assert.IsType<Algorithm.User>(first.Root) with { Output = [new Expr.Num(0)] };
        Assert.Throws<ArgumentException>(() => ImplicitArgumentResolver.ResolvePrevalidated(copied, structuralOperation: first.Operation));
        _ = ImplicitArgumentResolver.Resolve(first);
        Assert.Throws<ArgumentException>(() => ImplicitArgumentResolver.Resolve(first));
    }

    [Fact]
    public void NameResolvedHostEntryDoesNotRunInference()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("F=x+1\n0");
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(raw, diagnostics: diagnostics);
        Assert.Empty(Assert.IsType<Algorithm.User>(resolved.Properties.Single().Value).Params);
        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.SelfDependentInferredParameters);
    }

    [Fact]
    public void BoundUserNamespaceDoesNotReformItsReferenceRow()
    {
        var library = new Algorithm.User(null, [], [], [new Property("K", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]))], [new Expr.Num(0)]);
        var user = new Algorithm.User(null, [], [], [], [new Expr.Resolve("Lib")]);
        var root = new Algorithm.User(null, [], [], [new Property("Lib", library), new Property("User", user)], [new Expr.Num(0)]);
        var facts = AnalyzedStaticStructures.ForBoundAst(root);
        var scope = ElaboratedScopeLookup.CreateScope(root, completedContext: facts);
        var selected = ElaboratedScopeLookup.CompletedReceiver(new Expr.Resolve("User"), scope);
        Assert.Same(user, selected.Algorithm);
        Assert.Empty(selected.Algorithm!.Properties);
        Assert.NotNull(SemanticModelBuilder.Build(root));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PendingAliasRecipesCannotProveCompletedNamespaceAbsence(bool dotted)
    {
        var library = new Algorithm.User(null, [], [], [new Property("K", new Algorithm.User(null, [], [], [], [new Expr.Num(7)])) { IsPublic = true }], [new Expr.Num(0)]);
        var source = new Algorithm.User(null, [], [], [], [new Expr.Resolve("Lib")]);
        var alias = new Algorithm.Alias(source, source.Output[0]) { ResolvedStructureCell = AliasStructureCell.PendingOn(library) };
        Expr target = dotted ? new Expr.DotCall(new Expr.Resolve("A"), "Sub", null) : new Expr.Resolve("A");
        var root = new Algorithm.User(null, [], [target], [new Property("Lib", library), new Property("A", alias)], [new Expr.Num(0)]);
        var operation = StaticStructureAdmission.Create(root, phase: StaticAstPhase.Resolved).Operation;
        var absence = operation.Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, operation.Root,
            StaticQueryProjection.OpenMemberAbsence, "Missing", node: root.Opens[0]));
        Assert.True(absence.IsUnknown);
        var facts = AnalyzedStaticStructures.ForAdmittedSource(operation.Context(operation.Root));
        var scope = ElaboratedScopeLookup.CreateScope(root, completedContext: facts);
        Assert.Null(ElaboratedScopeLookup.ResolveOpenTarget(scope, root.Opens[0]));
        Assert.Null(root.CompletedStructure);
    }

    [Fact]
    public void DistinctHostViewsKeepOneDeclarationAndTheirOwnMemberSelections()
    {
        var left = new Algorithm.User(null, [], [],
            [new Property("V", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]))], [new Expr.Num(0)]);
        var right = left with { Properties = [new Property("V", new Algorithm.User(null, [], [], [], [new Expr.Num(9)]))] };
        Assert.Same(left.Declaration, right.Declaration);
        var root = new Algorithm.User(null, [], [], [new Property("A", left), new Property("B", right)],
            [new Expr.DotCall(new Expr.Resolve("A"), "V", null), new Expr.DotCall(new Expr.Resolve("B"), "V", null)]);
        var context = AnalyzedStaticStructures.ForBoundAst(root);
        var scope = ElaboratedScopeLookup.CreateScope(root, completedContext: context);
        foreach (var (name, expected) in new[] { ("A", 7), ("B", 9) })
        {
            var receiver = ElaboratedScopeLookup.CompletedReceiver(new Expr.Resolve(name), scope);
            var member = Assert.Single(receiver.Algorithm!.Properties).Value;
            Assert.Equal((Decimal128)expected, Assert.IsType<Expr.Num>(member.Output.Single()).Value);
        }
        Assert.NotNull(SemanticModelBuilder.Build(root));
        var actual = Evaluator.RunFlat(new Expr.AlgorithmExpr(root));
        Assert.False(actual.IsError);
        Assert.Equal(new Decimal128[] { 7, 9 }, actual.Value);
    }

    [Theory]
    [InlineData(false, 7)]
    [InlineData(true, 9)]
    public void HostViewsOfOneProviderAreDeduplicatedInWrittenOpenOrder(bool reversed, int expected)
    {
        var first = new Algorithm.User(null, [], [],
            [new Property("V", new Algorithm.User(null, [], [], [], [new Expr.Num(7)])) { IsPublic = true }], [new Expr.Num(0)]);
        var second = first with { Properties = [new Property("V", new Algorithm.User(null, [], [], [], [new Expr.Num(9)])) { IsPublic = true }] };
        var opens = (reversed ? new[] { "B", "A" } : new[] { "A", "B" }).Select(name => (Expr)new Expr.Resolve(name)).ToArray();
        var raw = new Algorithm.User(null, [], opens, [new Property("A", first), new Property("B", second)], [new Expr.Resolve("V")]);
        var input = ParameterDetector.Detect(raw);
        Assert.Empty(input.Diagnostics);
        var root = PropertyExposureResolver.Resolve(ImplicitArgumentResolver.Resolve(input));
        AssertValue(root, expected);
        var context = AnalyzedStaticStructures.ForBoundAst(root);
        var scope = ElaboratedScopeLookup.CreateScope(root, completedContext: context);
        Assert.Single(scope.GetResolvedOpenProviders());
    }

    [Fact]
    public void ResolvedAndModifiedHostTreesUseCurrentViewsWithoutReclassifyingUserBodies()
    {
        var original = SourceProvenance.ParseValid("open A\nLib={public K=7\n0}\nA=Lib\nK").Root;
        AssertValue(PropertyExposureResolver.Resolve(original), 7);
        var user = Assert.IsType<Algorithm.User>(original);
        var libProperty = user.Properties.Single(property => property.Name == "Lib");
        var lib = Assert.IsType<Algorithm.User>(libProperty.Value);
        var changedLib = lib with { Properties = [lib.Properties.Single().WithValue(new Algorithm.User(null, [], [], [], [new Expr.Num(9)]))] };
        var changed = user with { Properties = user.Properties.Select(property => property.Name == "Lib" ? property.WithValue(changedLib) : property).ToArray() };
        var facts = AnalyzedStaticStructures.ForBoundAst(changed);
        Assert.IsType<AnalyzedStaticStructures>(facts.Facts);
        Assert.NotNull(SemanticModelBuilder.Build(changed));
        var exposed = PropertyExposureResolver.Resolve(changed);
        Assert.NotNull(exposed);
        AssertValue(exposed, 9);
        var scope = ElaboratedScopeLookup.CreateScope(changed, completedContext: facts);
        Assert.Equal(9, Assert.IsType<Expr.Num>(ElaboratedScopeLookup.ResolveOpenTarget(scope, changed.Opens.Single())!.Properties.Single().Value.Output.Single()).Value);
    }

    [Fact]
    public void StandaloneSummaryPreservesCapturedRequirementProvenance()
    {
        var detected = ParameterDetector.Detect(SourceProvenance.ParseSyntaxValidRoot("Outer(x)={Lib={public K=x\n0}\nA=Lib\nP={open A\nK}\n0}\n0"));
        var resolved = ImplicitArgumentResolver.Resolve(detected);
        var outer = resolved.Properties.Single().Value;
        var graph = PropertyDependencyGraphBuilder.BuildSummaries(outer);
        var exposed = PropertyExposureResolver.Resolve(resolved);
        var p = exposed.Properties.Single().Value.Properties.Single(property => property.Name == "P");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, p.Exposure);
        Assert.True(graph.TryGetPropertyIndex("P", out _));
    }

    [Fact]
    public void AnalysisCancellationAndResourceRefusalPublishNoCompletedProgram()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("Lib={public K=7\n0}\nA=Lib\nA.K");
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var operation = StaticStructureAdmission.Create(raw).Operation;
        var cancelled = Assert.Throws<OperationCanceledException>(() => AnalyzedStaticStructures.ForAdmittedSource(operation.Context(operation.Root), cancellation.Token));
        Assert.Equal(cancellation.Token, cancelled.CancellationToken);
        Assert.Null(raw.CompletedStructure);
        var limited = new StaticStructureOperation(raw, new(100, 4, 100, 100));
        Assert.Throws<StaticQueryLimitExceededException>(() => AnalyzedStaticStructures.ForAdmittedSource(limited.Context(limited.Root)));
        Assert.Null(raw.CompletedStructure);
    }

    [Fact]
    public void RetainedAnalysisHasNoProducerOperationOrToken()
    {
        var (context, operation, token) = RetainAnalysis();
        for (var i = 0; i < 4; i++) { GC.Collect(); GC.WaitForPendingFinalizers(); GC.Collect(); }
        Assert.False(operation.IsAlive);
        Assert.False(token.IsAlive);
        Assert.NotNull(context.Facts.Facts(context.Key)?.Body);
        GC.KeepAlive(context);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (CompletedStructureContext Context, WeakReference Operation, WeakReference Token) RetainAnalysis()
    {
        var token = new CancellationTokenSource();
        var operation = StaticStructureAdmission.Create(SourceProvenance.ParseSyntaxValidRoot("Lib={public K=7\n0}\nA=Lib\nA.K"), cancellationToken: token.Token).Operation;
        var result = AnalyzedStaticStructures.ForAdmittedSource(operation.Context(operation.Root));
        return (result, new(operation), new(token));
    }

    [Fact]
    public void LegacyExposureAuthoritiesArePhysicallyAbsent()
    {
        var root = RepoRoot.Find();
        var graph = File.ReadAllText(Path.Combine(root, "src/KatLang/PropertyDependencyGraph.cs"));
        var exposure = File.ReadAllText(Path.Combine(root, "src/KatLang/PropertyExposureResolver.cs"));
        foreach (var obsolete in new[] { "NormalizeOpenPath", "ChargePath(", "NavigateNode", "NodePath", "PathIdentity", "TryResolveLocalHeadCandidate", "ActiveLocalHeads", "ActiveLocalPaths" })
            Assert.DoesNotContain(obsolete, graph);
        Assert.DoesNotContain("private bool TryProvide(", exposure);
        Assert.DoesNotContain("PropertyDependencyGraphBuilder.ChargePath", exposure);
        var resolver = File.ReadAllText(Path.Combine(root, "src/KatLang/ImplicitArgumentResolver.cs"));
        Assert.DoesNotContain("public static Algorithm Resolve(Algorithm root)", resolver);
        Assert.DoesNotContain("WithResolution(", resolver);
    }

    [Theory]
    [InlineData("open A\nA={public K=7\n0}\nK +", 0)]
    [InlineData("open Missing\nA=1\nA", 1)]
    public void ErroneousEditorInputsKeepLocalFactsWithoutLoading(string source, int minimumDiagnostics)
    {
        var parsed = Parser.Parse(source);
        Assert.True(parsed.Diagnostics.Count >= minimumDiagnostics);
        Assert.NotNull(SemanticModelBuilder.Build(parsed));
        Assert.NotNull(PropertyDependencyGraphBuilder.BuildSummaries(parsed.Root));
    }

    [Fact]
    public void StandaloneWorkIsBoundedAndCompletedConsumersReuseThePublication()
    {
        StaticQueryStatistics previous = default;
        foreach (var width in new[] { 16, 32, 64 })
        {
            var source = string.Concat(Enumerable.Range(0, width).Select(i => $"A{i}=Lib\n"))
                + "Lib={public K=7\n0}\nA0.K";
            var raw = SourceProvenance.ParseSyntaxValidRoot(source);
            var admission = StaticStructureAdmission.Create(raw);
            var analyzed = AnalyzedStaticStructures.ForAdmittedSource(admission.Operation.Context(admission.Operation.Root));
            var stats = Assert.IsType<AnalyzedStaticStructures>(analyzed.Facts).Statistics;
            var input = ParameterDetector.DetectPrevalidated(raw, structuralOperation: admission.Operation);
            var resolved = ImplicitArgumentResolver.Resolve(input);
            var exposed = PropertyExposureResolver.Resolve(resolved);
            Assert.Same(exposed.CompletedStructure!.Facts, AnalyzedStaticStructures.ForBoundAst(exposed).Facts);
            output.WriteLine(System.Text.Json.JsonSerializer.Serialize(new { width, standalone = stats, common = admission.Operation.Queries.Statistics }));
            Assert.True(stats.Entries > 0 && stats.Reads > 0 && stats.AdapterWork > 0);
            Assert.True(stats.Entries <= admission.Measurement.Limits.MaxEntries);
            Assert.True(stats.StorageUnits <= admission.Measurement.Limits.MaxStorageUnits);
            if (previous.Entries > 0)
            {
                Assert.True(stats.Entries < previous.Entries * 3);
                Assert.True(stats.Reads < previous.Reads * 3);
                Assert.True(stats.AdapterWork < previous.AdapterWork * 3);
            }
            previous = stats;
        }
    }

    private static void AssertValue(Algorithm root, int expected)
    {
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(root));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { expected }, result.Value);
    }
}
