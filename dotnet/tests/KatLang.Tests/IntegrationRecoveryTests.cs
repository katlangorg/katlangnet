using KatLang.Semantics;

namespace KatLang.Tests;

public sealed class IntegrationRecoveryTests
{
    [Theory]
    [InlineData("Math.Sqrt(9)", "Sqrt", true)]
    [InlineData("open Math\nSqrt(9)", "Sqrt", true)]
    [InlineData("A=Math\nA.Sqrt(9)", "Sqrt", true)]
    [InlineData("open A\nA=Math\nSqrt(9)", "Sqrt", true)]
    [InlineData("abs(-3)", "abs", true)]
    [InlineData("A=abs\nA(-3)", "A", false)]
    [InlineData("Math={public Sqrt(x)=x}\nMath.Sqrt(9)", "Sqrt", false)]
    [InlineData("open Math\nSqrt(x)=x\nSqrt(9)", "Sqrt", false)]
    [InlineData("1.string", "string", true)]
    public void AdmittedBuiltinIdentity_AgreesInOrdinaryAndRecoveryEditorTrees(string source, string name, bool builtin)
    {
        foreach (var recovery in new[] { false, true })
        {
            var parsed = recovery ? SourceProvenance.ParseAllowingDiagnostics(source + "\n@")
                : SourceProvenance.ParseValid(source);
            Assert.Equal(recovery, parsed.HasFrontEndErrors);
            var model = SemanticModelBuilder.Build(parsed.Parsed);
            var reference = Assert.Single(model.FindResolutions(name), site => site.Occurrence.Kind is OccurrenceKind.ResolveReference or OccurrenceKind.DotMemberReference);
            Assert.Equal(builtin ? IdentifierClassification.Builtin : IdentifierClassification.PropertyReference, reference.Classification);
            Assert.NotNull(reference.ResolvedProperty);
            Assert.Equal(builtin, reference.ResolvedDeclaration is null);
            if (builtin) Assert.Equal(PropertyShape.Builtin, reference.ResolvedProperty!.Shape);
            var math = Assert.Single(model.PreludeSymbols, symbol => symbol.Name == "Math");
            Assert.Contains(math.Members, member => member.Name == "Sqrt" && member.Classification == IdentifierClassification.Builtin);
        }
    }

    [Fact]
    public void MissingAuthoritativeMathStructure_RemainsConservative()
    {
        var root = SourceProvenance.ParseValid("Math.Sqrt(9)").Root;
        var publication = root.CompletedStructure!;
        var math = publication.Facts.Member(publication.Facts.PreludeKey, "Math")!;
        var copy = root with { };
        var facts = new CompletedStaticStructures(publication.Facts.PreludeKey);
        foreach (var key in publication.Facts.Scopes)
        {
            var body = publication.Facts.Facts(key)!;
            if (ReferenceEquals(key, math)) body = body with { Body = null,
                Receiver = CompletedStaticStructures.Selection.Unavailable, Open = CompletedStaticStructures.Selection.Unavailable };
            if (ReferenceEquals(key, publication.Entry)) body = body with { Body = copy };
            facts.Add(key, body);
        }
        facts.Seal();
        CompletedStaticStructures.Attach(copy, new(facts, publication.Entry));
        var model = SemanticModelBuilder.Build(copy);
        Assert.Empty(Assert.Single(model.PreludeSymbols, symbol => symbol.Name == "Math").Members);
        var reference = Assert.Single(model.FindResolutions("Sqrt"));
        Assert.NotEqual(IdentifierClassification.Builtin, reference.Classification);
        Assert.Null(reference.ResolvedDeclaration);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void UnregisteredChangedDefinition_IsRefusedBeforeAndAfterFreezing(bool frozen)
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("P=x+y\n0");
        var operation = StaticStructureAdmission.Create(raw).Operation;
        var body = Assert.IsType<Algorithm.User>(raw.Properties.Single().Value);
        var key = operation.ContextOf(operation.Root, body);
        operation.Publish(key, StaticPublicationStage.Detected, body);
        operation.Publish(key, StaticPublicationStage.Resolved, body);
        if (frozen)
        {
            operation.Publish(operation.Root, StaticPublicationStage.Detected, raw);
            operation.Publish(operation.Root, StaticPublicationStage.Resolved, raw);
            var outer = operation.Root;
            operation = operation.Freeze().Materialize(outer, SourceProvenance.ParseSyntaxValidRoot("0"),
                new Pattern.Bind("n"), new(1_000_000, 4, 200_000, 4_000_000));
        }
        Assert.Same(key, operation.ContextOf(key.Parent!, body));
        Assert.Throws<InvalidOperationException>(() => operation.ContextOf(key.Parent!, body with { Output = [] }));
        Assert.Same(body, operation.Published(key, StaticPublicationStage.Resolved));
        var changed = body with { Output = [] };
        var fresh = StaticStructureAdmission.Create(raw with { Properties = [raw.Properties.Single().WithValue(changed)] }).Operation;
        Assert.NotSame(key, fresh.ContextOf(fresh.Root, changed));
    }

    [Fact]
    public void CoherentlySuppliedCopiesAndRegisteredPassViews_KeepSeparateDefinitions()
    {
        var first = SourceProvenance.ParseSyntaxValidRoot("x+1");
        var second = first with { Output = [new Expr.Num(2)] };
        var raw = new Algorithm.User(null, [], [], [new Property("A", first), new Property("B", second)], []);
        var operation = StaticStructureAdmission.Create(raw).Operation;
        var a = operation.ContextOf(operation.Root, first);
        var b = operation.ContextOf(operation.Root, second);
        Assert.NotSame(a, b);
        Assert.Same(a.Declaration, b.Declaration);
        var view = first with { Output = [new Expr.Num(3)] };
        operation.RegisterView(a, view);
        Assert.Same(a, operation.ContextOf(operation.Root, view));
        Assert.Same(first, operation.SourceOf(a));
        Assert.Same(second, operation.SourceOf(b));
        Assert.NotSame(operation.ContextOf(operation.Root, first, new Pattern.Bind("x")),
            operation.ContextOf(operation.Root, first, new Pattern.Bind("y")));
    }

    [Fact]
    public void AnUnavailableRecoveryEntry_DoesNotCertifyAModifiedHostCopy()
    {
        var recovery = FrontEndPipeline.Process(StaticStructureWitnessSources.Cases["A.3.1"]);
        Assert.True(recovery.HasErrors);
        Assert.Contains(recovery.Diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.SelfDependentInferredParameters);
        var original = recovery.ElaboratedRoot;
        Assert.Null(original.CompletedStructure!.Facts.Facts(original.CompletedStructure.Entry!)!.Body);
        var copy = original with { Output = [] };
        Assert.Same(original.CompletedStructure.Facts, AnalyzedStaticStructures.ForBoundAst(original).Facts);
        Assert.NotSame(original.CompletedStructure.Facts, AnalyzedStaticStructures.ForBoundAst(copy).Facts);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public void SuppliedHostStages_KeepOwnerlessAncestorsAndBranchRegionsDistinct(int stage)
    {
        var lib = new Algorithm.User(null, [], [], [new Property("K", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]), IsPublic: true)], []);
        var hostA = new ScopeCtx(null, [], [new Property("Lib", lib)]);
        var hostB = new ScopeCtx(null, [], [new Property("Lib", lib)]);
        var body = new Algorithm.User(hostA, [], [new Expr.Resolve("Lib")], [], []);
        var a = ElaboratedScopeLookup.CreateScope(body, sourcePhase: (StaticAstPhase)stage);
        var b = ElaboratedScopeLookup.CreateScope(body with { Parent = hostB }, sourcePhase: (StaticAstPhase)stage);
        Assert.Single(a.GetResolvedOpenProviders());
        Assert.Single(b.GetResolvedOpenProviders());
        Assert.NotEqual(a.GetResolvedOpenProviders().Single().Identity, b.GetResolvedOpenProviders().Single().Identity);
        var shared = new Algorithm.User(null, [], [], [], []);
        var x = ElaboratedScopeLookup.CreateScope(shared, a, branchPattern: new Pattern.Bind("x"));
        var y = ElaboratedScopeLookup.CreateScope(shared, a, branchPattern: new Pattern.Bind("y"));
        Assert.NotSame(x.BoundLookupContext().Key, y.BoundLookupContext().Key);
        Assert.Contains("x", x.BoundLookupContext().Facts.Facts(x.BoundLookupContext().Key)!.Parameters);
        Assert.DoesNotContain("x", y.BoundLookupContext().Facts.Facts(y.BoundLookupContext().Key)!.Parameters);
    }

    [Fact]
    public void CoherentDistinctDefinitions_SurviveFreezeAndCannotBeRegisteredAsEachOthersViews()
    {
        var first = SourceProvenance.ParseSyntaxValidRoot("x+1");
        var second = first with { Output = [new Expr.Num(2)] };
        var root = new Algorithm.User(null, [], [], [new Property("A", first), new Property("B", second)], []);
        var operation = StaticStructureAdmission.Create(root).Operation;
        var a = operation.ContextOf(operation.Root, first);
        var b = operation.ContextOf(operation.Root, second);
        Assert.Throws<InvalidOperationException>(() => operation.RegisterView(a, second));
        Assert.Throws<InvalidOperationException>(() => operation.Publish(a, StaticPublicationStage.Detected, second));
        foreach (var (key, body) in new (StaticScopeKey, Algorithm)[] { (a, first), (b, second), (operation.Root, root) })
        {
            operation.Publish(key, StaticPublicationStage.Detected, body);
            operation.Publish(key, StaticPublicationStage.Resolved, body);
        }
        var outer = operation.Root;
        var fork = operation.Freeze().Materialize(outer, SourceProvenance.ParseSyntaxValidRoot("0"), new Pattern.Bind("n"),
            new(1_000_000, 4, 200_000, 4_000_000));
        Assert.Same(a, fork.ContextOf(outer, first));
        Assert.Same(b, fork.ContextOf(outer, second));
        Assert.Same(second, fork.Published(b, StaticPublicationStage.Resolved));
    }
}
