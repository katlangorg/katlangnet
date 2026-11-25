using System.Collections.Immutable;

namespace KatLang.Tests;

public sealed class WideDeconstructionPublicationTests
{
    private static string Wide(int count)
    {
        var names = string.Join(", ", Enumerable.Range(0, count).Select(i => $"x{i}"));
        return names + $" = range(1, {count})\nsum(({names}))";
    }

    [Theory]
    [InlineData(16)]
    [InlineData(64)]
    [InlineData(256)]
    public void RetargetingAbsentHelpers_DoesNotRebuildTheBodyCatalog(int count)
    {
        var root = SourceProvenance.ParseValid(Wide(count)).Root;
        var facts = root.CompletedStructure!.Facts;
        Assert.InRange(facts.BodyIndexBuilds, 0, 1);
        Assert.InRange(facts.BodyIndexScopeVisits, 0, facts.Count);
        Assert.InRange(facts.RetargetNodeVisits, count, 12 * count + 100);
        var targets = root.Properties.Where(property => property.Name.StartsWith('x')).ToArray();
        Assert.Equal(count, targets.Length);
        Assert.Equal(count, targets.Select(property => property.Value.Declaration).Distinct(ReferenceEqualityComparer.Instance).Count());
        var helpers = targets.Select(property => Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(
            Assert.IsType<Expr.Call>(Assert.Single(property.Value.Output)).Function).Algorithm)).ToArray();
        Assert.All(helpers, helper => Assert.Same(helpers[0].ParameterPatterns, helper.ParameterPatterns));
        Assert.Equal(count, helpers.Select(helper => helper.Declaration).Distinct(ReferenceEqualityComparer.Instance).Count());
        var builds = facts.BodyIndexBuilds;
        for (var i = 0; i < targets.Length; i++)
        {
            var owner = facts.Child(root.CompletedStructure.Entry!, targets[i].Value)!;
            Assert.Null(facts.Child(owner, helpers[i]));
        }
        Assert.Equal(builds, facts.BodyIndexBuilds);
        var observations = new EvaluationObservations();
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(root), observations: observations);
        Assert.True(result.IsOk);
        Assert.Equal((count * (count + 1) / 2).ToString(), SemanticExplorerHarness.Neutral(result.Value.Value));
        Assert.Equal(1, observations.DeconstructionFullBindCount);
    }

    private static Algorithm.User Empty() => new(null, [], [], [], []);
    private static CompletedStaticStructures.BodyFacts Body(StaticScopeKey key, Algorithm body)
        => new(body, new(StaticFactKind.Structure, key), new(StaticFactKind.Structure, key),
            new Dictionary<string, StaticScopeKey>(), new HashSet<string>(), ImmutableArray<CompletedStaticStructures.Selection>.Empty);

    [Fact]
    public void ParentAndPatternRegions_KeepSeparateChildIdentities()
    {
        var table = new StaticKeyTable();
        var graph = new CompletedStaticStructures(table.Root);
        var owner = new StaticScopeKey(table.Root, new object());
        var shared = Empty();
        var direct = new StaticScopeKey(table.Root, OpenProviderIdentity.DeclarationOf(shared));
        var nested = new StaticScopeKey(owner, OpenProviderIdentity.DeclarationOf(shared));
        var x = new Pattern.Bind("x");
        var y = new Pattern.Bind("y");
        var firstBranch = new StaticScopeKey(owner, OpenProviderIdentity.DeclarationOf(shared), x);
        var secondBranch = new StaticScopeKey(owner, OpenProviderIdentity.DeclarationOf(shared), y);
        foreach (var key in new[] { direct, nested, firstBranch, secondBranch }) graph.Add(key, Body(key, shared));
        Assert.Same(direct, graph.Child(table.Root, shared));
        Assert.Same(nested, graph.Child(owner, shared));
        Assert.Same(firstBranch, graph.Child(owner, shared, x));
        Assert.Same(secondBranch, graph.Child(owner, shared, y));
        Assert.Null(graph.Child(owner, shared, new Pattern.Bind("x")));
        Assert.Equal(0, graph.BodyIndexBuilds);
    }

    [Fact]
    public void AmbiguousDeclarations_StillSelectExactCurrentViews()
    {
        var table = new StaticKeyTable();
        var graph = new CompletedStaticStructures(table.Root);
        var first = Empty();
        var second = first with { Output = [new Expr.Num(2)] };
        var a = new StaticScopeKey(table.Root, OpenProviderIdentity.DeclarationOf(first));
        var b = new StaticScopeKey(table.Root, OpenProviderIdentity.DeclarationOf(second));
        graph.Add(a, Body(a, first));
        graph.Add(b, Body(b, second));
        Assert.Same(a, graph.Child(table.Root, first));
        Assert.Same(b, graph.Child(table.Root, second));
        var replacement = first with { Output = [new Expr.Num(3)] };
        graph.Retarget(a, replacement);
        Assert.Same(a, graph.Child(table.Root, replacement));
        Assert.Null(graph.Child(table.Root, first));
        Assert.Same(b, graph.Child(table.Root, second));
        Assert.Equal(2, graph.BodyIndexBuilds);
    }

    [Fact]
    public void AlternateOwnerIdentities_KeepExactViewsAcrossSealedExtensions()
    {
        var table = new StaticKeyTable();
        var budget = new StaticQueryResourceBudget(new(1000, 8, MaxStorageUnits: 1000));
        var graph = new CompletedStaticStructures(table.Root, resources: budget);
        var first = Empty();
        var second = first with { Output = [new Expr.Num(2)] };
        var a = new StaticScopeKey(table.Root, new object());
        var b = new StaticScopeKey(table.Root, new object());
        graph.Add(a, Body(a, first));
        graph.Add(b, Body(b, second));
        Assert.Equal(2, budget.MetadataUnits); // One exception entry for this declaration/parent/region.
        Assert.Same(a, graph.Child(table.Root, first));
        Assert.Same(b, graph.Child(table.Root, second));
        var replacement = first with { Output = [new Expr.Num(3)] };
        graph.Retarget(a, replacement);
        graph.Seal();
        var extension = new CompletedStaticStructures(table.Root, previous: graph);
        Assert.Same(a, extension.Child(table.Root, replacement));
        Assert.Same(b, extension.Child(table.Root, second));
        Assert.Null(extension.Child(new StaticScopeKey(table.Root, new object()), replacement));
    }

    [Fact]
    public void AlternateChildMetadata_RefusesAnInsufficientBudgetTerminally()
    {
        var root = new StaticKeyTable().Root;
        var graph = new CompletedStaticStructures(root,
            resources: new StaticQueryResourceBudget(new(1000, 8, MaxStorageUnits: 1)));
        var body = Empty();
        var key = new StaticScopeKey(root, new object());
        Assert.Throws<StaticQueryLimitExceededException>(() => graph.Add(key, Body(key, body)));
        Assert.True(graph.IsFailed);
        Assert.Throws<InvalidOperationException>(() => graph.Child(root, body));
    }

    [Theory]
    [InlineData("a,b=({open {public K=7}\nK+10},23)\na", "17")]
    [InlineData("Lib={public K=9\n0}\nAlias=Lib\na,b=({open Alias\nK},2)\na+b", "11")]
    [InlineData("a,*rest,z=[1,2,3,4]\na+rest.sum+z", "10")]
    [InlineData("a,b=((1,2),(3,4))\nx,y=a\nx+y+b.sum", "10")]
    [InlineData("F(seed)={a,b=(seed,seed*10)\na+b}\nF(1),F(2)", "S[11, 22]")]
    [InlineData("a,b,c=(1,2)\n5", "5")]
    public void SharedStorage_PreservesValueBoundariesAndWrittenOwners(string source, string expected)
    {
        _ = SourceProvenance.ParseValid(source);
        Assert.Equal(expected, SemanticExplorerHarness.Neutral(Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).Value));
    }

    [Theory]
    [InlineData("a,c,a", "S[S[10, 12, 10], S[20, 22, 20]]", 6)]
    [InlineData("c,a,b,c", "S[S[12, 10, 11, 12], S[22, 20, 21, 22]]", 6)]
    [InlineData("5", "S[5, 5]", 0)]
    public void HostEffects_AreSharedWithinAnActivationAndSeparateAcrossActivations(string rows, string expected, int calls)
    {
        var seen = new List<string>();
        var operations = HostOperations.Create(HostOperation.Create("emit", (arguments, _) =>
        {
            seen.Add(SemanticExplorerHarness.Neutral(arguments[0]));
            return arguments[0];
        }, "value"));
        var source = "F(seed)={a,b,c=(emit(seed),emit(seed+1),emit(seed+2))\n" + rows + "\n}\nF(10),F(20)";
        var options = new RunOptions { HostOperations = operations };
        var parsed = Parser.Parse(source, options);
        Assert.False(parsed.HasErrors, string.Join(';', parsed.Diagnostics));
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, options));
        Assert.Equal(expected, SemanticExplorerHarness.Neutral(result.Value));
        Assert.Equal(calls, seen.Count);
        if (calls != 0) Assert.Equal(new[] { "10", "11", "12", "20", "21", "22" }, seen);
        seen.Clear();
        var work = new EvaluationObservations();
        var observed = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), observations: work, hostOperations: operations).Result;
        Assert.True(observed.IsOk);
        Assert.Equal(SemanticExplorerHarness.Neutral(result.Value), SemanticExplorerHarness.Neutral(observed.Value.Value));
        Assert.Equal(calls == 0 ? 0 : 2, work.DeconstructionFullBindCount);
        Assert.Equal(calls, seen.Count);
    }

    [Fact]
    public void InvalidPatterns_KeepTheirCategoryAndWrittenPositions()
    {
        var syntax = Parser.ParseSyntax("a, b, a, c, b = range(1, 5)\na");
        Assert.Equal(new[] { DiagnosticCode.DuplicateProperty, DiagnosticCode.DuplicateProperty }, syntax.Diagnostics.Select(d => d.Code));
        Assert.Equal(new[] { new SourcePosition(1, 7), new SourcePosition(1, 13) }, syntax.Diagnostics.Select(d => Assert.NotNull(d.Span).Start));
        const string wrongArity = "x,y,z=(1,2)\nz";
        _ = SourceProvenance.ParseValid(wrongArity);
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(wrongArity));
        Assert.Equal(KatLangErrorCode.ArityMismatch, Assert.Single(failure.Errors).Code);
        Assert.Contains("Assignment pattern `x, y, z`", failure.ToDisplayString(), StringComparison.Ordinal);
    }

    [Fact]
    public void CancellationDuringRetargeting_CannotPublishASuccessfulUnit()
    {
        var detected = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(Wide(32)));
        Assert.Empty(detected.Diagnostics);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected);
        using var cancellation = new CancellationTokenSource();
        var work = new FrontEndTraversalObservations
        {
            StageObserver = (name, begin) => { if (name == "retarget-and-seal" && begin) cancellation.Cancel(); },
        };
        var error = Assert.Throws<OperationCanceledException>(() => PropertyExposureResolver.Resolve(resolved, work, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        var publication = Assert.IsType<CompletedStructurePublication>(resolved.CompletedStructure);
        Assert.True(publication.Facts.IsFailed);
        Assert.False(publication.Facts.IsSealed);
        Assert.Throws<InvalidOperationException>(() => publication.Facts.Child(publication.Entry!, resolved));
    }

    [Fact]
    public void CancellationInTheSharedRhs_DoesNotPublishAPartialSuccess()
    {
        using var cancellation = new CancellationTokenSource();
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.Create("emit", (arguments, _) =>
        {
            calls++;
            cancellation.Cancel();
            return arguments[0];
        }, "value"));
        const string source = "a,b=(emit(1),emit(2))\na+b";
        var options = new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token };
        var parsed = Parser.Parse(source, options);
        Assert.False(parsed.HasErrors);
        var error = Assert.Throws<OperationCanceledException>(() => KatLangEngine.Run(source, options));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(1, calls);
        var fresh = new RunOptions { HostOperations = HostOperations.Create(HostOperation.Create("emit", (arguments, _) => arguments[0], "value")) };
        Assert.Equal("3", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, fresh)).ToDisplayString());
    }
}
