namespace KatLang.Tests;

/// <summary>Contracts over actual unified work, never adapters for the deleted chase counters.</summary>
internal static class HistoricalContractAssertions
{
    internal static void FinalInputs(DetectedProgram program, Algorithm.User body)
    {
        var operation = program.Operation!;
        var scope = operation.ContextOf(operation.Root, body);
        var before = operation.Queries.Statistics;
        var key = StaticQueryKey.Inputs(scope);
        var answer = operation.Read(key);
        Assert.Equal(StaticFactKind.Inputs, answer.Kind);
        Assert.Equal(body.Params, Assert.IsType<string[]>(answer.Data));
        foreach (var name in body.Params)
            Assert.Equal(StaticFactKind.Yes, operation.Read(StaticQueryKey.IsInput(scope, name)).Kind);
        for (var repeat = 0; repeat < 8; repeat++) Assert.Same(answer, operation.Read(key));
        // Detection already reached these equations. A completed read cannot start another solve.
        Assert.Equal(before.Computations, operation.Queries.Statistics.Computations);
        Assert.Equal(before.Evaluations, operation.Queries.Statistics.Evaluations);
    }

    internal static void InputWork(FrontEndTraversalObservations observations)
    {
        var equations = observations.StaticQueryEvaluations.Where(pair => pair.Key.Kind == StaticQueryKind.IsInput
            && pair.Key.Projection == StaticQueryProjection.Default).ToArray();
        Assert.NotEmpty(equations);
        // These controlled witnesses require at most four information-driven evaluations of an input.
        Assert.All(equations, pair => Assert.InRange(pair.Value, 1, 4));
        Assert.Contains(observations.StaticQueryAnswers, pair => pair.Key.Kind == StaticQueryKind.Inputs
            && pair.Value == StaticFactKind.Inputs);
    }

    internal static long InputIndexWork(string source)
    {
        var program = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(program.Diagnostics);
        var queries = program.Operation!.Queries;
        Assert.InRange(queries.InputGraphBuilds, 1, queries.SyntaxIndexBuilds);
        return queries.InputGraphNodeVisits;
    }

    internal static void CompletedProviders(string rows)
    {
        foreach (var reverse in new[] { false, true })
        {
            var declarations = "Lib = { public Visible=7\n public Shared=8\n Private=9\n0 }\nAlias=Lib\nOther={ public Shared=10\n0 }\n";
            var source = declarations + "H={\nopen " + (reverse ? "Other, Alias, Lib" : "Lib, Alias, Other")
                + "\nShared=5\n" + rows + "\n}\n1";
            var work = new FrontEndTraversalObservations();
            var program = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source), observations: work);
            Assert.Empty(program.Diagnostics);
            var resolved = ImplicitArgumentResolver.ResolvePrevalidated(program, work);
            var root = PropertyExposureResolver.Resolve(resolved);
            var facts = root.CompletedStructure!.Facts;
            var prelude = ElaboratedScopeLookup.CreateScope(facts.Prelude, completedContext: facts.Context(facts.PreludeKey));
            var read = new FrontEndTraversalObservations();
            var indexes = new OpenMemberIndexCache(read);
            var scope = ElaboratedScopeLookup.CreateScope(root, prelude, observations: read, memberIndexes: indexes);
            var h = root.Properties.Single(property => property.Name == "H").Value;
            scope = ElaboratedScopeLookup.CreateScope(h, scope);
            var expected = (reverse ? new[] { "Other", "Lib" } : new[] { "Lib", "Other" })
                .Select(name => root.Properties.Single(property => property.Name == name).Value).ToArray();
            Assert.True(work.StaticOpenTargetComputations > 0);
            Assert.True(work.StaticOpenIndexMemberVisits > 0);
            var before = program.Operation!.Queries.Statistics;
            for (var repeat = 0; repeat < 8; repeat++)
            {
                Assert.Equal(expected, scope.GetResolvedOpenProviders().Select(provider => provider.Target));
                var visible = ElaboratedScopeLookup.LookupSingleOpenMember(scope, "Visible");
                Assert.NotNull(visible);
                Assert.Same(expected.Single(body => body.Properties.Any(property => property.Name == "Visible"))
                    .Properties.Single(property => property.Name == "Visible"), visible.Value.Hit.Property);
                Assert.Null(ElaboratedScopeLookup.LookupSingleOpenMember(scope, "Private"));
                Assert.Null(ElaboratedScopeLookup.LookupSingleOpenMember(scope, "Shared"));
                var owned = ElaboratedScopeLookup.SelectOwnedDeclaration(scope, "Shared", ElaboratedScopeLookup.OwnParameterBindings.Instance);
                Assert.True(owned.TryGetProperty(out _, out var hit));
                Assert.Same(h.Properties.Single(property => property.Name == "Shared"), hit.Property);
            }
            Assert.True(read.CompletedStaticStructureReads > 0);
            Assert.Same(facts, scope.CompletedContext?.Facts);
            Assert.Equal(before.Computations, program.Operation.Queries.Statistics.Computations);
            var diagnostics = new DiagnosticBag();
            OpenProviderValidator.Validate(root, diagnostics, (HostOperations?)null, read);
            Assert.Empty(diagnostics);
        }
    }
}
