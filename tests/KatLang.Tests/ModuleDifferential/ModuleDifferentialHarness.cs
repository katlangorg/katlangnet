using System.Globalization;

namespace KatLang.Tests;

internal static class ModuleDifferentialHarness
{
    /// <summary>Check each C# channel against the fixture and return only the tree Lean can evaluate.</summary>
    internal static async Task<string?> CheckAsync(ModuleDifferentialCase fixture, bool reverseFiles = false)
    {
        var engineServer = ModuleDifferentialCorpus.Server(reverseFiles);
        var engine = await KatLangEngine.RunAsync(fixture.Source, engineServer.Options());
        CheckFetches(fixture.Fetches, engineServer);

        var parseServer = ModuleDifferentialCorpus.Server(reverseFiles);
        var parsed = await Parser.ParseAsync(fixture.Source, parseServer.Options());
        CheckFetches(fixture.ParseFetches ?? fixture.Fetches, parseServer);

        if (fixture.Diagnostic is { } code)
        {
            Assert.True(parsed.HasErrors, fixture.Id);
            var diagnostic = Assert.Single(parsed.Diagnostics);
            Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
            Assert.Equal(code, diagnostic.Code);
            Assert.Equal(fixture.Span, diagnostic.Span);
            SemanticExplorerHarness.RequireEngineParseFailure(fixture.Id, parsed, engine);
            var error = Assert.Single(Assert.IsType<RunResult.ParseFailure>(engine).Errors);
            Assert.Equal(fixture.Span, error.Span);
            return null;
        }

        Assert.Empty(parsed.Diagnostics);
        var tree = new Expr.AlgorithmExpr(parsed.Root);
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(tree, EvaluationLimits.MaxSupportedAstDepth,
            AstConsumerProfile.EvaluatorIterativeJoinSpines, out var facts));
        Assert.Equal(fixture.Exclusion == ModuleLeanExclusion.DeferredRegion, facts.HasDeferredModuleRegion);
        if (facts.HasDeferredModuleRegion)
        {
            // The selected branch fetches during execution. Lean has no deferred-region form, so the encoder's
            // modeled-domain boundary refuses the admitted tree as evaluator evidence (LeanEncodingDomain), before
            // the branch materializes and after it: the tree keeps the placeholder's provisional body.
            RequireEvidenceRefusal(parsed.Root);
            var success = Assert.IsType<RunResult.Success>(engine);
            Assert.Equal(fixture.Expected, Neutral(success.Value, success.EmittedCount));
            var plainAsync = await Evaluator.RunAsync(tree);
            Assert.False(plainAsync.IsError, fixture.Id);
            Assert.Equal(success.Value, plainAsync.Value, Result.ValueComparer);
            CheckFetches(fixture.Fetches, parseServer);
            RequireEvidenceRefusal(parsed.Root);

            var countedServer = ModuleDifferentialCorpus.Server(reverseFiles);
            var clean = await SourceProvenance.ParseValidAsync(fixture.Source, countedServer.Options());
            var (asyncCounted, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(clean.Root));
            Assert.False(asyncCounted.IsError, fixture.Id);
            Assert.Equal(fixture.Expected, Neutral(asyncCounted.Value.Value, asyncCounted.Value.EmittedCount));
            CheckFetches(fixture.Fetches, countedServer);
            return null;
        }

        var plain = Evaluator.Run(tree);
        var counted = Evaluator.RunCounted(tree);
        Assert.Equal(counted.IsError, plain.IsError);
        if (counted.IsError)
        {
            var observed = DifferentialErrors.Observe(counted.Error);
            Assert.Equal(fixture.Expected, $"err {observed.Category}");
            Assert.Equal(fixture.Payload, observed.Payload);
            DifferentialErrors.RequireAgreement(fixture.Id, counted.Error, plain.Error);
            SemanticExplorerHarness.RequireEngineFailure(fixture.Id, counted.Error, engine);
        }
        else
        {
            Assert.Equal(fixture.Expected, Neutral(counted.Value.Value, counted.Value.EmittedCount));
            Assert.Equal(counted.Value.Value, plain.Value, Result.ValueComparer);
            var success = Assert.IsType<RunResult.Success>(engine);
            Assert.Equal(counted.Value.Value, success.Value, Result.ValueComparer);
            Assert.Equal(counted.Value.EmittedCount, success.EmittedCount);
        }

        // An unsupported encoding fails the case. Only explicitly listed exclusions can omit a guard.
        return LeanAstEncoder.EncodeProgram(parsed.Root);
    }

    private static void RequireEvidenceRefusal(Algorithm root)
        => Assert.Equal(LeanAstEncoding.DeferredRegionRefusal,
            Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeProgram(root)).Message);

    private static string Neutral(Result value, int emittedCount)
        => $"ok raw={SemanticExplorerHarness.Neutral(value)} n={emittedCount.ToString(CultureInfo.InvariantCulture)}";

    private static void CheckFetches(string[] urls, ModuleRouteAgreement.Modules server)
    {
        Assert.Equal(urls.Order(StringComparer.Ordinal), server.Fetches.Keys.Order(StringComparer.Ordinal));
        Assert.All(server.Fetches.Values, count => Assert.Equal(1, count));
    }
}
