using KatLang.Evaluation.Caching;
using KatLang.Tests.LanguageSpec;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

public class DifferentialObservationTests
{
    [Fact]
    public void PayloadChangesCannotHideBehindTheSameCategory()
    {
        EvalError expected = new EvalError.ArityMismatch(2, 1);
        foreach (var mutant in new EvalError[] { new EvalError.ArityMismatch(1, 1), new EvalError.ArityMismatch(2, 2), new EvalError.BadArity() })
        {
            Assert.Equal(SemanticExplorerHarness.ErrorCategory(expected), SemanticExplorerHarness.ErrorCategory(mutant));
            Assert.Throws<InvalidOperationException>(() => DifferentialErrors.RequireAgreement("mutant", expected, mutant));
        }
        DifferentialErrors.RequireAgreement("variadic", expected, new EvalError.VariadicArityMismatch("F", 2, 1));
        Assert.Throws<InvalidOperationException>(() => DifferentialErrors.RequireAgreement("branch",
            new EvalError.BranchArityMismatch("F", 2, 1), new EvalError.BranchOutputArityMismatch("F", 2, 1)));
    }

    [Fact]
    public void EveryErrorConstructorHasAnExplicitReviewedPolicy()
    {
        // Independent inventory, including C#-only host variants. Adding a new variant requires review.
        var contracts = DifferentialErrorContracts.All;
        Assert.Equal(28, contracts.Count);
        var hostNames = new[] { "EvaluationDepthExceeded", "EvaluationStepLimitExceeded", "EvaluationStackExhausted",
            "CollectionSizeLimitExceeded", "MaterializationLimitExceeded", "StringSizeLimitExceeded", "StringMaterializationLimitExceeded",
            "DisplayLengthLimitExceeded", "AstDepthLimitExceeded", "AstCycleDetected", "ModuleRegionMaterializationFailed" };
        // Internal markers that are never a run outcome (META-S3-0b's non-initiating observation).
        var internalNames = new[] { "ObservationPending" };
        var variants = typeof(EvalError).GetNestedTypes(System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.NonPublic)
            .Where(t => t.BaseType == typeof(EvalError)).ToArray();
        var expectedNames = contracts.Select(c => c.Error.GetType().Name).Distinct().Concat(hostNames).Concat(internalNames).Order().ToArray();
        Assert.Equal(expectedNames, variants.Select(t => t.Name).Order());
        foreach (var contract in contracts)
        {
            var observation = DifferentialErrors.Observe(contract.Error);
            Assert.Equal(contract.Policy, observation.Comparison);
            Assert.Equal(contract.Expected, observation.Payload);
            Assert.Equal(observation, DifferentialErrors.Observe(new EvalError.WithContext("ignored", contract.Error)));
        }
        foreach (var name in hostNames)
        {
            var error = (EvalError)System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(variants.Single(t => t.Name == name));
            Assert.Equal(ErrorComparison.HostOnly, DifferentialErrors.Observe(error).Comparison);
            Assert.Null(DifferentialErrors.Observe(error).Payload);
        }
        Assert.Throws<System.Diagnostics.UnreachableException>(() => DifferentialErrors.Observe(EvalError.ObservationPending.Instance));
        Assert.Throws<System.Diagnostics.UnreachableException>(() => EvalError.ObservationPending.Instance.Code);
        // The Lean switches are exhaustive (no wildcard); every new Lean constructor must be classified too.
        var lean = File.ReadAllText(Path.Combine(RepoRoot.Find(), "lean/KatLang.lean"));
        var taxonomy = lean[lean.IndexOf("inductive Error where", StringComparison.Ordinal)..];
        taxonomy = taxonomy[..taxonomy.IndexOf("deriving Repr", StringComparison.Ordinal)];
        var constructors = System.Text.RegularExpressions.Regex.Matches(taxonomy, @"(?m)^  \| (\w+)").Select(m => m.Groups[1].Value).ToArray();
        Assert.Equal(25, constructors.Length);
        foreach (var name in constructors)
            Assert.Contains("| ." + name, LeanObsTemplate.SharedDefinitions, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("F(x, y) = x + y\nF(1)", "err", 2, 1)]
    [InlineData("1 / 0", "err", -1, -1)]
    [InlineData("A = 1", "err", -1, -1)]
    [InlineData("F(x) = x\nF(", "parseError", -1, -1)]
    public void FailureObservationAlwaysExecutesThePublicEngine(string source, string outcome, int expected, int actual)
    {
        var calls = 0;
        var observation = SemanticExplorerHarness.Observe("public-coverage", source, text => { calls++; return KatLangEngine.Run(text); });
        Assert.Equal(1, calls);
        Assert.Equal(outcome, observation.Outcome);
        if (expected >= 0) Assert.Equal(new SharedErrorPayload("arity", [], [expected, actual]), observation.ErrorPayload);
    }

    [Fact]
    public void WrongPublicPhaseCategoryOrPayloadIsRejected()
    {
        var source = "F(x, y) = x + y\nF(1)";
        var root = SourceProvenance.ParseValid(source).Root;
        var diagnostic = KatLangError.FromEvalError(new EvalError.ArityMismatch(2, 1));
        var success = KatLangEngine.Run("1");
        var mutants = new RunResult[] {
            new RunResult.ParseFailure([diagnostic]), new RunResult.NoProgramOutput(root, diagnostic), success,
            new RunResult.EvalFailure(root, [KatLangError.FromEvalError(new EvalError.DivByZero())]),
            new RunResult.EvalFailure(root, [KatLangError.FromEvalError(new EvalError.ArityMismatch(1, 1))]) };
        foreach (var mutant in mutants)
            Assert.Throws<InvalidOperationException>(() => SemanticExplorerHarness.Observe("public-mutant", source, _ => mutant));
        var invalidSource = "F(x) = x\nF(";
        foreach (var mutant in mutants.Where(r => r is not RunResult.ParseFailure))
            Assert.Throws<InvalidOperationException>(() => SemanticExplorerHarness.Observe("parse-mutant", invalidSource, _ => mutant));
        Assert.Throws<InvalidOperationException>(() => SemanticExplorerHarness.Observe("parse-diagnostic-mutant", invalidSource,
            _ => new RunResult.ParseFailure([diagnostic])));
        // A source-less front-end failure must also report exactly the parser's error codes, in order.
        var rejected = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(invalidSource));
        Assert.Equal("parseError", SemanticExplorerHarness.Observe("parse-control", invalidSource, _ => rejected).Outcome);
        var wrongCode = KatLangError.FromDiagnostic(new Diagnostic("wrong", DiagnosticSeverity.Error, null) { Code = DiagnosticCode.UnsupportedSemicolon });
        Assert.DoesNotContain(rejected.Errors, e => e.Code == wrongCode.Code);
        foreach (var errors in new KatLangError[][] { [wrongCode], [.. rejected.Errors, wrongCode], [] })
            Assert.Throws<InvalidOperationException>(() => SemanticExplorerHarness.Observe("parse-code-mutant", invalidSource,
                _ => new RunResult.ParseFailure(errors)));
        // Dynamic output absence inside a property is different from root output absence.
        Assert.IsType<RunResult.NoProgramOutput>(KatLangEngine.Run("A = 1"));
        Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("A = { X = 1 }\nA"));
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("F(x) = missing\nF(1)"));
    }

    [Fact]
    public async Task CanonicalPayloadsAgreeOnAllEvaluatorAndPublicRoutes()
    {
        var cases = LanguageSpecCorpus.AllCases().Where(c => c.ExpectedErrorPayload is not null).ToArray();
        Assert.Equal(new[] { "binding-failure-outranks-repeated-name-conflict", "decon-arity-over", "decon-arity-under",
            "fixed-call-preserves-boundaries", "fixed-empty-spread-zero-items", "need-closed-core-demand-is-runtime",
            "need-container-call-checks-cardinality-first", "need-selected-signature-payload", "need-variadic-minimum-payload",
            "need-wrong-arity-precedes-cell-demand" }, cases.Select(c => c.Id).Order());
        foreach (var c in cases)
        {
            var ast = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(c.Source).Root);
            var counted = Evaluator.RunCounted(ast);
            Assert.True(counted.IsError);
            Assert.Equal(c.ExpectedErrorPayload, DifferentialErrors.Observe(counted.Error).Payload);
            var plain = Evaluator.Run(ast);
            Assert.True(plain.IsError);
            DifferentialErrors.RequireAgreement(c.Id, counted.Error, plain.Error);
            foreach (var optimized in new[] { false, true })
            {
                var route = Evaluator.RunCountedObserved(ast, enableOptimizations: optimized).Result;
                Assert.True(route.IsError);
                DifferentialErrors.RequireAgreement(c.Id, counted.Error, route.Error);
            }
            var twin = await Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: new SuspendingAsyncZeroArgPropertyResultCache());
            Assert.True(twin.Result.IsError);
            DifferentialErrors.RequireAgreement(c.Id, counted.Error, twin.Result.Error);
            SemanticExplorerHarness.RequireEngineFailure(c.Id, counted.Error, KatLangEngine.Run(c.Source));
            SemanticExplorerHarness.RequireEngineFailure(c.Id, counted.Error, await KatLangEngine.RunAsync(c.Source));
        }
    }

    [Fact]
    public void SupplementaryGuardCoverageCannotDisappear()
    {
        var artifact = SemanticExplorerLeanArtifactTests.GenerateArtifact();
        var kinds = System.Text.RegularExpressions.Regex.Matches(artifact,
            "(?m)^#guard errorObs .*kind := \"([^\"]+)\"")
            .GroupBy(m => m.Groups[1].Value).ToDictionary(g => g.Key, g => g.Count());
        var minimums = new Dictionary<string, int> {
            ["arity"] = 180, ["index"] = 90, ["div0"] = 12, ["spreadMissingOutput"] = 5,
            ["ambiguousOpen"] = 3, ["badArity"] = 3, ["missingOutput"] = 2,
            ["localOnlyProperty"] = 1, ["unresolvedImplicitParams"] = 1 };
        foreach (var (kind, minimum) in minimums)
            Assert.True(kinds.GetValueOrDefault(kind) >= minimum, $"Supplementary {kind} guards shrank below {minimum}.");
        var canonical = LanguageSpecArtifactsTests.GenerateArtifact();
        Assert.Equal(10, canonical.Split('\n').Count(l => l.StartsWith("#guard errorObs ", StringComparison.Ordinal)));
    }
}
