using KatLang.Evaluation;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

public class SequencePreparationParityTests
{
    [Theory]
    [InlineData("range(1, 3).filter(D).count")]
    [InlineData("count(range(1, 3).filter(D))")]
    [InlineData("count(filter(range(1, 3), D))")]
    public void HostBuiltZeroParameterAlias_PreservesWrapperArity(string pipeline)
    {
        var root = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid($"P(x) = x > 1\nD = 1\n{pipeline}").Root);
        // This host-built alias intentionally has no inferred parameters: source
        // elaboration would promote them. Direct AST evaluation is supported as-is.
        var alias = new Algorithm.User(null, [], [], [], [new Expr.Resolve("P")]);
        var ast = new Expr.AlgorithmExpr(root with
        {
            Properties = root.Properties.Select(p => p.Name == "D" ? new Property("D", alias) : p).ToArray(),
        });
        var diagnostics = new SequencePipelineDiagnostics();
        var generic = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var optimized = Evaluator.RunCountedObserved(ast, sequenceDiagnostics: diagnostics);
        Assert.True(generic.Result.IsError);
        var inner = generic.Result.Error;
        while (inner is EvalError.WithContext context) inner = context.Inner;
        var arity = Assert.IsType<EvalError.ArityMismatch>(inner);
        Assert.Equal(0, arity.Expected);
        Assert.Equal(1, arity.Actual);
        AssertParity(generic, optimized);
        Assert.Equal(1, diagnostics.GetSnapshot().FilterCountFusionHits);
    }

    public static IEnumerable<object[]> PredicateCases()
    {
        foreach (var predicate in new[] { "D", "(D)", "((D, ()))", "{D}", "P", "(P)", "{P}" })
        foreach (var body in new[] { "1", "1 / 0", "f(6) + 1", "'abcd'", "range(1, 5)" })
        foreach (var pipeline in new[]
        {
            $"E.filter({predicate}).count", $"A.filter({predicate}).count",
            $"range(1, 3).filter({predicate}).count", $"count(range(1, 3).filter({predicate}))",
            $"count(filter(range(1, 3), {predicate}))",
        })
            yield return [body, pipeline];
    }

    [Theory]
    [MemberData(nameof(PredicateCases))]
    public void PredicatePreparation_MatchesGeneric(string body, string pipeline)
    {
        var ast = Program($"f(0) = 0\nf(n) = f(n - 1)\nD = {body}\nP(x) = {body}\nE = ()\nA = (1, 2, 3)\n{pipeline}");
        foreach (var depth in new[] { 1, 2, 3, 8, 9, 10, 11, 32 })
        {
            var limits = new EvaluationLimits { MaxDepth = depth };
            var diagnostics = new SequencePipelineDiagnostics();
            var optimized = Evaluator.RunCountedObserved(ast, limits, sequenceDiagnostics: diagnostics);
            var generic = Evaluator.RunCountedObserved(ast, limits, enableOptimizations: false);
            AssertParity(generic, optimized);
            Assert.Equal(0, diagnostics.GetSnapshot().FilterCountFusionFallbacks);
            if (depth == 32)
                Assert.Equal(1, diagnostics.GetSnapshot().FilterCountFusionHits);
        }
    }

    /// <summary>
    /// A failed source is the verdict on both strategies, at every depth: the deep predicate
    /// <c>(D)</c> is a CALLBACK that neither strategy evaluates for its value, so it can add no
    /// work before or after the source's failure.
    /// </summary>
    [Theory]
    [InlineData("count(filter(range(1 / 0, 3), (D)))")]
    [InlineData("count(filter(range(1, 5), (D)))")]
    [InlineData("range(1 / 0, 3).filter((D)).count")]
    public void FailedSource_KeepsStrategyParity_WithoutEvaluatingThePredicate(string pipeline)
    {
        var ast = Program($"f(0) = 0\nf(n) = f(n - 1)\nD = f(6) + 1\n{pipeline}");
        foreach (var depth in new[] { 1, 2, 3, 8, 9, 10, 11, 32 })
        {
            var limits = new EvaluationLimits { MaxDepth = depth, MaxCollectionItems = 4 };
            AssertParity(
                Evaluator.RunCountedObserved(ast, limits, enableOptimizations: false),
                Evaluator.RunCountedObserved(ast, limits));
        }
    }

    /// <summary>
    /// A captured value in the predicate slot is a CALLBACK, never evaluated for its value
    /// (CALL-03): neither strategy materializes the string it would build, so no string limit
    /// is ever reached (before the PV-19 repair both strategies ran an eager value attempt that
    /// materialized it, and a limit of 3 was their terminal verdict). An empty source never
    /// invokes the predicate; a non-empty one invokes the zero-parameter value with one
    /// element — the ordinary arity error, identical on both strategies. The fused plan is
    /// prepared and executed in every case (no fallback, one hit): preparation evaluates
    /// nothing that could fail, so the arity error arises while the plan runs.
    /// </summary>
    [Theory]
    [InlineData("E.filter((D)).count", true)]
    [InlineData("A.filter(((D, ()))).count", false)]
    [InlineData("range(1, 3).filter({D}).count", false)]
    [InlineData("count(range(1, 3).filter((D)))", false)]
    [InlineData("count(filter(range(1, 3), (D)))", false)]
    public void CapturedStringPredicate_IsNeverEvaluated_SoNoStringLimitIsReached(string pipeline, bool emptySource)
    {
        var ast = Program($"f(0) = 'abcd'\nf(n) = f(n - 1)\nD = f(6)\nE = ()\nA = (1, 2, 3)\n{pipeline}");
        foreach (var cumulative in new[] { false, true })
        foreach (var limit in new[] { 3, 4, 5 })
        {
            var limits = cumulative
                ? new EvaluationLimits { MaxMaterializedStringChars = limit }
                : new EvaluationLimits { MaxStringLength = limit };
            var diagnostics = new SequencePipelineDiagnostics();
            // Public runs deliberately disable fusion for configured string limits.
            // Force ONLY that strategy flag here to exercise the fused implementation
            // under string limits, using the real evaluator and preparation helpers.
            var optimized = RunStrategy(ast, limits, true, diagnostics);
            var generic = RunStrategy(ast, limits, false, new SequencePipelineDiagnostics());
            AssertParity(generic, optimized);
            Assert.Equal(0, diagnostics.GetSnapshot().FilterCountFusionFallbacks);
            Assert.Equal(1, diagnostics.GetSnapshot().FilterCountFusionHits);
            Assert.Equal(0, optimized.Budget.MaterializedStringChars);
            if (emptySource)
            {
                Assert.True(optimized.Result.IsOk, optimized.Result.IsError ? optimized.Result.Error.ToString() : "");
            }
            else
            {
                var error = optimized.Result.Error;
                while (error is EvalError.WithContext context) error = context.Inner;
                if (pipeline.Contains("(D, ())", StringComparison.Ordinal))
                    Assert.Equal((0, 1), (Assert.IsType<EvalError.ArityMismatch>(error).Expected, Assert.IsType<EvalError.ArityMismatch>(error).Actual));
                else
                {
                    var arity = Assert.IsType<EvalError.ArityMismatch>(error);
                    Assert.Equal(0, arity.Expected);
                    Assert.Equal(1, arity.Actual);
                }
            }
        }
    }

    /// <summary>
    /// The fused predicate preparation evaluates nothing, in the caller's environment or any
    /// other: a captured predicate that would build <c>range(1, v)</c> from the enclosing
    /// activation's <c>v</c> never builds it, so the collection-size limit that value would
    /// break is never reached (before the PV-19 repair both strategies' eager value attempt
    /// built it in the caller's value environment and failed the limit). Both strategies agree:
    /// the empty source gives 0, a non-empty one the callback's ordinary arity error.
    /// </summary>
    [Theory]
    [InlineData("E.filter((D)).count", true)]
    [InlineData("count(filter(range(1, 3), ((D, ()))))", false)]
    public void CapturedPredicate_IsNeverEvaluated_SoItsValueIsNeverBuilt(string pipeline, bool emptySource)
    {
        var ast = Program($"Run(v) = {{ D = range(1, v)\nE = ()\n{pipeline} }}\nRun(7)");
        var limits = new EvaluationLimits { MaxCollectionItems = 6 };
        var diagnostics = new SequencePipelineDiagnostics();
        var generic = Evaluator.RunCountedObserved(ast, limits, enableOptimizations: false);
        var optimized = Evaluator.RunCountedObserved(ast, limits, sequenceDiagnostics: diagnostics);
        if (emptySource)
        {
            Assert.True(generic.Result.IsOk, generic.Result.IsError ? generic.Result.Error.ToString() : "");
            Assert.Equal(new Result.Atom(0), generic.Result.Value.Value);
        }
        else
        {
            var error = generic.Result.Error;
            while (error is EvalError.WithContext context) error = context.Inner;
            Assert.Equal((0, 1), (Assert.IsType<EvalError.ArityMismatch>(error).Expected, Assert.IsType<EvalError.ArityMismatch>(error).Actual));
        }

        AssertParity(generic, optimized);
        Assert.Equal(0, diagnostics.GetSnapshot().FilterCountFusionFallbacks);
    }

    /// <summary>
    /// The predicate is a CALLBACK slot: neither strategy evaluates it for its value, so its host
    /// effect never runs (before the PV-19 repair both strategies ran it once in an eager value
    /// attempt), and when it is invoked with an element the zero-parameter value is rejected
    /// by the binder before its body runs. A host effect in the SOURCE runs exactly once on both
    /// strategies — including when plain recognition falls back for a non-range source, which it
    /// does before evaluating anything.
    /// </summary>
    [Theory]
    [InlineData("E.filter((D)).count", "Mark()", 0, 0)]
    [InlineData("range(1, 3).filter((D)).count", "Mark()", 0, 0)]
    [InlineData("count(filter(range(1, 3), (D)))", "Mark()", 0, 0)]
    [InlineData("count(filter(range(1 / 0, 3), (D)))", "Mark()", 0, 0)]
    [InlineData("range(1 / 0, 3).filter((D)).count", "Mark()", 0, 0)]
    [InlineData("E.filter((D)).count", "Mark() / 0", 0, 0)]
    [InlineData("E.filter((D)).count", "{Mark(), range(1, 5)}", 0, 0)]
    [InlineData("count(filter(E, (D)))", "Mark()", 0, 1)]
    [InlineData("range(Mark(), 3).filter((D)).count", "1", 1, 0)]
    [InlineData("count(filter(range(Mark(), 3), (D)))", "1", 1, 0)]
    [InlineData("count(filter([Mark(), 2], (D)))", "1", 1, 1)]
    public void PredicateIsNeverEvaluated_AndSourceEffectsAreNeverReplayed(string pipeline, string body, int expectedCalls, int expectedFallbacks)
    {
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.Create("Mark", (_, _) =>
        {
            calls++;
            return new Result.Atom(1);
        }));
        var parsed = Parser.Parse($"D = {body}\nE = ()\n{pipeline}", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        var ast = new Expr.AlgorithmExpr(parsed.Root);
        var limits = new EvaluationLimits { MaxCollectionItems = 4 };
        var generic = Evaluator.RunCountedObserved(ast, limits, enableOptimizations: false, hostOperations: operations);
        Assert.Equal(expectedCalls, calls);
        calls = 0;
        var diagnostics = new SequencePipelineDiagnostics();
        var optimized = Evaluator.RunCountedObserved(ast, limits, sequenceDiagnostics: diagnostics, hostOperations: operations);
        Assert.Equal(expectedCalls, calls);
        AssertParity(generic, optimized);
        Assert.Equal(expectedFallbacks, diagnostics.GetSnapshot().FilterCountFusionFallbacks);
    }

    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) RunStrategy(
        Expr ast, EvaluationLimits limits, bool fused, SequencePipelineDiagnostics diagnostics)
    {
        var ctx = Evaluator.EvalCtx.Empty with
        {
            CallStack = [BuiltinRegistry.CreateRuntimePreludeAlgorithm()],
            EnableLoopOptimization = false,
            EnableSequencePipelineOptimization = fused,
            SequenceDiagnostics = diagnostics,
            Budget = EvaluationBudget.Create(limits),
        };
        return (Evaluator.EvalCounted(ast, ctx, []), ctx.Budget);
    }

    private static void AssertParity(
        (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) generic,
        (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) optimized)
    {
        Assert.Equal(generic.Result.IsError, optimized.Result.IsError);
        if (generic.Result.IsError)
        {
            Assert.Equal(generic.Result.Error.Code, optimized.Result.Error.Code);
            Assert.Equal(generic.Result.Error.IsResourceLimit, optimized.Result.Error.IsResourceLimit);
            Assert.Equal(DescribeErrorTree(generic.Result.Error), DescribeErrorTree(optimized.Result.Error));
        }
        else
        {
            Assert.Equal(generic.Result.Value.Value, optimized.Result.Value.Value, Result.ValueComparer);
            Assert.Equal(generic.Result.Value.EmittedCount, optimized.Result.Value.EmittedCount);
        }
        Assert.Equal(generic.Budget.PeakDepth, optimized.Budget.PeakDepth);
        Assert.Equal(generic.Budget.ConsumedSteps, optimized.Budget.ConsumedSteps);
        Assert.Equal(generic.Budget.MaterializedStringChars, optimized.Budget.MaterializedStringChars);
    }
}
