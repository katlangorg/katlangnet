using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Regression coverage for the prepared call-argument path: a zero-parameter parenthesized
/// block supplied to a patterned callee produces its combined value and explicit written-slot
/// view in one left-to-right evaluation.
/// </summary>
public class PatternedCallSingleEvaluationTests
{
    private const string OrdinarySingleEvaluationSource =
        "Make = range(1, 4)\n" +
        "Pair((items, marker)) = items.count + marker\n" +
        "Pair((Make(), 6))";

    private const string DottedSingleEvaluationSource =
        "Make = range(1, 4)\n" +
        "Pair((items, marker)) = items.count + marker\n" +
        "(Make(), 6).Pair";

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result.ListValue List(params Result[] items) => new(items);

    private static Result.SequenceValue Seq(params Result[] items) => new(items);

    private static Expr ParseProgram(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(
            parsed.HasErrors,
            string.Join(Environment.NewLine, parsed.Diagnostics.Select(static diagnostic => diagnostic.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static void AssertSemanticallyEqual(Result expected, Result actual)
        => Assert.True(
            Result.ValueComparer.Equals(expected, actual),
            $"Expected {expected} but got {actual}");

    private static Result EvaluateEveryMode(string source)
    {
        var expr = ParseProgram(source);
        var plainOptimized = Evaluator.Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null);
        var plainGeneric = Evaluator.Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: false,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: false,
            sequenceDiagnostics: null);
        var (countedOptimized, _) = Evaluator.RunCountedObserved(expr, enableOptimizations: true);
        var (countedGeneric, _) = Evaluator.RunCountedObserved(expr, enableOptimizations: false);
        var engine = KatLangEngine.Run(source);

        Assert.True(plainOptimized.IsOk, Failure("plain optimizer-on", plainOptimized));
        Assert.True(plainGeneric.IsOk, Failure("plain optimizer-off", plainGeneric));
        Assert.True(countedOptimized.IsOk, Failure("counted optimizer-on", countedOptimized));
        Assert.True(countedGeneric.IsOk, Failure("counted optimizer-off", countedGeneric));
        var engineSuccess = Assert.IsType<RunResult.Success>(engine);

        AssertSemanticallyEqual(plainOptimized.Value, plainGeneric.Value);
        AssertSemanticallyEqual(plainOptimized.Value, countedOptimized.Value.Value);
        AssertSemanticallyEqual(plainOptimized.Value, countedGeneric.Value.Value);
        AssertSemanticallyEqual(plainOptimized.Value, engineSuccess.Value);
        Assert.Equal(countedOptimized.Value.EmittedCount, countedGeneric.Value.EmittedCount);
        Assert.Equal(countedOptimized.Value.EmittedCount, engineSuccess.EmittedCount);
        return plainOptimized.Value;
    }

    private static string Failure<T>(string mode, EvalResult<T> result)
        => result.IsError ? $"{mode} failed: {result.Error}" : $"{mode} unexpectedly failed";

    private static (EvalResult<Evaluator.CountedResult> Result, long Steps, long Items) Observe(
        string source,
        bool optimize,
        EvaluationLimits? limits = null)
    {
        var (result, budget) = Evaluator.RunCountedObserved(
            ParseProgram(source),
            limits,
            enableOptimizations: optimize);
        return (result, budget.ConsumedSteps, budget.MaterializedItems);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PatternedOrdinaryCall_EvaluatesGroupedArgumentOnce(bool optimize)
    {
        var observed = Observe(OrdinarySingleEvaluationSource, optimize);

        Assert.True(observed.Result.IsOk, Failure("observed ordinary", observed.Result));
        AssertSemanticallyEqual(Atom(10), observed.Result.Value.Value);
        Assert.Equal(2, observed.Steps);
        Assert.Equal(6, observed.Items);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PatternedDottedCall_EvaluatesInjectedReceiverOnce(bool optimize)
    {
        var ordinary = Observe(OrdinarySingleEvaluationSource, optimize);
        var dotted = Observe(DottedSingleEvaluationSource, optimize);

        Assert.True(dotted.Result.IsOk, Failure("observed dotted", dotted.Result));
        AssertSemanticallyEqual(Atom(10), dotted.Result.Value.Value);
        Assert.Equal(ordinary.Steps, dotted.Steps);
        Assert.Equal(ordinary.Items, dotted.Items);
        Assert.Equal(2, dotted.Steps);
        Assert.Equal(6, dotted.Items);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ExactMaterializationBoundary_SucceedsInPlainAndCountedEvaluators(bool optimize)
    {
        var limits = new EvaluationLimits { MaxMaterializedItems = 6 };
        foreach (var source in new[] { OrdinarySingleEvaluationSource, DottedSingleEvaluationSource })
        {
            var expr = ParseProgram(source);
            var plain = Evaluator.Run(
                expr,
                new RunScopedZeroArgPropertyResultCache(),
                enableLoopOptimization: optimize,
                loopDiagnostics: null,
                enableSequencePipelineOptimization: optimize,
                sequenceDiagnostics: null,
                limits);
            var counted = Observe(source, optimize, limits);

            Assert.True(plain.IsOk, Failure("plain exact materialization boundary", plain));
            Assert.True(counted.Result.IsOk, Failure("counted exact materialization boundary", counted.Result));
            Assert.Equal(6, counted.Items);
        }
    }

    [Theory]
    [InlineData(nameof(OrdinarySingleEvaluationSource))]
    [InlineData(nameof(DottedSingleEvaluationSource))]
    public void ExactOperationalBoundaries_SucceedThroughPublicEngine(string sourceName)
    {
        var source = sourceName == nameof(OrdinarySingleEvaluationSource)
            ? OrdinarySingleEvaluationSource
            : DottedSingleEvaluationSource;

        var itemLimited = KatLangEngine.Run(
            source,
            new RunOptions { EvaluationLimits = new EvaluationLimits { MaxMaterializedItems = 6 } });
        var stepLimited = KatLangEngine.Run(
            source,
            new RunOptions { EvaluationLimits = new EvaluationLimits { MaxSteps = 2 } });

        Assert.Equal("10", Assert.IsType<RunResult.Success>(itemLimited).ToDisplayString());
        Assert.Equal("10", Assert.IsType<RunResult.Success>(stepLimited).ToDisplayString());
    }

    [Fact]
    public void OneBelowMaterializationBoundary_FailsWithoutCommittingRejectedWork()
    {
        var observed = Observe(
            OrdinarySingleEvaluationSource,
            optimize: false,
            new EvaluationLimits { MaxMaterializedItems = 5 });

        Assert.True(observed.Result.IsError);
        Assert.IsType<EvalError.MaterializationLimitExceeded>(Innermost(observed.Result.Error));
        Assert.Equal(4, observed.Items);
    }

    public static TheoryData<string, Result> GroupedShapeCases => new()
    {
        {
            "F((first, second)) = (first, second)\nF(((1, 2), 3))",
            Seq(Seq(Atom(1), Atom(2)), Atom(3))
        },
        {
            "F((sequence, list)) = (sequence, list)\nF(((1, 2), [3, 4]))",
            Seq(Seq(Atom(1), Atom(2)), List(Atom(3), Atom(4)))
        },
        {
            "A = (1, 2)\nF((x, y, z)) = (x, y, z)\nF((A*, 3))",
            Seq(Atom(1), Atom(2), Atom(3))
        },
        { "F((x)) = x\nF((7))", Atom(7) },
        { "A = ()\nF((x)) = x\nF((A))", Seq() },
        { "A = ()\nF((*items)) = items.count\nF((A*))", Atom(0) },
        {
            "S = ((1, 2), (3, 4))\nF((x, y)) = (x, y)\nF((S:0, 5))",
            Seq(Seq(Atom(1), Atom(2)), Atom(5))
        },
    };

    [Theory]
    [MemberData(nameof(GroupedShapeCases))]
    public void GroupedWrittenSlotShapes_ArePreservedAcrossEveryMode(string source, Result expected)
        => AssertSemanticallyEqual(expected, EvaluateEveryMode(source));

    [Fact]
    public void MultiParameterBlock_RemainsLazyOnTheAlgorithmOnlyChannel()
    {
        const string source =
            "Keep(function, (x, y)) = x + y\n" +
            "Keep({1 / 0 + value}, (3, 4))";

        AssertSemanticallyEqual(Atom(7), EvaluateEveryMode(source));
        var observed = Observe(source, optimize: false);
        Assert.True(observed.Result.IsOk);
        Assert.Equal(1, observed.Steps);
        Assert.Equal(2, observed.Items);
    }

    [Fact]
    public void FailingArgument_IsNotRetried_AndKeepsItsOriginalSpanAndContext()
    {
        const string source =
            "Fail = 1 / 0\n" +
            "Use((x, y)) = x + y\n" +
            "Use((Fail(), 9))";

        var observed = Observe(source, optimize: false);

        Assert.True(observed.Result.IsError);
        Assert.Equal(2, observed.Steps);
        Assert.Equal(0, observed.Items);
        Assert.Contains("call to Fail", observed.Result.Error.ToString(), StringComparison.Ordinal);
        var inner = Innermost(observed.Result.Error);
        Assert.IsType<EvalError.DivByZero>(inner);
        Assert.Equal(new SourceSpan(1, 8, 1, 12), inner.Span);
    }

    [Fact]
    public void EmptyOutputBlock_StillFailsOnceWithMissingOutput()
    {
        var parsed = Parser.Parse("F((x)) = x\nF((7))");
        Assert.False(parsed.HasErrors);
        var emptyBlock = new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: []));
        OutputBundle emptyArgs = [emptyBlock];
        var root = parsed.Root with
        {
            Output = [new Expr.Call(new Expr.Resolve("F"), emptyArgs)],
        };

        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(root),
            enableOptimizations: false);

        Assert.True(result.IsError);
        Assert.IsType<EvalError.MissingOutput>(Innermost(result.Error));
        Assert.Equal(1, budget.ConsumedSteps);
        Assert.Equal(0, budget.MaterializedItems);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RepeatedNamePatternedCall_EvaluatesEachGroupedArgumentOnce(bool optimize)
    {
        // A repeated-name patterned callee never consumes the explicit-slot
        // view, but its grouped arguments flow through the same prepared
        // assembly — each written block must still evaluate exactly once.
        const string source =
            "Make = range(1, 4)\n" +
            "Same(x, x) = x\n" +
            "Same((Make(), 6), (Make(), 6))";

        var observed = Observe(source, optimize);

        Assert.True(observed.Result.IsOk, Failure("repeated-name patterned", observed.Result));
        AssertSemanticallyEqual(
            Seq(List(Atom(1), Atom(2), Atom(3), Atom(4)), Atom(6)),
            observed.Result.Value.Value);
        Assert.Equal(3, observed.Steps);
        Assert.Equal(12, observed.Items);
    }

    [Fact]
    public void MultiEmittingSingleSlot_StaysOneWrittenItemInThePreparedView()
    {
        // Accumulator-vs-decomposition discriminator: `S:0` re-emits a two-item
        // counted supply, yet it occupies ONE written output slot of its group,
        // so the singleton pattern binds the whole selected pair. Recovering the
        // slot view by decomposing the combined counted value (count 2) would
        // wrongly present two items and fail the one-capture pattern. Surface
        // syntax folds redundant parentheses around a lone postfix expression,
        // so this written group is built on the host AST channel — the same
        // channel the empty-output-block regression uses.
        var parsed = Parser.Parse("S = ((1, 2), (3, 4))\nF((x)) = x\nF((9))");
        Assert.False(parsed.HasErrors);
        var projectionBlock = new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.Index(new Expr.Resolve("S"), new Expr.Num(0))]));
        OutputBundle callArgs = [projectionBlock];
        var root = parsed.Root with
        {
            Output = [new Expr.Call(new Expr.Resolve("F"), callArgs)],
        };

        foreach (var optimize in new[] { false, true })
        {
            var (result, _) = Evaluator.RunCountedObserved(
                new Expr.AlgorithmExpr(root),
                enableOptimizations: optimize);

            Assert.True(result.IsOk, Failure($"prepared written-slot view (optimize: {optimize})", result));
            AssertSemanticallyEqual(Seq(Atom(1), Atom(2)), result.Value.Value);
            Assert.Equal(1, result.Value.EmittedCount);
        }
    }

    [Fact]
    public void FlatCallee_RemainsAOneEvaluationNegativeControl()
    {
        const string flat = "Flat(value) = value.count\nFlat((range(1, 4), 6))";
        const string patterned =
            "Pair((items, marker)) = items.count + marker\n" +
            "Pair((range(1, 4), 6))";

        var flatObserved = Observe(flat, optimize: false);
        var patternedObserved = Observe(patterned, optimize: false);

        Assert.True(flatObserved.Result.IsOk, Failure("flat negative control", flatObserved.Result));
        Assert.True(patternedObserved.Result.IsOk, Failure("patterned control", patternedObserved.Result));
        Assert.Equal(1, flatObserved.Steps);
        Assert.Equal(6, flatObserved.Items);
        Assert.Equal(flatObserved.Steps, patternedObserved.Steps);
        Assert.Equal(flatObserved.Items, patternedObserved.Items);
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }
}
