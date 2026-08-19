using KatLang.Evaluation.Caching;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Public async API contract on the DEFAULT (fast) path: no run component is
/// async-capable, so <c>RunAsync</c>/<c>RunFlatAsync</c>/<c>KatLangEngine.RunAsync</c>
/// execute the synchronous pipeline inline and must (a) complete synchronously on the
/// calling thread — no thread offloading, no yielding — and (b) produce byte-identical
/// results, errors, budget verdicts, and operational counters to the synchronous APIs.
/// </summary>
public class AsyncEvaluationApiTests
{
    /// <summary>
    /// Representative program matrix: values, multi-row output, strings, lists,
    /// user calls, collection builtins, loops, and error outcomes. Sources must parse
    /// cleanly (SourceProvenance.ParseValid enforces it).
    /// </summary>
    public static TheoryData<string> Programs() =>
    [
        "1 + 2",
        "1\n2\n3",
        "'hello'",
        "[1, [2], ()]",
        "A = 1, 2, 3\nA",
        "A = 1, 2, 3\nA.sum",
        "F(x) = x * 2\nF(21)",
        "F(x) = x * 2\n[1, 2, 3].map(F)",
        "Step(n, acc) = (n + 1, acc + n)\nrepeat(Step, 5, 0, 0)",
        "Fib(0) = 0\nFib(1) = 1\nFib(n) = Fib(n - 1) + Fib(n - 2)\nFib(12)",
        "x, *rest = [1, 2, 3]\nrest",
        "1 / 0",
        "A = 1 / 0\nA",
        "count(1, 2, 3)",
    ];

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task RunAsync_DefaultPath_MatchesRun(string source)
    {
        var ast = AsyncEvaluationHarness.Ast(source);

        var sync = Evaluator.Run(ast);
        var task = Evaluator.RunAsync(ast);

        // Fast path: no async component exists, so the task must already be complete —
        // evaluation ran inline on this thread.
        Assert.True(task.IsCompletedSuccessfully);
        var async = await task;

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        if (sync.IsOk)
            Assert.True(Result.ValueComparer.Equals(sync.Value, async.Value));
    }

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task RunFlatAsync_DefaultPath_MatchesRunFlat(string source)
    {
        var ast = AsyncEvaluationHarness.Ast(source);

        var sync = Evaluator.RunFlat(ast);
        var task = Evaluator.RunFlatAsync(ast);

        Assert.True(task.IsCompletedSuccessfully);
        var async = await task;

        Assert.Equal(AsyncEvaluationHarness.NeutralOfFlat(sync), AsyncEvaluationHarness.NeutralOfFlat(async));
    }

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task EngineRunAsync_DefaultPath_MatchesEngineRun(string source)
    {
        var sync = KatLangEngine.Run(source);
        var task = KatLangEngine.RunAsync(source);

        Assert.True(task.IsCompletedSuccessfully);
        var async = await task;

        AssertEquivalentRunResults(sync, async);
    }

    [Fact]
    public async Task EngineRunAsync_ParseFailure_MatchesEngineRun()
    {
        const string source = "A = ;";
        var sync = KatLangEngine.Run(source);
        var async = await KatLangEngine.RunAsync(source);

        Assert.IsType<RunResult.ParseFailure>(sync);
        AssertEquivalentRunResults(sync, async);
    }

    [Fact]
    public async Task EngineRunAsync_NoProgramOutput_MatchesEngineRun()
    {
        const string source = "A = 1";
        var sync = KatLangEngine.Run(source);
        var async = await KatLangEngine.RunAsync(source);

        Assert.IsType<RunResult.NoProgramOutput>(sync);
        AssertEquivalentRunResults(sync, async);
    }

    [Fact]
    public async Task EngineRunAsync_LoadFailureWithAdditionalEvaluationErrors_MatchesEngineRun()
    {
        // A failing module fetch surfaces load diagnostics; when the remainder is
        // evaluable, the engine appends additional evaluation errors. The async engine
        // must mirror that combined projection exactly.
        const string source = "open 'https://katlang.org/missing.kat'\n1 / 0";
        var options = new RunOptions
        {
            DownloadCode = _ => throw new InvalidOperationException("fetch refused by test"),
        };

        var sync = KatLangEngine.Run(source, options);
        var async = await KatLangEngine.RunAsync(source, options);

        AssertEquivalentRunResults(sync, async);
    }

    public static TheoryData<string, int?, long?, int?> LimitVerdictCases() => new()
    {
        // program, maxDepth, maxSteps, maxCollectionItems
        { "Fib(0) = 0\nFib(1) = 1\nFib(n) = Fib(n - 1) + Fib(n - 2)\nFib(12)", 8, null, null },
        { "Step(n) = (n + 1, 1)\nwhile(Step, 0)", null, 100, null },
        { "range(1, 100)", null, null, 10 },
        { "A = 'aaaaaaaaaa'\nB = A + A\nB + B", null, null, null },
    };

    [Theory]
    [MemberData(nameof(LimitVerdictCases))]
    public async Task RunAsync_LimitVerdicts_MatchRun(string source, int? maxDepth, long? maxSteps, int? maxCollectionItems)
    {
        var ast = AsyncEvaluationHarness.Ast(source);
        var limits = new EvaluationLimits
        {
            MaxDepth = maxDepth,
            MaxSteps = maxSteps,
            MaxCollectionItems = maxCollectionItems,
        };

        var sync = Evaluator.Run(ast, limits);
        var async = await Evaluator.RunAsync(ast, limits);

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
    }

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task RunCountedObservedAsync_DefaultPath_ChargesIdenticalCounters(string source)
    {
        var ast = AsyncEvaluationHarness.Ast(source);

        var (syncResult, syncBudget) = Evaluator.RunCountedObserved(ast);
        var (asyncResult, asyncBudget) = await Evaluator.RunCountedObservedAsync(ast);

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(syncResult), AsyncEvaluationHarness.NeutralOf(asyncResult));
        Assert.Equal(syncBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        Assert.Equal(syncBudget.PeakDepth, asyncBudget.PeakDepth);
        Assert.Equal(syncBudget.MaterializedItems, asyncBudget.MaterializedItems);
        Assert.Equal(syncBudget.MaterializedStringChars, asyncBudget.MaterializedStringChars);
    }

    [Fact]
    public async Task RunAsync_PrebuiltAstBeyondStructuralCeiling_ReturnsStructuredError()
    {
        // Structural preflight applies to the async entry points exactly as to the
        // synchronous ones: a too-deep host-built tree is rejected with the structured
        // AST-depth error before any evaluation.
        Expr expr = new Expr.Num(1);
        for (var i = 0; i < EvaluationLimits.MaxSupportedAstDepth + 8; i++)
            expr = new Expr.Unary(UnaryOp.Minus, expr);

        var sync = Evaluator.Run(expr);
        var async = await Evaluator.RunAsync(expr);

        Assert.True(sync.IsError);
        Assert.True(async.IsError);
        Assert.IsType<EvalError.AstDepthLimitExceeded>(sync.Error);
        Assert.IsType<EvalError.AstDepthLimitExceeded>(async.Error);
    }

    internal static void AssertEquivalentRunResults(RunResult expected, RunResult actual)
    {
        Assert.Equal(expected.GetType(), actual.GetType());
        Assert.Equal(expected.ToDisplayString(), actual.ToDisplayString());

        switch (expected)
        {
            case RunResult.Success expectedSuccess:
                var actualSuccess = Assert.IsType<RunResult.Success>(actual);
                Assert.True(Result.ValueComparer.Equals(expectedSuccess.Value, actualSuccess.Value));
                Assert.Equal(expectedSuccess.Atoms, actualSuccess.Atoms);
                Assert.Equal(expectedSuccess.EmittedCount, actualSuccess.EmittedCount);
                Assert.Equal(expectedSuccess.OutputRows.Count, actualSuccess.OutputRows.Count);
                break;

            case RunResult.ParseFailure expectedParse:
                var actualParse = Assert.IsType<RunResult.ParseFailure>(actual);
                Assert.Equal(
                    expectedParse.Errors.Select(static e => e.ToString()),
                    actualParse.Errors.Select(static e => e.ToString()));
                break;

            case RunResult.EvalFailure expectedEval:
                var actualEval = Assert.IsType<RunResult.EvalFailure>(actual);
                Assert.Equal(
                    expectedEval.Errors.Select(static e => e.ToString()),
                    actualEval.Errors.Select(static e => e.ToString()));
                break;

            case RunResult.NoProgramOutput expectedNoOutput:
                var actualNoOutput = Assert.IsType<RunResult.NoProgramOutput>(actual);
                Assert.Equal(expectedNoOutput.Message, actualNoOutput.Message);
                break;
        }
    }
}
