namespace KatLang.Tests.Interpolation;

/// <summary>
/// STR-02 evaluation order and demand (VAL-12 under Model C): the holes of one evaluation of
/// an interpolated string are evaluated LEFT TO RIGHT, each EXACTLY ONCE, each converted at
/// once, and the first failure — an evaluation failure, a conversion failure, or a terminal
/// resource limit — stops the node, so no later hole runs. A hole reads its value the ordinary
/// way: a parameter demands its supplied cell (once, shared with every other read), a property
/// reads the zero-argument cache, <c>A()</c> evaluates afresh, and an interpolated string passed
/// as an argument is itself a suspended computation. Effects — host operations, seeded random
/// draws, cancellation — observe exactly that order on the sync and the async route.
/// </summary>
public class InterpolationDemandTests
{
    private sealed class EffectLog
    {
        public List<decimal> Entries { get; } = [];

        public HostOperations Operations(Action<decimal>? onLog = null) => HostOperations.Create(
            HostOperation.Create("Log", (args, _) =>
            {
                var value = (decimal)Assert.IsType<Result.Atom>(args[0]).Value;
                Entries.Add(value);
                onLog?.Invoke(value);
                return args[0];
            }, "x"));

        public HostOperations AsyncOperations() => HostOperations.Create(
            HostOperation.CreateAsync("Log", async (args, _) =>
            {
                await Task.Yield();
                Entries.Add((decimal)Assert.IsType<Result.Atom>(args[0]).Value);
                return args[0];
            }, "x"));
    }

    private static RunResult Run(string source, EffectLog log, EvaluationLimits? limits = null)
        => KatLangEngine.Run(source, new RunOptions { HostOperations = log.Operations(), EvaluationLimits = limits });

    private static string RunText(string source, EffectLog log)
        => Assert.IsType<RunResult.Success>(Run(source, log)).ToDisplayString().ReplaceLineEndings("\n");

    private static KatLangErrorCode FailureCode(RunResult result)
        => Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors).Code;

    [Fact]
    public void Holes_AreEvaluatedLeftToRight_EachExactlyOnce()
    {
        var log = new EffectLog();
        Assert.Equal("1-2-3", RunText("\"{Log(1)}-{Log(2)}-{Log(3)}\"", log));
        Assert.Equal(new decimal[] { 1, 2, 3 }, log.Entries);
    }

    [Fact]
    public void EveryEvaluationOfTheNode_EvaluatesItsHolesAgain()
    {
        var log = new EffectLog();
        Assert.Equal("1\n2", RunText("F(n) = \"{Log(n)}\"\nF(1), F(2)", log));
        Assert.Equal(new decimal[] { 1, 2 }, log.Entries);
    }

    [Fact]
    public void AParameterRead_DemandsItsSuppliedCellOnce_HoweverManyHolesReadIt()
    {
        var log = new EffectLog();
        Assert.Equal("77-7", RunText("F(x) = \"{x}{x}-{x}\"\nF(Log(7))", log));
        Assert.Equal(new decimal[] { 7 }, log.Entries);
    }

    [Fact]
    public void AnUnreadParameter_IsNeverDemanded()
    {
        var log = new EffectLog();
        Assert.Equal("1", RunText("F(x, y) = \"{x}\"\nF(1, Log(9))", log));
        Assert.Empty(log.Entries);
    }

    [Fact]
    public void AnInterpolatedArgument_IsSuspendedUntilDemanded_AndThenEvaluatedOnce()
    {
        var log = new EffectLog();
        Assert.Equal("0", RunText("Skip(s) = 0\nSkip(\"{Log(1)}\")", log));
        Assert.Empty(log.Entries);

        Assert.Equal("v2v2", RunText("Twice(s) = \"{s}{s}\"\nTwice(\"v{Log(2)}\")", log));
        Assert.Equal(new decimal[] { 2 }, log.Entries);
    }

    [Fact]
    public void APropertyRead_UsesTheZeroArgumentCache_WhileACallIsFresh()
    {
        var log = new EffectLog();
        Assert.Equal("55\n5", RunText("A = Log(5)\n\"{A}{A}\", A", log));
        Assert.Equal(new decimal[] { 5 }, log.Entries);

        var fresh = new EffectLog();
        Assert.Equal("55", RunText("A = Log(5)\n\"{A()}{A()}\"", fresh));
        Assert.Equal(new decimal[] { 5, 5 }, fresh.Entries);
    }

    [Fact]
    public void AnInterpolatedProperty_IsCachedLikeAnyZeroArgumentProperty()
    {
        var log = new EffectLog();
        Assert.Equal("4\n4\n4", RunText("T = \"{Log(4)}\"\nT, T, T()", log));
        Assert.Equal(new decimal[] { 4, 4 }, log.Entries);
    }

    [Fact]
    public void TheFirstFailingHole_StopsTheNode_AndNoLaterHoleRuns()
    {
        var log = new EffectLog();
        Assert.Equal(KatLangErrorCode.DivisionByZero, FailureCode(Run("\"{Log(1)}{1 div 0}{Log(3)}\"", log)));
        Assert.Equal(new decimal[] { 1 }, log.Entries);

        var missing = new EffectLog();
        Assert.Equal(KatLangErrorCode.MissingOutput, FailureCode(Run("B = { A = 1 }\n\"{Log(1)}{B}{Log(3)}\"", missing)));
        Assert.Equal(new decimal[] { 1 }, missing.Entries);
    }

    [Fact]
    public void ATerminalResourceLimitInAHole_EndsTheRun()
    {
        var log = new EffectLog();
        var result = Run("\"{range(1, 100)}{Log(3)}\", Log(4)", log, new EvaluationLimits { MaxCollectionItems = 10 });
        Assert.Equal(KatLangErrorCode.CollectionSizeLimitExceeded, FailureCode(result));
        Assert.Empty(log.Entries);
    }

    [Fact]
    public void AStringLimitCrossedByAppending_StopsBeforeTheNextHole()
    {
        var log = new EffectLog();
        var result = Run("\"{'ab'}{'cd'}{Log(1)}\"", log, new EvaluationLimits { MaxStringLength = 3 });
        Assert.Equal(KatLangErrorCode.StringSizeLimitExceeded, FailureCode(result));
        Assert.Empty(log.Entries);
    }

    [Fact]
    public void AnUnselectedBranch_IsNeverEvaluated()
    {
        var log = new EffectLog();
        Assert.Equal("a", RunText("\"{if(true, 'a', Log(1))}\"", log));
        Assert.Equal("[]", RunText("C(s) = Log(1) > 0\n\"{filter([], C)}\"", log));
        Assert.Empty(log.Entries);
    }

    [Fact]
    public void SeededRandomDraws_FollowTheHoleOrder()
    {
        const long seed = 424242;
        var rows = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "randomInt(1, 1000000), randomInt(1, 1000000)", new RunOptions { RandomSeed = seed })).ToDisplayString()
            .ReplaceLineEndings("\n").Split('\n');
        var text = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "\"{randomInt(1, 1000000)}|{randomInt(1, 1000000)}\"", new RunOptions { RandomSeed = seed })).ToDisplayString();
        Assert.Equal($"{rows[0]}|{rows[1]}", text);
    }

    [Fact]
    public async Task AnAsynchronousHostOperationInAHole_IsAwaitedInOrder()
    {
        var log = new EffectLog();
        var result = await KatLangEngine.RunAsync(
            "F(x) = \"{x}{x}\"\n\"{Log(1)}<{F(Log(2))}>{Log(3)}\"",
            new RunOptions { HostOperations = log.AsyncOperations() });
        Assert.Equal("1<22>3", Assert.IsType<RunResult.Success>(result).ToDisplayString());
        Assert.Equal(new decimal[] { 1, 2, 3 }, log.Entries);
    }

    [Fact]
    public void ASynchronousRun_RejectsAnAsynchronousConfiguration()
    {
        var log = new EffectLog();
        Assert.Throws<InvalidOperationException>(() =>
            KatLangEngine.Run("\"{Log(1)}\"", new RunOptions { HostOperations = log.AsyncOperations() }));
        Assert.Empty(log.Entries);
    }

    [Fact]
    public void CancellationDuringAHole_StopsTheRunBeforeTheNextHole()
    {
        using var cancellation = new CancellationTokenSource();
        var log = new EffectLog();
        var options = new RunOptions
        {
            HostOperations = log.Operations(onLog: value =>
            {
                if (value == 1)
                    cancellation.Cancel();
            }),
            EvaluationCancellationToken = cancellation.Token,
        };

        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => KatLangEngine.Run("\"{Log(1)}{Log(2)}\"", options));
        Assert.Equal(cancellation.Token, thrown.CancellationToken);
        Assert.Equal(new decimal[] { 1 }, log.Entries);
    }

    [Theory]
    [InlineData("\"a{1}b{(2, [3, 'x'])}c\"")]
    [InlineData("F(x) = \"{x}{x}\"\nF(\"{1}\")")]
    [InlineData("A = 7\n\"{A}{A()}{\"{A}\"}\"")]
    [InlineData("\"{1 div 0}\"")]
    [InlineData("B = { A = 1 }\n\"{B}\"")]
    [InlineData("\"<{\"[{\"({1})\"}]\"}>\"")]
    [InlineData("Step(s) = \"{s}x\"\nStep.repeat(3, '')")]
    public async Task TheAsyncTwin_AgreesWithTheSyncEvaluator(string source)
    {
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var sync = Evaluator.RunCounted(expr);
        var asynchronous = await Evaluator.RunCountedAsync(expr, new AsyncEvaluation.PassThroughAsyncZeroArgPropertyResultCache());
        Assert.Equal(sync.IsError, asynchronous.IsError);
        if (sync.IsError)
        {
            Assert.Equal(KatLangError.FromEvalError(sync.Error).Code, KatLangError.FromEvalError(asynchronous.Error).Code);
            Assert.Equal(sync.Error.Span, asynchronous.Error.Span);
        }
        else
        {
            Assert.True(Result.ValueComparer.Equals(sync.Value.Value, asynchronous.Value.Value));
            Assert.Equal(sync.Value.EmittedCount, asynchronous.Value.EmittedCount);
        }
    }

    [Theory]
    [InlineData("Step(s) = \"{s}x\"\nStep.repeat(4, '')", "xxxx")]
    [InlineData("Step(s, n) = \"{s}{n}\", n + 1\nStep.repeat(3, '', 1)", "(123, 4)")]
    public void ALoopStepThatInterpolates_RunsIdenticallyOnEveryStrategy(string source, string expected)
    {
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var (planned, plannedBudget) = Evaluator.RunCountedObserved(expr, enableOptimizations: true);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(expr, enableOptimizations: false);
        Assert.False(planned.IsError);
        Assert.False(generic.IsError);
        Assert.True(Result.ValueComparer.Equals(planned.Value.Value, generic.Value.Value));
        Assert.Equal(plannedBudget.ConsumedSteps, genericBudget.ConsumedSteps);
        Assert.Equal(plannedBudget.ConsumedExpressionCheckpoints, genericBudget.ConsumedExpressionCheckpoints);
        Assert.Equal(plannedBudget.MaterializedStringChars, genericBudget.MaterializedStringChars);
        Assert.Equal(expected, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }
}
