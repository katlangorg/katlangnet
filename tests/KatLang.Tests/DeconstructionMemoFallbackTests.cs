namespace KatLang.Tests;

public class DeconstructionMemoFallbackTests
{
    [Fact]
    public async Task DeferredModuleImport_PreservesTheSharedParserSignatureAfterSuspension()
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var gate = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var downloads = 0;
        var parsed = await Parser.ParseAsync(
            "F(0) = 0, 0, 0\nF(1) = {\n    open 'https://katlang.org/decon/deferred.kat'\n    H, T, H\n}\nF(1)",
            new RunOptions
            {
                DownloadCode = async (_, token) =>
                {
                    downloads++;
                    entered.TrySetResult();
                    await gate.Task.WaitAsync(token);
                    return "h, *t = 1, 2, 3\npublic H = h\npublic T = t";
                },
            });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));
        Assert.Equal(0, downloads);
        var observations = new EvaluationObservations();
        var pending = Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), observations: observations).AsTask();
        try
        {
            await entered.Task.WaitAsync(TimeSpan.FromSeconds(30));
            Assert.False(pending.IsCompleted);
        }
        finally
        {
            gate.TrySetResult();
        }
        var (result, budget) = await pending.WaitAsync(TimeSpan.FromSeconds(30));
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        Assert.Equal("S[1, L[2, 3], 1]", SixRouteAgreement.Neutral(result.Value.Value));
        Assert.Equal(1, downloads);
        Assert.Equal(1, observations.DeconstructionFullBindCount);
        Assert.Equal(0, budget.CurrentDepth);
    }

    [Theory]
    [InlineData(DeconstructionMemoEligibilityTests.Route.Generic)]
    [InlineData(DeconstructionMemoEligibilityTests.Route.Optimized)]
    [InlineData(DeconstructionMemoEligibilityTests.Route.SuspendingAsync)]
    public async Task CapturedCopiedHelper_KeepsOrdinaryLaziness(DeconstructionMemoEligibilityTests.Route route)
    {
        var root = DeconstructionMemoEligibilityTests.Parse("Capture(meta op) = op.Invoke()\na, b = 1 / 0, 2\n0");
        var body = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "a").Value);
        var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
        var helper = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(call.Function).Algorithm);
        var changed = helper with
        {
            ParameterPatterns = [new CaptureParameterPattern("unused"), new CaptureParameterPattern("tail", Kind: ParameterKind.Collecting)],
            Output = [new Expr.Param("tail")],
        };
        Algorithm.User Program(Algorithm.User callee) => root with
        {
            Properties = [.. root.Properties, new Property("H", callee)],
            Output = [new Expr.Call(new Expr.Resolve("Capture"),
                [new Expr.Call(new Expr.Resolve("H"), [new Expr.Resolve("$deconstruct$0")])])],
        };
        var ordinary = await DeconstructionMemoEligibilityTests.Observe(
            new Expr.AlgorithmExpr(Program(changed with { AssignmentDeconstructionTarget = null })), route);
        var actual = await DeconstructionMemoEligibilityTests.Observe(new Expr.AlgorithmExpr(Program(changed)), route);
        Assert.Equal("ok L[] n=1 | ", ordinary.Comparable);
        Assert.Equal(ordinary.ToString(), actual.ToString());
    }

    [Theory]
    [InlineData(DeconstructionMemoEligibilityTests.Route.Generic)]
    [InlineData(DeconstructionMemoEligibilityTests.Route.Optimized)]
    [InlineData(DeconstructionMemoEligibilityTests.Route.SuspendingAsync)]
    public async Task CopiedHelperWithAnUnusedArgument_KeepsOrdinaryLaziness(DeconstructionMemoEligibilityTests.Route route)
    {
        var root = DeconstructionMemoEligibilityTests.Parse("a, b = 1 / 0, 2\na");
        var body = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "a").Value);
        var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
        var helper = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(call.Function).Algorithm);
        var changed = helper with
        {
            ParameterPatterns = ParameterPattern.FromDeclarations([
                new ParameterDeclaration("unused"), new ParameterDeclaration("tail", Kind: ParameterKind.Collecting)]),
            Output = [new Expr.Param("tail")],
        };
        var program = root with
        {
            Properties = [.. root.Properties.Select(p => p.Name == "a"
                ? p with { Value = body with { Output = [call with { Function = new Expr.AlgorithmExpr(changed) }] } }
                : p)],
        };
        var ordinary = await DeconstructionMemoEligibilityTests.Observe(
            new Expr.AlgorithmExpr(DeconstructionMemoEligibilityTests.WithoutDeconstructionMetadata(program)), route);
        var actual = await DeconstructionMemoEligibilityTests.Observe(new Expr.AlgorithmExpr(program), route);
        Assert.Equal("ok L[] n=1 | ", ordinary.Comparable);
        Assert.Equal(ordinary.ToString(), actual.ToString());
    }

    [Theory]
    [InlineData(DeconstructionMemoEligibilityTests.Route.Generic)]
    [InlineData(DeconstructionMemoEligibilityTests.Route.Optimized)]
    [InlineData(DeconstructionMemoEligibilityTests.Route.SuspendingAsync)]
    public async Task CopiedHelperWithDuplicateDeclarations_KeepsOrdinaryBodyChecks(DeconstructionMemoEligibilityTests.Route route)
    {
        var root = DeconstructionMemoEligibilityTests.Parse("a, b = 1, 2\na");
        var body = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "a").Value);
        var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
        var helper = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(call.Function).Algorithm);
        var value = new Algorithm.User(null, [], [], [], [new Expr.Num(3)]);
        var changed = helper with { Properties = [new Property("X", value), new Property("X", value)] };
        var program = root with
        {
            Properties = [.. root.Properties.Select(p => p.Name == "a"
                ? p with { Value = body with { Output = [call with { Function = new Expr.AlgorithmExpr(changed) }] } }
                : p)],
        };
        var ordinary = await DeconstructionMemoEligibilityTests.Observe(
            new Expr.AlgorithmExpr(DeconstructionMemoEligibilityTests.WithoutDeconstructionMetadata(program)), route);
        var actual = await DeconstructionMemoEligibilityTests.Observe(new Expr.AlgorithmExpr(program), route);
        Assert.StartsWith("err ", ordinary.Comparable);
        Assert.Equal(ordinary.Comparable, actual.Comparable);
    }
}
