using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>Independent S2 probes: operation order and preserved channels across view transport.</summary>
public class CallReferenceS2ReviewTests
{
    private const string Prelude = """
        Capture(meta op) = op
        Pair(a, b) = a + b
        Ignore(a, b) = 0
        Square(x) = x * x
        Apply(f, x) = f(x)
        """;

    private sealed record Observation(string Outcome, string Effects);

    private static async Task<Observation> Observe(string body, int route)
    {
        var effects = new List<string>();
        var operations = HostOperations.Create(
            HostOperation.Create("mark", (args, _) =>
            {
                effects.Add(SemanticExplorerHarness.Neutral(args[0]));
                return args[0];
            }, "x"),
            HostOperation.Create("supplied", (_, _) =>
            {
                effects.Add("supply");
                return new Result.SequenceValue([new Result.Atom(10), new Result.Atom(20)]);
            }));
        var source = Prelude + "\n" + body;
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(d => d.Message)));
        string outcome;
        if (route == 0)
        {
            outcome = KatLangEngine.Run(source, new RunOptions { HostOperations = operations }) switch
            {
                RunResult.Success success => "ok " + SemanticExplorerHarness.Neutral(success.Value),
                RunResult.EvalFailure failure => "err " + failure.Errors[0].Code,
                _ => throw new InvalidOperationException("The program did not reach evaluation."),
            };
        }
        else
        {
            var root = new Expr.AlgorithmExpr(parsed.Root);
            var (result, _) = route == 3
                ? await Evaluator.RunCountedObservedAsync(root,
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                    hostOperations: operations)
                : Evaluator.RunCountedObserved(root, enableOptimizations: route == 2, hostOperations: operations);
            outcome = result.IsOk ? "ok " + SemanticExplorerHarness.Neutral(result.Value.Value)
                : "err " + KatLangError.FromEvalError(result.Error).Code;
        }
        return new(outcome, string.Join(",", effects));
    }

    [Theory]
    [InlineData("R = Capture(Pair(supplied()*))\nR.Arguments[mark(1), mark(0)]", "ok S[20, 10]", "1,supply,0")]
    [InlineData("R = Capture(Pair(mark(10), mark(20)))\nR.Arguments[mark(1), mark(0), mark(1)]", "ok S[20, 10, 20]", "1,20,0,10,1")]
    [InlineData("R = Capture(Pair(mark(10), mark(20)))\nR.Arguments[mark(true), mark(0)]", "err TypeMismatch", "true")]
    [InlineData("R = Capture(Pair(1 / 0, mark(20)))\nR.Arguments[mark(0), mark(true)]", "err DivisionByZero", "0")]
    [InlineData("R = Capture(Pair(supplied()*))\nR.Arguments[mark(true), supplied()*]", "err TypeMismatch", "supply,true")]
    [InlineData("R = Capture(Pair(supplied()*))\nR.Arguments[()*]", "ok S[]", "")]
    [InlineData("R = Capture(Pair(supplied()*))\nR.Arguments[mark(9), mark(0)]", "err BadIndex", "9,supply")]
    public async Task SelectionFormsItsSupplyThenValidatesAndDemandsInOrder(string body, string expected, string effects)
    {
        for (var route = 0; route < 4; route++)
            Assert.Equal(new Observation(expected, effects), await Observe(body, route));
    }

    [Theory]
    [InlineData("R = Capture(Ignore(Square(3), 1 / 0))\nTake(meta x, y) = x\nA = Take(R.Arguments*)\nB = Take(R.Arguments*)\nA == B, A.Invoke(), R.Invoke()", "ok S[true, 9, 0]", "")]
    [InlineData("Make(f) = Capture(Apply(f, 3))\nR = Make(Square)\nInside(f) = Apply(R.Arguments*)\nInside({ x + 1 }), R.Invoke()", "ok S[9, 9]", "")]
    [InlineData("Make(f) = Capture(f(1, 2))\nR = Make(5)\nR.Arguments.count, R.Arguments[1]", "ok S[2, 2]", "")]
    [InlineData("Make(f) = Capture(f(1, 2))\nR = Make(5)\nR.Arguments.count + R.Invoke()", "err NotAnAlgorithm", "")]
    [InlineData("R = Capture(Pair(mark(3), mark(4)))\nUse(x, x, y, y) = x + y\nUse(R.Arguments[0], R.Arguments[0], R.Arguments[1], R.Arguments[1])", "ok 7", "3,4")]
    [InlineData("R = Capture(Pair(3, 4))\nPair([R.Arguments]**), R.Invoke()", "ok S[7, 7]", "")]
    [InlineData("R = Capture(Pair(3, 4))\nPair([R.Arguments]***)", "err TypeMismatch", "")]
    public async Task TransportPreservesMetaCallableOwnershipAndLayerBoundaries(string body, string expected, string effects)
    {
        for (var route = 0; route < 4; route++)
            Assert.Equal(new Observation(expected, effects), await Observe(body, route));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CompletedBuiltinAndViewPreparationShareTheSameCellObjects(bool asynchronous)
    {
        var checkedPlan = false;
        var operations = HostOperations.Create(HostOperation.Create("Grab", (_, _) =>
            throw new InvalidOperationException("The META receiver seam must intercept this call."), "operation"));
        var experiment = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Grab"] = cells =>
            {
                var owner = Assert.IsType<NeedCell>(cells[0]);
                var plan = Assert.IsType<Evaluator.InvocationPlan>(owner.Suspension);
                var view = Evaluator.ReifyMeta(owner).Value.ArgumentView;
                var ctx = plan.Caller;
                var value = asynchronous ? owner.DemandAsync().AsTask().GetAwaiter().GetResult() : owner.Demand();
                Assert.True(value.IsOk);
                Assert.Equal(new Result.Atom(2), value.Value.Value);
                var original = Assert.Single(plan.PreparedCells!);
                var first = asynchronous ? Evaluator.PrepareArgumentViewAsync(view, ctx).AsTask().GetAwaiter().GetResult()
                    : Evaluator.PrepareArgumentView(view, ctx);
                var second = asynchronous ? Evaluator.PrepareArgumentViewAsync(view, ctx).AsTask().GetAwaiter().GetResult()
                    : Evaluator.PrepareArgumentView(view, ctx);
                Assert.True(first.IsOk);
                Assert.True(second.IsOk);
                Assert.Same(original, Assert.Single(first.Value));
                Assert.Same(original, Assert.Single(second.Value));
                Assert.Equal(1, plan.SupplyFormations);
                checkedPlan = true;
                return new Result.Atom(0);
            },
        });
        var parsed = Parser.Parse("Grab(count([3, 4]))", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(d => d.Message)));
        using (InvocationPlanTestSeam.Activate(experiment))
        {
            var root = new Expr.AlgorithmExpr(parsed.Root);
            var (result, _) = asynchronous
                ? await Evaluator.RunCountedObservedAsync(root,
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: operations, observations: new EvaluationObservations())
                : Evaluator.RunCountedObserved(root, hostOperations: operations, observations: new EvaluationObservations());
            Assert.True(result.IsOk);
        }
        Assert.True(checkedPlan);
    }

    [Theory]
    [InlineData("R.Arguments == R.Arguments", "ok true", 0)]
    [InlineData("R.Arguments[]", "ok S[]", 0)]
    [InlineData("R.Arguments[true]", "err TypeMismatch", 0)]
    [InlineData("R.Arguments.count, R.Invoke(), Pair(R.Arguments*)", "ok S[2, 7, 7]", 1)]
    [InlineData("R.Arguments[1], R.Arguments.first", "ok S[4, 3]", 1)]
    public async Task DeferredSourceAdmissionOccursOnlyWhenTheViewNeedsItsSupply(string row, string expected, int expectedDownloads)
    {
        var downloads = 0;
        var run = await KatLangEngine.RunAsync(Prelude + "\n" + """
            F(0) = 0
            F(n) = {
                open 'https://katlang.org/s2-review/source.kat'
                V
            }
            R = Capture(Pair(F(1)*))
            """ + "\n" + row, new RunOptions
        {
            DownloadCode = async (_, _) =>
            {
                Interlocked.Increment(ref downloads);
                await Task.Yield();
                return "public V = 3, 4";
            },
        });
        var outcome = run switch
        {
            RunResult.Success success => "ok " + SemanticExplorerHarness.Neutral(success.Value),
            RunResult.EvalFailure failure => "err " + failure.Errors[0].Code,
            _ => throw new InvalidOperationException("Expected evaluation, got " + run),
        };
        Assert.Equal(expected, outcome);
        Assert.Equal(expectedDownloads, downloads);
    }

    [Fact]
    public async Task DeferredSourceCancellationThroughViewPreparationKeepsTheOriginalException()
    {
        using var tokens = new CancellationTokenSource();
        OperationCanceledException? observed = null;
        var downloads = 0;
        var operations = HostOperations.Create(HostOperation.Create("Grab", (_, _) =>
            throw new InvalidOperationException("The META receiver seam must intercept this call."), "operation"));
        var parsed = await Parser.ParseAsync(Prelude + "\n" + """
            F(0) = 0
            F(n) = {
                open 'https://katlang.org/s2-review/cancel.kat'
                (3, 4)
            }
            Grab(Pair(F(1)*))
            """, new RunOptions
        {
            HostOperations = operations,
            SourceProcessingCancellationToken = tokens.Token,
            DownloadCode = async (_, _) =>
            {
                Interlocked.Increment(ref downloads);
                await Task.Yield();
                tokens.Cancel();
                tokens.Token.ThrowIfCancellationRequested();
                return "public V = 1";
            },
        });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(d => d.Message)));
        Assert.Equal(0, downloads);
        using var active = InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam(
            new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
            {
                ["Grab"] = cells =>
                {
                    var reference = Evaluator.ReifyMeta(cells[0]).Value;
                    var view = reference.ArgumentView;
                    var ctx = reference.Plan.Caller;
                    observed = Assert.ThrowsAny<OperationCanceledException>(() =>
                        Evaluator.PrepareArgumentViewAsync(view, ctx).AsTask().GetAwaiter().GetResult());
                    var repeated = Assert.ThrowsAny<OperationCanceledException>(() =>
                        Evaluator.PrepareArgumentViewAsync(view, ctx).AsTask().GetAwaiter().GetResult());
                    Assert.Same(observed, repeated);
                    return new Result.Atom(0); // The run must reject this attempt to absorb source cancellation.
                },
            }));
        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations));
        Assert.NotNull(observed);
        Assert.Same(observed, thrown);
        Assert.Equal(tokens.Token, thrown.CancellationToken);
        Assert.Equal(1, downloads);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task OrdinaryPreparationFailureIsSharedByViewValueAndInvoke(bool asynchronous)
    {
        var effects = 0;
        var checkedPlan = false;
        var operations = HostOperations.Create(
            HostOperation.Create("mark", (args, _) => { effects++; return args[0]; }, "x"),
            HostOperation.Create("Grab", (_, _) => throw new InvalidOperationException("META receiver missing"), "operation"));
        var parsed = Parser.Parse(Prelude + "\nFail = mark(1) / 0, 2\nGrab(Pair(Fail()*))",
            new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(d => d.Message)));
        using var active = InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam(
            new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
            {
                ["Grab"] = cells =>
                {
                    var owner = Assert.IsType<NeedCell>(cells[0]);
                    var reference = Evaluator.ReifyMeta(owner).Value;
                    var plan = reference.Plan;
                    var ctx = plan.Caller;
                    var view = reference.ArgumentView;
                    var first = asynchronous ? Evaluator.PrepareArgumentViewAsync(view, ctx).AsTask().GetAwaiter().GetResult()
                        : Evaluator.PrepareArgumentView(view, ctx);
                    var second = asynchronous ? Evaluator.PrepareArgumentViewAsync(view, ctx).AsTask().GetAwaiter().GetResult()
                        : Evaluator.PrepareArgumentView(view, ctx);
                    Assert.True(first.IsError);
                    Assert.Same(first.Error, second.Error);
                    var invoke = asynchronous ? Evaluator.InvokeCallReferenceValueAsync(reference, ctx).AsTask().GetAwaiter().GetResult()
                        : Evaluator.InvokeCallReferenceValue(reference, ctx);
                    var value = asynchronous ? owner.DemandAsync().AsTask().GetAwaiter().GetResult() : owner.Demand();
                    Assert.Equal(KatLangErrorCode.DivisionByZero, KatLangError.FromEvalError(invoke.Error).Code);
                    Assert.Equal(KatLangErrorCode.DivisionByZero, KatLangError.FromEvalError(value.Error).Code);
                    Assert.Equal(1, plan.SupplyFormations);
                    Assert.Equal(1, effects);
                    checkedPlan = true;
                    return new Result.Atom(0);
                },
            }));
        var root = new Expr.AlgorithmExpr(parsed.Root);
        var (result, _) = asynchronous
            ? await Evaluator.RunCountedObservedAsync(root,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: operations, observations: new EvaluationObservations())
            : Evaluator.RunCountedObserved(root, hostOperations: operations, observations: new EvaluationObservations());
        Assert.True(result.IsOk); // An ordinary failure can be inspected by this internal seam.
        Assert.True(checkedPlan);
    }
}
