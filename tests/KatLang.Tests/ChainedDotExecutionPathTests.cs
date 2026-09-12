using KatLang.Semantics;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>Chain resolution across value boundaries, ownership, and execution strategies.</summary>
public class ChainedDotExecutionPathTests
{
    private const string Lib = "Lib = {\n public Sub = {\n  public Q = 7\n  public F(x, y) = x * 10 + y\n  3\n }\n}\n";

    [Theory]
    [InlineData("Lib.Sub.Q", "7")]
    [InlineData("((Lib.Sub)).Q", "7")]
    [InlineData("Lib~.Sub.Q", "7")]
    [InlineData("Lib.~Sub.Q", "7")]
    [InlineData("Lib.~~Sub.~Q", "7")]
    [InlineData("Q(x) = 99\nLib.Sub.Q", "7")]
    [InlineData("Ext(x) = x + 1\nLib.Sub.Q.Ext.Ext", "9")]
    [InlineData("Q(x) = x + 1\nLib.Sub().Q", "4")]
    [InlineData("Q(x) = x + 1\nLib.Sub.F(2, 3).Q", "24")]
    [InlineData("F(a, b, c) = a * 100 + b * 10 + c\nLib.Sub.F(2, 3)", "23")]
    [InlineData("F(a, b, c) = a * 100 + b * 10 + c\n(3, 4).count.F(2, 3)", "223")]
    [InlineData("Call0(f) = f()\nCall0(Lib.Sub.Q)", "7")]
    [InlineData("Call0(f) = f()\nForward(f) = Call0(f)\nForward(Lib.Sub.Q)", "7")]
    [InlineData("Alias = Lib.Sub\nQ(x) = x + 1\nAlias.Q", "4")]
    [InlineData("if(0, Lib.Sub.F(0), Lib.Sub.Q)", "7")]
    [InlineData("Step(x) = x + Lib.Sub.Q\nrepeat(Step, 3, 0)", "21")]
    [InlineData("[1, 2].map({x + Lib.Sub.Q})", "[8, 9]")]
    [InlineData("K(Sub, Q) = Lib.Sub.Q\nK(99, 100)", "7")]
    [InlineData("K(Lib) = Lib.Sub.Q\nK({public Sub = {public Q = 11}})", "11")]
    [InlineData("E = {public Q(x) = 99}\nK = {\n open E\n Lib.Sub.Q\n}\nK", "7")]
    [InlineData("E = {public Q(x) = 99}\nK = {\n open Lib.Sub, E\n Lib.Sub.Q\n}\nK", "7")]
    [InlineData("F(x) = {\n public Structural = 88\n x + 1\n}\nStructural(x) = x * 10\n3.F.Structural", "40")]
    [InlineData("K = {\n Need = z\n Step = Lib.Sub.Q + Need\n Step\n}\nK(5)", "12")]
    [InlineData("t(x) = 99\nOuter(t) = {\n Inner = Lib.Sub.t\n Inner\n}\nOuter({x + 1})", "4")]
    [InlineData("Collect(*items) = items\nLib.Sub.Q.Collect", "[7]")]
    [InlineData("Collect(*items) = items\n(1, 2, 3).Collect.count", "3")]
    [InlineData("Collect(*items) = items\n((1, 2, 3)).Collect.count", "1")]
    public async Task ChainMatrix_MatchesGenericOptimizedAndSuspendingEvaluation(string tail, string expected)
    {
        var source = Lib + tail;
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(expected, success.ToDisplayString());
        var ast = AsyncEvaluationHarness.Ast(source);
        var (generic, budget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (optimized, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: true);
        var (twin, twinBudget) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            ast, zeroArgPropertyResultCache: new SuspendingAsyncZeroArgPropertyResultCache()));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(optimized));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(twin));
        Assert.Equal(budget.ConsumedSteps, twinBudget.ConsumedSteps);
        Assert.Equal(budget.PeakDepth, twinBudget.PeakDepth);
    }

    [Theory]
    [InlineData("Lib.Sub.Q", "7", 1)]
    [InlineData("Lib.Sub.string", "5", 1)]
    [InlineData("Lib.Sub.F(2, 3).string", "23", 0)]
    [InlineData("Lib.Sub.E.E", "7", 1)]
    [InlineData("Lib.Sub.Q, Lib.Sub.Q", "7\n7", 1)]
    public async Task HostCall_SuspendsWithoutReplayingReceiverOrContainer(string tail, string expected, int calls)
    {
        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var count = 0;
        var operations = HostOperations.Create(HostOperation.CreateAsync("Data", (_, _) =>
        {
            count++;
            return new ValueTask<Result>(gate.Task);
        }));
        var source = Lib.Replace("public Q = 7", "public Q = Data() + 2").Replace("  3", "  Data()")
            + "E(x) = x + 1\n" + tail;
        var pending = KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations });
        Assert.Equal(calls, count);
        if (calls > 0) Assert.False(pending.IsCompleted);
        gate.SetResult(Atom(5));
        var success = Assert.IsType<RunResult.Success>(await pending);
        Assert.Equal(expected, success.ToDisplayString().Replace("\r\n", "\n", StringComparison.Ordinal));
        Assert.Equal(calls, count);
    }

    [Fact]
    public async Task DeferredModule_StaysIndeterminateUntilSelectionThenNavigatesStructurally()
    {
        const string source = "F(0) = {\n M = load('https://example.test/a')\n M.Sub.Q\n}\nF(1) = 99\nQ(x) = 80\nF(1), F(0)";
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["example.test"],
            DownloadCode = async (_, _) =>
            {
                downloads++;
                await Task.Yield();
                return "public Sub = {public Q = 7}";
            },
        };
        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors);
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Equal(IdentifierClassification.DeferredModuleReference, model.FindResolutionAt(3, 8)!.Classification);
        Assert.Equal(0, downloads);
        var result = await Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(1, downloads);
        Assert.Equal("S[99, 7]", SemanticExplorerHarness.Neutral(result.Value));
    }

    [Fact]
    public void InaccessibleInUnusedNeighborDoesNotBreakValidRoot()
    {
        const string source = "G(x) = {\n public Sub = {\n  public Q = 1\n  x\n }\n 0\n}\nUnused = G.Sub.Q\n7";
        Assert.Equal("7", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Fact]
    public void HigherOrderWrapperDoesNotAcquireStructuralMemberSignature()
    {
        var result = EvalFull(Lib + "Call1(f) = f(9)\nCall1(Lib.Sub.F)");
        Assert.True(result.IsError);
        var error = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(0, error.Expected);
        Assert.Equal(1, error.Actual);
    }

    [Theory]
    [InlineData("Lib.Sub.filter({x > 0}).count", 1)]
    [InlineData("Lib.Sub.Q.filter({x > 0}).count", 1)]
    [InlineData("Lib.Sub.F(2, 3).filter({x > 0}).count", 1)]
    [InlineData("Lib.Sub.E.filter({x > 0}).count", 1)]
    public void FusionActuallyEngages(string tail, int expectedHits)
    {
        var ast = AsyncEvaluationHarness.Ast(Lib + "E(x) = x + 1\n" + tail);
        var diagnostics = new KatLang.Optimizations.Sequences.SequencePipelineDiagnostics();
        var (fused, _) = Evaluator.RunCountedObserved(ast, sequenceDiagnostics: diagnostics);
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(fused));
        Assert.Equal(expectedHits, diagnostics.GetSnapshot().FilterCountFusionHits);
    }

    [Fact]
    public void SuccessfulStructuralFilter_ShutsOutBuiltinFusion()
    {
        const string source = "Lib = {\n public Sub = {\n  public filter(f) = [9, 10, 11]\n  3\n }\n}\nLib.Sub.filter({x > 0}).count";
        var ast = AsyncEvaluationHarness.Ast(source);
        var diagnostics = new KatLang.Optimizations.Sequences.SequencePipelineDiagnostics();
        var (fused, _) = Evaluator.RunCountedObserved(ast, sequenceDiagnostics: diagnostics);
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        Assert.Equal("ok raw=3 n=1", AsyncEvaluationHarness.NeutralOf(generic));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(fused));
        Assert.Equal(0, diagnostics.GetSnapshot().FilterCountFusionHits);
    }

    [Theory]
    [InlineData(2)]
    [InlineData(8)]
    [InlineData(24)]
    public void DeepStructuralChains_NeedNoLexicalMemberBindings(int depth)
    {
        var body = "public Leaf = 7";
        for (var i = depth - 1; i >= 0; i--)
            body = $"public N{i} = {{\n{body}\n}}";
        var path = "Root." + string.Join(".", Enumerable.Range(0, depth).Select(i => $"N{i}")) + ".Leaf";
        var source = $"Root = {{\n{body}\n}}\nK = {path}\nK";
        var parsed = SourceProvenance.ParseValid(source);
        Assert.Empty(parsed.Root.Params);
        Assert.Empty(Assert.Single(parsed.Root.Properties, p => p.Name == "K").Value.Params);
        Assert.Equal("7", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }
}
