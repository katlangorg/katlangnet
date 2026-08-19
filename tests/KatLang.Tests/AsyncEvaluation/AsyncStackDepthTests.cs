namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Stack-shape safety of the async twin family. The SYNCHRONOUS evaluator's calibrated
/// guarantees are untouched (its code is unchanged and its own pins keep running); these
/// tests characterize the TWIN path, whose synchronously-completing async frames are
/// larger than their synchronous counterparts:
///
/// <list type="bullet">
///   <item>On the documented supported environment (1 MiB thread), the heaviest
///   recursion shapes must complete or fail with a STRUCTURED error under the default
///   deterministic depth ceiling — never a process-terminating overflow. The
///   <c>TryEnsureSufficientExecutionStack</c> backstop shared with the synchronous
///   family is what converts an outgrown stack into
///   <see cref="EvalError.EvaluationStackExhausted"/>.</item>
///   <item>Pure expression SPINES stay iterative in the twin machine, so a deep flat
///   chain evaluates on a 384 KiB thread exactly as the synchronous machine's pin
///   demonstrates for the synchronous path.</item>
///   <item>On an ordinary test thread, the twin path's verdicts for depth-limited
///   recursion equal the synchronous verdicts exactly.</item>
/// </list>
/// </summary>
public class AsyncStackDepthTests
{
    private static EvalResult<Evaluator.CountedResult> RunTwinSynchronouslyCompleting(
        Expr ast, EvaluationLimits? limits = null)
    {
        var pending = Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache(), limits);

        // Pass-through seam: the twin path completes synchronously, so the whole spine
        // consumed the CURRENT thread's stack — which is exactly what these probes measure.
        Assert.True(pending.IsCompleted);
        return pending.GetAwaiter().GetResult();
    }

    [Fact]
    public void TwinPath_DepthLimitedRecursion_AtReducedDeterministicCeiling_MatchesSyncVerdict()
    {
        // At a reduced deterministic ceiling the twin path's larger frames still fit
        // any supported stack comfortably, so the verdict is the DETERMINISTIC depth
        // error on both paths — exact equality.
        const string source = "F(0) = 0\nF(n) = F(n - 1)\nF(500)";
        var ast = AsyncEvaluationHarness.Ast(source);
        var limits = new EvaluationLimits { MaxDepth = 32 };

        var sync = Evaluator.RunCounted(ast, new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(), limits);
        var async = RunTwinSynchronouslyCompleting(ast, limits);

        Assert.Equal("err evaluationDepthExceeded", AsyncEvaluationHarness.NeutralOf(sync));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
    }

    [Fact]
    public void TwinPath_DepthLimitedRecursion_AtDefaultCeilingOnDefaultThread_IsStructured()
    {
        // CHARACTERIZATION FINDING (reported in the Phase 2 notes): the twin family's
        // synchronously-completing async frames are larger than their synchronous
        // counterparts, so on a default-sized thread a deep sync-completing chain can
        // reach the shared TryEnsureSufficientExecutionStack backstop BEFORE the
        // deterministic 128-level ceiling. The outcome is then the STRUCTURED
        // stack-exhausted error where the synchronous path reports the deterministic
        // depth error — both resource-limit verdicts of the same safety envelope,
        // never a process crash. A genuine suspension unwinds the evaluator frames
        // leading to the await, but continuation placement remains host/runtime-owned,
        // so the twin-only stack checks still protect resumed evaluation.
        const string source = "F(0) = 0\nF(n) = F(n - 1)\nF(500)";
        var ast = AsyncEvaluationHarness.Ast(source);

        var sync = Evaluator.RunCounted(ast);
        var async = RunTwinSynchronouslyCompleting(ast);

        Assert.True(sync.IsError);
        Assert.True(async.IsError);
        Assert.Equal("evaluationDepthExceeded", SemanticExplorerHarness.ErrorCategory(sync.Error));
        Assert.Contains(
            SemanticExplorerHarness.ErrorCategory(async.Error),
            new[] { "evaluationDepthExceeded", "evaluationStackExhausted" });
    }

    /// <summary>
    /// The four measured heaviest recursion shapes from the depth-ceiling calibration
    /// (collection-callback recursion, recursion through <c>if</c>, dotted recursion,
    /// plain clause recursion), each driven to the deterministic default ceiling.
    /// </summary>
    public static TheoryData<string, string> HeaviestRecursionShapes() => new()
    {
        { "plain-clause", "F(0) = 0\nF(n) = F(n - 1)\nF(500)" },
        { "through-if", "F(n) = if(n, F(n - 1), 0)\nF(500)" },
        { "dotted", "Lib = {public F(n) = if(n, Lib.F(n - 1), 0)}\nLib.F(500)" },
        { "collection-callback", "F(n) = if(n, [n - 1].map(F).first, 0)\nF(500)" },
    };

    [Theory]
    [MemberData(nameof(HeaviestRecursionShapes))]
    public void TwinPath_HeaviestShapes_OnOneMiBThread_ProduceStructuredOutcomes(string shapeId, string source)
    {
        _ = shapeId;
        var ast = AsyncEvaluationHarness.Ast(source);

        EvalResult<Evaluator.CountedResult>? syncOutcome = null;
        EvalResult<Evaluator.CountedResult>? asyncOutcome = null;

        AstStructuralDepthProcessTests.RunOnThreadWithStack(1_048_576, () =>
        {
            syncOutcome = Evaluator.RunCounted(ast);
        });

        AstStructuralDepthProcessTests.RunOnThreadWithStack(1_048_576, () =>
        {
            asyncOutcome = RunTwinSynchronouslyCompleting(ast);
        });

        // Both paths: a structured outcome, never an unhandled overflow (an overflow
        // would have terminated the process before these assertions ran). The twin
        // path's larger frames may legitimately trade a depth verdict for the
        // structured stack backstop on this minimum-supported stack; both are
        // resource-limit verdicts of the same run-safety envelope.
        Assert.True(syncOutcome!.Value.IsError);
        Assert.True(asyncOutcome!.Value.IsError);

        var syncCategory = SemanticExplorerHarness.ErrorCategory(syncOutcome.Value.Error);
        var asyncCategory = SemanticExplorerHarness.ErrorCategory(asyncOutcome.Value.Error);
        Assert.Contains(syncCategory, new[] { "evaluationDepthExceeded", "evaluationStackExhausted" });
        Assert.Contains(asyncCategory, new[] { "evaluationDepthExceeded", "evaluationStackExhausted" });
    }

    [Fact]
    public void TwinPath_DeepFlatExpressionSpine_On384KiBThread_MatchesSync()
    {
        // 250 additions: a flat operator chain at the language's supported chain depth
        // class. The twin spine machine is iterative like the synchronous one, so this
        // must evaluate on the same 384 KiB thread the synchronous iterative-spine pin
        // uses — one async driver frame, O(1) stack per spine node.
        var source = string.Join(" + ", Enumerable.Repeat("1", 250));
        var ast = AsyncEvaluationHarness.Ast(source);
        var sync = Evaluator.RunCounted(ast);
        Assert.True(sync.IsOk);

        EvalResult<Evaluator.CountedResult>? asyncOutcome = null;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(393_216, () =>
        {
            asyncOutcome = RunTwinSynchronouslyCompleting(ast);
        });

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(asyncOutcome!.Value));
    }

    [Fact]
    public void TwinPath_NestedAlgorithmBodies_OnOneMiBThread_StructuredOrSuccess()
    {
        // Nested zero-declaration algorithm bodies at 120 levels (2 counted structural
        // units per level — the calibration's "deepest remaining recursive shape"),
        // host-built because the parser's own nesting budget rejects the equivalent
        // brace source before evaluation is reached. The twin path must either
        // evaluate it or fail structurally on this minimum-supported stack.
        Expr ast = new Expr.Num(42);
        for (var level = 0; level < 120; level++)
        {
            ast = new Expr.AlgorithmExpr(new Algorithm.User(
                Parent: null, Parameters: [], Opens: [], Properties: [], Output: [ast]));
        }

        var sync = Evaluator.RunCounted(ast);

        EvalResult<Evaluator.CountedResult>? asyncOutcome = null;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(1_048_576, () =>
        {
            asyncOutcome = RunTwinSynchronouslyCompleting(ast);
        });

        if (asyncOutcome!.Value.IsOk)
        {
            Assert.Equal(
                AsyncEvaluationHarness.NeutralOf(sync),
                AsyncEvaluationHarness.NeutralOf(asyncOutcome.Value));
        }
        else
        {
            Assert.Equal(
                "evaluationStackExhausted",
                SemanticExplorerHarness.ErrorCategory(asyncOutcome.Value.Error));
        }
    }
}
