using KatLang.Tests.LanguageSpec;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Corpus-wide differential pin of the async TWIN FAMILY against the synchronous
/// evaluator (the semantic oracle), in the neutral encoding shared with the Lean
/// artifacts.
///
/// <para>Three-way comparison per case: (1) the async twin path (async-capable cache,
/// completing synchronously) must produce the sync DEFAULT path's outcome; (2) it must
/// charge exactly the operational counters of the sync GENERIC-strategies path
/// (optimizations disabled — the strategy mode the twin family mirrors); and (3) the
/// twin path must never touch the SYNCHRONOUS seam member. A fourth suite re-runs the
/// language-spec corpus with GENUINE suspension at every property access (thread-hopping
/// resumption) and requires identical outcomes and counters — proving suspension changes
/// no result and no accounting.</para>
/// </summary>
public class AsyncTwinDifferentialTests
{
    private static readonly IReadOnlyDictionary<string, SpecCase> SpecById =
        LanguageSpecCorpus.AllCases()
            .Where(static c => c.Outcome != SpecOutcome.ParseError)
            .ToDictionary(static c => c.Id, StringComparer.Ordinal);

    private static readonly IReadOnlyDictionary<string, ExplorerCase> ExplorerById =
        SemanticExplorerCorpus.AllCases().ToDictionary(static c => c.Id, StringComparer.Ordinal);

    public static TheoryData<string> SpecCaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var id in SpecById.Keys.OrderBy(static id => id, StringComparer.Ordinal))
            data.Add(id);
        return data;
    }

    public static TheoryData<string> ExplorerCaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var id in ExplorerById.Keys.OrderBy(static id => id, StringComparer.Ordinal))
            data.Add(id);
        return data;
    }

    [Theory]
    [MemberData(nameof(SpecCaseIds))]
    public async Task LanguageSpecCase_AsyncTwinPath_MatchesSyncOutcomeAndGenericCounters(string caseId)
        => await AssertTwinPathMatches(SpecById[caseId].Source);

    [Theory]
    [MemberData(nameof(ExplorerCaseIds))]
    public async Task ExplorerCase_AsyncTwinPath_MatchesSyncOutcomeAndGenericCounters(string caseId)
        => await AssertTwinPathMatches(ExplorerById[caseId].Source);

    [Fact]
    public async Task MathExp_AsyncTwinPath_MatchesSyncOutcomeAndGenericCounters()
        => await AssertTwinPathMatches("Math.Exp(1)\nexp(-1)");

    /// <summary>
    /// Bulk expression-work parity at SCALE. The corpus programs above stay far below
    /// one 4096-checkpoint block, so their step equality cannot see a per-node
    /// checkpoint asymmetry; a loop of 40960 iterations can. The twin's counted dispatch
    /// head used to delegate its sync-delegable leaves (<c>Num</c>, <c>StringLiteral</c>,
    /// <c>Grace</c>) to the plain <c>Eval</c> HEAD, which charged the node's checkpoint a
    /// second time, while the synchronous spine machine delivers the same leaf child
    /// through plain <c>Eval</c> exactly once — so <c>repeat({x + 1}, 40960, 0)</c>
    /// needed 41020 steps synchronously and 41030 on the twin, and one <c>MaxSteps</c>
    /// admitted the program on one path and rejected it on the other. Both heads now
    /// enter the shared UNCHARGED leaf core (<c>EvalLeafUncharged</c>). The synchronous
    /// counted head likewise entered the plain head for <c>NativeCall</c> (two charges)
    /// where the twin's own <c>NativeCall</c> case charged once; the <c>Math.Abs</c> row
    /// pins that second asymmetry, whose per-iteration surplus used to cancel the leaf
    /// surplus by coincidence (82010 on both paths before; 82000 on both now).
    /// </summary>
    [Theory]
    [InlineData("repeat({x + 1}, 40960, 0)", 41020L)]
    [InlineData("repeat({Math.Abs(x) + 1}, 40960, 0)", 82000L)]
    [InlineData("repeat({x + 'a'.count}, 40960, 0)", null)]
    [InlineData("G(y) = 1\nrepeat({x + G(x)}, 40960, 0)", null)]
    public async Task LargeLoop_AsyncTwinPath_ChargesExactlyTheSyncGenericSteps(string source, long? expectedSteps)
    {
        var ast = AsyncEvaluationHarness.Ast(source);

        var (sync, syncBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        Assert.False(sync.IsError, AsyncEvaluationHarness.NeutralOf(sync));
        if (expectedSteps is { } steps)
            Assert.Equal(steps, syncBudget.ConsumedSteps);

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (asyncResult, asyncBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(asyncResult));
        Assert.Equal(syncBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        Assert.Equal(syncBudget.PeakDepth, asyncBudget.PeakDepth);
        Assert.Equal(0, cache.SyncAccesses);

        // The minimum admitting step budget is the same on both paths: exactly the
        // consumed steps admit the program, one step less rejects it.
        foreach (var maxSteps in new[] { 1, syncBudget.ConsumedSteps / 2, syncBudget.ConsumedSteps - 1, syncBudget.ConsumedSteps, syncBudget.ConsumedSteps + 1 })
        {
            var limits = new EvaluationLimits { MaxSteps = maxSteps };
            var (syncAtLimit, syncLimitBudget) = Evaluator.RunCountedObserved(ast, limits, enableOptimizations: false);
            var (asyncAtLimit, asyncLimitBudget) = await AsyncEvaluationHarness.Complete(
                Evaluator.RunCountedObservedAsync(
                    ast,
                    limits,
                    zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));

            Assert.Equal(AsyncEvaluationHarness.NeutralOf(syncAtLimit), AsyncEvaluationHarness.NeutralOf(asyncAtLimit));
            Assert.Equal(syncLimitBudget.ConsumedSteps, asyncLimitBudget.ConsumedSteps);
            Assert.Equal(Math.Min(maxSteps, syncBudget.ConsumedSteps), syncLimitBudget.ConsumedSteps);
            Assert.Equal(syncLimitBudget.PeakDepth, asyncLimitBudget.PeakDepth);
            Assert.Equal(syncLimitBudget.MaterializedItems, asyncLimitBudget.MaterializedItems);
            Assert.Equal(syncLimitBudget.MaterializedStringChars, asyncLimitBudget.MaterializedStringChars);
            Assert.Equal(maxSteps < syncBudget.ConsumedSteps, syncAtLimit.IsError);
            if (syncAtLimit.IsError)
            {
                Assert.IsType<EvalError.EvaluationStepLimitExceeded>(syncAtLimit.Error);
                Assert.IsType<EvalError.EvaluationStepLimitExceeded>(asyncAtLimit.Error);
                Assert.Equal(DescribeErrorTree(syncAtLimit.Error), DescribeErrorTree(asyncAtLimit.Error));
            }
        }
    }

    // One iteration step plus six work checkpoints per iteration: binary dispatch,
    // three spine transitions, parameter and literal. Three setup checkpoints
    // (repeat dispatch, count and initial literal); the root program bypasses dispatch.
    [Theory]
    [InlineData(0, 0)]
    [InlineData(1, 1)]
    [InlineData(2, 2)]
    [InlineData(3, 3)]
    [InlineData(681, 681)]
    [InlineData(682, 682)]
    [InlineData(683, 684)]
    [InlineData(4096, 4102)]
    public async Task IncrementLoop_ExactSmallAndBulkBoundaryCosts(int iterations, long expectedSteps)
    {
        var ast = AsyncEvaluationHarness.Ast($"repeat({{x + 1}}, {iterations}, 0)");
        foreach (var limit in new[] { Math.Max(1, expectedSteps - 1), Math.Max(1, expectedSteps), expectedSteps + 1 })
        {
            var limits = new EvaluationLimits { MaxSteps = limit };
            var sync = Evaluator.RunCountedObserved(ast, limits, enableOptimizations: false);
            var twin = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                ast, limits, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));
            Assert.Equal(limit < expectedSteps, sync.Result.IsError);
            Assert.Equal(Math.Min(limit, expectedSteps), sync.Budget.ConsumedSteps);
            Assert.Equal(sync.Budget.ConsumedSteps, twin.Budget.ConsumedSteps);
            Assert.Equal(sync.Budget.PeakDepth, twin.Budget.PeakDepth);
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync.Result), AsyncEvaluationHarness.NeutralOf(twin.Result));
            if (sync.Result.IsError)
            {
                Assert.IsType<EvalError.EvaluationStepLimitExceeded>(sync.Result.Error);
                Assert.Equal(DescribeErrorTree(sync.Result.Error), DescribeErrorTree(twin.Result.Error));
            }
            else
                Assert.Equal(iterations.ToString(), SemanticExplorerHarness.Neutral(sync.Result.Value.Value));
        }
    }

    [Theory]
    [InlineData("repeat({if(x < 2000, x + 1, 1 / 0)}, 4096, 0)")]
    [InlineData("repeat({-x}, 4096, 'bad')")]
    [InlineData("repeat({Math.Abs(x)}, 4096, 'bad')")]
    [InlineData("F(x) = 1 / x\nrepeat({F(x)}, 4096, 0)")]
    public async Task RepeatedBodyFailures_MatchFullDiagnosticsAndCounters(string source)
    {
        var ast = AsyncEvaluationHarness.Ast(source);
        var sync = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var twin = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            ast, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));
        Assert.True(sync.Result.IsError);
        Assert.True(twin.Result.IsError);
        Assert.Equal(DescribeErrorTree(sync.Result.Error), DescribeErrorTree(twin.Result.Error));
        Assert.Equal(sync.Budget.ConsumedSteps, twin.Budget.ConsumedSteps);
        Assert.Equal(sync.Budget.PeakDepth, twin.Budget.PeakDepth);
        Assert.Equal(sync.Budget.MaterializedItems, twin.Budget.MaterializedItems);
        Assert.Equal(sync.Budget.MaterializedStringChars, twin.Budget.MaterializedStringChars);
    }

    [Theory]
    [MemberData(nameof(SpecCaseIds))]
    public async Task LanguageSpecCase_GenuineSuspensionAtEveryPropertyAccess_ChangesNothing(string caseId)
    {
        var source = SpecById[caseId].Source;
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
            return;

        var ast = new Expr.AlgorithmExpr(parsed.Root);
        var (syncGeneric, syncBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var syncDefault = Evaluator.RunCounted(ast);

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var (asyncResult, asyncBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(syncDefault), AsyncEvaluationHarness.NeutralOf(asyncResult));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(syncGeneric), AsyncEvaluationHarness.NeutralOf(asyncResult));

        // Host-side suspension inside the seam changes no evaluator accounting.
        Assert.Equal(syncBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        Assert.Equal(syncBudget.PeakDepth, asyncBudget.PeakDepth);
        Assert.Equal(syncBudget.MaterializedItems, asyncBudget.MaterializedItems);
        Assert.Equal(syncBudget.MaterializedStringChars, asyncBudget.MaterializedStringChars);
    }

    private static async Task AssertTwinPathMatches(string source)
    {
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
            return;

        var ast = new Expr.AlgorithmExpr(parsed.Root);

        var syncDefault = Evaluator.RunCounted(ast);
        var (syncGeneric, syncBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);

        // The optimized and generic sync strategies must agree on the outcome (pinned
        // elsewhere; re-checked here because the twin comparison leans on it).
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(syncDefault), AsyncEvaluationHarness.NeutralOf(syncGeneric));

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (asyncResult, asyncBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(syncDefault), AsyncEvaluationHarness.NeutralOf(asyncResult));

        // Value-level equality, not just neutral-encoding equality.
        if (syncDefault.IsOk)
        {
            Assert.True(Result.ValueComparer.Equals(syncDefault.Value.Value, asyncResult.Value.Value));
            Assert.Equal(syncDefault.Value.EmittedCount, asyncResult.Value.EmittedCount);
        }

        // Operational counters equal the sync GENERIC strategies — the mode the twin
        // family mirrors; limit verdicts are strategy-independent by construction.
        Assert.Equal(syncBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        Assert.Equal(syncBudget.PeakDepth, asyncBudget.PeakDepth);
        Assert.Equal(syncBudget.MaterializedItems, asyncBudget.MaterializedItems);
        Assert.Equal(syncBudget.MaterializedStringChars, asyncBudget.MaterializedStringChars);

        // The async twin path must never consult the SYNCHRONOUS seam member.
        Assert.Equal(0, cache.SyncAccesses);
    }
}
