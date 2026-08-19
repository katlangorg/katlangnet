using KatLang.Tests.LanguageSpec;

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
