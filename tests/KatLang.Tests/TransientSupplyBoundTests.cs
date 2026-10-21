using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// SEC-01 (October 2026): every TRANSIENT item supply — a call's effective argument supply, a postfix
/// selection's selector supply, a loop step's row supply, and the slot accumulators of list literals,
/// output captures and written groups — checks its WHOLE size before retaining any spread expansion,
/// including written prefix/suffix slots (<see cref="EvaluationBudget.AdmitsTransientExpansion"/>).
/// Purely written supplies remain source-bounded; internal joins bound all leaf occurrences.
/// Once a supply overflows it forms
/// COUNT-ONLY to its end (later spreads still run, in written order) and is refused there with
/// <see cref="EvalError.CollectionSizeLimitExceeded"/> over its full size.
///
/// <para>Every program runs on the synchronous generic and optimized routes and on the async twin, which
/// must agree on the outcome (with the refusal's position), the host effects, the cumulative
/// materialization, and the transient peak. The ALLOCATION EVIDENCE is
/// <see cref="EvaluationBudget.PeakTransientExpansion"/>: the largest admitted total size of an expanded
/// supply, asserted never to exceed the effective limit — the unbounded formation
/// built the whole oversized supply before any check.</para>
/// </summary>
public class TransientSupplyBoundTests(ITestOutputHelper output)
{
    private sealed class Effects
    {
        public int Traces;

        public override string ToString() => $"traces={Traces}";
    }

    private sealed record Outcome(string Text, long Materialized, int Peak, string Effects);

    private static HostOperations Operations(Effects effects) => HostOperations.Create(
        HostOperation.Create("trace", (args, _) => { effects.Traces++; return args[0]; }, "x"));

    private static Expr Program(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static string Describe(EvalError error)
    {
        var span = error.Span;
        var inner = error;
        while (inner is EvalError.WithContext context)
        {
            inner = context.Inner;
            span ??= inner.Span;
        }

        var at = span is { } s ? $" @{s.Start.Line}:{s.Start.Column}" : "";
        return inner switch
        {
            EvalError.CollectionSizeLimitExceeded limit => $"err limit {limit.Limit}/{limit.Requested}{at}",
            EvalError.ArityMismatch arity => $"err arity {arity.Expected}/{arity.Actual}",
            _ => "err " + inner.GetType().Name,
        };
    }

    private static string Text(EvalResult<Evaluator.CountedResult> result)
        => result.IsOk ? "ok " + SemanticExplorerHarness.Neutral(result.Value.Value) : Describe(result.Error);

    private static Outcome Sync(string source, EvaluationLimits? limits, bool optimized, LoopOptimizationDiagnostics? loops = null)
    {
        var effects = new Effects();
        var operations = Operations(effects);
        var (result, budget) = Evaluator.RunCountedObserved(
            Program(source, operations), limits, enableOptimizations: optimized, loopDiagnostics: loops, hostOperations: operations);
        return new(Text(result), budget.MaterializedItems, budget.PeakTransientExpansion, effects.ToString());
    }

    private static Outcome AsyncTwin(string source, EvaluationLimits? limits)
    {
        var effects = new Effects();
        var operations = Operations(effects);
        var (result, budget) = Evaluator.RunCountedObservedAsync(
            Program(source, operations), limits, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
            hostOperations: operations).AsTask().GetAwaiter().GetResult();
        return new(Text(result), budget.MaterializedItems, budget.PeakTransientExpansion, effects.ToString());
    }

    /// <summary>
    /// Runs <paramref name="source"/> on every route, requires them to agree, and requires the transient
    /// peak to stay within the effective collection limit.
    /// </summary>
    private static Outcome Observe(string source, int? maxCollectionItems = null)
    {
        var limits = maxCollectionItems is { } max ? new EvaluationLimits { MaxCollectionItems = max } : null;
        var generic = Sync(source, limits, optimized: false);
        foreach (var (route, other) in new[]
        {
            ("optimized", Sync(source, limits, optimized: true)),
            ("async twin", AsyncTwin(source, limits)),
        })
        {
            Assert.True(generic == other, $"{route}: {other} vs generic {generic}");
        }

        Assert.InRange(generic.Peak, 0, maxCollectionItems ?? EvaluationLimits.MaxSupportedCollectionItems);
        return generic;
    }

    private static void AssertOutcome(string expected, string source, int? maxCollectionItems = null, string? effects = null, int? peak = null)
    {
        var outcome = Observe(source, maxCollectionItems);
        Assert.Equal(expected, outcome.Text);
        if (effects is not null) Assert.Equal(effects, outcome.Effects);
        if (peak is not null) Assert.Equal(peak, outcome.Peak);
    }

    // ── T1: list literals ────────────────────────────────────────────────────

    [Fact]
    public void ListLiteral_RepeatedSpread_RefusedBeforeTheAccumulatorPassesTheLimit()
        => AssertOutcome("err limit 5/6 @2:1", "A = [1, 2, 3]\n[A*, A*]", maxCollectionItems: 5, peak: 3);

    [Fact]
    public void ListLiteral_RepeatedSpread_AtTheBoundarySucceeds()
        => AssertOutcome("ok L[1, 2, 3, 1, 2, 3]", "A = [1, 2, 3]\n[A*, A*]", maxCollectionItems: 6, peak: 6);

    [Fact]
    public void ListLiteral_OverflowedElementsStillRunInWrittenOrder()
        => AssertOutcome("err limit 5/7 @2:1", "A = [1, 2, 3]\n[A*, A*, trace(9)]", maxCollectionItems: 5, effects: "traces=1");

    // ── T2: captures and written groups ──────────────────────────────────────

    [Fact]
    public void SequenceCapture_RepeatedSpread_Refused()
        => AssertOutcome("err limit 5/6 @2:6", "A = (1, 2, 3)\nB = (A*, A*)\nB.count", maxCollectionItems: 5, peak: 3);

    [Fact]
    public void SequenceCapture_RepeatedSpread_AtTheBoundarySucceeds()
        => AssertOutcome("ok 6", "A = (1, 2, 3)\nB = (A*, A*)\nB.count", maxCollectionItems: 6);

    [Fact]
    public void WrittenGroupInsideAList_RepeatedSpread_Refused()
        => AssertOutcome("err limit 5/6 @2:3", "A = (1, 2, 3)\n[(A*, A*)]", maxCollectionItems: 5, peak: 3);

    [Fact]
    public async Task SequenceJoin_HostBuilt_RepeatedSpread_Refused()
    {
        var list = new Expr.ListLiteral(OutputBundle.TakeOwnership([new Expr.Num(1), new Expr.Num(2), new Expr.Num(3)]));
        var join = new Expr.SequenceConstruct(new Expr.SequenceSpread(list), new Expr.SequenceSpread(list));
        var ast = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [join]));
        foreach (var optimized in new[] { false, true })
        {
            var refused = Evaluator.RunCountedObserved(ast, new EvaluationLimits { MaxCollectionItems = 5 }, enableOptimizations: optimized);
            Assert.True(refused.Result.IsError);
            var limit = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(refused.Result.Error);
            Assert.Equal((5, 6L), (limit.Limit, limit.Requested));
            Assert.InRange(refused.Budget.PeakTransientExpansion, 0, 5);
            var admitted = Evaluator.RunCountedObserved(ast, new EvaluationLimits { MaxCollectionItems = 6 }, enableOptimizations: optimized);
            Assert.True(admitted.Result.IsOk);
            Assert.Equal(6, admitted.Budget.PeakTransientExpansion);
        }
        var asyncRefused = await Evaluator.RunCountedObservedAsync(ast,
            new EvaluationLimits { MaxCollectionItems = 5 }, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.True(asyncRefused.Result.IsError);
        Assert.Equal("err limit 5/6", Describe(asyncRefused.Result.Error));
        Assert.InRange(asyncRefused.Budget.PeakTransientExpansion, 0, 5);
    }

    private static (long BeforeFirstEffect, int Peak) ObserveJoinDag(int depth, bool spread)
    {
        long started = 0, beforeFirst = 0;
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.Create("trace", (args, _) =>
        {
            if (calls++ == 0)
                beforeFirst = GC.GetAllocatedBytesForCurrentThread() - started;
            return args[0];
        }, "x"));
        Expr node = new Expr.Call(new Expr.Resolve("trace"), OutputBundle.TakeOwnership([new Expr.Num(1)]));
        if (spread) node = new Expr.SequenceSpread(node);
        for (var i = 0; i < depth; i++)
            node = new Expr.SequenceConstruct(node, node);
        var ast = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [node]));
        started = GC.GetAllocatedBytesForCurrentThread();
        var (result, budget) = Evaluator.RunCountedObserved(ast,
            new EvaluationLimits { MaxCollectionItems = 4 }, enableOptimizations: false, hostOperations: operations);
        Assert.True(result.IsError);
        Assert.Equal($"err limit 4/{1 << depth}", Describe(result.Error));
        Assert.Equal(1 << depth, calls);
        return (beforeFirst, budget.PeakTransientExpansion);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SequenceJoin_SharedDag_DoesNotFlattenLeafMetadataBeforeEvaluation(bool spread)
    {
        // A bounded allocation probe, not an OOM test: twelve shared joins have 4096
        // leaf occurrences. No occurrence-sized buffer is needed before the first effect.
        ObserveJoinDag(3, spread); // Warm the run and callback before measuring.
        var small = ObserveJoinDag(8, spread);
        var large = ObserveJoinDag(12, spread);
        output.WriteLine($"spread={spread}: before first effect, 256 leaves = {small.BeforeFirstEffect} B; 4096 leaves = {large.BeforeFirstEffect} B; retained peak = {large.Peak}");
        Assert.True(large.BeforeFirstEffect < small.BeforeFirstEffect + 16_384,
            $"Before first effect: 256 leaves = {small.BeforeFirstEffect} B; 4096 leaves = {large.BeforeFirstEffect} B");
        Assert.Equal(4, large.Peak);
    }

    // ── T3: the effective argument supply under the DEFAULT ceiling ──────────

    [Fact]
    public void CallSupply_DefaultCeiling_ProtectsTheCallerSupply()
        => AssertOutcome("err limit 100000/200000 @3:7",
            "A = range(1, 100000)\nF(*items) = items.count\nF(A*, A*)", peak: 100_000);

    [Fact]
    public void CallSupply_DefaultCeiling_AnIgnoredCollectorIsStillRefused()
        => AssertOutcome("err limit 100000/200000 @3:7", "A = range(1, 100000)\nF(*items) = 1\nF(A*, A*)");

    [Fact]
    public void CallSupply_DefaultCeiling_OneFullSpreadSucceeds()
        => AssertOutcome("ok 100000", "A = range(1, 100000)\nF(*items) = items.count\nF(A*)", peak: 100_000);

    [Fact]
    public void CallSupply_DefaultCeiling_IncludesWrittenSlots()
        => AssertOutcome("err limit 100000/100001 @3:6", "A = range(1, 100000)\nF(x, *xs) = 1\nF(0, A*)");

    // ── T4: fixed arity, ignored collectors, precedence ──────────────────────

    [Fact]
    public void FixedArity_OversizedSupply_IsTheResourceRefusal()
        => AssertOutcome("err limit 5/6 @3:7", "A = [1, 2, 3]\nF(a, b) = a\nF(A*, A*)", maxCollectionItems: 5);

    [Fact]
    public void FixedArity_WithinTheLimit_KeepsItsArityVerdict()
        => AssertOutcome("err arity 2/6", "A = [1, 2, 3]\nF(a, b) = a\nF(A*, A*)", maxCollectionItems: 6);

    [Fact]
    public void LaterSpreadFailure_StillWinsOverTheOverflow()
        => AssertOutcome("err DivByZero", "A = [1, 2, 3]\nF(*xs) = 1\nF(A*, A*, (1 / 0)*)", maxCollectionItems: 5);

    [Fact]
    public void LaterSpread_StillRunsCountOnly_ThenTheSupplyIsRefused()
        => AssertOutcome("err limit 5/7 @3:7", "A = [1, 2, 3]\nF(*xs) = 1\nF(A*, A*, trace(7)*)", maxCollectionItems: 5, effects: "traces=1");

    [Fact]
    public void EarlierSpread_RunsBeforeTheOverflow()
        => AssertOutcome("err limit 5/7 @3:18", "A = [1, 2, 3]\nF(*xs) = 1\nF(trace(7)*, A*, A*)", maxCollectionItems: 5, effects: "traces=1");

    [Fact]
    public void OrdinaryArguments_StaySuspended_WhenTheSupplyIsRefused()
        => AssertOutcome("err limit 5/7 @3:7", "A = [1, 2, 3]\nF(*xs) = 1\nF(A*, A*, trace(7))", maxCollectionItems: 5, effects: "traces=0");

    [Fact]
    public void OrdinaryArguments_StaySuspended_WithinTheLimit()
        => AssertOutcome("ok 1", "A = [1, 2, 3]\nF(*xs) = 1\nF(A*, A*, trace(7))", maxCollectionItems: 7, effects: "traces=0");

    [Fact]
    public void WrittenSlots_ConsForwardingAtTheBoundarySucceeds()
        => AssertOutcome("ok 3", "A = [1, 2, 3]\nF(x, *xs) = xs.count\nF(0, A*)", maxCollectionItems: 4, peak: 4);

    [Fact]
    public void WrittenSlots_AreNotCounted_AManyArgumentCallUnderATinyLimitSucceeds()
        => AssertOutcome("ok 6", "F(a, b, c) = a + b + c\nF(1, 2, 3)", maxCollectionItems: 2, peak: 0);

    [Fact]
    public void CallSupply_WrittenPrefixCountsBeforeAppendingASpread()
        => AssertOutcome("err limit 3/4 @3:6", "A = [1, 2, 3]\nF(x, *xs) = xs.count\nF(0, A*)", maxCollectionItems: 3);

    [Fact]
    public void CallSupply_WrittenSuffixCannotGrowAnExpandedSupplyPastTheLimit()
        => AssertOutcome("err limit 3/4 @3:7", "A = [1, 2, 3]\nF(*xs) = 1\nF(A*, trace(0))", maxCollectionItems: 3, effects: "traces=0");

    [Fact]
    public void ListLiteral_WrittenPrefixCountsBeforeAppendingASpread()
        => AssertOutcome("err limit 3/4 @2:1", "A = [1, 2, 3]\n[0, A*]", maxCollectionItems: 3, peak: 0);

    // ── T5: known collector-slice forwarding ─────────────────────────────────

    private const string Doubling = "G(n, *xs) = if(n == 0, xs.count, G(n - 1, xs*, xs*))\n";

    [Fact]
    public void KnownSliceForwarding_WithinTheLimit_DemandsTheSharedCellOnce()
        => AssertOutcome("ok 1024", Doubling + "G(10, trace(1))", effects: "traces=1", peak: 1025);

    [Fact]
    public void KnownSliceForwarding_RecursiveDuplicationIsBounded_AndNeverDemanded()
        => AssertOutcome("err limit 100/129 @1:48", Doubling + "G(10, trace(1))", maxCollectionItems: 100, effects: "traces=0", peak: 65);

    [Fact]
    public void KnownSliceForwarding_WrittenPrefixIsIncludedWithoutDemandingTheCells()
        => AssertOutcome("err limit 3/4 @2:21", "F(*xs) = 1\nForward(*xs) = F(0, xs*)\nForward(trace(1), trace(2), trace(3))",
            maxCollectionItems: 3, effects: "traces=0");

    // ── T6: CallReference argument views and retained plans ──────────────────

    private const string Meta = "Capture(meta operation) = operation\nCount(*xs) = xs.count\n";

    [Fact]
    public void ArgumentView_RepeatedSpread_RefusedWithoutDemandingTheViewCells()
        => AssertOutcome("err limit 5/6 @4:21", Meta + "R = Capture(Count(trace(1), trace(2), trace(3)))\nCount(R.Arguments*, R.Arguments*)",
            maxCollectionItems: 5, effects: "traces=0", peak: 3);

    [Fact]
    public void ArgumentView_RepeatedSpread_AtTheBoundarySucceeds()
        => AssertOutcome("ok 6", Meta + "R = Capture(Count(1, 2, 3))\nCount(R.Arguments*, R.Arguments*)", maxCollectionItems: 6);

    [Fact]
    public void ArgumentView_BoundLeavesInvokeAndSharingUnchanged()
        => AssertOutcome("ok S[3, 3]", Meta + "R = Capture(Count(trace(1), trace(2), trace(3)))\nCount(R.Arguments*), R.Invoke()",
            maxCollectionItems: 3, effects: "traces=3");

    [Fact]
    public void ArgumentView_ExpandedSupplyIncludesWrittenSlotsWithoutDemand()
        => AssertOutcome("err limit 3/4 @4:10", Meta + "R = Capture(Count(trace(1), trace(2), trace(3)))\nCount(0, R.Arguments*)",
            maxCollectionItems: 3, effects: "traces=0");

    // ── T7: postfix selection supplies ───────────────────────────────────────

    [Fact]
    public void SelectionSupply_RepeatedSpread_Refused()
        => AssertOutcome("err limit 5/6 @3:7", "I = (0, 1, 2)\nL = [10, 20, 30]\nL[I*, I*]", maxCollectionItems: 5, peak: 3);

    [Fact]
    public void SelectionSupply_RepeatedSpread_AtTheBoundarySucceeds()
        => AssertOutcome("ok S[10, 20, 30, 10, 20, 30]", "I = (0, 1, 2)\nL = [10, 20, 30]\nL[I*, I*]", maxCollectionItems: 6);

    [Fact]
    public void SelectionSupply_OrdinarySelectorsStayUndemanded_WhenRefused()
        => AssertOutcome("err limit 5/7 @3:7", "I = (0, 1, 2)\nL = [10, 20, 30]\nL[I*, I*, trace(0)]", maxCollectionItems: 5, effects: "traces=0");

    [Fact]
    public void SelectionSupply_ExpandedSupplyIncludesWrittenSlots()
        => AssertOutcome("err limit 3/4 @3:6", "I = (0, 1, 2)\nL = [10, 20, 30]\nL[0, I*]", maxCollectionItems: 3);

    [Fact]
    public async Task PublicEngine_DefaultAndAsyncEntryPointsEnforceTheSameSupplyBound()
    {
        const string source = "A = [1, 2, 3]\nF(*xs) = 1\nF(A*, A*)";
        var options = new RunOptions { EvaluationLimits = new EvaluationLimits { MaxCollectionItems = 5 } };
        var sync = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source, options));
        var asyncResult = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source, options));
        Assert.Equal(KatLangErrorCode.CollectionSizeLimitExceeded, Assert.Single(sync.Errors).Code);
        Assert.Equal(sync.Errors.Select(static e => (e.Code, e.Span, e.Message)),
            asyncResult.Errors.Select(static e => (e.Code, e.Span, e.Message)));
    }

    [Fact]
    public async Task CountOnlyOverflow_GenuineAsyncSpreadStillRuns_AndLaterFailureWins()
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var effects = new List<string>();
        var operations = HostOperations.Create(HostOperation.CreateAsync("trace", async (args, token) =>
        {
            effects.Add("entered");
            entered.SetResult();
            await release.Task.WaitAsync(token);
            effects.Add("resumed");
            return args[0];
        }, "x"));
        const string source = "A = [1, 2, 3]\nF(*xs) = 1\nF(0, A*, trace(9)*, (1 / 0)*)";
        var pending = Evaluator.RunCountedObservedAsync(Program(source, operations),
            new EvaluationLimits { MaxCollectionItems = 3 }, hostOperations: operations).AsTask();
        try
        {
            await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
            Assert.False(pending.IsCompleted);
            Assert.Equal(["entered"], effects);
        }
        finally
        {
            release.TrySetResult();
        }
        var (result, budget) = await pending.WaitAsync(TimeSpan.FromSeconds(10));
        Assert.True(result.IsError);
        Assert.Equal("err DivByZero", Describe(result.Error));
        Assert.Equal(["entered", "resumed"], effects);
        Assert.InRange(budget.PeakTransientExpansion, 0, 3);
    }

    // ── Loop step row supplies: generic and planned ──────────────────────────

    private const string RepeatStep = "S(a, b, c) = a, b*, c*\nrepeat(S(0, [1, 2], [3, 4]), 1)";

    [Theory]
    [InlineData(3, "err limit 3/5 @1:21")]
    [InlineData(4, "err limit 4/5")]
    [InlineData(5, "ok S[0, 1, 2, 3, 4]")]
    public void RepeatRows_GenericAndPlanned_AgreeOnTheBound(int limit, string expected)
    {
        var outcome = Observe(RepeatStep, limit);
        Assert.StartsWith(expected, outcome.Text);
    }

    [Fact]
    public void RepeatRows_TheOptimizedRouteRunsThePlannedLoop()
    {
        var loops = new LoopOptimizationDiagnostics();
        var planned = Sync(RepeatStep, new EvaluationLimits { MaxCollectionItems = 3 }, optimized: true, loops);
        Assert.Equal(1, loops.OptimizedLoopHits);
        Assert.StartsWith("err limit 3/5", planned.Text);
    }

    [Fact]
    public void RepeatRows_PlannedHandover_FormsTheSameBoundedSupply()
    {
        // Multi-item spread rows hand the planned round over to the generic continuation
        // (LoopOptimizer.MaterializeGenericHandoverSlots), which re-forms the row supply under the bound.
        var effects = new Effects();
        var operations = Operations(effects);
        var loops = new LoopOptimizationDiagnostics();
        var observations = new EvaluationObservations();
        var (result, budget) = Evaluator.RunCountedObserved(Program(RepeatStep, operations),
            new EvaluationLimits { MaxCollectionItems = 5 }, loopDiagnostics: loops, observations: observations, hostOperations: operations);
        Assert.Equal("ok S[0, 1, 2, 3, 4]", Text(result));
        Assert.Equal(1, loops.OptimizedLoopHits);
        Assert.Equal(1, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(5, budget.PeakTransientExpansion);
        Assert.Equal("ok S[0, 1, 2, 3, 4]", Observe(RepeatStep, 5).Text);
    }

    [Fact]
    public void RepeatRows_SingleItemSpreads_EnforceTheBoundDuringPlannedIterations()
    {
        const string source = "S(a, b, c) = a*, b*, c*\nrepeat(S(1, 2, 3), 2)";
        var loops = new LoopOptimizationDiagnostics();
        Sync(source, new EvaluationLimits { MaxCollectionItems = 2 }, optimized: true, loops);
        Assert.Equal(1, loops.OptimizedLoopHits);
        Assert.StartsWith("err limit 2/3 @1:22", Observe(source, 2).Text);
    }

    [Fact]
    public void WhileRows_SingleItemSpreads_IncludeTheFinalFlagInEveryStrategy()
    {
        const string source = "W(a, b) = a*, b*, true\nwhile(W(1, 2))";
        var loops = new LoopOptimizationDiagnostics();
        Sync(source, new EvaluationLimits { MaxCollectionItems = 2 }, optimized: true, loops);
        Assert.Equal(1, loops.OptimizedLoopHits);
        Assert.StartsWith("err limit 2/3 @1:19", Observe(source, 2).Text);
    }

    [Fact]
    public void WhileRows_FalseFlagDoesNotFormAnExpandedNextState()
        => AssertOutcome("ok S[1, 2]", "W(a, b) = a*, b*, false\nwhile(W(1, 2))", maxCollectionItems: 2, peak: 0);

    [Fact]
    public void WhileRows_GenericAndPlanned_AgreeOnTheBound()
    {
        const string source = "W(a, b, c) = a + 1, b*, c*, a < 1\nwhile(W(0, [1, 2], [3, 4]))";
        var loops = new LoopOptimizationDiagnostics();
        Sync(source, new EvaluationLimits { MaxCollectionItems = 3 }, optimized: true, loops);
        Assert.Equal(1, loops.OptimizedLoopHits);
        Assert.StartsWith("err limit 3/6 @1:25", Observe(source, 3).Text);
    }

    [Fact]
    public void WhileRows_StateAndFlagAtATinyLimit_AreNotCounted()
        => AssertOutcome("ok S[2, 0]", "W(a, b) = a + 1, b, a < 2\nwhile(W(0, 0))", maxCollectionItems: 2, peak: 0);
}
