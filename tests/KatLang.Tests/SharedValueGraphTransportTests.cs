using KatLang.Optimizations.Loops;
using KatLang.Evaluation;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// A deep SHARED value graph built by an ordinary in-budget loop reaches algorithm-only slots — a
/// <c>while</c> step slot, a callback slot of a sequence builtin, a builtin used as a reducer — as
/// Ready data, and stays data: it is passed on unchanged and has no CALLABLE identity (NEED-06), so
/// an invoking slot that needs a callable reports <c>NotAnAlgorithm</c> (Q-06) and a slot that is
/// never invoked is never projected. A value is a DAG, not a tree (<c>Wrap = [x, x]</c> applied n
/// times reaches n+1 distinct nodes through 2^n root-to-leaf paths in n in-budget steps), so any
/// walk of these values proportional to PATHS would be exponential and unbudgeted; the depth-40
/// programs below complete with their ordinary outcome.
///
/// <para>History: before Model C such an argument was rebuilt into an expression-tree wrapper
/// (<c>CountedArgAlgorithm</c> over the <c>Result</c>-to-<c>Expr</c> conversion
/// <c>Evaluator.ResultToExpr</c>), whose path-expanding walk attempted a ~2^40-node rebuild on
/// these very programs until it was memoized by reference identity (August 2026). Model C
/// (October 2026) deleted the wrapper, and the conversion, left with test callers only, was
/// retired on October 13 2026 together with its run-scoped work counter. The evaluation of
/// shared <see cref="Expr"/> subgraphs themselves is pinned by
/// <see cref="SharedExprOccurrenceSemanticsTests"/>.</para>
/// </summary>
public class SharedValueGraphTransportTests
{
    private const int ShallowDepth = 20;

    private const int DeepDepth = 40;

    private static IReadOnlyList<Result> Children(Result value) => value switch
    {
        Result.SequenceValue(var items) => items,
        Result.ListValue(var items) => items,
        _ => [],
    };

    private static int DistinctStructureNodes(Result value)
    {
        var seen = new HashSet<Result>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Result>();
        pending.Push(value);
        while (pending.Count > 0)
        {
            var node = pending.Pop();
            if (node is not (Result.SequenceValue or Result.ListValue) || !seen.Add(node))
                continue;
            foreach (var child in Children(node))
                pending.Push(child);
        }

        return seen.Count;
    }

    /// <summary>
    /// The doubling DAG built by an ordinary in-budget loop — the same recipe the F16 Normalize
    /// regressions use: <c>Wrap</c> stores its ONE bound argument in both element slots, so each
    /// step adds one node reachable through twice as many paths.
    /// </summary>
    private static string DagProgram(string body, int depth = DeepDepth)
        => $"""
            Wrap = [x, x]
            A = Wrap.repeat({depth}, 1)
            {body}
            """;

    /// <summary>
    /// Build one depth-<paramref name="dagDepth"/> shared value DAG, then duplicate that SAME
    /// result reference into 2^<paramref name="duplicationDepth"/> emitted slots in only
    /// <paramref name="duplicationDepth"/> loop steps. Grouping <c>B*</c> makes those slots one
    /// sequence-valued collection item, which builtin <c>while</c> used as the reducer receives
    /// as ONE argument (one sequence value — selection is a value boundary).
    /// </summary>
    private static string MultiEmissionDagProgram(
        string body,
        int dagDepth = ShallowDepth,
        int duplicationDepth = 5)
        => $"""
            Wrap = [x, x]
            A = Wrap.repeat({dagDepth}, 1)
            Dup(*xs) = xs*, xs*
            B = Dup.repeat({duplicationDepth}, A)
            {body}
            """;

    private sealed record ObservedSourceRun(
        bool IsError,
        EvalError? InnermostError,
        Result? Value,
        int? Emitted,
        string? ErrorTree,
        long Steps,
        long ExpressionCheckpoints,
        long MaterializedItems,
        long MaterializedStringChars,
        int PeakDepth,
        LoopOptimizationDiagnosticsSnapshot LoopStats);

    private static ObservedSourceRun ObserveSource(string source, bool optimize)
    {
        var loopDiagnostics = new LoopOptimizationDiagnostics();
        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root),
            enableOptimizations: optimize,
            loopDiagnostics: loopDiagnostics);

        return Observation(result, budget, loopDiagnostics);
    }

    private static ObservedSourceRun Observation(
        EvalResult<Evaluator.CountedResult> result,
        EvaluationBudget budget,
        LoopOptimizationDiagnostics loopDiagnostics)
        => new(
            result.IsError,
            result.IsError ? Innermost(result.Error) : null,
            result.IsError ? null : result.Value.Value,
            result.IsError ? null : result.Value.EmittedCount,
            result.IsError ? LoopDiagnosticParityAssertions.DescribeErrorTree(result.Error) : null,
            budget.ConsumedSteps,
            budget.ConsumedExpressionCheckpoints,
            budget.MaterializedItems,
            budget.MaterializedStringChars,
            budget.PeakDepth,
            loopDiagnostics.GetSnapshot());

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LoopStepSlot_ReadyValueHasNoCallableIdentity(bool optimize)
    {
        var run = ObserveSource(DagProgram("while(A*, 1)"), optimize);

        // A spread item is Ready data with no CALLABLE identity: it is no step (Q-06).
        Assert.True(run.IsError);
        Assert.Equal("while step", Assert.IsType<EvalError.NotAnAlgorithm>(run.InnermostError).Description);
        if (optimize)
        {
            Assert.True(run.LoopStats.OptimizedLoopHits > 0);
            Assert.All(run.LoopStats.LoopPlans, plan => Assert.Equal("Wrap.repeat", plan.Identity));
        }
        else
        {
            Assert.Equal(0, run.LoopStats.LoopPlanBuilds);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AlgorithmSuffixSlot_NeverProjectsAnUnusedReadyValue(bool optimize)
    {
        // reduce calls map(element, accumulator): map((), A) receives the depth-40 DAG in its
        // callback slot, but an empty collection invokes no callback, so the slot is never
        // projected and the result is the empty list.
        var run = ObserveSource(DagProgram("((), ()).reduce(map, A)"), optimize);

        Assert.False(run.IsError);
        var list = Assert.IsType<Result.ListValue>(run.Value);
        Assert.Empty(list.Items);
        Assert.Equal(1, run.Emitted);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SequenceItemSlot_RepeatedReferencesAreReadyDataWithNoCallableIdentity(bool optimize)
    {
        var run = ObserveSource(
            MultiEmissionDagProgram("[(B*)].reduce(while, 1)"),
            optimize);

        // `while` invoked as the reducer receives the element as ITS step: Ready data
        // with no CALLABLE identity (Q-06).
        Assert.True(run.IsError);
        Assert.Equal("while step", Assert.IsType<EvalError.NotAnAlgorithm>(run.InnermostError).Description);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SequenceItemSlot_SharedDescendantsAreReadyDataWithNoCallableIdentity(bool optimize)
    {
        var run = ObserveSource(
            DagProgram("[([A, 1], [A, 2])].reduce(while, 1)", ShallowDepth),
            optimize);

        Assert.True(run.IsError);
        Assert.Equal("while step", Assert.IsType<EvalError.NotAnAlgorithm>(run.InnermostError).Description);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    public async Task ReadyGraphTransport_PreservesDiagnosticsAndRawWorkAcrossExecutionRoutes(int scenario)
    {
        var source = scenario switch
        {
            0 => DagProgram("while(A*, 1)"),
            1 => DagProgram("((), ()).reduce(map, A)"),
            2 => MultiEmissionDagProgram("[(B*)].reduce(while, 1)"),
            3 => DagProgram("[([A, 1], [A, 2])].reduce(while, 1)", ShallowDepth),
            _ => throw new ArgumentOutOfRangeException(nameof(scenario)),
        };
        var generic = ObserveSource(source, optimize: false);
        var optimized = ObserveSource(source, optimize: true);
        Assert.True(optimized.LoopStats.OptimizedLoopHits > 0);
        Assert.Equal(0, generic.LoopStats.LoopPlanBuilds);
        AssertSameOutcomeAndWork(generic, optimized);

        // The ordinary async facade uses the synchronous optimized path here. The async
        // cache separately forces the generic twin family and really suspends at property
        // accesses; its counters prove that the synchronous cache seam was never used.
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var facadeDiagnostics = new LoopOptimizationDiagnostics();
        var (facade, facadeBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(expr, loopDiagnostics: facadeDiagnostics));
        Assert.True(facadeDiagnostics.GetSnapshot().OptimizedLoopHits > 0);
        AssertSameOutcomeAndWork(optimized, Observation(facade, facadeBudget, facadeDiagnostics));

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var twinDiagnostics = new LoopOptimizationDiagnostics();
        var (twin, twinBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(expr, zeroArgPropertyResultCache: cache, loopDiagnostics: twinDiagnostics));
        Assert.True(cache.AsyncAccesses > 0);
        Assert.Equal(0, cache.SyncAccesses);
        Assert.NotEmpty(cache.ThreadHops);
        Assert.Equal(0, twinDiagnostics.GetSnapshot().LoopPlanBuilds);
        AssertSameOutcomeAndWork(generic, Observation(twin, twinBudget, twinDiagnostics));
    }

    private static void AssertSameOutcomeAndWork(ObservedSourceRun expected, ObservedSourceRun actual)
    {
        Assert.Equal(expected.IsError, actual.IsError);
        Assert.Equal(expected.ErrorTree, actual.ErrorTree);
        if (!expected.IsError)
            Assert.Equal(Assert.IsAssignableFrom<Result>(expected.Value), Assert.IsAssignableFrom<Result>(actual.Value), Result.ValueComparer);
        Assert.Equal(expected.Emitted, actual.Emitted);
        Assert.Equal(expected.Steps, actual.Steps);
        Assert.True(expected.ExpressionCheckpoints > 0);
        Assert.Equal(expected.ExpressionCheckpoints, actual.ExpressionCheckpoints);
        Assert.Equal(expected.MaterializedItems, actual.MaterializedItems);
        Assert.Equal(expected.MaterializedStringChars, actual.MaterializedStringChars);
        Assert.Equal(expected.PeakDepth, actual.PeakDepth);
    }

    [Fact]
    public void ReadyValueTransport_PlainCountedAndFlatEntryPointsAgree()
    {
        // Entry-point parity for the successful transport program: every public entry point
        // observes the same value.
        var source = DagProgram("((), ()).reduce(map, A)");
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var plain = Evaluator.Run(expr);
        Assert.False(plain.IsError);
        var plainList = Assert.IsType<Result.ListValue>(plain.Value);
        Assert.Empty(plainList.Items);

        var counted = Evaluator.RunCounted(expr);
        Assert.False(counted.IsError);
        Assert.Equal(plain.Value, counted.Value.Value, Result.ValueComparer);
        Assert.Equal(1, counted.Value.EmittedCount);

        var flat = Evaluator.RunFlat(expr);
        Assert.False(flat.IsError);
        Assert.Empty(flat.Value);
    }

    [Fact]
    public void LoopStepReadyValue_ErrorEntryPointsAgree()
    {
        var source = DagProgram("while(A*, 1)");
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var plain = Evaluator.Run(expr);
        var counted = Evaluator.RunCounted(expr);
        var flat = Evaluator.RunFlat(expr);

        Assert.True(plain.IsError);
        Assert.True(counted.IsError);
        Assert.True(flat.IsError);
        Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(plain.Error));
        Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(counted.Error));
        Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(flat.Error));
        Assert.Equal(plain.Error.ToString(), counted.Error.ToString());
        Assert.Equal(plain.Error.ToString(), flat.Error.ToString());
        Assert.Equal(plain.Error.Span, counted.Error.Span);
        Assert.Equal(plain.Error.Span, flat.Error.Span);
    }

    [Fact]
    public void SourceDag_IsActuallyShared_NotATreeThatHappensToBeSmall()
    {
        // The depth-40 programs above are meaningful only if the runtime value really is a DAG.
        // Pin the reference topology of the loop-built value directly: every level stores the SAME
        // child reference twice.
        var source = DagProgram("A", depth: 12);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        Assert.False(result.IsError);

        var level = result.Value;
        for (var i = 0; i < 12; i++)
        {
            var items = Assert.IsType<Result.ListValue>(level).Items;
            Assert.Equal(2, items.Count);
            Assert.Same(items[0], items[1]);
            level = items[0];
        }

        Assert.Equal(new Result.Atom(1), level);
        Assert.Equal(12, DistinctStructureNodes(result.Value!));
    }

    [Fact]
    public void MultiEmissionSourceGraph_RepeatsTheSameDeepRootReference()
    {
        const int dagDepth = 12;
        const int duplicationDepth = 5;
        var source = MultiEmissionDagProgram("B", dagDepth, duplicationDepth);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        Assert.False(result.IsError);

        var emitted = Assert.IsType<Result.SequenceValue>(result.Value).Items;
        Assert.Equal(1 << duplicationDepth, emitted.Count);
        Assert.All(emitted, item => Assert.Same(emitted[0], item));

        // The sequence root plus the depth-12 A chain: width is explicit in the root edges, but
        // the repeated deep structure remains one physical subgraph.
        Assert.Equal(dagDepth + 1, DistinctStructureNodes(result.Value));
    }
}
