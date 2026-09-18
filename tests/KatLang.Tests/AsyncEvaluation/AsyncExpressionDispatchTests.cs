namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Dispatch-equivalence pins for the async twin dispatch (M10).
///
/// <para><c>EvalCountedAsync</c> is a compiler-exhaustive switch expression over the
/// closed <see cref="Expr"/> hierarchy, mirrored case for case on <c>EvalCounted</c>: a
/// newly added variant fails the build until it is given an explicit twin case or joins
/// the enumerated sync-delegable leaf group (<c>Num</c>, <c>StringLiteral</c>, and the
/// illegal-in-eval <c>Grace</c>). What the compiler cannot prove is that a variant's arm
/// is the RIGHT one: a recursive variant delegated to the synchronous evaluator would
/// evaluate its children synchronously — bypassing the async twin family — while still
/// passing outcome-differential tests (the sync oracle produces the same values).</para>
///
/// <para>These tests pin the contract three ways: (1) every variant dispatches through
/// the twin path with the synchronous outcome; (2) the declared sync-delegable leaves
/// really are leaves — delegation touches neither cache seam; (3) for every recursive
/// variant, an async-sensitive property access placed in each meaningful child position
/// routes through the ASYNC cache seam with genuine suspension — a variant silently
/// delegated to sync evaluation would reach the synchronous seam instead and fail the
/// counters.</para>
/// </summary>
public class AsyncExpressionDispatchTests
{
    private static Algorithm.User EmptyAlgorithm(params Expr[] output)
        => new(Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: output);

    private static IReadOnlyDictionary<string, Expr> VariantSamples => ExprVariantCatalog.Samples;

    // ── Per-variant dispatch equivalence through the twin path ──────────────

    public static TheoryData<string> AllVariantNames() => ExprVariantCatalog.VariantNames();

    /// <summary>
    /// Every current variant dispatches through the async twin path (as a root
    /// program output row), produces exactly the synchronous outcome — ok or
    /// error alike — and never touches the synchronous seam member.
    /// </summary>
    [Theory]
    [MemberData(nameof(AllVariantNames))]
    public async Task EveryVariant_DispatchesThroughTheTwinPathWithTheSyncOutcome(string variant)
    {
        var ast = new Expr.AlgorithmExpr(EmptyAlgorithm(VariantSamples[variant]));

        var sync = Evaluator.RunCounted(ast);

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var async = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        Assert.Equal(0, cache.SyncAccesses);
    }

    /// <summary>
    /// The sync-delegable leaf group enumerated by BOTH counted dispatches. Grace is
    /// the sole structurally composite member: evaluation deliberately rejects it
    /// without touching its Inner expression.
    /// </summary>
    public static TheoryData<string> SyncDelegatedLeafNames() => new()
    {
        nameof(Expr.Grace),
        nameof(Expr.Num),
        nameof(Expr.StringLiteral),
    };

    /// <summary>
    /// The declared sync-delegable leaves really are leaves: delegating them to
    /// the synchronous evaluator evaluates no child, so the run touches NEITHER
    /// seam member and still matches the synchronous outcome exactly (including
    /// Grace's illegal-in-eval structured error).
    /// </summary>
    [Theory]
    [MemberData(nameof(SyncDelegatedLeafNames))]
    public async Task SyncDelegatedLeaves_DelegateExactlyAndTouchNoSeam(string variant)
    {
        var ast = new Expr.AlgorithmExpr(EmptyAlgorithm(VariantSamples[variant]));

        var sync = Evaluator.RunCounted(ast);

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var async = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        Assert.Equal(0, cache.SyncAccesses);
        Assert.Equal(0, cache.AsyncAccesses);
    }

    /// <summary>
    /// NativeCall is an explicit async case because its declared-argument reads
    /// are ordinary <c>Expr.Param</c> value reads, and an argument bound on the
    /// ALGORITHM channel makes one of those reads re-enter an algorithm body. A
    /// native whose arguments are ordinary bound values evaluates nothing, so it
    /// still touches no property-cache seam; the algorithm-channel case is
    /// pinned by <see cref="NativeArgumentAlgorithmDemand_RoutesThroughTheAsyncSeam"/>.
    /// </summary>
    [Fact]
    public async Task NativeCallWithValueBoundArguments_TouchesNoSeam()
    {
        // The catalog's bare NativeCall has an unbound x and fails before computation.
        // Bind a real value so this pin exercises successful native argument demand.
        var wrapper = new Algorithm.User(
            Parent: null, ParameterPatterns: Algorithm.NormalParameters(["x"]), Opens: [], Properties: [],
            Output: [new Expr.NativeCall("Abs", ["x"])]);
        var ast = new Expr.Call(new Expr.AlgorithmExpr(wrapper), [new Expr.Num(-7)]);
        var sync = Evaluator.RunCounted(ast);
        Assert.True(sync.IsOk, AsyncEvaluationHarness.NeutralOf(sync));
        Assert.True(Result.ValueComparer.Equals(new Result.Atom(7), sync.Value.Value));
        Assert.Equal(1, sync.Value.EmittedCount);
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var async = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        Assert.Equal(0, cache.SyncAccesses);
        Assert.Equal(0, cache.AsyncAccesses);
    }

    /// <summary>
    /// The recursive NativeCall child position: a Math member argument that
    /// binds only on the ALGORITHM channel makes the wrapper's declared-argument
    /// read demand that algorithm's value, which must run on the ASYNC seam. A
    /// NativeCall silently delegated to synchronous evaluation would reach the
    /// SYNCHRONOUS seam member instead and fail the counters.
    /// </summary>
    [Fact]
    public async Task NativeArgumentAlgorithmDemand_RoutesThroughTheAsyncSeam()
    {
        // `Wrapped` binds Math.Sqrt's `x` on the algorithm channel only (its own
        // value evaluation fails), so the wrapper body demands its value, which
        // re-enters `Wrapped`'s body through the zero-argument property seam.
        var ast = new Expr.AlgorithmExpr(
            KatLang.Tests.SourceProvenance.ParseValid(
                """
                P = 4
                Wrapped = P + 1 / 0
                Math.Sqrt(Wrapped)
                """).Root);

        var (sync, syncBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var (async, asyncBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        Assert.Equal(syncBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        Assert.Equal(syncBudget.PeakDepth, asyncBudget.PeakDepth);
        Assert.Equal(syncBudget.MaterializedItems, asyncBudget.MaterializedItems);
        Assert.Equal(syncBudget.MaterializedStringChars, asyncBudget.MaterializedStringChars);
        Assert.Equal(0, cache.SyncAccesses);
        Assert.True(cache.AsyncAccesses > 0);
        Assert.Equal(cache.AsyncAccesses, cache.ThreadHops.Count);
    }

    [Fact]
    public async Task NativeArgumentAlgorithmDemand_TightLimitsMatchSyncVerdictsAndCounters()
    {
        var ast = new Expr.AlgorithmExpr(
            KatLang.Tests.SourceProvenance.ParseValid(
                """
                P = 4
                Wrapped = P + 1 / 0
                Math.Sqrt(Wrapped)
                """).Root);
        var (_, baselineBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var limits = new[]
        {
            new EvaluationLimits { MaxSteps = Math.Max(1, baselineBudget.ConsumedSteps - 1) },
            new EvaluationLimits { MaxDepth = Math.Max(1, baselineBudget.PeakDepth - 1) },
        };

        foreach (var limit in limits)
        {
            var (sync, syncBudget) = Evaluator.RunCountedObserved(
                ast, limit, enableOptimizations: false);
            var cache = new PassThroughAsyncZeroArgPropertyResultCache();
            var (async, asyncBudget) = await AsyncEvaluationHarness.Complete(
                Evaluator.RunCountedObservedAsync(
                    ast, limit, zeroArgPropertyResultCache: cache));

            Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
            Assert.Equal(syncBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
            Assert.Equal(syncBudget.PeakDepth, asyncBudget.PeakDepth);
            Assert.Equal(syncBudget.MaterializedItems, asyncBudget.MaterializedItems);
            Assert.Equal(syncBudget.MaterializedStringChars, asyncBudget.MaterializedStringChars);
            Assert.Equal(0, cache.SyncAccesses);
        }
    }

    [Fact]
    public async Task NativeArgumentAlgorithmDemand_ObservesCancellationDuringRedemand()
    {
        var ast = new Expr.AlgorithmExpr(
            KatLang.Tests.SourceProvenance.ParseValid(
                """
                P = 4
                Wrapped = P + 1 / 0
                Math.Sqrt(Wrapped)
                """).Root);
        using var cancellation = new CancellationTokenSource();
        var cache = new CancellingAsyncZeroArgPropertyResultCache(
            cancelAtAccess: 3,
            cancellation);

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedAsync(
                ast, cache, limits: null, cancellationToken: cancellation.Token));

        Assert.Equal(cancellation.Token, thrown.CancellationToken);
        Assert.True(cache.AsyncAccesses >= 3);
        Assert.Equal(0, cache.ObservedBudget!.CurrentDepth);
    }

    // ── Recursive child positions route through the ASYNC seam ──────────────

    /// <summary>
    /// One program per recursive variant and child position, each placing a
    /// zero-argument property access (the async-sensitive construct) INSIDE
    /// that child position. Argument-slot programs use a small expression spine
    /// (<c>P + 0</c>) so the access resolves through the cache seam rather than
    /// the builtin-argument funnel, which bypasses the cache by design.
    /// </summary>
    public static TheoryData<string, string> AsyncSensitiveChildPrograms() => new()
    {
        { "Resolve.PropertyAccess", "P = 5\nP" },
        { "Unary.Operand", "P = 5\n-P" },
        { "Binary.Left", "P = 5\nP + 1" },
        { "Binary.Right", "P = 5\n1 + P" },
        { "Index.Target", "P = (1, 2)\nP:0" },
        { "Index.Selector", "P = 1\n(7, 8):P" },
        { "SequenceSpread.Operand", "P = (1, 2)\nP*" },
        { "ListLiteral.Item", "P = 5\n[P, 2]" },
        { "Capture.Row", "P = 5\n(P, 2)" },
        { "AlgorithmExpr.OutputRow", "P = 5\n{P}" },
        { "Call.Argument", "P = 5\nF(x) = x + 1\nF(P + 0)" },
        { "DotCall.Target", "P = 5\n(P, 2).count" },
        { "DotCall.Argument", "P = 2\n(7, 8, 9).take(P + 0)" },
    };

    /// <summary>
    /// Every composite variant that evaluates children has an async-sensitive program
    /// here (or the host-built <see cref="Expr.SequenceConstruct"/> pin below), so a new
    /// recursive variant's seam routing is tested or the table fails. Grace is
    /// deliberately illegal-in-eval and never evaluates Inner; Resolve has no structural
    /// child, but its property-value demand is async-sensitive and stays in the matrix.
    /// </summary>
    [Fact]
    public void AsyncSensitivePrograms_CoverEveryCompositeVariantThatEvaluatesChildren()
        => ExprVariantCatalog.AssertCoversEveryCompositeVariant(
            AsyncSensitiveChildPrograms()
                .Select(row => ((string)row[0]!).Split('.')[0])
                .Where(name => name != nameof(Expr.Resolve))
                .Append(nameof(Expr.SequenceConstruct)),
            $"{nameof(AsyncExpressionDispatchTests)}.{nameof(AsyncSensitiveChildPrograms)}",
            nameof(Expr.Grace));

    [Theory]
    [MemberData(nameof(AsyncSensitiveChildPrograms))]
    public async Task RecursiveVariant_ChildEvaluationRoutesThroughTheAsyncSeam(string position, string source)
    {
        _ = position;
        await AssertChildRoutesThroughAsyncSeam(AsyncEvaluationHarness.Ast(source));
    }

    /// <summary>
    /// SequenceConstruct is the internal join node the parser never produces,
    /// so its child positions are pinned from a host-built tree: both join
    /// children evaluate through the async twin family.
    /// </summary>
    [Fact]
    public async Task SequenceConstruct_ChildEvaluationRoutesThroughTheAsyncSeam()
    {
        var root = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties: [new Property("P", EmptyAlgorithm(new Expr.Num(5)))],
            Output: new OutputBundle(
            [
                new Expr.SequenceConstruct(new Expr.Resolve("P"), new Expr.Num(1)),
                new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Resolve("P")),
            ]));

        await AssertChildRoutesThroughAsyncSeam(new Expr.AlgorithmExpr(root));
    }

    /// <summary>
    /// Param is not structurally composite (its fields are names, not expressions), but
    /// its AlgEnv branch DEMANDS a bound zero-parameter algorithm's output — a recursive
    /// child evaluation awaited directly from the dispatch arm. The surface route is a
    /// semantically erroring eager argument (a semantic value-channel error is never
    /// retained on the binding, so the forwarded demand re-evaluates the thunk — pinned
    /// by <c>EvaluationLimitsTests</c>); the demand's re-evaluation must route the
    /// thunk's property access through the ASYNC seam even though the run ends in the
    /// synchronous error. Plain <c>Eval</c>'s Param case reproduces the same lookups, so
    /// a Param arm silently delegated to synchronous evaluation would return the correct
    /// error — only the seam counters expose the synchronous child evaluation.
    /// </summary>
    [Fact]
    public async Task Param_AlgorithmBoundValueDemand_RoutesThroughTheAsyncSeam()
    {
        // Eager argument evaluation accesses Bad (miss) and P, fails semantically, and
        // leaves an algorithm-only binding; w's value demand inside G re-evaluates the
        // thunk, accessing P again through the seam before reproducing the error.
        var ast = AsyncEvaluationHarness.Ast("P = 5\nBad = P + 1 / 0\nG(w) = w\nF(v) = G(v)\nF(Bad)");

        var sync = Evaluator.RunCounted(ast);
        Assert.True(sync.IsError, "expected the demanded thunk to reproduce the semantic error");

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var async = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        Assert.True(
            cache.AsyncAccesses >= 3,
            "expected the eager accesses AND the re-demanded thunk's property access to reach the async seam");
        Assert.Equal(0, cache.SyncAccesses);
        Assert.Equal(cache.AsyncAccesses, cache.ThreadHops.Count);
    }

    /// <summary>
    /// The M10 behavioral core: the child's property access must reach the
    /// ASYNC seam member with genuine suspension at every access, never the
    /// synchronous seam member, and the suspending run must still produce
    /// exactly the synchronous outcome. A recursive variant silently delegated
    /// to synchronous evaluation would evaluate its children through the
    /// synchronous seam and fail the counters even if the value matched.
    /// </summary>
    private static async Task AssertChildRoutesThroughAsyncSeam(Expr ast)
    {
        var sync = Evaluator.RunCounted(ast);
        Assert.False(sync.IsError, AsyncEvaluationHarness.NeutralOf(sync));

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var async = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        Assert.True(Result.ValueComparer.Equals(sync.Value.Value, async.Value.Value));
        Assert.Equal(sync.Value.EmittedCount, async.Value.EmittedCount);

        Assert.True(cache.AsyncAccesses > 0, "expected the child's property access to reach the async seam");
        Assert.Equal(0, cache.SyncAccesses);
        Assert.Equal(cache.AsyncAccesses, cache.ThreadHops.Count);
    }
}
