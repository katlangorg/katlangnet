namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Mechanical exhaustiveness pins for the async twin dispatch (M10).
///
/// <para><c>EvalCountedAsync</c> used to end in an open default that delegated
/// every unmatched variant to the SYNCHRONOUS evaluator on the assumption it was
/// a leaf. A newly added recursive <see cref="Expr"/> variant would therefore
/// have evaluated its children synchronously — bypassing the async twin family —
/// while still passing outcome-differential tests (the sync oracle produces the
/// same values). The dispatch now enumerates the sync-delegable leaves
/// explicitly (<c>Num</c>, <c>StringLiteral</c>, synchronous <c>NativeCall</c>,
/// and the illegal-in-eval <c>Grace</c>) and fails loudly on anything else, in
/// lock-step with the synchronous <c>EvalCounted</c> mirror.</para>
///
/// <para>These tests pin the contract three ways: (1) a reflection-complete
/// classification of every concrete variant into explicitly-async-cased vs
/// sync-delegable-leaf; (2) every variant dispatches through the twin path
/// without an unhandled-variant failure and with the synchronous outcome;
/// (3) for every recursive variant, an async-sensitive property access placed
/// in each meaningful child position routes through the ASYNC cache seam with
/// genuine suspension — a variant silently delegated to sync evaluation would
/// reach the synchronous seam instead and fail the counters.</para>
/// </summary>
public class AsyncDispatchExhaustivenessTests
{
    // ── Declared dispatch classification (reflection-complete) ──────────────

    private enum AsyncDispatchPolicy
    {
        /// <summary>Handled by an explicit case of the async twin dispatch.</summary>
        ExplicitAsyncCase,

        /// <summary>
        /// Delegated to the synchronous evaluator because the variant provably
        /// evaluates no child expression (Grace is the illegal-in-eval
        /// catch-all: a structured error, no child evaluation).
        /// </summary>
        SyncDelegatedLeaf,

        /// <summary>
        /// NativeCall only: a native naming an ASYNCHRONOUS host operation is
        /// intercepted by the guarded async case (the one Phase 3 await site,
        /// pinned by the Hosting suites); every other native is a synchronous
        /// leaf and delegates.
        /// </summary>
        SplitOnAsynchronousHostOperation,
    }

    private static IReadOnlyDictionary<string, AsyncDispatchPolicy> DeclaredPolicies { get; } =
        new Dictionary<string, AsyncDispatchPolicy>(StringComparer.Ordinal)
        {
            [nameof(Expr.Param)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.Resolve)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.EmptySequence)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.Unary)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.Binary)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.Index)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.ListLiteral)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.SequenceConstruct)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.SequenceSpread)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.AlgorithmExpr)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.Capture)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.Call)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.DotCall)] = AsyncDispatchPolicy.ExplicitAsyncCase,
            [nameof(Expr.NativeCall)] = AsyncDispatchPolicy.SplitOnAsynchronousHostOperation,
            [nameof(Expr.Num)] = AsyncDispatchPolicy.SyncDelegatedLeaf,
            [nameof(Expr.StringLiteral)] = AsyncDispatchPolicy.SyncDelegatedLeaf,
            [nameof(Expr.Grace)] = AsyncDispatchPolicy.SyncDelegatedLeaf,
        };

    /// <summary>
    /// A newly added <see cref="Expr"/> variant must be classified here before
    /// the dispatch pins below can cover it — and must then be given an explicit
    /// case in BOTH counted dispatch twins (their fail-loud defaults reject
    /// anything unclassified at runtime).
    /// </summary>
    [Fact]
    public void DeclaredPolicies_CoverEveryExprVariant()
    {
        var declared = typeof(Expr).GetNestedTypes()
            .Where(type => !type.IsAbstract && typeof(Expr).IsAssignableFrom(type))
            .Select(type => type.Name)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();

        Assert.Equal(
            declared,
            DeclaredPolicies.Keys.OrderBy(name => name, StringComparer.Ordinal).ToList());
        Assert.Equal(
            declared,
            VariantSamples.Keys.OrderBy(name => name, StringComparer.Ordinal).ToList());
    }

    private static bool HasStructuralExprChildren(Type variantType)
        => variantType
            .GetProperties(System.Reflection.BindingFlags.Public
                | System.Reflection.BindingFlags.Instance
                | System.Reflection.BindingFlags.DeclaredOnly)
            .Any(property =>
                typeof(Expr).IsAssignableFrom(property.PropertyType)
                || typeof(Algorithm).IsAssignableFrom(property.PropertyType)
                || typeof(OutputBundle).IsAssignableFrom(property.PropertyType)
                || typeof(IEnumerable<Expr>).IsAssignableFrom(property.PropertyType));

    /// <summary>
    /// A future composite variant cannot be placed in the synchronous delegation
    /// group merely by adding it to the policy/sample tables. Grace is the sole
    /// structural exception: evaluation deliberately rejects it without touching
    /// its Inner expression.
    /// </summary>
    [Fact]
    public void SyncDelegatedPolicies_ContainNoEvaluatedCompositeVariant()
    {
        var structurallyCompositeDelegates = DeclaredPolicies
            .Where(pair => pair.Value == AsyncDispatchPolicy.SyncDelegatedLeaf)
            .Select(pair => typeof(Expr).GetNestedType(pair.Key))
            .Where(type => type is not null && HasStructuralExprChildren(type))
            .Select(type => type!.Name)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();

        Assert.Equal([nameof(Expr.Grace)], structurallyCompositeDelegates);
    }

    // ── Per-variant dispatch coverage through the twin path ─────────────────

    private static Algorithm.User EmptyAlgorithm(params Expr[] output)
        => new(Parent: null, Parameters: [], Opens: [], Properties: [], Output: output);

    private static IReadOnlyDictionary<string, Expr> VariantSamples { get; } = BuildVariantSamples();

    private static IReadOnlyDictionary<string, Expr> BuildVariantSamples()
    {
        var leaf = new Expr.Num(1);
        return new Dictionary<string, Expr>(StringComparer.Ordinal)
        {
            [nameof(Expr.Param)] = new Expr.Param("p"),
            [nameof(Expr.Num)] = leaf,
            [nameof(Expr.StringLiteral)] = new Expr.StringLiteral("s"),
            [nameof(Expr.Unary)] = new Expr.Unary(UnaryOp.Minus, leaf),
            [nameof(Expr.Binary)] = new Expr.Binary(BinaryOp.Add, leaf, leaf),
            [nameof(Expr.Index)] = new Expr.Index(new Expr.Capture([leaf, leaf]), new Expr.Num(0)),
            [nameof(Expr.SequenceConstruct)] = new Expr.SequenceConstruct(leaf, leaf),
            [nameof(Expr.EmptySequence)] = new Expr.EmptySequence(0),
            [nameof(Expr.SequenceSpread)] = new Expr.SequenceSpread(new Expr.Capture([leaf, leaf])),
            [nameof(Expr.ListLiteral)] = new Expr.ListLiteral([leaf, leaf]),
            [nameof(Expr.Resolve)] = new Expr.Resolve("R"),
            [nameof(Expr.DotCall)] = new Expr.DotCall(new Expr.Capture([leaf, leaf]), "count"),
            [nameof(Expr.Grace)] = new Expr.Grace(leaf, 1),
            [nameof(Expr.AlgorithmExpr)] = new Expr.AlgorithmExpr(EmptyAlgorithm(leaf)),
            [nameof(Expr.Capture)] = new Expr.Capture([leaf, leaf]),
            [nameof(Expr.Call)] = new Expr.Call(new Expr.Resolve("F"), new OutputBundle([leaf])),
            [nameof(Expr.NativeCall)] = new Expr.NativeCall("Abs", ["x"]),
        };
    }

    public static TheoryData<string> AllVariantNames()
    {
        var data = new TheoryData<string>();
        foreach (var name in BuildVariantSamples().Keys.OrderBy(name => name, StringComparer.Ordinal))
            data.Add(name);
        return data;
    }

    /// <summary>
    /// Every current variant dispatches through the async twin path (as a root
    /// program output row) without an unhandled-variant failure, produces
    /// exactly the synchronous outcome — ok or error alike — and never touches
    /// the synchronous seam member.
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

    public static TheoryData<string> SyncDelegatedLeafNames()
    {
        var data = new TheoryData<string>();
        foreach (var (name, policy) in DeclaredPolicies.OrderBy(pair => pair.Key, StringComparer.Ordinal))
        {
            if (policy == AsyncDispatchPolicy.SyncDelegatedLeaf)
                data.Add(name);
        }

        return data;
    }

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
    /// NativeCall has a split policy, but the ordinary built-in/synchronous-host
    /// branch is still one of the four sync-delegable leaves and must touch no
    /// property-cache seam.
    /// </summary>
    [Fact]
    public async Task SynchronousNativeCall_DelegatesExactlyAndTouchesNoSeam()
    {
        var ast = new Expr.AlgorithmExpr(EmptyAlgorithm(VariantSamples[nameof(Expr.NativeCall)]));
        var sync = Evaluator.RunCounted(ast);
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var async = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, cache));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        Assert.Equal(0, cache.SyncAccesses);
        Assert.Equal(0, cache.AsyncAccesses);
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

    [Fact]
    public void AsyncSensitivePrograms_CoverEveryCompositeVariantThatEvaluatesChildren()
    {
        var structurallyComposite = typeof(Expr).GetNestedTypes()
            .Where(type => !type.IsAbstract && typeof(Expr).IsAssignableFrom(type))
            .Where(HasStructuralExprChildren)
            // Grace is deliberately illegal-in-eval and never evaluates Inner.
            .Where(type => type.Name != nameof(Expr.Grace))
            .Select(type => type.Name)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();
        var exercised = AsyncSensitiveChildPrograms()
            .Select(row => ((string)row[0]!).Split('.')[0])
            // Resolve has no structural child, but its property-value demand is
            // async-sensitive and remains covered by the same behavioral matrix.
            .Where(name => name != nameof(Expr.Resolve))
            .Append(nameof(Expr.SequenceConstruct))
            .Distinct(StringComparer.Ordinal)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();

        Assert.Equal(structurallyComposite, exercised);
    }

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
            Parameters: [],
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
