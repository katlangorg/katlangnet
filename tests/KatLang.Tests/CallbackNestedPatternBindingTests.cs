using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// S3 — CALLBACK BINDING USES THE ORDINARY CALL'S NESTED-PATTERN RULES (September 2026).
///
/// <para>When a callback operation supplies ONE value <c>V</c> to a callable whose parameter
/// is a nested sequence-value pattern <c>P</c>, binding <c>V</c> follows exactly the rules of
/// the ordinary call <c>P(V)</c>: the same success or failure, the same bound values, and the
/// same binding reason on failure (the innermost error and the nested group it is attributed
/// to — only the outer call/map/filter/reduce frames differ). Both binders open a pattern's
/// value through the ONE rule <c>SequenceValuePatternItems</c> (Lean
/// <c>Result.sequenceValuePatternItems</c>): a sequence or list opens one level, and any other
/// value — a number, a string, a Boolean — is a ONE-item supply at every group size. The
/// counted callback binder used to fall back only for one-item groups, so
/// <c>map([7], P)</c> with <c>P((x, *rest))</c> failed with a bare BadArity while
/// <c>P(7)</c> bound <c>x = 7, rest = []</c>.</para>
///
/// <para>The qualifications stay: the callback OPERATION decides how many values it supplies
/// (map and filter one element, reduce element plus accumulator, flat callees the row
/// convention), selection passes a value, spread opens a value, and an empty collection
/// invokes nothing. Lean: the S3 guards in <c>CoreTests/SequenceCallbackBuiltins.lean</c>.</para>
/// </summary>
public class CallbackNestedPatternBindingTests
{
    /// <summary>Nested-pattern shapes, each with the names its one-value list body reports.</summary>
    public static TheoryData<string, string> Patterns => new()
    {
        { "(x)", "x" },
        { "(x, *rest)", "x, rest" },
        { "(*xs)", "xs" },
        { "(x, y)", "x, y" },
        { "(*init, z)", "init, z" },
        { "(x, *r, z)", "x, r, z" },
        { "((x, *r))", "x, r" },
        { "(a, (b, *r))", "a, b, r" },
        { "(x, x)", "x" },
        { "(((x)))", "x" },
    };

    /// <summary>
    /// Supplied values: scalars of every kind, the empty sequence value, sequence values
    /// (flat, nested, with an empty item, with a repeated item), lists (empty, singleton,
    /// pair, holding a pair, holding a list, holding an empty sequence), and redundant
    /// groupings, which are the same value.
    /// </summary>
    private static readonly string[] Values =
    [
        "7", "'s'", "true", "()", "(1, 2)", "(1, 2, 3)", "((1, 2), 3)", "((), 1)", "(7, 7)",
        "[]", "[5]", "[1, 2]", "[(1, 2)]", "[[1, 2]]", "[()]", "(7)", "((1, 2))", "((7))",
    ];

    private static string Callee(string pattern, string names) => $"P({pattern}) = [{names}]\n";

    // ── The law: the same value binds the same pattern the same way ──────────

    [Theory]
    [MemberData(nameof(Patterns))]
    public void EveryCallbackOperation_BindsTheSuppliedValueLikeTheOrdinaryCall(string pattern, string names)
    {
        var callee = Callee(pattern, names);
        var keep = $"K({pattern}) = true\n";
        var reducer = $"R({pattern}, acc) = [{names}, acc]\n";
        foreach (var value in Values)
        {
            var direct = Run(callee + $"P({value})");

            AssertBindsAlike(direct, Run(callee + $"map([{value}], P)"), $"map([{value}], P) vs P({value}) for {pattern}");
            AssertBindsAlike(direct, Run(callee + $"[{value}].map(P)"), $"[{value}].map(P) vs P({value}) for {pattern}");

            // Selection passes a value: a stored list's element reaches the callback exactly
            // as the selection `L:0` reaches the ordinary call.
            AssertBindsAlike(
                Run(callee + $"L = [{value}]\nP(L:0)"),
                Run(callee + $"L = [{value}]\nmap(L, P)"),
                $"map(L, P) vs P(L:0) with L = [{value}] for {pattern}");

            // filter: the predicate binds the element like the call; a kept element is the
            // element itself, so the result is the one-element list `[value]`.
            var filtered = Run(keep + $"filter([{value}], K)");
            if (direct.IsOk)
            {
                Assert.True(filtered.IsOk, $"filter([{value}], K) failed for {pattern}: {Describe(filtered)}");
                Assert.Equal(Neutral(Run($"[{value}]")), Neutral(filtered));
            }
            else
            {
                Assert.True(filtered.IsError, $"filter([{value}], K) succeeded for {pattern} although P({value}) failed");
                Assert.Equal(BindingReason(direct.Error), BindingReason(filtered.Error));
            }

            // reduce supplies element AND accumulator: compare with the two-argument call.
            AssertEqualOutcome(
                Run(reducer + $"R({value}, 0)"),
                Run(reducer + $"reduce([{value}], R, 0)"),
                $"reduce([{value}], R, 0) vs R({value}, 0) for {pattern}");
        }
    }

    [Fact]
    public void ScalarOneItemFallback_IsOneItem_NeverZero_NeverMore()
    {
        // The characteristic cells, pinned directly so a regression shared by BOTH paths
        // cannot pass the agreement matrix: a scalar is ONE item for a head plus collector,
        // a collector plus suffix, and a nested group, and one item too few for a pair.
        AssertDisplay("P((x, *rest)) = [x, rest]\nP(7)\nmap([7], P)\n[7].map(P)", "[7, []]\n[[7, []]]\n[[7, []]]");
        AssertDisplay("P((x, *rest)) = [x, rest]\nmap(('s', true), P)", "[[s, []], [true, []]]");
        AssertDisplay("P((*init, z)) = [init, z]\nmap([7], P)", "[[[], 7]]");
        AssertDisplay("P(((x, *r))) = [x, r]\nmap([7], P)", "[[7, []]]");
        AssertDisplay("P((a, (b, *r))) = [a, b, r]\nmap([(1, 2)], P)", "[[1, 2, []]]");
        AssertDisplay("P((x, *rest)) = [x, rest]\nmap((7, (8, 9), [10]), P)", "[[7, []], [8, [9]], [10, []]]");

        foreach (var source in new[]
        {
            "P((x, y)) = [x, y]\nP(7)",
            "P((x, y)) = [x, y]\nmap([7], P)",
            "P((x, y)) = [x, y]\n[7].map(P)",
            "P((x, y)) = x > 0\nfilter([7], P)",
            "P((x, y), acc) = acc\nreduce([7], P, 0)",
        })
        {
            var result = Run(source);
            Assert.True(result.IsError, source);
            Assert.Equal("ArityMismatch(2, 1) in [(x, y)]", BindingReason(result.Error));
        }

        // `(x, *r, z)` needs two items: a scalar supplies one (at least 2, received 1).
        Assert.Equal(
            BindingReason(Run("P((x, *r, z)) = x\nP(7)").Error),
            BindingReason(Run("P((x, *r, z)) = x\nmap([7], P)").Error));
    }

    [Fact]
    public void CallbackFailure_KeepsTheCallbackFrameAndASourceLocation()
    {
        // Only the OUTER frame differs from the direct call: the callback failure carries the
        // map transform frame structurally, renders the same pattern message the direct call
        // renders, and stays located (a present span on the map row, never a fabricated one).
        var result = Run("P((x, y)) = [x, y]\n\nmap([7], P)");
        var direct = Run("P((x, y)) = [x, y]\n\nP(7)");
        Assert.True(result.IsError);
        Assert.True(direct.IsError);

        var frames = new List<string>();
        for (var current = result.Error; current is EvalError.WithContext context; current = context.Inner)
            frames.Add(context.Context);
        Assert.Contains(frames, frame => frame.Contains("while evaluating map transform", StringComparison.Ordinal));

        var error = KatLangError.FromEvalError(result.Error);
        Assert.Equal("Sequence-value parameter pattern `(x, y)` expects 2 values, but received 1 value.", error.Message);
        Assert.Equal(KatLangError.FromEvalError(direct.Error).Message, error.Message);
        Assert.Equal(KatLangError.FromEvalError(direct.Error).Code, error.Code);
        var span = Assert.IsType<SourceSpan>(error.Span);
        Assert.Equal(3, span.Start.Line);
    }

    // ── Value boundaries: callback provenance changes nothing ───────────────

    [Fact]
    public void CallbackItems_AreValues_NotOpenedByIteration()
    {
        // A list element and a sequence element are ONE value each: a flat one-parameter
        // callee receives them whole, and only the pattern (as in the direct call) or an
        // explicit spread opens them.
        AssertDisplay("Wrap(x) = [x]\nmap([(1, 2), [3, 4], ()], Wrap)", "[[(1, 2)], [[3, 4]], [()]]");
        AssertDisplay("P((*xs)) = xs\nmap([(1, 2), [3, 4], ()], P)", "[[1, 2], [3, 4], []]");
        AssertDisplay("P((*xs)) = xs\n[P((1, 2)), P([3, 4]), P(())]", "[[1, 2], [3, 4], []]");
        AssertDisplay("Coll(*xs) = xs\nmap([[1, 2]], Coll)", "[[[1, 2]]]");
        AssertDisplay("Coll(*xs) = xs\nColl([1, 2]*)", "[1, 2]");

        // A singleton list's element is the callback item, with its own identity: the pair
        // inside `[(1, 2)]` reaches `(x)` as ONE pair value it cannot bind to one item.
        Assert.Equal(
            BindingReason(Run("P((x)) = x\nP((1, 2))").Error),
            BindingReason(Run("P((x)) = x\nmap([(1, 2)], P)").Error));
    }

    [Fact]
    public void EmptyCollection_InvokesNothing_WhileAnEmptyItem_IsOneInvocation()
    {
        var ticks = new List<Decimal128>();
        var operations = TickOperations(ticks);

        Assert.Equal("[]", DisplayWith("P((x, *rest)) = [Tick(1), x]\nmap([], P)", operations));
        Assert.Empty(ticks);

        // `()` is one selected value: one invocation, bound like `P(())`.
        Assert.Equal("[[1, []]]", DisplayWith("P((*xs)) = [Tick(1), xs]\nmap([()], P)", operations));
        Assert.Equal([(Decimal128)1], ticks);
    }

    [Fact]
    public void CallbackSlots_ReceiveTheAlgorithm_AndUnusedCallbacksNeverRun()
    {
        // S1: a callable written in the callback slot that CAN satisfy a zero-argument value
        // demand is still passed as a callable — never demanded before (or instead of) its
        // invocations — and an empty collection runs it zero times. (The same callable
        // FORWARDED THROUGH A PARAMETER currently reaches the slot as its demanded value — a
        // pre-existing callback-channel defect recorded in SEMANTIC-ALIGNMENT.md beside S3,
        // which never affects a nested-pattern callee: a top-level group needs one slot.)
        var ticks = new List<Decimal128>();
        var operations = TickOperations(ticks);

        Assert.Equal("[]", DisplayWith("Z(*xs) = [Tick(1), xs]\nmap([], Z)", operations));
        Assert.Empty(ticks);
        Assert.Equal("[[1, [7]]]", DisplayWith("Z(*xs) = [Tick(1), xs]\nmap([7], Z)", operations));
        Assert.Equal([(Decimal128)1], ticks);

        ticks.Clear();
        Assert.Equal("[[1, 7, []]]", DisplayWith("P((x, *rest)) = [Tick(1), x, rest]\nmap([7], P)", operations));
        Assert.Equal([(Decimal128)1], ticks);
    }

    [Fact]
    public void CallbackBodies_RunExactlyOnceInCollectionOrder()
    {
        var ticks = new List<Decimal128>();
        var operations = TickOperations(ticks);

        Assert.Equal(
            "[[7, []], [8, [9]], [10, []]]",
            DisplayWith("P((x, *rest)) = [Tick(x), rest]\nmap((7, (8, 9), [10]), P)", operations));
        Assert.Equal([(Decimal128)7, 8, 10], ticks);

        // A binding failure stops the traversal at the failing element: nothing after it runs.
        ticks.Clear();
        Assert.StartsWith(
            "err",
            NeutralWith("P((x, y)) = [Tick(x), y]\nmap([(1, 2), 7, (3, 4)], P)", operations),
            StringComparison.Ordinal);
        Assert.Equal([(Decimal128)1], ticks);
    }

    // ── Clause families use the ordinary branch matcher ─────────────────────

    [Theory]
    [InlineData("7")]
    [InlineData("0")]
    [InlineData("(1, 2)")]
    [InlineData("(1, 2, 3)")]
    [InlineData("[1, 2]")]
    [InlineData("()")]
    public void ClauseFamilyCallbacks_SelectTheBranchTheOrdinaryCallSelects(string value)
    {
        const string family = "F(0) = [100]\nF((a, b)) = [a + b]\nF((x)) = [x]\n";
        var direct = Run(family + $"F({value})");
        var mapped = Run(family + $"map([{value}], F)");
        if (direct.IsOk)
        {
            AssertBindsAlike(direct, mapped, $"map([{value}], F)");
            return;
        }

        // Branch selection is the ordinary matcher, so both fail to match; the no-match error
        // names the family in the direct call and the callback ROLE in the callback — a
        // pre-existing, Lean-aligned label (NoMatchingBranch(calleeName)), not a binding
        // difference.
        Assert.Equal("NoMatchingBranch(F) in []", BindingReason(direct.Error));
        Assert.True(mapped.IsError, $"map([{value}], F) succeeded although F({value}) matched no branch");
        Assert.Equal("NoMatchingBranch(map transform) in []", BindingReason(mapped.Error));
    }

    // ── Strategies: generic, optimized, async, fused ────────────────────────

    [Theory]
    [MemberData(nameof(Patterns))]
    public void CallbackBinding_AgreesAcrossGenericOptimizedAndAsyncExecution(string pattern, string names)
    {
        var callee = Callee(pattern, names);
        foreach (var value in Values)
        {
            foreach (var program in new[]
            {
                $"map([{value}], P)",
                $"[{value}, {value}].map(P)",
                $"R({pattern}, acc) = [{names}, acc]\nreduce([{value}], R, 0)",
                $"R({pattern}, *acc) = [{names}, acc]\nreduce([{value}], R, (1, 2))",
            })
            {
                AssertStrategiesAgree(callee + program, expectFusion: false);
            }

            // The fusion-recognized spelling: the optimized leg runs the fused filter→count
            // pipeline (engagement asserted), which binds through the same predicate path.
            AssertStrategiesAgree(callee + $"K({pattern}) = true\n[{value}, {value}].filter(K).count", expectFusion: true);
        }
    }

    // ── The reducer's accumulator-slot route (top-level collecting accumulator) ──

    /// <summary>
    /// Initial accumulators and the ordinary-call spelling of the SAME supply: a reducer with
    /// a top-level collecting accumulator parameter receives the element followed by the
    /// accumulator's one-level slots, so the ordinary call supplies those slots as written
    /// arguments (a slot is collected exactly in both: final there, a non-lone written slot
    /// or a lone list here).
    /// </summary>
    private static readonly (string Initial, string Slots)[] Accumulators =
    [
        ("0", "0"),
        ("(1, 2)", "1, 2"),
        ("((1, 2), 3)", "(1, 2), 3"),
        ("[1, 2]", "[1, 2]"),
    ];

    [Theory]
    [MemberData(nameof(Patterns))]
    public void AccumulatorSlotReducers_BindTheElementLikeTheOrdinaryCallWithTheSameSupply(string pattern, string names)
    {
        var reducer = $"R({pattern}, *acc) = [{names}, acc]\n";
        foreach (var value in Values)
        {
            foreach (var (initial, slots) in Accumulators)
            {
                AssertEqualOutcome(
                    Run(reducer + $"R({value}, {slots})"),
                    Run(reducer + $"reduce([{value}], R, {initial})"),
                    $"reduce([{value}], R, {initial}) vs R({value}, {slots}) for {pattern}");
            }
        }

        // The documented example, pinned by value.
        AssertDisplay("R((a, *r), *acc) = [a, r, acc]\nreduce([7], R, (1, 2))\nR(7, 1, 2)", "[7, [], [1, 2]]\n[7, [], [1, 2]]");
    }

    // ── The explorer's direct/callback template pairs are related, value by value ──

    [Theory]
    [InlineData("patternHead", "patternHeadMap")]
    [InlineData("patternPair", "patternPairMap")]
    public void ExplorerTemplatePairs_MapEveryValueExactlyAsTheDirectCall(string directTemplate, string callbackTemplate)
    {
        // Each template is pinned against Lean on its own (SemanticExplorerCases.lean); this
        // relates the two spellings for every corpus value: the callback's one mapped element
        // is the direct result, or both fail in the same category.
        var cases = SemanticExplorerCorpus.AllCases();
        var direct = cases.Where(c => c.TemplateId == directTemplate).ToDictionary(c => c.ValueId);
        var callback = cases.Where(c => c.TemplateId == callbackTemplate).ToDictionary(c => c.ValueId);
        Assert.Equal(SemanticExplorerCorpus.Values.Count, direct.Count);
        Assert.Equal(direct.Keys.OrderBy(static id => id), callback.Keys.OrderBy(static id => id));

        foreach (var (valueId, directCase) in direct)
        {
            var directObservation = SemanticExplorerHarness.Observe(directCase);
            var callbackObservation = SemanticExplorerHarness.Observe(callback[valueId]);
            var expected = directObservation.Outcome == "ok"
                ? $"ok raw=L[{directObservation.Raw}] n=1"
                : directObservation.Neutral;
            Assert.True(
                expected == callbackObservation.Neutral,
                $"{callbackTemplate}__{valueId}: expected {expected} (from {directObservation.Neutral}) but observed {callbackObservation.Neutral}");
        }
    }

    [Theory]
    [InlineData("K((x, *rest)) = x > 1\n[7, 1, 3].filter(K).count", "ok raw=2 n=1")]
    [InlineData("K((x, *rest)) = x > 1\n(7, (1, 5), [3], 1).filter(K).count", "ok raw=2 n=1")]
    [InlineData("K((x, *rest)) = x > 2\ncount(filter(range(1, 5), K))", "ok raw=3 n=1")]
    [InlineData("K((x, y)) = x > 1\n[7, 1].filter(K).count", "err arity")]
    public void FilterCountFusion_BindsNestedPatternPredicatesLikeTheGenericPath(string source, string expected)
    {
        var sequence = new SequencePipelineDiagnostics();
        var (fused, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(source), sequenceDiagnostics: sequence);
        var (generic, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(source), enableOptimizations: false);

        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(generic));
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(fused));
        Assert.Equal(1, sequence.GetSnapshot().FilterCountFusionHits);
    }

    [Fact]
    public async Task SuspendedCallback_BindsTheSameValues_ExactlyOnce()
    {
        // The async twin calls the same binder; the host operation in the callback body
        // genuinely suspends on the first element, and resumption neither re-binds nor
        // re-invokes anything.
        const string source = "P((x, *rest)) = [Tick(x), rest]\nmap((7, (8, 9), [10]), P)";
        var syncTicks = new List<Decimal128>();
        var expected = NeutralWith(source, TickOperations(syncTicks));
        Assert.Equal("ok raw=L[L[7, L[]], L[8, L[9]], L[10, L[]]] n=1", expected);

        var ticks = new List<Decimal128>();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var operations = HostOperations.Create(HostOperation.CreateAsync("Tick", async (args, _) =>
        {
            ticks.Add(Assert.IsType<Result.Atom>(args[0]).Value);
            if (ticks.Count == 1)
            {
                reached.SetResult();
                await release.Task;
            }
            return args[0];
        }, "value"));
        var ast = new Expr.AlgorithmExpr(Parse(source, operations));
        var pending = Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache(), hostOperations: operations).AsTask();
        try
        {
            await reached.Task.WaitAsync(TimeSpan.FromSeconds(45));
            Assert.False(pending.IsCompleted);
            Assert.Equal([(Decimal128)7], ticks);
        }
        finally
        {
            release.TrySetResult();
        }

        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(await pending.WaitAsync(TimeSpan.FromSeconds(45))));
        Assert.Equal(syncTicks, ticks);
    }

    [Fact]
    public async Task SuspendedCallback_BindingFailureAfterResumption_MatchesTheSynchronousFailure()
    {
        const string source = "P((x, y)) = [Tick(x), y]\nmap([(1, 2), 7], P)";
        var syncTicks = new List<Decimal128>();
        var expected = Evaluator.RunCounted(
            new Expr.AlgorithmExpr(Parse(source, TickOperations(syncTicks))),
            new RunScopedZeroArgPropertyResultCache(),
            hostOperations: TickOperations(syncTicks));
        Assert.True(expected.IsError);
        Assert.Equal("ArityMismatch(2, 1) in [(x, y)]", BindingReason(expected.Error));

        var ticks = new List<Decimal128>();
        var operations = HostOperations.Create(HostOperation.CreateAsync("Tick", async (args, _) =>
        {
            ticks.Add(Assert.IsType<Result.Atom>(args[0]).Value);
            await Task.Yield();
            return args[0];
        }, "value"));
        var actual = await Evaluator.RunCountedAsync(
            new Expr.AlgorithmExpr(Parse(source, operations)),
            new PassThroughAsyncZeroArgPropertyResultCache(),
            hostOperations: operations).AsTask().WaitAsync(TimeSpan.FromSeconds(45));

        Assert.True(actual.IsError);
        Assert.Equal(BindingReason(expected.Error), BindingReason(actual.Error));
        Assert.Equal([(Decimal128)1], ticks);
    }

    [Fact]
    public async Task CancellationWhileACallbackIsSuspended_CancelsTheRun_WithoutReplay()
    {
        using var cancellation = new CancellationTokenSource();
        var ticks = new List<Decimal128>();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var options = new RunOptions
        {
            EvaluationCancellationToken = cancellation.Token,
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("Tick", async (args, _) =>
            {
                ticks.Add(Assert.IsType<Result.Atom>(args[0]).Value);
                reached.TrySetResult();
                await release.Task;
                return args[0];
            }, "value")),
        };

        var pending = KatLangEngine.RunAsync("P((x, *rest)) = [Tick(x), rest]\nmap((7, 8), P)", options);
        await reached.Task.WaitAsync(TimeSpan.FromSeconds(45));
        cancellation.Cancel();
        release.SetResult();

        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => pending.WaitAsync(TimeSpan.FromSeconds(45)));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal([(Decimal128)7], ticks);
    }

    // ── Host-built pattern shapes: the law is structural, not parser-specific ──

    public static TheoryData<string> HostShapes => new()
    {
        "empty group",
        "empty group then collector",
        "deeply nested collector",
        "collector between two nested groups",
    };

    [Theory]
    [MemberData(nameof(HostShapes))]
    public void HostBuiltPatterns_BindCallbackValuesLikeTheOrdinaryCall(string shape)
    {
        var (patterns, names) = HostPattern(shape);
        var callee = new Algorithm.User(
            Parent: null,
            ParameterPatterns: patterns,
            Opens: [],
            Properties: [],
            Output: [new Expr.ListLiteral([.. names.Select(static name => (Expr)new Expr.Param(name))])]);

        foreach (var argument in new Expr[]
        {
            new Expr.Num(7),
            new Expr.EmptySequence(0),
            new Expr.Capture([new Expr.Num(1), new Expr.Num(2)]),
            new Expr.ListLiteral([new Expr.Num(5)]),
            new Expr.ListLiteral([new Expr.Capture([new Expr.Num(1), new Expr.Num(2)]), new Expr.Num(3)]),
        })
        {
            var direct = RunHost(callee, new Expr.Call(new Expr.Resolve("P"), [argument]));
            var mapped = RunHost(callee, new Expr.Call(new Expr.Resolve("map"), [new Expr.ListLiteral([argument]), new Expr.Resolve("P")]));
            AssertBindsAlike(direct, mapped, $"{shape} over {argument}");
        }
    }

    private static (IReadOnlyList<ParameterPattern> Patterns, string[] Names) HostPattern(string shape)
        => shape switch
        {
            "empty group" => ([new SequenceValueParameterPattern([])], []),
            "empty group then collector" => (
                [new SequenceValueParameterPattern([]), new CaptureParameterPattern("r", Kind: ParameterKind.Collecting)],
                ["r"]),
            "deeply nested collector" => (
                [new SequenceValueParameterPattern([
                    new SequenceValueParameterPattern([
                        new SequenceValueParameterPattern([new CaptureParameterPattern("r", Kind: ParameterKind.Collecting)])])])],
                ["r"]),
            "collector between two nested groups" => (
                [new SequenceValueParameterPattern([
                    new SequenceValueParameterPattern([new CaptureParameterPattern("x")]),
                    new CaptureParameterPattern("m", Kind: ParameterKind.Collecting),
                    new SequenceValueParameterPattern([new CaptureParameterPattern("z")])])],
                ["x", "m", "z"]),
            _ => throw new ArgumentOutOfRangeException(nameof(shape), shape, null),
        };

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static EvalResult<Result> Run(string source)
        => Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));

    private static EvalResult<Result> RunHost(Algorithm.User callee, Expr output)
        => Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties: [new Property("P", callee)],
            Output: [output])));

    private static Algorithm.User Parse(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static diagnostic => diagnostic.Message)));
        return parsed.Root;
    }

    private static HostOperations TickOperations(List<Decimal128> ticks)
        => HostOperations.Create(HostOperation.Create("Tick", (args, _) =>
        {
            ticks.Add(Assert.IsType<Result.Atom>(args[0]).Value);
            return args[0];
        }, "value"));

    private static string NeutralWith(string source, HostOperations operations)
        => AsyncEvaluationHarness.NeutralOf(Evaluator.RunCounted(
            new Expr.AlgorithmExpr(Parse(source, operations)),
            new RunScopedZeroArgPropertyResultCache(),
            hostOperations: operations));

    private static string DisplayWith(string source, HostOperations operations)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, new RunOptions { HostOperations = operations }))
            .ToDisplayString()
            .ReplaceLineEndings("\n");

    private static void AssertDisplay(string source, string expected)
        => Assert.Equal(expected, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n"));

    private static string Neutral(EvalResult<Result> result) => AsyncEvaluationHarness.NeutralOf(result);

    private static string Describe(EvalResult<Result> result)
        => result.IsOk ? Neutral(result) : KatLangError.FromEvalError(result.Error).Message;

    /// <summary>
    /// The direct call's bound result is the callback's ONE mapped element, or both fail for
    /// the same binding reason.
    /// </summary>
    private static void AssertBindsAlike(EvalResult<Result> direct, EvalResult<Result> callback, string label)
    {
        if (direct.IsOk)
        {
            Assert.True(callback.IsOk, $"{label}: the direct call gave {Neutral(direct)} but the callback failed: {Describe(callback)}");
            Assert.True(
                Result.ValueComparer.Equals(new Result.ListValue([direct.Value]), callback.Value),
                $"{label}: the direct call bound {Neutral(direct)} but the callback mapped {Neutral(callback)}");
            return;
        }

        Assert.True(callback.IsError, $"{label}: the direct call failed ({Describe(direct)}) but the callback gave {Neutral(callback)}");
        Assert.Equal(BindingReason(direct.Error), BindingReason(callback.Error));
    }

    private static void AssertEqualOutcome(EvalResult<Result> expected, EvalResult<Result> actual, string label)
    {
        if (expected.IsOk)
        {
            Assert.True(actual.IsOk, $"{label}: expected {Neutral(expected)} but failed: {Describe(actual)}");
            Assert.True(Result.ValueComparer.Equals(expected.Value, actual.Value), $"{label}: {Neutral(expected)} vs {Neutral(actual)}");
            return;
        }

        Assert.True(actual.IsError, $"{label}: expected failure ({Describe(expected)}) but got {Neutral(actual)}");
        Assert.Equal(BindingReason(expected.Error), BindingReason(actual.Error));
    }

    /// <summary>
    /// The pattern-binding reason of a failure: the innermost error with its payload and the
    /// nested sequence-value groups it is attributed to — everything except the outer
    /// call/map/filter/reduce frames, which legitimately differ between the direct call and a
    /// callback invocation.
    /// </summary>
    private static string BindingReason(EvalError error)
    {
        var groups = new List<string>();
        while (error is EvalError.WithContext context)
        {
            if (context.ErrorContext is SequenceValueParameterBindingContext group)
                groups.Add(group.PatternDisplayName);
            error = context.Inner;
        }

        // The full structured payload of every kind a binding failure can carry, so a
        // payload difference can never hide behind an equal error TYPE.
        var payload = error switch
        {
            EvalError.ArityMismatch arity => $"ArityMismatch({arity.Expected}, {arity.Actual})",
            EvalError.VariadicArityMismatch variadic => $"VariadicArityMismatch({variadic.CalleeName}, {variadic.ExpectedMinimum}, {variadic.Actual})",
            EvalError.NoMatchingBranch noMatch => $"NoMatchingBranch({noMatch.AlgorithmName})",
            EvalError.TypeMismatch mismatch => $"TypeMismatch({mismatch.Message})",
            EvalError.BadArity => "BadArity",
            _ => $"{error.GetType().Name}[{error.Code}]",
        };
        return $"{payload} in [{string.Join(", ", groups)}]";
    }

    /// <summary>
    /// Generic, optimized, and async-twin execution agree on the outcome AND, for a failure,
    /// on the full binding reason (an error category alone would not tell the ordinary
    /// nested-group ArityMismatch from the former bare BadArity). With
    /// <paramref name="expectFusion"/> the optimized leg must actually run the fused
    /// filter→count pipeline; otherwise no optimizer can engage for the shape (planned loops
    /// decline patterned steps), and the leg pins that the optimizer switch changes nothing.
    /// </summary>
    private static void AssertStrategiesAgree(string source, bool expectFusion)
    {
        var ast = AsyncEvaluationHarness.Ast(source);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var sequence = new SequencePipelineDiagnostics();
        var (planned, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: true, sequenceDiagnostics: sequence);
        var expected = AsyncEvaluationHarness.NeutralOf(generic);
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(planned));
        Assert.Equal(expectFusion ? 1 : 0, sequence.GetSnapshot().FilterCountFusionHits);

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (asyncResult, asyncBudget) = AsyncEvaluationHarness
            .Complete(Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache))
            .GetAwaiter()
            .GetResult();
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(asyncResult));
        Assert.Equal(genericBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        Assert.Equal(0, cache.SyncAccesses);

        if (generic.IsError)
        {
            var reason = BindingReason(generic.Error);
            Assert.Equal(reason, BindingReason(planned.Error));
            Assert.Equal(reason, BindingReason(asyncResult.Error));
        }
    }
}
