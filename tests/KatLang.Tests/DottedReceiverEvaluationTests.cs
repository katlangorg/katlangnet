using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// A dotted receiver's VALUE is computed at most once per dotted operation.
///
/// <para><c>A.F(B)</c> means <c>F(A, B)</c>, so the two forms must agree on value, emitted
/// count, error, and resource consumption. They did not: the sequence-builtin dot path
/// evaluated the receiver to dispatch on it, then reified that result back into an AST
/// literal (<c>CountedArgAlgorithm</c> / <c>ResultToExpr</c>) which the builtin evaluated
/// AGAIN — so <c>range(1, 10).count</c> materialized twenty item slots for one ten-item
/// collection. A cached receiver property did not help, because the duplicate was a
/// reconstruction from the already-evaluated result rather than a second evaluation of the
/// source expression.</para>
///
/// <para>The follow-up correction made the reification itself lazy: the receiver is carried
/// forward as a prepared counted value with NO eagerly constructed expression-tree wrapper,
/// because the ordinary value path never consumes one. The wrapper is synthesized only if an
/// algorithm-only consumer requests the argument's algorithm channel, observed through the
/// run-scoped <see cref="EvaluationObservations.CountedArgumentReificationCount"/> counter
/// (see the lazy-reification section below).</para>
///
/// <para>Resource counts are the primary evidence here; nothing asserts elapsed time.</para>
/// </summary>
public class DottedReceiverEvaluationTests
{
    /// <summary>
    /// The smallest cumulative materialization budget that lets <paramref name="source"/>
    /// complete — a deterministic measure of how many item slots the run creates.
    /// </summary>
    private static long RequiredItemSlots(string source, bool optimize = true)
    {
        for (long n = 0; n <= 2_000; n++)
        {
            var limits = new EvaluationLimits { MaxMaterializedItems = n == 0 ? 1 : n };
            var expr = new Expr.Block(Parser.Parse(source).Root);
            var result = optimize
                ? Evaluator.Run(expr, limits)
                : Evaluator.Run(
                    expr, UncachedZeroArgPropertyResultCache.Instance,
                    enableLoopOptimization: false, loopDiagnostics: null,
                    enableSequencePipelineOptimization: false, sequenceDiagnostics: null, limits);
            if (!result.IsError) return n == 0 ? 1 : n;
        }

        Assert.Fail($"`{source}` never completed within the probe range.");
        return -1;
    }

    private static Result Value(string source)
    {
        var result = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root));
        if (result.IsError)
            Assert.Fail($"`{source}` failed: {KatLangError.FromEvalError(result.Error).Message}");
        return result.Value;
    }

    private static string DisplayOf(string source) => KatLangEngine.Run(source).ToDisplayString();

    // ── The reported defect ──────────────────────────────────────────────────

    [Fact]
    public void DottedCollectionBuiltin_MaterializesItsReceiverExactlyOnce()
    {
        Assert.Equal(10, RequiredItemSlots("range(1, 10)"));
        Assert.Equal(10, RequiredItemSlots("count(range(1, 10))"));
        Assert.Equal(10, RequiredItemSlots("range(1, 10).count"));
    }

    [Fact]
    public void CachedReceiverProperty_AlsoMaterializesOnce()
    {
        Assert.Equal(10, RequiredItemSlots("V = range(1, 10)\ncount(V)"));
        Assert.Equal(10, RequiredItemSlots("V = range(1, 10)\nV.count"));
    }

    [Fact]
    public void ExplicitZeroArgumentCallReceiver_MaterializesOnce()
        => Assert.Equal(
            RequiredItemSlots("V = range(1, 10)\ncount(V())"),
            RequiredItemSlots("V = range(1, 10)\nV().count"));

    // ── Ordinary/dotted parity across every collection builtin ───────────────

    [Theory]
    [InlineData("count(C)", "C.count")]
    [InlineData("sum(C)", "C.sum")]
    [InlineData("first(C)", "C.first")]
    [InlineData("last(C)", "C.last")]
    [InlineData("min(C)", "C.min")]
    [InlineData("max(C)", "C.max")]
    [InlineData("avg(C)", "C.avg")]
    [InlineData("order(C)", "C.order")]
    [InlineData("orderDesc(C)", "C.orderDesc")]
    [InlineData("distinct(C)", "C.distinct")]
    [InlineData("atoms(C)", "C.atoms")]
    [InlineData("take(C, 3)", "C.take(3)")]
    [InlineData("skip(C, 3)", "C.skip(3)")]
    [InlineData("contains(C, 3)", "C.contains(3)")]
    [InlineData("map(C, Double)", "C.map(Double)")]
    [InlineData("filter(C, Big)", "C.filter(Big)")]
    [InlineData("reduce(C, Add, 0)", "C.reduce(Add, 0)")]
    public void OrdinaryAndDottedForms_AgreeOnValueAndResources(string ordinary, string dotted)
    {
        const string preamble = "Double(x) = x * 2\nBig(x) = x > 5\nAdd(a, b) = a + b\n";
        var ordinarySource = $"{preamble}C = range(1, 10)\n{ordinary}";
        var dottedSource = $"{preamble}C = range(1, 10)\n{dotted}";

        Assert.Equal(Value(ordinarySource), Value(dottedSource), Result.ValueComparer);
        Assert.Equal(DisplayOf(ordinarySource), DisplayOf(dottedSource));
        Assert.Equal(RequiredItemSlots(ordinarySource), RequiredItemSlots(dottedSource));
    }

    // ── Receiver value kinds ─────────────────────────────────────────────────

    [Theory]
    [InlineData("7")]
    [InlineData("'text'")]
    [InlineData("()")]
    [InlineData("(1, 2, 3)")]
    [InlineData("[]")]
    [InlineData("[7]")]
    [InlineData("[1, 2, 3]")]
    [InlineData("[(1, 2), [3, 4]]")]
    [InlineData("[range(1, 3)*, 9]")]
    public void EveryReceiverValueKind_AgreesBetweenForms(string receiver)
    {
        var ordinarySource = $"R = {receiver}\ncount(R)";
        var dottedSource = $"R = {receiver}\nR.count";

        Assert.Equal(Value(ordinarySource), Value(dottedSource), Result.ValueComparer);
        Assert.Equal(RequiredItemSlots(ordinarySource), RequiredItemSlots(dottedSource));
    }

    // ── Receiver source forms ────────────────────────────────────────────────

    [Theory]
    [InlineData("[1, 2, 3]")]                       // list literal
    [InlineData("range(1, 5)")]                     // ordinary call
    [InlineData("(1, 2, 3)")]                       // parenthesized body
    [InlineData("Pick(1)")]                         // conditional call
    [InlineData("[1, 2, 3].take(2)")]               // nested dotted chain
    [InlineData("[[1, 2], [3, 4]]:0")]              // index result
    [InlineData("[1, 2, 3].map(Double)")]           // callback result
    public void EveryReceiverSourceForm_AgreesBetweenForms(string receiver)
    {
        const string preamble = "Double(x) = x * 2\nPick(0) = [9]\nPick(n) = [1, 2, 3]\n";
        var ordinarySource = $"{preamble}count({receiver})";
        var dottedSource = $"{preamble}({receiver}).count";

        Assert.Equal(Value(ordinarySource), Value(dottedSource), Result.ValueComparer);
        Assert.Equal(RequiredItemSlots(ordinarySource), RequiredItemSlots(dottedSource));
    }

    // ── Structural property access is untouched ──────────────────────────────

    [Fact]
    public void StructuralPropertyAccess_IsNotTurnedIntoAnExtensionCall()
    {
        Assert.Equal("7", DisplayOf("Object = {\n    public Value = 7\n}\nObject.Value"));
        Assert.Equal("7", DisplayOf("Object = {\n    public Value = 7\n    public Get = Value\n}\nObject.Get"));
    }

    [Fact]
    public void UnknownStructuralMember_StillFails()
        => Assert.IsType<RunResult.EvalFailure>(
            KatLangEngine.Run("Object = {\n    public Value = 7\n}\nObject.Missing"));

    [Fact]
    public void ExportedStructuralMember_KeepsItsExistingVisibilityOutcome()
        => Assert.Equal("7", DisplayOf("Object = {\n    Hidden = 7\n}\nObject.Hidden"));

    // ── User extension-style calls ───────────────────────────────────────────

    [Fact]
    public void UserExtensionCall_AgreesBetweenForms()
    {
        Assert.Equal(
            RequiredItemSlots("F(c) = c.count\nF(range(1, 10))"),
            RequiredItemSlots("F(c) = c.count\nrange(1, 10).F"));

        Assert.Equal(
            RequiredItemSlots("T(c, n) = take(c, n)\nT(range(1, 10), 3)"),
            RequiredItemSlots("T(c, n) = take(c, n)\nrange(1, 10).T(3)"));
    }

    [Fact]
    public void HigherOrderReceiver_KeepsItsAlgorithmMeaning()
    {
        // The receiver is callable, and the callee invokes it. Dotted syntax must not
        // reduce it to a value.
        Assert.Equal("14", DisplayOf("Apply(g, v) = g(v)\nDouble(x) = x * 2\nDouble.Apply(7)"));
        Assert.Equal(
            DisplayOf("Apply(g, v) = g(v)\nDouble(x) = x * 2\nApply(Double, 7)"),
            DisplayOf("Apply(g, v) = g(v)\nDouble(x) = x * 2\nDouble.Apply(7)"));
    }

    // ── Nested chains ────────────────────────────────────────────────────────

    [Fact]
    public void NestedChain_EvaluatesEachLinkReceiverOnce()
    {
        const string preamble = "B(x) = x > 5\nD(x) = x * 2\n";
        var ordinarySource = $"{preamble}count(map(filter(range(1, 10), B), D))";
        var dottedSource = $"{preamble}range(1, 10).filter(B).map(D).count";

        Assert.Equal(Value(ordinarySource), Value(dottedSource), Result.ValueComparer);
        Assert.Equal(RequiredItemSlots(ordinarySource), RequiredItemSlots(dottedSource));
    }

    // ── Plain / counted / engine and optimizer parity ────────────────────────

    [Theory]
    [InlineData("range(1, 10).count")]
    [InlineData("range(1, 10).order")]
    [InlineData("B(x) = x > 5\nrange(1, 10).filter(B).count")]
    public void PlainCountedAndEngine_Agree(string source)
    {
        var expr = new Expr.Block(Parser.Parse(source).Root);
        var plain = Evaluator.Run(expr);
        var counted = Evaluator.RunCounted(expr, UncachedZeroArgPropertyResultCache.Instance);
        var engine = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));

        Assert.False(plain.IsError);
        Assert.False(counted.IsError);
        Assert.Equal(plain.Value, counted.Value.Value, Result.ValueComparer);
        Assert.Equal(plain.Value, engine.Value, Result.ValueComparer);
        Assert.Equal(counted.Value.EmittedCount, engine.EmittedCount);
    }

    [Theory]
    [InlineData("range(1, 10).order")]
    [InlineData("range(1, 10).distinct")]
    [InlineData("D(x) = x * 2\nrange(1, 10).map(D)")]
    public void OptimizedAndGenericPaths_ChargeTheSame(string source)
        => Assert.Equal(RequiredItemSlots(source, optimize: false), RequiredItemSlots(source, optimize: true));

    [Theory]
    [InlineData("range(1, 10).count")]
    [InlineData("range(1, 10).sum")]
    [InlineData("B(x) = x > 5\nrange(1, 10).filter(B).count")]
    public void FusedPipelines_ChargeNoMoreThanTheGenericPath(string source)
    {
        // A fused pipeline materializes nothing, so it legitimately charges LESS — that
        // difference is the documented fusion contract. What must never happen is the
        // optimized path charging MORE than the generic one.
        Assert.True(RequiredItemSlots(source, optimize: true) <= RequiredItemSlots(source, optimize: false));
    }

    // ── Budget-boundary parity ───────────────────────────────────────────────

    [Fact]
    public void OrdinaryAndDottedForms_CrossCumulativeBoundariesIdentically()
    {
        const string ordinary = "count(range(1, 10))";
        const string dotted = "range(1, 10).count";

        for (long budget = 1; budget <= 24; budget++)
        {
            var limits = new EvaluationLimits { MaxMaterializedItems = budget };
            Assert.Equal(
                Evaluator.Run(new Expr.Block(Parser.Parse(ordinary).Root), limits).IsError,
                Evaluator.Run(new Expr.Block(Parser.Parse(dotted).Root), limits).IsError);
        }
    }

    // ── Errors, order, and spans ─────────────────────────────────────────────

    [Fact]
    public void ReceiverErrorStillWinsOverSuffixArgumentError()
    {
        // Evaluation order is unchanged: the receiver is prepared first, so its error is
        // the one reported.
        var result = KatLangEngine.Run("range(1, 10).take(Missing)");
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Contains("Missing", failure.Errors[0].Message);
    }

    [Fact]
    public void ReceiverEvaluationError_IsSurfacedWithASpan()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("Missing.count"));
        Assert.NotNull(failure.Errors[0].StartLine);
    }

    [Fact]
    public void ResourceLimitReachedByTheReceiver_IsReportedIdenticallyInBothForms()
    {
        var limits = new EvaluationLimits { MaxCollectionItems = 5 };
        var ordinary = Evaluator.Run(new Expr.Block(Parser.Parse("count(range(1, 10))").Root), limits);
        var dotted = Evaluator.Run(new Expr.Block(Parser.Parse("range(1, 10).count").Root), limits);

        // Spans differ because the two SOURCES differ; the structured payload must not.
        var ordinaryLimit = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ordinary.Error);
        var dottedLimit = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(dotted.Error);
        Assert.Equal(ordinaryLimit.Limit, dottedLimit.Limit);
        Assert.Equal(ordinaryLimit.Requested, dottedLimit.Requested);
        Assert.NotNull(dottedLimit.Span);
    }

    // ── Observed-run parity: values, counts, errors, and charged work ────────

    /// <summary>One observed run: semantic outcome plus the work the run charged.</summary>
    private sealed record ObservedRun(
        string Outcome,
        int? Emitted,
        long Steps,
        long Items,
        long StringChars,
        int PeakDepth,
        long Reifications);

    /// <summary>
    /// Runs <paramref name="source"/> once with a fresh run-scoped
    /// <see cref="EvaluationObservations"/> (zero by construction, no reset, no static
    /// state). <paramref name="optimize"/> defaults to false so the GENERIC dot-call path —
    /// the one that prepares the receiver argument — is the path observed.
    /// </summary>
    private static ObservedRun Observe(string source, bool optimize = false)
    {
        var observations = new EvaluationObservations();
        return ObserveCore(source, optimize, observations);
    }

    private static ObservedRun ObserveCore(
        string source,
        bool optimize,
        EvaluationObservations? observations)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, $"`{source}` did not parse.");

        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.Block(parsed.Root),
            enableOptimizations: optimize,
            observations: observations);

        return new ObservedRun(
            result.IsError
                ? "err:" + SemanticExplorerHarness.ErrorCategory(result.Error)
                : "ok:" + SemanticExplorerHarness.Neutral(result.Value.Value),
            result.IsError ? null : result.Value.EmittedCount,
            budget.ConsumedSteps,
            budget.MaterializedItems,
            budget.MaterializedStringChars,
            budget.PeakDepth,
            observations?.CountedArgumentReificationCount ?? 0);
    }

    [Theory]
    [InlineData("7")]
    [InlineData("'text'")]
    [InlineData("()")]
    [InlineData("(1, 2, 3)")]
    [InlineData("[]")]
    [InlineData("[7]")]
    [InlineData("[1, 2, 3]")]
    [InlineData("[(1, 2), [3, 4]]")]
    [InlineData("((1, 2), (3, 4))")]
    [InlineData("range(1, 6)")]
    public void ValueOnlyDotReceivers_MatchPlainCallsOnValueCountErrorsAndCharges(string receiver)
    {
        // Success AND failure cases live in this matrix (`().first` and `'text'.sum` are
        // arity errors; both forms must agree on the category). Steps are asserted
        // separately: a zero-argument property receiver charges its property-access
        // invocation on the dot path only, a pre-existing accounting difference outside
        // this matrix's relation.
        foreach (var (plain, dotted) in new (string, string)[]
        {
            ("count(R)", "R.count"),
            ("first(R)", "R.first"),
            ("take(R, 2)", "R.take(2)"),
            ("skip(R, 1)", "R.skip(1)"),
            ("sum(R)", "R.sum"),
        })
        {
            var a = Observe($"R = {receiver}\n{plain}");
            var b = Observe($"R = {receiver}\n{dotted}");

            Assert.Equal(a.Outcome, b.Outcome);
            Assert.Equal(a.Emitted, b.Emitted);
            Assert.Equal(a.Items, b.Items);
            Assert.Equal(a.StringChars, b.StringChars);
            Assert.Equal(0, a.Reifications);
            Assert.Equal(0, b.Reifications);
        }
    }

    [Theory]
    [InlineData("count(range(1, 10))", "range(1, 10).count")]
    [InlineData("take(range(1, 10), 3)", "range(1, 10).take(3)")]
    [InlineData("Bad(3) = 'a' + 1\nBad(x) = x * 2\nmap(range(1, 6), Bad)", "Bad(3) = 'a' + 1\nBad(x) = x * 2\nrange(1, 6).map(Bad)")]
    [InlineData("B(x) = x > 5\nD(x) = x * 2\ncount(map(filter(range(1, 10), B), D))", "B(x) = x > 5\nD(x) = x * 2\nrange(1, 10).filter(B).map(D).count")]
    public void CallShapedReceivers_ChargeExactlyEqualWorkInBothForms(string plain, string dotted)
    {
        // For call-shaped receivers no property-access asymmetry exists, so the two
        // spellings must agree on EVERY observation, steps included.
        Assert.Equal(Observe(plain), Observe(dotted));
    }

    // ── Higher-order builtins: callbacks stay unevaluated until applied ──────

    [Fact]
    public void CallbacksRemainUnevaluatedUntilApplied()
    {
        // An always-failing callback over an empty receiver never runs, in both forms and
        // for both collection kinds — the callback algorithm is carried, not pre-evaluated.
        Assert.Equal("ok:L[]", Observe("Boom(x) = 'a' + 1\n().map(Boom)").Outcome);
        Assert.Equal("ok:L[]", Observe("Boom(x) = 'a' + 1\n[].map(Boom)").Outcome);
        Assert.Equal("ok:L[]", Observe("Boom(x) = 'a' + 1\nmap((), Boom)").Outcome);
        Assert.Equal("ok:L[]", Observe("Boom(x) = 'a' + 1\nmap([], Boom)").Outcome);
        Assert.Equal("ok:L[]", Observe("Boom(x) = 'a' + 1\n().filter(Boom)").Outcome);
        Assert.Equal("ok:7", Observe("Boom(x) = 'a' + 1\n().reduce(Boom, 7)").Outcome);
    }

    [Theory]
    [InlineData("map(range(1, 6), Bad)", "range(1, 6).map(Bad)")]
    [InlineData("filter(range(1, 6), Bad)", "range(1, 6).filter(Bad)")]
    [InlineData("reduce(range(1, 6), BadReducer, 0)", "range(1, 6).reduce(BadReducer, 0)")]
    public void FailingCallbacks_FailIdenticallyInBothForms(string plain, string dotted)
    {
        // The callback fails on element 3, so both forms must fail with the same category
        // AFTER the same amount of work (failure order and short-circuit preserved).
        const string preamble =
            "Bad(3) = 'a' + 1\nBad(x) = x * 2\nBadReducer(acc, 3) = 'a' + 1\nBadReducer(acc, x) = acc + x\n";
        var a = Observe(preamble + plain);
        var b = Observe(preamble + dotted);

        Assert.Equal("err:type", a.Outcome);
        Assert.Equal(a, b);
    }

    // ── Frozen generic-path accounting ───────────────────────────────────────

    [Theory]
    [InlineData("V = range(1, 10)\nV.count", 1, 10, "ok:10")]
    [InlineData("V = range(1, 10)\nV().count", 1, 10, "ok:10")]
    [InlineData("V = range(1, 10)\ncount(V())", 1, 10, "ok:10")]
    [InlineData("V = range(1, 10)\nV.take(3)", 1, 13, "ok:L[1, 2, 3]")]
    [InlineData("D(x) = x * 2\nV = range(1, 3)\nV.map(D)", 4, 6, "ok:L[2, 4, 6]")]
    public void GenericDotPath_ChargesExactlyTheFrozenWork(string source, long steps, long items, string outcome)
    {
        // These absolute charges were captured from the EAGER implementation and verified
        // unchanged by the lazy-receiver change: a zero-argument builtin property, an
        // explicit-call receiver, a suffix argument, and a higher-order builtin evaluate
        // their receiver exactly once and charge identical steps and item slots.
        var run = Observe(source);
        Assert.Equal(outcome, run.Outcome);
        Assert.Equal(steps, run.Steps);
        Assert.Equal(items, run.Items);
        Assert.Equal(0, run.Reifications);
    }

    [Theory]
    [InlineData("take(range(1, 10), 3)", "range(1, 10).take(3)", 16)]
    [InlineData("D(x) = x * 2\nmap(range(1, 8), D)", "D(x) = x * 2\nrange(1, 8).map(D)", 20)]
    public void SuffixAndCallbackForms_CrossCumulativeBoundariesIdentically(string ordinary, string dotted, long maxBudget)
    {
        for (long budget = 1; budget <= maxBudget; budget++)
        {
            var limits = new EvaluationLimits { MaxMaterializedItems = budget };
            Assert.Equal(
                Evaluator.Run(new Expr.Block(Parser.Parse(ordinary).Root), limits).IsError,
                Evaluator.Run(new Expr.Block(Parser.Parse(dotted).Root), limits).IsError);
        }
    }

    // ── Lazy receiver reification ────────────────────────────────────────────
    //
    // The dotted receiver is evaluated exactly once and carried forward ONLY as a
    // prepared counted value; the legacy expression-tree wrapper (CountedArgAlgorithm →
    // ResultToExpr, an O(receiver size) rebuild) is never constructed for ordinary dot
    // calls. No public KatLang program can put the dot receiver ITSELF into an
    // algorithm-only position — it always binds the fixed `collection` parameter through
    // the value channel — so the lazy fallback is exercised through the same prepared-
    // argument machinery's other producers: builtin-as-callback dispatch routes
    // pre-evaluated values into builtin argument positions, where an algorithm-only slot
    // (a loop step, an algorithm-kind suffix argument) synthesizes the wrapper exactly
    // when requested.

    [Theory]
    [InlineData("range(1, 6).count")]
    [InlineData("V = range(1, 6)\nV.count")]
    [InlineData("V = range(1, 6)\nV.first")]
    [InlineData("V = range(1, 6)\nV.take(2)")]
    [InlineData("V = range(1, 6)\nV.skip(1)")]
    [InlineData("V = range(1, 6)\nV.sum")]
    [InlineData("D(x) = x * 2\nV = range(1, 6)\nV.map(D)")]
    [InlineData("B(x) = x > 3\nV = range(1, 6)\nV.filter(B)")]
    [InlineData("A(a, b) = a + b\nV = range(1, 6)\nV.reduce(A, 0)")]
    [InlineData("B(x) = x > 5\nD(x) = x * 2\nrange(1, 10).filter(B).map(D).count")]
    [InlineData("[(1, 2), [3, 4]].take(1)")]
    [InlineData("'text'.count")]
    [InlineData("().count")]
    [InlineData("[].first")]
    [InlineData("A = (1, 2, 3)\n(A*).count")]
    public void OrdinaryDotCalls_NeverReifyTheReceiver(string source)
    {
        Assert.Equal(0, Observe(source, optimize: false).Reifications);
        Assert.Equal(0, Observe(source, optimize: true).Reifications);
    }

    [Fact]
    public void FluentSpreadCall_BypassesDotReceiverPreparation()
    {
        // A*.count lowers to count(A*), so it supplies three ordinary arguments and fails
        // fixed arity without ever entering SequenceBuiltinDotReceiverArgs. Parenthesized
        // (A*).count is the capture-receiver case covered by the direct theory above.
        var run = Observe("A = (1, 2, 3)\nA*.count", optimize: false);
        Assert.Equal("err:arity", run.Outcome);
        Assert.Equal(0, run.Reifications);
    }

    [Theory]
    [InlineData("range(1, 6).count")]
    [InlineData("'text'.sum")]
    [InlineData("S = 5\nwhile(S*, 1)")]
    [InlineData("((), ()).reduce(map, ())")]
    public void ReificationObservation_IsSemanticallyAndOperationallyPassive(string source)
    {
        var observed = Observe(source, optimize: false);
        var unobserved = ObserveCore(source, optimize: false, observations: null);

        Assert.Equal(observed.Outcome, unobserved.Outcome);
        Assert.Equal(observed.Emitted, unobserved.Emitted);
        Assert.Equal(observed.Steps, unobserved.Steps);
        Assert.Equal(observed.Items, unobserved.Items);
        Assert.Equal(observed.StringChars, unobserved.StringChars);
        Assert.Equal(observed.PeakDepth, unobserved.PeakDepth);
    }

    [Fact]
    public void AlgorithmOnlyFallback_ReifiesLazily_ExactlyWhenRequested()
    {
        // Loop step slot (ResolveArgumentAlgorithm): the spread supplies the step argument
        // as a prepared VALUE, and resolving the step's algorithm channel builds exactly
        // one wrapper. The zero-parameter wrapper then mismatches the one-slot loop state,
        // which is the pre-existing outcome for a value in step position.
        var loopStep = Observe("S = 5\nwhile(S*, 1)");
        Assert.Equal(1, loopStep.Reifications);
        Assert.Equal("err:arity", loopStep.Outcome);

        // Algorithm-kind suffix slot (PrepareSequenceBuiltinSuffixArg): `map` used as the
        // reducer receives prepared (element, accumulator) arguments, routing the accumulator
        // into its mapper slot. The first reduction step builds one wrapper, then fails
        // applying the zero-parameter mapper to an element.
        var suffixSlot = Observe("(5, 6).reduce(map, ())");
        Assert.Equal(1, suffixSlot.Reifications);
        Assert.Equal("err:arity", suffixSlot.Outcome);

        // Successful wrapper use: mapping an EMPTY collection never applies the mapper, so
        // both reduction steps succeed — the wrapper is still built at binding time, once
        // per reducer invocation.
        var success = Observe("((), ()).reduce(map, ())");
        Assert.Equal(2, success.Reifications);
        Assert.Equal("ok:L[]", success.Outcome);

        // NOT requested → NOT built: `repeat` as the reducer arity-errors before its step
        // slot is resolved…
        var notRequested = Observe("R = (1, 2)\nR.reduce(repeat, 0)");
        Assert.Equal(0, notRequested.Reifications);
        Assert.Equal("err:arity", notRequested.Outcome);

        // …and an empty reduction never invokes the reducer at all.
        var neverInvoked = Observe("().reduce(map, 7)");
        Assert.Equal(0, neverInvoked.Reifications);
        Assert.Equal("ok:7", neverInvoked.Outcome);
    }

    // ── Large and nested receivers ───────────────────────────────────────────

    [Fact]
    public void LargeReceiver_SupportsRepeatedDotCallsWithoutReification()
    {
        var run = Observe("R = range(1, 2000)\nR.count + R.sum + R.count + R.max");

        // 2000 + 2001000 + 2000 + 2000; the receiver is materialized once (2000 slots)
        // and reused by all four dot calls without any expression-tree reconstruction.
        Assert.Equal("ok:2007000", run.Outcome);
        Assert.Equal(2000, run.Items);
        Assert.Equal(0, run.Reifications);
    }

    [Fact]
    public void DeeplyNestedReceiver_SupportsRepeatedDotCallsWithoutReification()
    {
        var nested = new string('[', 40) + "7" + new string(']', 40);
        var run = Observe($"N = {nested}\nN.count + N.count");

        Assert.Equal("ok:2", run.Outcome);
        Assert.Equal(40, run.Items);
        Assert.Equal(0, run.Reifications);
    }
}
