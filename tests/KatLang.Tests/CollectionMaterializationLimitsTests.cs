using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// Deterministic collection materialization limits: the always-active per-collection
/// item ceiling (host-process safety) and the optional cumulative per-run budget.
///
/// <para>Boundary assertions configure explicit small limits so every assertion is exact
/// and platform-independent. The one test that uses the default ceiling asserts only
/// that the established <c>range(1, 10000000)</c> reproducer is rejected — not how long
/// it takes.</para>
/// </summary>
public class CollectionMaterializationLimitsTests
{
    private static EvalResult<Result> Eval(string source, EvaluationLimits? limits = null)
        => Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), limits);

    private static EvalError ErrorOf(string source, EvaluationLimits? limits = null)
    {
        var result = Eval(source, limits);
        if (!result.IsError)
            Assert.Fail($"expected a structured error, got {result.Value}");
        return result.Error;
    }

    private static EvaluationLimits Items(int maxCollectionItems) => new() { MaxCollectionItems = maxCollectionItems };

    private static EvaluationLimits Total(long maxMaterializedItems) => new() { MaxMaterializedItems = maxMaterializedItems };

    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) Observe(
        string source,
        EvaluationLimits? limits = null,
        bool optimized = true)
        => Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root),
            limits,
            enableOptimizations: optimized);

    // ── Configuration and validation ─────────────────────────────────────────

    [Theory]
    [InlineData(0)]
    [InlineData(-1)]
    [InlineData(int.MinValue)]
    public void MaxCollectionItems_ZeroOrNegative_Throws(int value)
        => Assert.Throws<ArgumentOutOfRangeException>(() => new EvaluationLimits { MaxCollectionItems = value });

    [Theory]
    [InlineData(0L)]
    [InlineData(-1L)]
    public void MaxMaterializedItems_ZeroOrNegative_Throws(long value)
        => Assert.Throws<ArgumentOutOfRangeException>(() => new EvaluationLimits { MaxMaterializedItems = value });

    [Fact]
    public void MaxCollectionItems_AboveSupportedMaximum_IsClampedDown()
    {
        Assert.Equal(
            EvaluationLimits.MaxSupportedCollectionItems,
            new EvaluationLimits { MaxCollectionItems = int.MaxValue }.EffectiveMaxCollectionItems);
        Assert.Equal(EvaluationLimits.MaxSupportedCollectionItems, EvaluationLimits.Default.EffectiveMaxCollectionItems);
        Assert.Equal(16, new EvaluationLimits { MaxCollectionItems = 16 }.EffectiveMaxCollectionItems);
    }

    [Fact]
    public void Defaults_AreCollectionCeilingAndNoCumulativeBudget()
    {
        Assert.Null(EvaluationLimits.Default.MaxCollectionItems);
        Assert.Null(EvaluationLimits.Default.MaxMaterializedItems);
        Assert.Equal(EvaluationLimits.MaxSupportedCollectionItems, EvaluationBudget.Create(null).MaxCollectionItems);
        Assert.Equal(0, EvaluationBudget.Create(null).MaterializedItems);
    }

    // ── The established reproducer ───────────────────────────────────────────

    [Fact]
    public void GiantRange_IsRejectedUnderDefaultLimits()
    {
        var error = ErrorOf("range(1, 10000000).count");
        var limit = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(error);
        Assert.Equal(EvaluationLimits.MaxSupportedCollectionItems, limit.Limit);
        Assert.Equal(10_000_000L, limit.Requested);
    }

    [Fact]
    public void GiantRange_IsRejectedThroughEveryEngineSurface()
    {
        const string source = "range(1, 10000000).count";
        Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        Assert.Throws<KatLangException>(() => KatLangEngine.EvaluateToAtoms(source));
        Assert.Contains("Collection size limit", KatLangEngine.EvaluateToString(source));
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(
            Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root)).Error);
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(
            Evaluator.RunCounted(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), UncachedZeroArgPropertyResultCache.Instance).Error);
    }

    // ── Range: exact boundary and bounds handling ────────────────────────────

    [Fact]
    public void Range_ExactlyAtLimit_Succeeds()
        => Assert.False(Eval("range(1, 10).count", Items(10)).IsError);

    [Fact]
    public void Range_OneOverLimit_ReportsRequestedCount()
    {
        var limit = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ErrorOf("range(1, 11).count", Items(10)));
        Assert.Equal(10, limit.Limit);
        Assert.Equal(11L, limit.Requested);
    }

    [Fact]
    public void Range_SingleItem_NeedsOneSlot()
    {
        Assert.False(Eval("range(5, 5).count", Items(1)).IsError);
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ErrorOf("range(5, 6).count", Items(1)));
    }

    [Fact]
    public void Range_DescendingBounds_ChargeTheSameCardinality()
    {
        // Inclusive bounds always yield at least one element, in either direction.
        Assert.False(Eval("range(10, 1).count", Items(10)).IsError);
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ErrorOf("range(11, 1).count", Items(10)));
    }

    [Fact]
    public void Range_EnormousBounds_AreRejectedWithoutOverflow()
    {
        // Cardinality is computed from the bounds with a saturating conversion, so an
        // absurd span is rejected rather than wrapping into a small count.
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(
            ErrorOf("range(-100000000000000000000, 100000000000000000000).count"));
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ErrorOf("range(0, 99999999999999999999).count"));
    }

    // ── Collection builtins charge their true output count ───────────────────

    [Theory]
    [InlineData("range(1, 6).map(Double).count\nDouble(x) = x * 2")]
    [InlineData("range(1, 6).order.count")]
    [InlineData("range(1, 6).orderDesc.count")]
    [InlineData("range(1, 6).distinct.count")]
    public void CollectionBuiltins_ProducingSixItems_NeedSixSlots(string source)
    {
        Assert.False(Eval(source, Items(6)).IsError);
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ErrorOf(source, Items(5)));
    }

    [Fact]
    public void TakeAndSkip_ChargeTheirBoundedOutput_NotTheirInput()
    {
        // take(6, 2) keeps 2 items, so a 2-slot limit is enough even though the input
        // needed 6 — the limit is per collection, and `range` already paid for its own.
        Assert.False(Eval("Values = range(1, 6)\nValues.take(2).count", Items(6)).IsError);
        Assert.False(Eval("Values = range(1, 6)\nValues.skip(4).count", Items(6)).IsError);
    }

    [Fact]
    public void Filter_ChargesTheKeptCount()
    {
        const string source = "Big(x) = x > 3\nrange(1, 6).filter(Big).count";
        Assert.False(Eval(source, Items(6)).IsError);          // input needs 6, kept needs 3
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ErrorOf(source, Items(5)));
    }

    // ── atoms: the one expanding producer ────────────────────────────────────

    [Fact]
    public void Atoms_FlatteningWithinLimit_Succeeds()
        => Assert.False(Eval("[1, [2, 3], 4].atoms.count", Items(4)).IsError);

    [Fact]
    public void Atoms_ExpandingBeyondItsInput_IsBounded()
    {
        // Nesting a value inside itself doubles the atom count while adding only two item
        // slots, so `atoms` can vastly exceed every collection it traverses. The traversal
        // itself must stop, not merely the result construction.
        const string source =
            "A = [1, 2]\nB = [A, A]\nC = [B, B]\nD = [C, C]\nE = [D, D]\nE.atoms.count";
        Assert.False(Eval(source, Items(32)).IsError);
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ErrorOf(source, Items(31)));
    }

    // ── Literals, capture, spread ────────────────────────────────────────────

    [Fact]
    public void ListLiteral_ChargesItsElementSlots()
    {
        Assert.False(Eval("[1, 2, 3].count", Items(3)).IsError);
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ErrorOf("[1, 2, 3, 4].count", Items(3)));
    }

    [Fact]
    public void ListLiteralWithSpread_ChargesTheExpandedSlots()
    {
        const string source = "Values = [1, 2, 3]\n[Values*, Values*].count";
        Assert.False(Eval(source, Items(6)).IsError);
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ErrorOf(source, Items(5)));
    }

    [Fact]
    public void SequenceCaptureWithSpread_IsBounded()
    {
        // `(A*, A*)` doubles a captured sequence value; without charging capture this
        // is an unbounded growth path that never touches a collection builtin.
        const string source = "A = (1, 2, 3)\nB = (A*, A*)\nB.count";
        Assert.False(Eval(source, Items(6)).IsError);
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(ErrorOf(source, Items(5)));
    }

    [Fact]
    public void OrdinaryFlatVariadic_IsCheckedBeforeItsExactListIsCreated()
    {
        const string source = "F(*items) = items.count\nF(1, 2, 3, 4)";
        var failed = Observe(source, Items(3));
        var error = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(failed.Result.Error);
        Assert.Equal(4, error.Requested);
        Assert.Equal(0, failed.Budget.MaterializedItems);

        var exact = Observe(source, Total(4));
        Assert.False(exact.Result.IsError);
        Assert.Equal(4, exact.Budget.MaterializedItems);
    }

    [Fact]
    public void CollectingBinding_DefaultHardCeilingRejectsDoubledMaximumRange()
    {
        const string source =
            "A = range(1, 100000)\n" +
            "F(*items) = items.count\n" +
            "F(A*, A*)";

        var observed = Observe(source);
        var error = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(observed.Result.Error);
        Assert.Equal(EvaluationLimits.MaxSupportedCollectionItems, error.Limit);
        Assert.Equal(2L * EvaluationLimits.MaxSupportedCollectionItems, error.Requested);
        // The range and the two explicit caller-side spreads each create one checked
        // 100,000-slot sequence/list value. The rejected 200,000-item collected list itself
        // is not charged because its reservation fails before construction.
        Assert.Equal(3L * EvaluationLimits.MaxSupportedCollectionItems, observed.Budget.MaterializedItems);
    }

    [Theory]
    [InlineData("F((head, *tail)) = tail.count\nF((1, 2, 3))", 5)]
    [InlineData("x, *tail = [1, 2, 3, 4]\ntail.count", 7)]
    [InlineData("Collect(*items) = items.count\nRows = [1, 2]\nRows.map(Collect)", 6)]
    [InlineData("Collect(*items) = items.count\nRows = [1, 2]\nRows.reduce(Collect, 0)", 6)]
    public void EveryCollectingBindingShape_ChargesItsExactPersistentList(string source, long expectedItems)
    {
        var observed = Observe(source, Total(expectedItems));
        Assert.False(observed.Result.IsError);
        Assert.Equal(expectedItems, observed.Budget.MaterializedItems);

        Assert.IsType<EvalError.MaterializationLimitExceeded>(
            Observe(source, Total(expectedItems - 1)).Result.Error);
    }

    public static TheoryData<string> MultiSlotLoopSources => new()
    {
        "Step(a, b) = a, b\nStep.repeat(0, 1, 2)",
        "Step(a, b) = a + 1, b + 1\nStep.repeat(3, 1, 2)",
        "Step(a, b) = a + 1, b + 1, a < 2\nStep.while(0, 2)",
    };

    [Theory]
    [MemberData(nameof(MultiSlotLoopSources))]
    public void GenericAndOptimizedLoops_ChargeOnlyTheirFinalPersistentState(string source)
    {
        foreach (var optimized in new[] { false, true })
        {
            var exact = Observe(source, Total(2), optimized);
            Assert.False(exact.Result.IsError);
            Assert.Equal(2, exact.Budget.MaterializedItems);

            Assert.IsType<EvalError.MaterializationLimitExceeded>(
                Observe(source, Total(1), optimized).Result.Error);
            Assert.IsType<EvalError.CollectionSizeLimitExceeded>(
                Observe(source, Items(1), optimized).Result.Error);
        }

        if (!source.Contains("repeat(0", StringComparison.Ordinal))
        {
            var diagnostics = new LoopOptimizationDiagnostics();
            var result = Evaluator.Run(
                new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root),
                new RunScopedZeroArgPropertyResultCache(),
                enableLoopOptimization: true,
                diagnostics,
                Total(2));
            Assert.False(result.IsError);
            Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);
        }
    }

    [Fact]
    public void DirectNestedSpreads_ChargeEveryRealSequenceRecapture()
    {
        const string oneLayer = "A = (1, 2, 3)\nA*";
        const string twoLayers = "A = (1, 2, 3)\nA**";

        var one = Observe(oneLayer, Total(9));
        var two = Observe(twoLayers, Total(12));
        Assert.False(one.Result.IsError);
        Assert.False(two.Result.IsError);
        Assert.Equal(9, one.Budget.MaterializedItems);
        Assert.Equal(12, two.Budget.MaterializedItems);
        Assert.IsType<EvalError.MaterializationLimitExceeded>(Observe(twoLayers, Total(11)).Result.Error);
    }

    [Fact]
    public void NestedCollections_ChargeOuterSlotsSeparatelyFromInnerOnes()
    {
        // [[1, 2], [3, 4]] is three collections: two inner pairs and one outer pair.
        // The per-collection ceiling therefore only has to admit 2, not 4.
        Assert.False(Eval("[[1, 2], [3, 4]].count", Items(2)).IsError);
    }

    // ── Cumulative materialization budget ────────────────────────────────────

    [Fact]
    public void CumulativeBudget_ExactBoundary()
    {
        // One materialized range of ten items costs exactly ten slots.
        Assert.False(Eval("range(1, 10)", Total(10)).IsError);
        Assert.IsType<EvalError.MaterializationLimitExceeded>(ErrorOf("range(1, 10)", Total(9)));
    }

    [Fact]
    public void CumulativeBudget_SeveralIndividuallyLegalCollections_ExceedTheRunTotal()
    {
        // Each range is comfortably within the per-collection ceiling; together they are
        // not within the run total. This is the case a per-collection limit cannot catch.
        const string one = "range(1, 10)";
        const string three = "range(1, 10), range(1, 10), range(1, 10)";

        Assert.False(Eval(one, Total(10)).IsError);
        Assert.IsType<EvalError.MaterializationLimitExceeded>(ErrorOf(three, Total(10)));
        Assert.False(Eval(three, Total(1_000)).IsError);
    }

    [Fact]
    public void CumulativeBudget_CachedPropertyReuse_DoesNotRepayExistingSlots()
    {
        // `Values` is materialized once and then served from the zero-argument property
        // cache, so later reads do not re-charge the slots it already created. Rebuilding
        // an equal collection each time does, and runs out of the same budget.
        Assert.False(Eval(
            "Values = range(1, 10)\nValues.count + Values.count + Values.count + Values.count",
            Total(30)).IsError);

        Assert.IsType<EvalError.MaterializationLimitExceeded>(ErrorOf(
            "range(1, 10).count + range(1, 10).count + range(1, 10).count + range(1, 10).count",
            Total(30)));
    }

    [Fact]
    public void CumulativeBudget_IsSharedByNestedCallbacks()
        => Assert.IsType<EvalError.MaterializationLimitExceeded>(
            ErrorOf("Wrap(x) = [x, x]\nrange(1, 10).map(Wrap).count", Total(25)));

    // ── Strategy independence of the cumulative budget ───────────────────────

    [Theory]
    [InlineData("range(1, 100000).filter({x > 0}).count")]
    [InlineData("range(1, 100000).count")]
    [InlineData("range(1, 100000).sum")]
    [InlineData("D(x) = x\nrange(1, 100000).map(D).count")]
    public void MaterializationVerdict_IsIndependentOfAnUnrelatedStepBudget(string source)
    {
        // A configured MaxMaterializedItems forces the generic sequence paths
        // (CreateRootCtx), exactly like a configured step or string budget: fused
        // pipelines charge only the per-collection boundary, never the cumulative
        // counter, so leaving them enabled made this verdict flip when an unrelated
        // never-reached MaxSteps happened to disable fusion.
        var alone = Eval(source, new EvaluationLimits { MaxMaterializedItems = 10 });
        var withSteps = Eval(source, new EvaluationLimits { MaxMaterializedItems = 10, MaxSteps = 100_000_000 });

        Assert.True(alone.IsError, $"expected the cumulative limit to bound `{source}`");
        Assert.True(withSteps.IsError);
        Assert.Equal(alone.Error.GetType(), withSteps.Error.GetType());
    }

    [Fact]
    public void FailedReservation_DoesNotCorruptTheRunTotal()
    {
        // The over-limit collection is rejected before any counter moves, so an earlier
        // failure can never make a later legal program behave differently.
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxCollectionItems = 10, MaxMaterializedItems = 10 });
        Assert.Null(budget.TryReserveCollection(4));
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(budget.TryReserveCollection(11));
        Assert.IsType<EvalError.MaterializationLimitExceeded>(budget.TryReserveCollection(7));
        Assert.Equal(4, budget.MaterializedItems);
        Assert.Null(budget.TryReserveCollection(6));
        Assert.Equal(10, budget.MaterializedItems);
    }

    // ── Optimizer parity ─────────────────────────────────────────────────────

    private static EvalResult<Result> EvalWithOptimizations(string source, EvaluationLimits limits, bool optimized)
        => Evaluator.Run(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root),
            UncachedZeroArgPropertyResultCache.Instance,
            enableLoopOptimization: optimized,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: optimized,
            sequenceDiagnostics: null,
            limits);

    [Theory]
    [InlineData("range(1, 10).count")]
    [InlineData("range(1, 10).sum")]
    [InlineData("Big(x) = x > 3\nrange(1, 10).filter(Big).count")]
    public void OptimizedAndGenericPaths_AgreeBelowTheLimit(string source)
    {
        var optimized = EvalWithOptimizations(source, Items(10), optimized: true);
        var generic = EvalWithOptimizations(source, Items(10), optimized: false);

        Assert.False(optimized.IsError);
        Assert.False(generic.IsError);
        Assert.Equal(generic.Value, optimized.Value, Result.ValueComparer);
    }

    [Theory]
    [InlineData("range(1, 11).count")]
    [InlineData("range(1, 11).sum")]
    [InlineData("Big(x) = x > 3\nrange(1, 11).filter(Big).count")]
    public void OptimizedAndGenericPaths_ProduceTheSameErrorOneOverTheLimit(string source)
    {
        // A fused pipeline never materializes the range, but it must still reject exactly
        // what the generic path rejects: the source asked for the collection either way.
        var optimized = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(
            EvalWithOptimizations(source, Items(10), optimized: true).Error);
        var generic = Assert.IsType<EvalError.CollectionSizeLimitExceeded>(
            EvalWithOptimizations(source, Items(10), optimized: false).Error);

        Assert.Equal(generic.Limit, optimized.Limit);
        Assert.Equal(generic.Requested, optimized.Requested);
    }

    [Fact]
    public void ConfiguredCumulativeBudget_ForcesGenericPaths_SoBothStrategiesAgree()
    {
        // Formerly the fused filter-count skipped the cumulative charge for the
        // collections it never materialized, so the SAME program under the SAME
        // Total(1) budget succeeded fused and failed generic — the verdict was a
        // function of which internal strategy ran (and configuring an unrelated
        // MaxSteps flipped it by disabling fusion). A configured cumulative budget
        // now forces the generic sequence paths in CreateRootCtx, exactly like a
        // configured step or string budget: the budget's meaning is
        // strategy-independent by construction.
        const string source = "Big(x) = x > 3\nrange(1, 100).filter(Big).count";
        Assert.IsType<EvalError.MaterializationLimitExceeded>(
            EvalWithOptimizations(source, Total(1), optimized: true).Error);
        Assert.IsType<EvalError.MaterializationLimitExceeded>(
            EvalWithOptimizations(source, Total(1), optimized: false).Error);

        // Unconfigured cumulative budget: fusion stays eligible and the pipeline
        // still allocates nothing (the per-collection boundary is checked on both
        // paths identically).
        Assert.False(Eval(source).IsError);
    }

    // ── Engine host projection ───────────────────────────────────────────────

    [Fact]
    public void EngineHostAtomProjection_IsBounded()
    {
        // The host projection opens both sequence and list boundaries recursively, so a
        // small result value can flatten into a huge host list. A successful evaluation
        // must not be followed by an unbounded allocation on the way out.
        const string source = "A = [1, 2]\nB = [A, A]\nC = [B, B]\nD = [C, C]\nD";
        Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, new RunOptions { EvaluationLimits = Items(16) }));

        var failure = Assert.IsType<RunResult.EvalFailure>(
            KatLangEngine.Run(source, new RunOptions { EvaluationLimits = Items(8) }));
        Assert.Contains("Collection size limit", failure.Errors[0].Message);
    }

    // ── Interaction with the existing limits ─────────────────────────────────

    [Fact]
    public void DepthAndStepErrors_AreUnchanged()
    {
        Assert.IsType<EvalError.EvaluationDepthExceeded>(
            ErrorOf("f(0) = 0\nf(n) = f(n - 1)\nf(40)", new EvaluationLimits { MaxDepth = 8 }));
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(
            ErrorOf("Step = x, 1\nStep.while(0)", new EvaluationLimits { MaxSteps = 500 }));
    }

    [Fact]
    public void WhicheverLimitIsReachedFirst_IsDeterministic()
    {
        // The collection ceiling is checked when the collection is about to be built, so a
        // program that is over BOTH reports the limit it reaches first in evaluation order:
        // the range materializes before the loop that would exhaust the step budget.
        var error = ErrorOf(
            "range(1, 1000).count",
            new EvaluationLimits { MaxCollectionItems = 10, MaxSteps = 1_000_000 });
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(error);
    }

    // ── State isolation ──────────────────────────────────────────────────────

    [Fact]
    public void RepeatedAndConcurrentRuns_SharingOneOptionsInstance_EachStartFresh()
    {
        var options = new RunOptions { EvaluationLimits = Total(1_000) };
        const string source = "range(1, 10).count + range(1, 10).count + range(1, 10).count";

        for (var i = 0; i < 3; i++)
            Assert.Equal("30", KatLangEngine.Run(source, options).ToDisplayString());

        var results = new string[16];
        Parallel.For(0, results.Length, i => results[i] = KatLangEngine.Run(source, options).ToDisplayString());
        Assert.All(results, r => Assert.Equal("30", r));
    }

    // ── In-limit programs are untouched ──────────────────────────────────────

    [Theory]
    [InlineData("range(1, 5).sum", "15")]
    [InlineData("[1, 2, 3]", "[1, 2, 3]")]
    [InlineData("()", "()")]
    [InlineData("[].count", "0")]
    [InlineData("range(1, 4).orderDesc", "[4, 3, 2, 1]")]
    public void InLimitPrograms_AreUnaffected(string source, string expected)
    {
        Assert.Equal(expected, KatLangEngine.Run(source).ToDisplayString());
        Assert.Equal(expected, KatLangEngine.Run(source, new RunOptions { EvaluationLimits = Items(64) }).ToDisplayString());
    }
}
