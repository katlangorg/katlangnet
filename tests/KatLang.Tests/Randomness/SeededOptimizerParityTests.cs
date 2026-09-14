using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.Randomness.SeededRun;

namespace KatLang.Tests.Randomness;

/// <summary>
/// Optimizer strategies are C#-only execution paths over the generic semantics, and
/// a seed makes their draw count and order observable. Each differential here PROVES
/// through the optimizers' own diagnostics that the intended optimized path actually
/// executed (and that the comparison run was genuinely generic) — an accidental
/// generic-vs-generic agreement would prove nothing — and then requires the seeded
/// result to equal both the generic result and the test-side oracle.
/// </summary>
public class SeededOptimizerParityTests
{
    private const long Seed = 777;
    private const string StreamSentinel = "\nMath.RandomInt(0, 4294967296)";

    private const string RandomLoop =
        "Step(n) = n + Math.RandomInt(0, 10)\n" +
        "repeat(Step, 5, 0)";

    private const string RandomFilterCount =
        "V(x) = Math.Random(0, 1) < 0.5\n" +
        "range(1, 20).filter(V).count";

    private static (
        EvalResult<Result> Result,
        LoopOptimizationDiagnosticsSnapshot Loop,
        SequencePipelineDiagnosticsSnapshot Sequence) RunObserved(
            string source, bool optimize, long? seed, EvaluationLimits? limits = null)
    {
        var loop = new LoopOptimizationDiagnostics();
        var sequence = new SequencePipelineDiagnostics();
        var result = Evaluator.Run(
            Program(source),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: optimize,
            loop,
            enableSequencePipelineOptimization: optimize,
            sequence,
            limits,
            randomSeed: seed);
        return (result, loop.GetSnapshot(), sequence.GetSnapshot());
    }

    private static Result Value(EvalResult<Result> result)
    {
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        return result.Value;
    }

    /// <summary>The oracle's loop total: five RandomInt(0, 10) draws, one per iteration, in order.</summary>
    private static Decimal128 ExpectedLoopTotal(ReferenceSplitMix64? words = null)
    {
        words ??= Words(Seed);
        var total = Decimal128.Zero;
        for (var i = 0; i < 5; i++)
            total += ReferenceRandomOracle.RandomInt(words, 0, 10);
        return total;
    }

    /// <summary>The oracle's count: how many of twenty Random(0, 1) draws, in order, fall below one half.</summary>
    private static Decimal128 ExpectedFilteredCount(ReferenceSplitMix64? words = null)
    {
        words ??= Words(Seed);
        var count = 0;
        for (var i = 0; i < 20; i++)
        {
            if (ReferenceRandomOracle.Random(words, D(0), D(1)) < D("0.5"))
                count++;
        }

        return D(count);
    }

    // ── §24.1 Loop optimizer ──────────────────────────────────────────────────

    [Fact]
    public void PlannedLoop_WithAGenericRandomRow_DrawsExactlyLikeTheGenericLoop()
    {
        var optimized = RunObserved(RandomLoop + StreamSentinel, optimize: true, Seed);
        var generic = RunObserved(RandomLoop + StreamSentinel, optimize: false, Seed);

        // Strategy evidence: the loop WAS planned and executed through the optimized
        // executor, and the random call inside it fell back to generic evaluation on
        // every iteration (a planned expression cannot host a Math native draw).
        Assert.Equal(1, optimized.Loop.OptimizedLoopHits);
        Assert.Equal(1, optimized.Loop.LoopExecutions);
        Assert.Equal(5, optimized.Loop.LoopIterations);
        Assert.True(
            optimized.Loop.GenericExpressionEvaluationsInsideOptimizedLoops >= 5,
            $"expected one generic row evaluation per iteration, saw {optimized.Loop.GenericExpressionEvaluationsInsideOptimizedLoops}");
        var plan = Assert.Single(optimized.Loop.LoopPlans);
        Assert.True(plan.Optimized);
        Assert.Equal(1, plan.ExecutionCount);
        var output = Assert.Single(plan.Expressions, static expression => expression.Role == "output");
        Assert.False(output.Planned);
        Assert.NotNull(output.FallbackReason);

        // The comparison run is genuinely generic.
        Assert.Equal(0, generic.Loop.OptimizedLoopHits);
        Assert.Equal(0, generic.Loop.LoopPlanBuilds);

        var words = Words(Seed);
        Decimal128[] expected = [ExpectedLoopTotal(words), LowWordMod2Pow32(words)];
        AssertSameAtoms(expected, Value(optimized.Result).ToHostAtoms());
        AssertSameAtoms(expected, Value(generic.Result).ToHostAtoms());
    }

    // ── §24.2 Sequence fusion ─────────────────────────────────────────────────

    [Fact]
    public void FusedFilterCount_WithARandomPredicate_DrawsExactlyLikeTheGenericPipeline()
    {
        var optimized = RunObserved(RandomFilterCount + StreamSentinel, optimize: true, Seed);
        var generic = RunObserved(RandomFilterCount + StreamSentinel, optimize: false, Seed);

        // Strategy evidence: fusion happened once, the predicate ran once per source
        // item in order, and the comparison run never fused.
        Assert.Equal(1, optimized.Sequence.FilterCountFusionHits);
        Assert.Equal(0, optimized.Sequence.FilterCountFusionFallbacks);
        Assert.Equal(20, optimized.Sequence.FilterCountPredicateCalls);
        var pipeline = Assert.Single(optimized.Sequence.Pipelines, static pipeline => pipeline.Optimized);
        Assert.Equal(1, pipeline.ExecutionCount);
        Assert.Equal(20, pipeline.PredicateCalls);
        Assert.Equal(0, generic.Sequence.FilterCountFusionHits);
        Assert.DoesNotContain(generic.Sequence.Pipelines, static pipeline => pipeline.Optimized);

        // A duplicate draw at predicate item 4 still gives count 6 for this seed.
        // The next stream value distinguishes that replay: 2136270094 vs 3890862503.
        var words = Words(Seed);
        Decimal128[] expected = [ExpectedFilteredCount(words), LowWordMod2Pow32(words)];
        AssertSameAtoms(expected, Value(optimized.Result).ToHostAtoms());
        AssertSameAtoms(expected, Value(generic.Result).ToHostAtoms());
    }

    // ── §24.3 Unrelated limits that disable a strategy ────────────────────────

    [Fact]
    public void AStepBudget_DisablesLoopPlanning_WithoutChangingTheSeededResult()
    {
        // A configured MaxSteps forces the generic loop strategy (CreateRootCtx); the
        // program's control flow is unchanged, so the stream is consumed identically.
        var limited = RunObserved(RandomLoop + StreamSentinel, optimize: true, Seed, new EvaluationLimits { MaxSteps = 100_000 });
        var unlimited = RunObserved(RandomLoop + StreamSentinel, optimize: true, Seed);

        Assert.Equal(0, limited.Loop.OptimizedLoopHits);
        Assert.Equal(1, unlimited.Loop.OptimizedLoopHits);
        var words = Words(Seed);
        AssertSameAtoms([ExpectedLoopTotal(words), LowWordMod2Pow32(words)], Value(limited.Result).ToHostAtoms());
        AssertSameValue(Value(unlimited.Result), Value(limited.Result));
    }

    [Fact]
    public void AStringBudget_DisablesSequenceFusion_WithoutChangingTheSeededResult()
    {
        var limited = RunObserved(RandomFilterCount + StreamSentinel, optimize: true, Seed, new EvaluationLimits { MaxMaterializedStringChars = 10_000 });
        var unlimited = RunObserved(RandomFilterCount + StreamSentinel, optimize: true, Seed);

        Assert.Equal(0, limited.Sequence.FilterCountFusionHits);
        Assert.Equal(1, unlimited.Sequence.FilterCountFusionHits);
        var words = Words(Seed);
        AssertSameAtoms([ExpectedFilteredCount(words), LowWordMod2Pow32(words)], Value(limited.Result).ToHostAtoms());
        AssertSameValue(Value(unlimited.Result), Value(limited.Result));
    }

    [Fact]
    public void ASeed_DoesNotDisableTheOptimizers()
    {
        // Seeded and unseeded runs take the same strategies: the seed changes values,
        // never eligibility.
        var seeded = RunObserved(RandomLoop + "\n" + RandomFilterCount, optimize: true, Seed);
        var unseeded = RunObserved(RandomLoop + "\n" + RandomFilterCount, optimize: true, seed: null);

        Assert.Equal(unseeded.Loop.OptimizedLoopHits, seeded.Loop.OptimizedLoopHits);
        Assert.Equal(1, seeded.Loop.OptimizedLoopHits);
        Assert.Equal(unseeded.Sequence.FilterCountFusionHits, seeded.Sequence.FilterCountFusionHits);
        Assert.Equal(1, seeded.Sequence.FilterCountFusionHits);
    }

    [Fact]
    public void EngineRun_UsesTheSameOptimizedStrategiesAndTheSameStream()
    {
        // The public engine (optimizers on by default) must agree with the oracle for
        // the combined program: the loop's five draws first, then the predicate's
        // twenty, all from ONE stream.
        var words = Words(Seed);
        var total = Decimal128.Zero;
        for (var i = 0; i < 5; i++)
            total += ReferenceRandomOracle.RandomInt(words, 0, 10);
        var count = 0;
        for (var i = 0; i < 20; i++)
        {
            if (ReferenceRandomOracle.Random(words, D(0), D(1)) < D("0.5"))
                count++;
        }

        var success = Success(RandomLoop + "\n" + RandomFilterCount, Seed);

        AssertSameAtoms([total, D(count)], success.Atoms);
    }
}
