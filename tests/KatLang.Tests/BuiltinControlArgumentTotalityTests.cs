using System.Globalization;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Totality of builtin control arguments at the host-representation extremes: every
/// documented-total public entry point must return a structured result for every
/// VALIDATED numeric control argument — never throw a host exception. Lean's core
/// models these arguments as unbounded <c>Int</c>s, so the C# <c>decimal</c> runtime
/// must guard each narrowing itself.
///
/// <para>These pin the August 2026 fixes for three such leaks: <c>range</c>
/// enumeration stepping past an inclusive bound at the <c>decimal</c> extremes (and
/// its cardinality subtraction overflowing for opposite-sign extremes) on both the
/// generic and fused pipeline paths; <c>take</c>/<c>skip</c> narrowing their count
/// with an unguarded <c>(int)</c> cast; and <c>repeat</c> narrowing its count to
/// <c>long</c> BEFORE the <c>&gt;= 0</c> domain check. All three previously escaped
/// <see cref="KatLangEngine.Run(string, RunOptions?)"/> as raw
/// <see cref="OverflowException"/>s.</para>
/// </summary>
public class BuiltinControlArgumentTotalityTests
{
    private static readonly string DecMax = decimal.MaxValue.ToString(CultureInfo.InvariantCulture);
    private static readonly string DecMaxMinusTwo = (decimal.MaxValue - 2m).ToString(CultureInfo.InvariantCulture);

    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static IReadOnlyList<decimal> FlatValues(string source)
    {
        var result = Evaluator.RunFlat(Program(source));
        if (result.IsError)
            Assert.Fail($"expected a value for `{source}`, got {result.Error}");
        return result.Value;
    }

    private static EvalError StructuredError(string source, EvaluationLimits? limits = null)
    {
        var result = Evaluator.Run(Program(source), limits);
        Assert.True(result.IsError, $"expected a structured error for `{source}`");
        return result.Error;
    }

    private static EvalError UnwrapContext(EvalError error)
    {
        while (error is EvalError.WithContext(_, var inner))
            error = inner;
        return error;
    }

    // ── range at the decimal extremes ────────────────────────────────────────

    [Fact]
    public void Range_AtDecimalMaximum_YieldsTheInclusiveValues()
    {
        // The ascending enumerator must stop ON the inclusive bound, not step past
        // it: `current += 1m` after yielding decimal.MaxValue overflowed the host.
        Assert.Equal(
            [decimal.MaxValue - 2m, decimal.MaxValue - 1m, decimal.MaxValue],
            FlatValues($"range({DecMaxMinusTwo}, {DecMax})"));
    }

    [Fact]
    public void Range_SingleValueAtDecimalMaximum_YieldsThatValue()
        => Assert.Equal([decimal.MaxValue], FlatValues($"range({DecMax}, {DecMax})"));

    [Fact]
    public void Range_DescendingToDecimalMinimum_YieldsTheInclusiveValues()
    {
        // The descending twin: `current -= 1m` past decimal.MinValue.
        Assert.Equal(
            [-(decimal.MaxValue - 2m), -(decimal.MaxValue - 1m), decimal.MinValue],
            FlatValues($"range(0 - {DecMaxMinusTwo}, 0 - {DecMax})"));
    }

    [Fact]
    public void Range_SpanningBothExtremes_IsRejectedByTheCollectionLimit()
    {
        // The cardinality `Stop - Start` itself exceeds decimal.MaxValue here, so the
        // count must saturate without performing the overflowing subtraction, and the
        // ordinary collection-size limit rejects the request as a structured error.
        var error = StructuredError($"range(0 - {DecMax}, {DecMax})");
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(UnwrapContext(error));
    }

    [Fact]
    public void Range_AtDecimalMaximum_FusedPipelineAgreesWithGenericPath()
    {
        // The fused filter/count pipeline enumerates the range through its own call
        // site; both paths share the enumeration helper and must agree exactly in
        // both directions at the decimal boundaries.
        const string predicate = "P(x) = 1\n";
        Assert.Equal([3m], FlatValues($"{predicate}range({DecMaxMinusTwo}, {DecMax}).filter(P).count"));
        Assert.Equal([3m], FlatValues($"{predicate}count(filter(range({DecMaxMinusTwo}, {DecMax}), P))"));
        Assert.Equal([3m], FlatValues($"{predicate}range(0 - {DecMaxMinusTwo}, 0 - {DecMax}).filter(P).count"));
        Assert.Equal([3m], FlatValues($"{predicate}count(filter(range(0 - {DecMaxMinusTwo}, 0 - {DecMax}), P))"));

        var fusedSpan = StructuredError($"{predicate}range(0 - {DecMax}, {DecMax}).filter(P).count");
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(UnwrapContext(fusedSpan));
    }

    [Fact]
    public void Range_AtDecimalMaximum_PlainAndCountedEvaluatorsAgree()
    {
        var expr = Program($"range({DecMaxMinusTwo}, {DecMax})");
        var plain = Evaluator.Run(expr);
        var counted = Evaluator.RunCounted(expr);
        Assert.False(plain.IsError);
        Assert.False(counted.IsError);
        Assert.Equal(plain.Value, counted.Value.Value, Result.ValueComparer);
    }

    // ── take / skip saturate on oversized counts ─────────────────────────────

    public static TheoryData<string> OversizedCounts => new()
    {
        "2147483648",             // int.MaxValue + 1: the exact narrowing boundary
        "99999999999",            // comfortably beyond int, well inside decimal
        decimal.MaxValue.ToString(CultureInfo.InvariantCulture),
    };

    [Theory]
    [MemberData(nameof(OversizedCounts))]
    public void Take_OversizedCount_ReturnsAllItems(string count)
    {
        Assert.Equal([1m, 2m, 3m], FlatValues($"take([1, 2, 3], {count})"));
        Assert.Equal([1m, 2m, 3m], FlatValues($"[1, 2, 3].take({count})"));
    }

    [Theory]
    [MemberData(nameof(OversizedCounts))]
    public void Skip_OversizedCount_ReturnsTheEmptyList(string count)
    {
        Assert.Empty(FlatValues($"skip([1, 2, 3], {count})"));
        Assert.Empty(FlatValues($"[1, 2, 3].skip({count})"));
    }

    [Fact]
    public void TakeAndSkip_OversizedCounts_AgreeAcrossPlainAndCountedEvaluators()
    {
        foreach (var source in new[] { $"take([1, 2, 3], {DecMax})", $"skip([1, 2, 3], {DecMax})" })
        {
            var expr = Program(source);
            var plain = Evaluator.Run(expr);
            var counted = Evaluator.RunCounted(expr);
            Assert.False(plain.IsError, source);
            Assert.False(counted.IsError, source);
            Assert.Equal(plain.Value, counted.Value.Value, Result.ValueComparer);
        }
    }

    [Fact]
    public void TakeAndSkip_HugeNegativeCounts_KeepTheDocumentedNonPositiveBehavior()
    {
        Assert.Empty(FlatValues($"take([1, 2, 3], 0 - {DecMax})"));
        Assert.Equal([1m, 2m, 3m], FlatValues($"skip([1, 2, 3], 0 - {DecMax})"));
    }

    // ── repeat validates its count before narrowing ──────────────────────────

    [Fact]
    public void Repeat_HugeNegativeCount_IsTheOrdinaryDomainError_OnBothEvaluators()
    {
        // A count below long.MinValue must produce the SAME structured domain error
        // as a small negative count — the (long) narrowing formerly ran first and
        // threw. The plain and counted dispatchers are independent copies of this
        // guard, so both are pinned.
        foreach (var source in new[]
        {
            $"Inc = x + 1\nInc.repeat(0 - {DecMax}, 0)",
            $"Inc = x + 1\nrepeat(Inc, 0 - {DecMax}, 0)",
        })
        {
            var expr = Program(source);
            var plain = Evaluator.Run(expr);
            var counted = Evaluator.RunCounted(expr);
            Assert.True(plain.IsError, source);
            Assert.True(counted.IsError, source);
            Assert.IsType<EvalError.IllegalInEval>(UnwrapContext(plain.Error));
            Assert.IsType<EvalError.IllegalInEval>(UnwrapContext(counted.Error));
        }
    }

    [Fact]
    public void Repeat_CountBeyondLongRange_SaturatesAndRunsUnderTheStepBudget()
    {
        // A whole count above long.MaxValue is behaviorally "unbounded": it must
        // saturate (not overflow) and then stop on the ordinary step budget exactly
        // like any other over-budget loop.
        var error = StructuredError(
            $"Inc = x + 1\nInc.repeat({DecMax}, 0)",
            new EvaluationLimits { MaxSteps = 1_000 });
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(UnwrapContext(error));
    }

    // ── The totality umbrella (T12): no boundary program throws ──────────────

    public static TheoryData<string> BoundaryPrograms
    {
        get
        {
            var max = DecMax;
            var nearMax = DecMaxMinusTwo;
            var data = new TheoryData<string>
            {
                // range bound shapes, plain / dot / spread-argument spellings
                $"range({nearMax}, {max})",
                $"range({max}, {max})",
                $"range(0 - {nearMax}, 0 - {max})",
                $"range(0 - {max}, {max})",
                $"range({nearMax}, {max}).count",
                $"count(range({nearMax}, {max})*)",
                $"P(x) = 1\nrange({nearMax}, {max}).filter(P).count",
                // take/skip control-argument extremes, both spellings
                $"take([1, 2, 3], {max})",
                $"skip([1, 2, 3], {max})",
                $"[1, 2, 3].take({max})",
                $"[1, 2, 3].skip({max})",
                "take([1, 2, 3], 2147483647)",
                "take([1, 2, 3], 2147483648)",
                "skip([1, 2, 3], 2147483648)",
                $"take([1, 2, 3], 0 - {max})",
                $"skip([1, 2, 3], 0 - {max})",
                $"take([1, 2, 3]*, {max})",
                // repeat count extremes (step budget bounds the saturated run)
                $"Inc = x + 1\nInc.repeat({max}, 0)",
                $"Inc = x + 1\nInc.repeat(0 - {max}, 0)",
                "Inc = x + 1\nInc.repeat(2147483648, 0)",
                $"Inc = x + 1\nrepeat(Inc, {max}, 0)",
                // other builtins receiving extreme numeric arguments
                $"[1, 2, 3].contains({max})",
                $"[1, 2, 3].contains(0 - {max})",
                $"sum([{max}, 0])",
                $"[{max}]:0",
            };
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(BoundaryPrograms))]
    public void BoundaryProgram_NeverThrows_OnAnyPublicEntryPoint(string source)
    {
        // Success and structured failure are BOTH acceptable outcomes here; the one
        // outcome this pin forbids is a host exception escaping a documented-total
        // entry point. Any escaping exception fails the theory with the program text.
        var limits = new EvaluationLimits { MaxSteps = 10_000 };
        var options = new RunOptions { EvaluationLimits = limits };

        Assert.NotNull(KatLangEngine.Run(source, options));
        Assert.NotNull(KatLangEngine.EvaluateToString(source, options));
        try
        {
            _ = KatLangEngine.EvaluateToAtoms(source, options);
        }
        catch (KatLangException)
        {
            // The documented structured-error channel for this entry point.
        }

        var expr = Program(source);
        _ = Evaluator.Run(expr, limits);
        _ = Evaluator.RunFlat(expr, limits);
        _ = Evaluator.RunCounted(expr, UncachedZeroArgPropertyResultCache.Instance, limits);
    }
}
