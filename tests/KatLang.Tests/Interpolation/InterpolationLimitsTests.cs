using KatLang.Evaluation;

namespace KatLang.Tests.Interpolation;

/// <summary>
/// STR-02 string limits (C#-only host policy): interpolation is the one way source builds a
/// longer string, so its text is bounded by the per-string ceiling
/// (<see cref="EvaluationLimits.MaxStringLength"/>) and the run's cumulative string budget
/// (<see cref="EvaluationLimits.MaxMaterializedStringChars"/>). Each piece is checked against the
/// LIVE capacity before it is appended — no oversized text is ever built, no later hole runs once
/// the text crossed — and the finished text is reserved once, exactly its length. Crossing is the
/// ordinary terminal string-limit error whose requested length is the length the text reached.
/// </summary>
public class InterpolationLimitsTests
{
    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) Observe(string source, EvaluationLimits? limits)
        => Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), limits);

    private static EvalError ErrorOf(string source, EvaluationLimits limits)
    {
        var (result, _) = Observe(source, limits);
        Assert.True(result.IsError, "expected a string-limit error");
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static EvaluationLimits Str(int max) => new() { MaxStringLength = max };

    [Fact]
    public void TextExactlyAtTheCeiling_Succeeds()
    {
        var (result, _) = Observe("\"{'ab'}{'cd'}\"", Str(4));
        Assert.False(result.IsError);
        Assert.Equal("abcd", Assert.IsType<Result.Str>(result.Value.Value).Value);
    }

    [Theory]
    [InlineData("\"{'ab'}{'cde'}\"", 5)]
    [InlineData("\"abc{'d'}e\"", 5)]
    [InlineData("\"abcde{1}\"", 5)]
    [InlineData("\"{[1, 2]}\"", 5)]
    [InlineData("\"{(12, 345)}\"", 5)]
    public void TheAppendThatCrossesTheCeiling_IsTheStringSizeError_RequestingTheLengthReached(string source, long requested)
    {
        var limit = Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf(source, Str(4)));
        Assert.Equal(4, limit.Limit);
        Assert.Equal(requested, limit.Requested);
        Assert.NotNull(limit.Span);
    }

    [Fact]
    public void ACrossingIsTerminal_AndBuildsNoOversizedText()
    {
        var (result, budget) = Observe("\"{'ab'}{'cd'}\"", Str(3));
        Assert.IsType<EvalError.StringSizeLimitExceeded>(result.Error);
        // Only the two hole literals were reserved; the crossing text was never reserved.
        Assert.Equal(4, budget.MaterializedStringChars);
    }

    [Fact]
    public void TheCumulativeBudget_CountsTheHolesStringsAndTheFinishedText()
    {
        var (exact, exactBudget) = Observe("\"{'ab'}{'cd'}\"", new EvaluationLimits { MaxMaterializedStringChars = 8 });
        Assert.False(exact.IsError);
        Assert.Equal(8, exactBudget.MaterializedStringChars);

        var (failure, failureBudget) = Observe("\"{'ab'}{'cd'}\"", new EvaluationLimits { MaxMaterializedStringChars = 7 });
        var limit = Assert.IsType<EvalError.StringMaterializationLimitExceeded>(failure.Error);
        Assert.Equal(4, failureBudget.MaterializedStringChars);
        Assert.Equal(7, limit.Limit);
    }

    [Fact]
    public void ALiveCapacityCheck_SeesStringsTheHolesCreatedBeforeTheAppend()
    {
        // 'abc' (3) is materialized while the text is "x" (1): the live capacity left for the
        // text is 7 - 3 = 4, so "x" + "abc" fits only as 4 <= 4, and the final reservation of the
        // 4-unit text then needs 3 + 4 = 7 units in all.
        var (fits, _) = Observe("\"x{'abc'}\"", new EvaluationLimits { MaxMaterializedStringChars = 7 });
        Assert.False(fits.IsError);
        var (crosses, _) = Observe("\"x{'abc'}\"", new EvaluationLimits { MaxMaterializedStringChars = 6 });
        Assert.IsType<EvalError.StringMaterializationLimitExceeded>(crosses.Error);
    }

    [Fact]
    public void Doubling_IsBoundedByTheCeiling_WithTheRequestedLengthOfTheCrossingAppend()
    {
        // D doubles its argument: twenty doublings of 'x' would be 2^20 = 1,048,576 units, past
        // the 1,000,000 ceiling; the crossing append is the second half of the twentieth.
        var limit = Assert.IsType<EvalError.StringSizeLimitExceeded>(
            ErrorOf("D(s) = \"{s}{s}\"\nD.repeat(20, 'x')", new EvaluationLimits()));
        Assert.Equal(EvaluationLimits.MaxSupportedStringLength, limit.Limit);
        Assert.Equal(1L << 20, limit.Requested);

        var (nineteen, _) = Observe("D(s) = \"{s}{s}\"\nD.repeat(19, 'x')", null);
        Assert.False(nineteen.IsError);
        Assert.Equal(1 << 19, Assert.IsType<Result.Str>(nineteen.Value.Value).Value.Length);
    }

    [Fact]
    public void AHugeHoleValue_StopsAtTheFirstPieceThatCrosses()
    {
        var limit = Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf("\"{range(1, 50000)}\"", Str(1_000)));
        Assert.InRange(limit.Requested, 1_001, 1_010);
    }

    [Fact]
    public void ZeroCeiling_RefusesEveryNonEmptyText_AndAdmitsTheEmptyOne()
    {
        Assert.False(Observe("\"{''}\"", Str(0)).Result.IsError);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf("\"{1}\"", Str(0)));
    }

    [Fact]
    public void TheLimitIsUtf16CodeUnits()
    {
        Assert.False(Observe("\"{'\U0001D54F'}\"", Str(4)).Result.IsError);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf("\"{'\U0001D54F'}{'\U0001D54F'}x\"", Str(4)));
    }

    [Fact]
    public async Task ACrossingIsTheSameErrorOnTheAsyncTwin()
    {
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("\"{'ab'}{'cde'}\"").Root);
        var sync = Evaluator.RunCounted(expr, new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(), Str(4));
        var asynchronous = await Evaluator.RunCountedAsync(expr, new AsyncEvaluation.PassThroughAsyncZeroArgPropertyResultCache(), Str(4));
        var syncLimit = Assert.IsType<EvalError.StringSizeLimitExceeded>(sync.Error);
        var asyncLimit = Assert.IsType<EvalError.StringSizeLimitExceeded>(asynchronous.Error);
        Assert.Equal(syncLimit.Requested, asyncLimit.Requested);
        Assert.Equal(syncLimit.Span, asyncLimit.Span);
    }
}
