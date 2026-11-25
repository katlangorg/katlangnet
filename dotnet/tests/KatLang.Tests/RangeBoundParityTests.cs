using System.Numerics;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// The range-bound safety policy (integer bounds within the ±1e34 exact-unit-step
/// domain) must hold IDENTICALLY on every execution path that builds an inclusive
/// range: the synchronous evaluator, the async twin, and sequence-pipeline direct
/// range iteration (which shares the synchronous entry). The async twin originally
/// re-implemented only the whole-number half of the validation and omitted the
/// magnitude check — above 1e34 a unit step is absorbed (<c>x + 1 == x</c>) while
/// the computed cardinality still looks small enough to pass collection limits, so
/// enumeration could spin forever. Both paths now share
/// <c>Evaluator.ValidateRangeBound</c>; these tests pin the parity and the
/// non-hang property.
/// </summary>
public class RangeBoundParityTests
{
    private static EvalResult<IReadOnlyList<Decimal128>> EvalSync(string source)
        => Evaluator.RunFlat(AsyncEvaluationHarness.Ast(source));

    /// <summary>
    /// Runs through the async TWIN evaluator (an async-capable cache forces the twin
    /// family; a plain RunFlatAsync would take the synchronous fast path and prove
    /// nothing about the twin). Bounded await: a wedged twin fails the test instead
    /// of hanging the suite — this is the safe nontermination-regression pattern the
    /// async suites already use.
    /// </summary>
    private static async Task<EvalResult<Evaluator.CountedResult>> EvalTwin(string source)
        => await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(
                AsyncEvaluationHarness.Ast(source),
                new PassThroughAsyncZeroArgPropertyResultCache()));

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    // ── The drift reproduction: sync rejected, async accepted ────────────────

    [Fact]
    public void Sync_RangeAtTwiceTheExactBound_IsRejected()
    {
        var result = EvalSync("range(2e34, 2e34)");
        Assert.True(result.IsError);
        var error = Assert.IsType<EvalError.IllegalInEval>(Innermost(result.Error));
        Assert.Contains("range start", error.Reason);
    }

    [Fact]
    public async Task Async_RangeAtTwiceTheExactBound_IsRejected()
    {
        var result = await EvalTwin("range(2e34, 2e34)");
        Assert.True(result.IsError);
        var error = Assert.IsType<EvalError.IllegalInEval>(Innermost(result.Error));
        Assert.Contains("range start", error.Reason);
    }

    [Fact]
    public async Task Async_RangeWithAbsorbedSpanAboveTheBound_RejectsInsteadOfSpinning()
    {
        // The nontermination shape: 2e34 + 10 rounds back to 2e34, so before the
        // shared validator the async twin computed a tiny cardinality, passed the
        // collection limits, and then stepped +1 forever without advancing. The
        // bounded await above turns any regression into a loud failure.
        var result = await EvalTwin("range(2e34, 2e34 + 10)");
        Assert.True(result.IsError);
        Assert.IsType<EvalError.IllegalInEval>(Innermost(result.Error));
    }

    // ── Boundary parity: ±1e33 and ±1e34 behave identically on both paths ────

    [Theory]
    [InlineData("range(1e33, 1e33 + 2)", "1000000000000000000000000000000000 1000000000000000000000000000000001 1000000000000000000000000000000002")]
    [InlineData("range(1e34 - 2, 1e34)", "9999999999999999999999999999999998 9999999999999999999999999999999999 10000000000000000000000000000000000")]
    [InlineData("range(0 - 1e33 - 2, 0 - 1e33)", "-1000000000000000000000000000000002 -1000000000000000000000000000000001 -1000000000000000000000000000000000")]
    [InlineData("range(0 - 1e34, 0 - 1e34 + 2)", "-10000000000000000000000000000000000 -9999999999999999999999999999999999 -9999999999999999999999999999999998")]
    public async Task ExactBoundaryRanges_EnumerateIdenticallyOnBothPaths(string source, string expectedAtoms)
    {
        var expected = expectedAtoms
            .Split(' ')
            .Select(static text => Decimal128.Parse(text, System.Globalization.CultureInfo.InvariantCulture))
            .ToArray();

        var sync = EvalSync(source);
        Assert.False(sync.IsError, $"sync failed: {(sync.IsError ? sync.Error : null)}");
        Assert.Equal(expected, sync.Value);

        var twin = await EvalTwin(source);
        Assert.False(twin.IsError, $"async twin failed: {(twin.IsError ? twin.Error : null)}");
        Assert.Equal(expected, twin.Value.Value.ToHostAtoms());
    }

    [Theory]
    [InlineData("range(2e34, 5)", "range start")]
    [InlineData("range(5, 2e34)", "range stop")]
    [InlineData("range(0 - 2e34, 5)", "range start")]
    [InlineData("range(5, 0 - 2e34)", "range stop")]
    public async Task BeyondBoundRanges_RejectIdenticallyOnBothPaths(string source, string expectedBoundName)
    {
        var sync = EvalSync(source);
        Assert.True(sync.IsError);
        var syncError = Assert.IsType<EvalError.IllegalInEval>(Innermost(sync.Error));
        Assert.Contains(expectedBoundName, syncError.Reason);

        var twin = await EvalTwin(source);
        Assert.True(twin.IsError);
        var twinError = Assert.IsType<EvalError.IllegalInEval>(Innermost(twin.Error));
        Assert.Equal(syncError.Reason, twinError.Reason);
    }

    // ── The fail-loud enumeration backstop ───────────────────────────────────

    [Fact]
    public void Enumeration_WithUnvalidatedAbsorbingBounds_FailsLoudInsteadOfSpinning()
    {
        // Internal-invariant guard: bounds that bypass ValidateRangeBound (possible
        // only for internal callers) must throw on the first absorbed step, never
        // loop. This is the same fail-loud discipline as the budget underflow guards.
        // The stop must be parsed directly: written arithmetic `2e34 + 10` would
        // itself absorb back to 2e34 and leave nothing to step over. At this
        // magnitude the quantum is 10, so 2e34 + 10 is the NEXT representable value
        // and the unit step from 2e34 toward it can never arrive.
        var twoE34 = Decimal128.Parse("2e34", System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture);
        var nextRepresentable = Decimal128.Parse("2.000000000000000000000000000000001e34", System.Globalization.NumberStyles.Float, System.Globalization.CultureInfo.InvariantCulture);
        Assert.True(nextRepresentable > twoE34);
        var bounds = new Evaluator.InclusiveRange(twoE34, nextRepresentable);

        Assert.Throws<InvalidOperationException>(() =>
        {
            foreach (var _ in Evaluator.EnumerateInclusiveRangeValues(bounds))
            {
            }
        });
    }
}
