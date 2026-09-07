using System.Globalization;
using System.Numerics;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

public class Decimal128IntegerPowerReviewTests
{
    private static Decimal128 N(string text) => Decimal128.Parse(text, CultureInfo.InvariantCulture);

    [Fact]
    public void BoundedExactRationals_LieInTheReturnedValuesRoundingCells()
    {
        // Independent oracle: materialize these bounded exact rational powers,
        // then compare them to BOTH exact midpoints around the returned value.
        // No production decomposition, rounding, or interval helper is reused.
        foreach (var (coefficient, scale, exponent) in new (string, int, int)[]
        {
            ("4605889780318500696115135255278667", -33, 3),
            ("4605889780318500696115135255278666", -33, 3),
            ("11", -1, -34), ("5", 0, 49), ("5", 0, -50),
            ("5", 0, -100), ("2", 0, 112), ("2", 0, 113),
            ("2", 0, -49), ("2", 0, -50), ("-2", 0, -49),
            ("5", -2059, 3), ("-5", -2059, 3),
            ("15", -3089, 2), ("25", -3089, 2),
            ("1", -3088, 2), ("1", -3089, 2),
            ("9999999999999999999999999999999999", -3105, 2),
            ("2", 3072, 2), ("4", 3072, 2), ("-4", 2050, 3),
            ("9999999999999999999999999999999999", -33, 127),
            ("1000000000000000000000000000000001", -33, -127),
        })
            CheckPower(coefficient, scale, exponent);

        var random = new Random(0xB406);
        for (var i = 0; i < 256; i++)
        {
            var digits = random.Next(1, 35);
            var coefficient = random.Next(1, 10).ToString(CultureInfo.InvariantCulture)
                + string.Concat(Enumerable.Range(1, digits - 1).Select(_ => random.Next(10)));
            if ((i & 1) != 0)
                coefficient = "-" + coefficient;
            var exponent = random.Next(1, 129) * ((i & 2) == 0 ? 1 : -1);
            CheckPower(coefficient, random.Next(-34, 5), exponent);
        }
    }

    private static void CheckPower(string coefficientText, int scale, int exponent)
    {
        var coefficient = BigInteger.Parse(coefficientText, CultureInfo.InvariantCulture);
        var exact = Fraction.Scaled(BigInteger.Pow(BigInteger.Abs(coefficient), Math.Abs(exponent)), scale * Math.Abs(exponent));
        if (exponent < 0)
            exact = new Fraction(exact.Denominator, exact.Numerator);
        var b = N($"{coefficientText}e{scale}");
        Assert.True(Decimal128Numerics.TryIntegerPower(b, exponent, out var actual));
        Assert.Equal(coefficient.Sign < 0 && (exponent & 1) != 0, Decimal128.IsNegative(actual));
        AssertRoundingCell(exact, Decimal128.Abs(actual), $"{coefficientText}e{scale} ^ {exponent}");
    }

    private static void AssertRoundingCell(Fraction exact, Decimal128 actual, string source)
    {
        Assert.False(Decimal128.IsNaN(actual), source);
        if (Decimal128.IsInfinity(actual))
        {
            Assert.True(CompareToMidpoint(exact, Fraction.Of(Decimal128.MaxValue), Fraction.Scaled(1, 6145)) >= 0, source);
            return;
        }

        var here = Fraction.Of(actual);
        var next = Decimal128.BitIncrement(actual);
        var upper = Decimal128.IsInfinity(next) ? Fraction.Scaled(1, 6145) : Fraction.Of(next);
        var upperComparison = CompareToMidpoint(exact, here, upper);
        var lowerComparison = actual == 0 ? 1 : CompareToMidpoint(exact, Fraction.Of(Decimal128.BitDecrement(actual)), here);
        Assert.True(lowerComparison >= 0 && upperComparison <= 0, $"{source}: outside rounding cell of {actual:E33}");
        if (lowerComparison == 0 || upperComparison == 0)
        {
            // At a tie the retained coefficient on the target grid must be even.
            var text = actual.ToString("E33", CultureInfo.InvariantCulture).Split('E');
            var scientificExponent = int.Parse(text[1], CultureInfo.InvariantCulture);
            var retained = BigInteger.Parse(text[0].Replace(".", ""), CultureInfo.InvariantCulture);
            retained /= BigInteger.Pow(10, Math.Max(-6176 - (scientificExponent - 33), 0));
            Assert.True(retained.IsEven, $"{source}: odd retained coefficient at an exact tie");
        }
    }

    private static int CompareToMidpoint(Fraction value, Fraction a, Fraction b)
        => (2 * value.Numerator * a.Denominator * b.Denominator).CompareTo(
            value.Denominator * (a.Numerator * b.Denominator + b.Numerator * a.Denominator));

    private readonly record struct Fraction(BigInteger Numerator, BigInteger Denominator)
    {
        public static Fraction Scaled(BigInteger coefficient, int scale)
            => scale >= 0 ? new(coefficient * BigInteger.Pow(10, scale), 1) : new(coefficient, BigInteger.Pow(10, -scale));

        public static Fraction Of(Decimal128 value)
        {
            var text = value.ToString("E33", CultureInfo.InvariantCulture).Split('E');
            return Scaled(BigInteger.Parse(text[0].Replace(".", ""), CultureInfo.InvariantCulture),
                int.Parse(text[1], CultureInfo.InvariantCulture) - 33);
        }
    }

    [Fact]
    public void Certification_UsesTheLastPermittedPrecision_AndRejectsAnInvalidCap()
    {
        var b = N("4.605889780318500696115135255278667");
        Assert.False(Decimal128Numerics.TryIntegerPower(b, 3, 39, 39, out _));
        // 40, not the next doubled precision 78, is the last allowed attempt.
        Assert.True(Decimal128Numerics.TryIntegerPower(b, 3, 39, 40, out var certified));
        Assert.Equal(N("97.71036217420039313913263975817349"), certified);
        Assert.Throws<ArgumentOutOfRangeException>(() => Decimal128Numerics.TryIntegerPower(b, 3, 35, 34, out _));

        var span = new SourceSpan(1, 1, 1, 39);
        var failed = Evaluator.EvalPow(span, b, 3, initialWorkingDigits: 39, maxWorkingDigits: 39);
        Assert.True(failed.IsError);
        var error = Assert.IsType<EvalError.IllegalInEval>(failed.Error);
        Assert.Equal(span, error.Span);
        Assert.Contains("39-digit working-precision limit", error.Reason);
    }

    [Fact]
    public async Task CertificationFailure_PropagatesThroughSyncCountedAndSuspendingAsyncRuns()
    {
        // The cache seam injects the ACTUAL cap verdict into an otherwise legal
        // program. No source input is asserted to exhaust the production cap.
        var ast = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("P = 0\n7\nP\n9").Root);
        var sync = Evaluator.Run(ast, new CertificationFailureCache());
        var counted = Evaluator.RunCounted(ast, new CertificationFailureCache());
        var asyncResult = await Evaluator.RunAsync(ast, new CertificationFailureCache());
        var asyncCounted = await Evaluator.RunCountedAsync(ast, new CertificationFailureCache());
        Assert.True(sync.IsError);
        Assert.True(counted.IsError);
        Assert.True(asyncResult.IsError);
        Assert.True(asyncCounted.IsError);
        foreach (var failure in new[] { sync.Error, counted.Error, asyncResult.Error, asyncCounted.Error })
        {
            var inner = failure;
            while (inner is EvalError.WithContext context)
                inner = context.Inner;
            Assert.Contains("39-digit working-precision limit", Assert.IsType<EvalError.IllegalInEval>(inner).Reason);
        }
    }

    private sealed class CertificationFailureCache : IAsyncZeroArgPropertyResultCache
    {
        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
            => Evaluator.EvalPow(null, N("4.605889780318500696115135255278667"), 3, 39, 39).Error;

        public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
            ZeroArgPropertyExecution execution, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            await Task.Yield();
            return GetOrEvaluate(execution, () => throw new InvalidOperationException("The seam supplies the cap verdict."));
        }
    }

    [Fact]
    public void SharedRounding_CertifiesTiesCarriesAndSubnormalBoundaries()
    {
        foreach (var (coefficient, scale) in new (string, int)[]
        {
            ("10000000000000000000000000000000005", 0), // retained even
            ("10000000000000000000000000000000015", 0), // retained odd
            ("99999999999999999999999999999999994", 0),
            ("99999999999999999999999999999999995", 0), // carry
            ("99999999999999999999999999999999995", 6110), // overflow tie
            ("9999999999999999999999999999999995", -6177), // normal boundary
            ("5", -6177), ("15", -6177), ("25", -6177),
        })
        {
            var integer = BigInteger.Parse(coefficient, CultureInfo.InvariantCulture);
            var rounded = Decimal128Numerics.RoundRational(integer, 1, scale);
            AssertRoundingCell(Fraction.Scaled(integer, scale), rounded.ToDecimal128(false), $"{coefficient}e{scale}");
            Assert.Equal(-rounded.ToDecimal128(false), rounded.ToDecimal128(true));
            Assert.True(Decimal128.IsNegative(rounded.ToDecimal128(true)));
        }
    }

    [Fact]
    public void AverageOverflowRescue_PreservesNegativeTiesSignedZeroAndQuantum()
    {
        const string max = "9999999999999999999999999999999999e6111";
        foreach (var (residual, expected) in new[] { ("-3e-6176", "-0"), ("-9e-6176", "-2e-6176"), ("-15e-6176", "-2e-6176") })
        {
            var source = $"avg((-{max}, -{max}, {max}, {max}, {residual}, 0))";
            var value = Assert.IsType<Result.Atom>(Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).Value).Value;
            Assert.Equal(N(expected), value);
            Assert.True(Decimal128.IsNegative(value));
        }
        var mean = Assert.IsType<Result.Atom>(Assert.IsType<RunResult.Success>(KatLangEngine.Run($"avg((-{max}, -{max}))")).Value).Value;
        Assert.Equal(-Decimal128.MaxValue, mean);
        Assert.True(Decimal128.HaveSameQuantum(Decimal128.MaxValue, mean));
        var sum = Assert.IsType<Result.Atom>(Assert.IsType<RunResult.Success>(KatLangEngine.Run($"sum(({max}, {max}, -{max}))")).Value).Value;
        Assert.True(Decimal128.IsPositiveInfinity(sum));
    }

    [Theory]
    [InlineData("5", -50, "1125899906842624e-50", -68)]
    [InlineData("-5", -51, "-2251799813685248e-51", -69)]
    [InlineData("0.05", -50, "1125899906842624e50", 32)]
    public void CertifiedReciprocal_PreservesACompatiblePreviousQuantum(string b, int exponent, string exact, int quantum)
    {
        var actual = Assert.IsType<RunResult.Success>(KatLangEngine.Run($"({b}) ^ {exponent}"));
        var number = Assert.IsType<Result.Atom>(actual.Value).Value;
        Assert.Equal(N(exact), number);
        Assert.Equal(quantum, Decimal128.ILogB(Decimal128.GetQuantum(number)));
    }

    [Theory]
    [InlineData("10", -6146)]
    [InlineData("-10", -6147)]
    [InlineData("2", -20420)]
    public void PositiveIntermediateOverflow_RetainsTheExistingDelegation(string b, int exponent)
    {
        var expected = Evaluator.CanonicalizeMathResult(Decimal128.Pow(N(b), exponent));
        var actual = Assert.IsType<Result.Atom>(Evaluator.EvalPow(null, N(b), exponent).Value).Value;
        Assert.Equal(expected, actual);
        Assert.True(Decimal128.HaveSameQuantum(expected, actual));
    }
}
