using System.Globalization;
using System.Numerics;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

public class NumericSemanticLawReviewTests
{
    private const string Maximum = "9999999999999999999999999999999999e6111";
    private static Decimal128 N(string text) => Decimal128.Parse(text, CultureInfo.InvariantCulture);
    private static RunResult.Success Run(string source, RunOptions? options = null)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, options));

    // This oracle does not round an expected value. It compares the exact integer sum
    // against BOTH adjacent rounding midpoints, including the asymmetric power-of-ten
    // cells and subnormal floor. Input literals are constructed as exact coefficients;
    // E33 below is used only to decode the returned value and its immediate neighbors.
    private readonly record struct Scaled(BigInteger Coefficient, int Exponent)
    {
        public static Scaled Of(Decimal128 value)
        {
            var parts = value.ToString("E33", CultureInfo.InvariantCulture).Split('E');
            return new(BigInteger.Parse(parts[0].Replace(".", ""), CultureInfo.InvariantCulture),
                int.Parse(parts[1], CultureInfo.InvariantCulture) - 33);
        }
        public BigInteger At(int exponent) => Coefficient * BigInteger.Pow(10, Exponent - exponent);
        public override string ToString() => Coefficient.ToString(CultureInfo.InvariantCulture)
            + "e" + Exponent.ToString(CultureInfo.InvariantCulture);
    }

    private static void CheckMean(Scaled[] inputs, string label)
    {
        var source = "avg([" + string.Join(",", inputs.Select(x => x.ToString())) + "])";
        var actual = Assert.Single(Run(source).Atoms);
        Assert.True(Decimal128.IsFinite(actual), label);
        var here = Scaled.Of(actual);
        var previous = Decimal128.BitDecrement(actual);
        var next = Decimal128.BitIncrement(actual);
        var lower = Decimal128.IsInfinity(previous) ? new Scaled(-1, 6145) : Scaled.Of(previous);
        var upper = Decimal128.IsInfinity(next) ? new Scaled(1, 6145) : Scaled.Of(next);
        var q = inputs.Select(x => x.Exponent).Append(here.Exponent).Append(lower.Exponent).Append(upper.Exponent).Min();
        var twiceSum = 2 * inputs.Aggregate(BigInteger.Zero, (sum, item) => sum + item.At(q));
        var bottom = inputs.Length * (lower.At(q) + here.At(q));
        var top = inputs.Length * (here.At(q) + upper.At(q));
        Assert.True(bottom <= twiceSum && twiceSum <= top, $"{label}: {source} outside cell of {actual:E33}");
        if (twiceSum == bottom || twiceSum == top)
        {
            // At subnormal magnitudes E33 pads beyond the storage floor: remove
            // that padding before deciding the parity of the retained coefficient.
            var retained = here.Coefficient / BigInteger.Pow(10, Math.Max(0, -6176 - here.Exponent));
            Assert.True(retained.IsEven, $"{label}: odd coefficient at a tie: {actual:E33}");
        }
        if (!twiceSum.IsZero)
            Assert.Equal(twiceSum.Sign < 0, Decimal128.IsNegative(actual));
    }

    [Fact]
    public void Mean_MidpointsAndNeighbors_NormalSubnormalBothSigns_UseOneRounding()
    {
        foreach (var q in new[] { -6176, -6175, -6143, -33, 0, 6078, 6111 })
        foreach (var c in new[] { BigInteger.One, new BigInteger(2), BigInteger.Pow(10, 33), BigInteger.Pow(10, 33) + 1, BigInteger.Pow(10, 34) - 2 })
        foreach (var sign in new[] { -1, 1 })
        foreach (var highCount in new[] { 1, 2, 3 })
        {
            var values = Enumerable.Range(0, 4).Select(i => new Scaled(sign * (c + (i < highCount ? 1 : 0)), q)).ToArray();
            CheckMean(values, $"midpoint q={q} c={c} high={highCount}");
        }

        // Intermediate overflow forces exact accumulation; these means are the
        // half-quantum ties 0.5, 1.5, 2.5, 3.5 times Epsilon, with both signs.
        var maximum = new Scaled(BigInteger.Pow(10, 34) - 1, 6111);
        foreach (var c in new[] { -21, -15, -9, -3, 3, 9, 15, 21 })
            CheckMean([maximum, maximum, maximum with { Coefficient = -maximum.Coefficient },
                maximum with { Coefficient = -maximum.Coefficient }, new(c, -6176), new(0, 0)], $"overflow/subnormal {c}");
    }

    [Fact]
    public void Mean_GeneratedCoefficientAndQuantumCorpus_LiesInExactRoundingCellsInEveryOrder()
    {
        const int seed = 0x6A24;
        var random = new Random(seed);
        for (var index = 0; index < 1000; index++)
        {
            var inputs = Enumerable.Range(0, random.Next(1, 12)).Select(_ =>
            {
                var text = random.Next(1, 10).ToString(CultureInfo.InvariantCulture)
                    + string.Concat(Enumerable.Range(0, random.Next(0, 34)).Select(_ => (char)('0' + random.Next(10))));
                var coefficient = BigInteger.Parse(text, CultureInfo.InvariantCulture) * (random.Next(2) == 0 ? 1 : -1);
                return new Scaled(coefficient, random.Next(4) switch { 0 => -6176, 1 => 6111, 2 => random.Next(-40, 41), _ => random.Next(-6176, 6112) });
            }).ToArray();
            var label = $"seed={seed} case={index}";
            CheckMean(inputs, label);
            CheckMean(inputs.OrderBy(x => x.Exponent).ToArray(), label + " ascending quantum");
            CheckMean(inputs.OrderByDescending(x => x.Exponent).ToArray(), label + " descending quantum");
        }
    }

    [Theory]
    [InlineData("0", -6176, -7000, true)]
    [InlineData("0", 6111, 7000, true)]
    [InlineData("1", -6176, -6176, true)]
    [InlineData("1", -6177, -6176, false)]
    [InlineData("10", -6177, -6176, true)]
    [InlineData("1", 6144, 6111, true)]
    [InlineData("1", 6145, 6111, false)]
    [InlineData("9999999999999999999999999999999999", 6111, 6111, true)]
    [InlineData("99999999999999999999999999999999991", 6110, 6111, false)]
    [InlineData("10000000000000000000000000000000000", 0, 0, true)]
    [InlineData("10000000000000000000000000000000001", 0, 0, false)]
    [InlineData("123000000000000000000000000000000000000000000000000", -50, -50, true)]
    public void TryExactConversion_NeverSucceedsByRounding(string coefficient, int exponent, int preferred, bool success)
    {
        foreach (var sign in new[] { -1, 1 })
        {
            var integer = sign * BigInteger.Parse(coefficient, CultureInfo.InvariantCulture);
            Assert.Equal(success, Decimal128Numerics.TryExactDecimal128(integer, exponent, preferred, out var actual));
            if (!success) continue;
            Assert.True(Decimal128.IsFinite(actual));
            var returned = Scaled.Of(actual);
            var q = Math.Min(exponent, returned.Exponent);
            Assert.Equal(new Scaled(integer, exponent).At(q), returned.At(q));
            if (integer.IsZero)
            {
                Assert.False(Decimal128.IsNegative(actual));
                Assert.Equal(Math.Clamp(preferred, -6176, 6111), Decimal128Numerics.QuantumExponent(actual));
            }
        }
    }

    [Theory]
    [InlineData("0.9999999999999999999999999999999999", "-9223372036854775808")]
    [InlineData("1.0000000000000000001", "-9223372036854775808")]
    [InlineData("1.0000000000000000001", "9999999999999999999999999999999999")]
    [InlineData("1.0000000000000000001", "-9999999999999999999999999999999999")]
    [InlineData("0.9999999999999999999999999999999999", "9999999999999999999999999999999999")]
    [InlineData("1.0000000000000000001", "10000000000000000001")]
    public void HugeExponentParity_IsDerivedFromTheExactInteger(string basis, string exponent)
    {
        var odd = !BigInteger.Parse(exponent, CultureInfo.InvariantCulture).IsEven;
        var positive = Assert.Single(Run($"{basis} ^ ({exponent})").Atoms);
        var negative = Assert.Single(Run($"(-{basis}) ^ ({exponent})").Atoms);
        Assert.Equal(odd ? -positive : positive, negative);
        Assert.Equal(odd, Decimal128.IsNegative(negative));
    }

    [Theory]
    [InlineData("0.9899999999999999999999999999999999", false)]
    [InlineData("0.99", true)]
    [InlineData("0.9900000000000000000000000000000001", true)]
    [InlineData("1.009999999999999999999999999999999", true)]
    [InlineData("1.01", true)]
    [InlineData("1.010000000000000000000000000000001", false)]
    [InlineData("NaN", false)]
    [InlineData("Infinity", false)]
    [InlineData("-0", false)]
    public void NearOneBand_HasExactInclusiveBoundaries(string basis, bool inside)
        => Assert.Equal(inside, Decimal128Numerics.IsInNearOnePowerBand(N(basis)));

    // Independent libmpdec (220 digits) and mpmath (140 and 220 digits) agree on
    // these reference digits. Neither reference uses KatLang's fixed-point series,
    // certified-power helper, nor RoundRational. These are approximation checks.
    [Theory]
    [InlineData("-1.0000000000000000001", "-9223372036854775808", "0.39758870852479882655105114046463307531038487705798")]
    [InlineData("-1.0000000000000000001", "10000000000000000001", "-2.7182818284590452354962015627756147595241288498391")]
    [InlineData("1.000000000000002", "-7080000000000000000", "2.4554791452764879921308416055888989074251451627553e-6150")]
    [InlineData("-1.000000000000002", "-7080000000000000001", "-2.4554791452764830811725510526227365623230399172822e-6150")]
    public void DelegatedPower_IndependentReferences_AgreeThroughEveryCallSpelling(string basis, string exponent, string reference)
    {
        var expected = N(reference);
        var ulp = Decimal128.ScaleB(Decimal128.One, Math.Max(-6176, Decimal128.ILogB(Decimal128.Abs(expected)) - 33));
        Decimal128? first = null;
        foreach (var source in new[]
        {
            $"({basis}) ^ ({exponent})", $"pow({basis}, {exponent})", $"Math.Pow({basis}, {exponent})",
            $"open Math\nPow({basis}, {exponent})", $"({basis}).pow({exponent})",
            $"P(x) = pow(x, {exponent})\nfirst(map([{basis}], P))",
        })
        {
            var actual = Assert.Single(Run(source).Atoms);
            Assert.True(Decimal128.Abs(actual - expected) <= ulp, source);
            if (first is { } value) Assert.Equal(value, actual);
            first = actual;
        }
    }

    [Theory]
    [InlineData("sqrt(-1) ^ 0", "1")]
    [InlineData("sqrt(-1) ^ 2", "NaN")]
    [InlineData("1 ^ sqrt(-1)", "1")]
    [InlineData("0.995 ^ sqrt(-1)", "NaN")]
    [InlineData("0.995 ^ (-ln(0))", "0")]
    [InlineData("0.995 ^ ln(0)", "Infinity")]
    [InlineData("(-0.995) ^ (-ln(0))", "0")]
    [InlineData("1.005 ^ (-ln(0))", "Infinity")]
    [InlineData("1.005 ^ ln(0)", "0")]
    [InlineData("(-0) ^ 0", "1")]
    [InlineData("(-0) ^ 3", "-0")]
    [InlineData("(-0) ^ 2", "0")]
    [InlineData("ln(0) ^ -3", "-0")]
    [InlineData("ln(0) ^ 3", "-Infinity")]
    [InlineData("(-0.995) ^ 2.0", "0.990025")]
    [InlineData("(-0.995) ^ 2.000000000000000000000000000000001", "NaN")]
    [InlineData("(-0.995) ^ 1.999999999999999999999999999999999", "NaN")]
    public void PowerSpecialsAndIntegrality_KeepTheEstablishedDomain(string source, string expected)
    {
        var actual = Assert.Single(Run(source).Atoms);
        var wanted = N(expected);
        Assert.Equal(wanted, actual);
        if (!Decimal128.IsNaN(wanted)) Assert.Equal(Decimal128.IsNegative(wanted), Decimal128.IsNegative(actual));
    }

    [Fact]
    public void DenseQuantumMean_HasABoundedAllocationCost_WithoutATimingThreshold()
    {
        // The accumulator on the pinned SDK allocates about 60 MiB; the 96 MiB
        // allowance includes evaluator overhead. The old per-quantum full-span Pow10 loop
        // allocates over 116 MiB even before evaluator overhead. This is a fixture
        // regression budget, not a new language resource limit or a speed assertion.
        var values = Enumerable.Range(-6176, 12000).Reverse().Select(q => "1e" + q.ToString(CultureInfo.InvariantCulture));
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("avg([" + string.Join(',', values) + "])").Root);
        Assert.False(Evaluator.RunCounted(program).IsError); // warm the same path
        var before = GC.GetAllocatedBytesForCurrentThread();
        var result = Evaluator.RunCounted(program);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.False(result.IsError);
        Assert.True(allocated < 96L * 1024 * 1024, $"Dense-quantum mean allocated {allocated} bytes");
        // Geometric sum (10^12000 - 1) * 10^-6176 / (9 * 12000), rounded once.
        Assert.Equal(N("9.259259259259259259259259259259259e5818"), Assert.IsType<Result.Atom>(result.Value.Value).Value);
    }

    [Fact]
    public void ExactMean_RemainsBehindCollectionStepAndCancellationChokepoints()
    {
        // Two user calls exceed the one-invocation budget; numeric additions
        // themselves are not individual evaluation steps.
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("F(x) = avg([x,1e34,-1e34])\nF(F(1))").Root);
        foreach (var (limits, errorType) in new[]
        {
            (new EvaluationLimits { MaxCollectionItems = 2 }, typeof(EvalError.CollectionSizeLimitExceeded)),
            (new EvaluationLimits { MaxMaterializedItems = 2 }, typeof(EvalError.MaterializationLimitExceeded)),
            (new EvaluationLimits { MaxSteps = 1 }, typeof(EvalError.EvaluationStepLimitExceeded)),
        })
        {
            var (result, _) = Evaluator.RunCountedObserved(program, limits: limits);
            Assert.True(result.IsError, errorType.Name);
            Assert.True(result.Error.IsResourceLimit);
            Assert.Equal(errorType, result.Error.GetType());
        }
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        Assert.Throws<OperationCanceledException>(() => Evaluator.RunCountedObserved(program, cancellationToken: cancellation.Token));
    }

    [Theory]
    [InlineData("avg((1, 1e34, -1e34))")]
    [InlineData("avg((1.0, 2.00))")]
    [InlineData("(-0.9999999999999999999999999999999999) ^ 1e34")]
    [InlineData("(-1.000000000000002) ^ -7080000000000000001")]
    public async Task ChangedPaths_ResumeAfterAGenuineSuspension(string source)
    {
        var expected = Run(source);
        var actual = await RunSuspending(source);
        Assert.Equal(expected.Value, actual.Value);
        Assert.Equal(expected.ToDisplayString(), actual.ToDisplayString());
    }

    internal static async Task<RunResult.Success> RunSuspending(string source)
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("ReviewGate", (_, _) =>
            {
                Interlocked.Increment(ref calls);
                entered.SetResult();
                return new ValueTask<Result>(release.Task);
            })),
        };
        var pending = KatLangEngine.RunAsync($"AfterGate(x) = if(x == 0, {{\n{source}\n}}, 99)\nAfterGate(ReviewGate())", options);
        try
        {
            await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
            Assert.False(pending.IsCompleted);
        }
        finally { release.TrySetResult(new Result.Atom(0)); }
        var result = Assert.IsType<RunResult.Success>(await pending);
        Assert.Equal(1, calls);
        return result;
    }

    [Theory]
    [InlineData("-1.0000000000000000001", "10000000000000000001")]
    [InlineData("-1.000000000000002", "-7080000000000000001")]
    [InlineData("1.0000000000000000001", "-9223372036854775808")]
    public void PowerLoop_HasAWitnessOfPlannedDispatch(string basis, string exponent)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid($"Step(x) = x ^ ({exponent})\nrepeat(Step, 1, {basis})").Root);
        var diagnostics = new LoopOptimizationDiagnostics();
        var (planned, _) = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics);
        var (generic, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        Assert.False(planned.IsError);
        Assert.False(generic.IsError);
        Assert.Equal(generic.Value, planned.Value);
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
    }

    [Fact]
    public void MeanSpecials_StayOnTheSequentialIeeePath()
    {
        foreach (var source in new[] { "avg(-0)", "avg((-0,-0))", "avg((-0,0))", "avg((0,-0))", "avg((0 * -1, -4 mod 2))" })
            Assert.False(Decimal128.IsNegative(Assert.Single(Run(source).Atoms)));
        Assert.True(Decimal128.IsNaN(Assert.Single(Run($"avg(({Maximum}, {Maximum}, ln(0)))").Atoms)));
        Assert.Equal(Decimal128.NegativeInfinity, Assert.Single(Run($"avg(({Maximum}, ln(0), {Maximum}))").Atoms));
        foreach (var special in new[] { "sqrt(-1)", "ln(0)", "-ln(0)" })
            Assert.Equal(Run(special).Value, Run($"avg({special})").Value);
        var empty = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("avg([])"));
        Assert.Equal(KatLangErrorCode.ArityMismatch, Assert.Single(empty.Errors).Code);
    }

    [Fact]
    public void QuantumTies_RetainFirstRepresentative_AndNumericEqualityHashesAgree()
    {
        foreach (var first in new[] { "1", "1.0", "1.00" })
        foreach (var second in new[] { "1", "1.0", "1.00" })
        foreach (var aggregate in new[] { "min", "max" })
            Assert.True(Decimal128.HaveSameQuantum(N(first), Assert.Single(Run($"{aggregate}(({first},{second}))").Atoms)));
        foreach (var group in new[] { new[] { N("1"), N("1.0"), N("1.00") }, new[] { N("0"), N("-0"), N("-0.00") }, new[] { Decimal128.NaN, -Decimal128.NaN } })
        foreach (var a in group)
        foreach (var b in group)
        {
            var left = new Result.Atom(a);
            var right = new Result.Atom(b);
            Assert.True(Result.ValueComparer.Equals(left, right));
            Assert.Equal(Result.ValueComparer.GetHashCode(left), Result.ValueComparer.GetHashCode(right));
        }
    }

    [Theory]
    [InlineData("1", "1.000000000000000000000000000000001")]
    [InlineData("9e6144", "9.000000000000000000000000000000001e6144")]
    [InlineData("-9.000000000000000000000000000000001e6144", "-9e6144")]
    [InlineData("-1e-6176", "1e-6176")]
    [InlineData("1e-6176", "2e-6176")]
    public void RandomScaling_ExcludesUpperEndpointEvenWhenRoundingWouldReachIt(string start, string end)
    {
        foreach (var fraction in new[] { Decimal128.Zero, N("0.5"), N("0.9999999999999999999999999999999999") })
        {
            var value = Evaluator.ScaleRandomUnitFractionToHalfOpenRange(N(start), N(end), fraction);
            Assert.True(value >= N(start) && value < N(end));
        }
    }

    [Fact]
    public void ChangedNumbersAndDiagnostics_AreIndependentOfCultureAndDisplayDefaults()
    {
        var saved = CultureInfo.CurrentCulture;
        var savedUi = CultureInfo.CurrentUICulture;
        try
        {
            var sources = new[] { "avg((1,1e34,-1e34))", "(-1.0000000000000000001)^10000000000000000001", "range(1.0,3)" };
            var expected = sources.Select(s => Run(s).Value).ToArray();
            var badSources = new[] { "pow(-0, -0.5)", "DisplayDecimals = 99\npow(-0, -0.5)" };
            var failures = badSources.Select(s => Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(s)).ToDisplayString()).ToArray();
            foreach (var culture in new[] { "en-US", "de-DE", "ar-SA" })
            foreach (var places in new int?[] { null, 0, 99 })
            {
                CultureInfo.CurrentCulture = CultureInfo.CurrentUICulture = CultureInfo.GetCultureInfo(culture);
                var options = new RunOptions { DefaultDisplayDecimals = places };
                for (var i = 0; i < sources.Length; i++)
                    Assert.True(Result.ValueComparer.Equals(expected[i], Run(sources[i], options).Value), sources[i]);
                for (var i = 0; i < badSources.Length; i++)
                    Assert.Equal(failures[i], Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(badSources[i], options)).ToDisplayString());
            }
        }
        finally { CultureInfo.CurrentCulture = saved; CultureInfo.CurrentUICulture = savedUi; }
    }
}
