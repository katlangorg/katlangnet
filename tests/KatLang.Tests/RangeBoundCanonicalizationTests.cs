using System.Globalization;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// K6-R6: accepted whole-number bounds produce canonical integer range elements in
/// sync, async, and fused execution. Assert quantum and zero sign on the atoms:
/// Decimal128 equality ignores both, and formatting alone cannot establish the rule.
/// </summary>
public class RangeBoundCanonicalizationTests
{
    private static Decimal128 N(string text)
        => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);

    private static string Display(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString();

    private static IReadOnlyList<Decimal128> Atoms(string source)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        return result.Value;
    }

    /// <summary>
    /// Runs through the async TWIN family (an async-capable cache forces it; a plain
    /// RunFlatAsync would take the synchronous fast path and prove nothing about the
    /// twin), with the harness's bounded await.
    /// </summary>
    private static async Task<IReadOnlyList<Decimal128>> TwinAtoms(string source)
    {
        var result = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(
                AsyncEvaluationHarness.Ast(source),
                new PassThroughAsyncZeroArgPropertyResultCache()));
        if (result.IsError)
            Assert.Fail($"Expected async twin success but got error: {result.Error}");
        return result.Value.Value.ToHostAtoms();
    }

    private static int QuantumExponent(Decimal128 value)
        => Decimal128.ILogB(Decimal128.GetQuantum(value));

    /// <summary>
    /// Range integers use exponent 0, except for the ±1e34 endpoints (exponent 1),
    /// and never negative zero. Value equality alone can see neither distinction.
    /// </summary>
    private static void AssertCanonicalIntegers(IReadOnlyList<Decimal128> atoms, string context)
    {
        Assert.NotEmpty(atoms);
        foreach (var atom in atoms)
        {
            var text = atom.ToString(CultureInfo.InvariantCulture);
            Assert.True(Decimal128.IsInteger(atom), $"{context}: {text} is not an integer");
            var expectedExponent = Decimal128.Abs(atom) == N("1e34") ? 1 : 0;
            Assert.True(
                QuantumExponent(atom) == expectedExponent,
                $"{context}: {text} carries quantum exponent {QuantumExponent(atom)} instead of {expectedExponent}");
            Assert.False(
                atom == Decimal128.Zero && Decimal128.IsNegative(atom),
                $"{context}: negative zero leaked into the range");
        }
    }

    // ── The audit reproduction and every spelling-sensitive shape ────────────

    [Theory]
    // The reproduction: the same integer bounds, three spellings, one list.
    [InlineData("range(1, 3)", "[1, 2, 3]")]
    [InlineData("range(1.0, 3)", "[1, 2, 3]")]
    [InlineData("range(1, 3.0)", "[1, 2, 3]")]
    [InlineData("range(1.00, 3.000)", "[1, 2, 3]")]
    // Exponent spellings carry a quantum too (positive exponents merely display plain).
    [InlineData("range(1e1, 12)", "[10, 11, 12]")]
    [InlineData("range(100e-2, 300e-2)", "[1, 2, 3]")]
    [InlineData("range(0e5, 1)", "[0, 1]")]
    // Zero: signed and fractional spellings become canonical integer zero.
    [InlineData("range(-0, 2)", "[0, 1, 2]")]
    [InlineData("range(-0.0, 2)", "[0, 1, 2]")]
    [InlineData("range(0.0, 2.0)", "[0, 1, 2]")]
    [InlineData("range(2, -0.0)", "[2, 1, 0]")]
    // Descending, singleton, and negative bounds follow the same rule; inclusivity
    // and direction are untouched (`range(1.0, 0)` is still the two-item descent).
    [InlineData("range(3.0, 1)", "[3, 2, 1]")]
    [InlineData("range(1.0, 0)", "[1, 0]")]
    [InlineData("range(2.0, 2.0)", "[2]")]
    [InlineData("range(-0.0, 0)", "[0]")]
    [InlineData("range(-0, -0.0)", "[0]")]
    [InlineData("range(-3.0, -1)", "[-3, -2, -1]")]
    [InlineData("range(-1, -3.00)", "[-1, -2, -3]")]
    // Bounds that arrive through properties and arithmetic, not literals.
    [InlineData("Lo = 1.0\nHi = 3.0\nrange(Lo, Hi)", "[1, 2, 3]")]
    [InlineData("range(0.5 + 0.5, 3)", "[1, 2, 3]")]
    [InlineData("range(0.0 - 0.0, 2)", "[0, 1, 2]")]
    [InlineData("range(0.0 * -1, 2)", "[0, 1, 2]")]
    [InlineData("range(-0e-6176, 0e6111)", "[0]")]
    public async Task IntegralBoundSpelling_NeverReachesTheList(string source, string expectedDisplay)
    {
        Assert.Equal(expectedDisplay, Display(source));

        var sync = Atoms(source);
        AssertCanonicalIntegers(sync, source);

        var twin = await TwinAtoms(source);
        Assert.Equal(sync, twin);
        AssertCanonicalIntegers(twin, source + " (async twin)");
    }

    [Theory]
    [InlineData("range(1, 3)", "[1, 2, 3]")]
    [InlineData("range(3, 1)", "[3, 2, 1]")]
    [InlineData("range(-2, 2)", "[-2, -1, 0, 1, 2]")]
    [InlineData("range(5, 5)", "[5]")]
    [InlineData("range(0, 0)", "[0]")]
    public void CanonicalBounds_AreUnchanged(string source, string expectedDisplay)
    {
        Assert.Equal(expectedDisplay, Display(source));
        AssertCanonicalIntegers(Atoms(source), source);
    }

    [Fact]
    public void SameIntegerBounds_AreOneList_ForEverySpelling()
    {
        string[] spellings =
        [
            "range(1, 3)",
            "range(1.0, 3)",
            "range(1, 3.0)",
            "range(1.00, 3.000)",
            "range(1e0, 3)",
            "range(0.5 + 0.5, 3)",
        ];

        var reference = Atoms(spellings[0]);
        foreach (var spelling in spellings)
        {
            Assert.Equal("[1, 2, 3]", Display(spelling));
            var atoms = Atoms(spelling);
            Assert.Equal(reference, atoms);
            for (var i = 0; i < atoms.Count; i++)
            {
                Assert.True(
                    Decimal128.HaveSameQuantum(reference[i], atoms[i]),
                    $"{spelling}: item {i} has a different quantum than range(1, 3)");
            }
        }

        // Structural equality was never the problem and still holds.
        Assert.Equal(new[] { Decimal128.One }, Atoms("range(1.0, 3) == range(1, 3)"));
    }

    // ── The optimizer's direct range iteration shares the seam ───────────────

    [Fact]
    public void SequencePipelineDirectRange_IteratesCanonicalIntegers()
    {
        // `.string` renders the quantum, so the predicate observes representation:
        // before the fix the fused range iterated `2.0`, its string was '2.0', and
        // the count was 0 (the generic strategy agreed, so parity alone could not
        // have caught it).
        var source = """
            IsTwo(x) = x.string == '2'
            range(1.0, 3).filter(IsTwo).count
            """;

        var generic = EvalFull(source, enableLoopOptimization: false, enableSequencePipelineOptimization: false);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");
        Assert.Equal(new[] { Decimal128.One }, generic.Value.ToHostAtoms());

        var diagnostics = new SequencePipelineDiagnostics();
        var optimized = Evaluator.Run(
            new Expr.AlgorithmExpr(ParseValidRoot(source)),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: diagnostics);
        if (optimized.IsError)
            Assert.Fail($"Expected optimized success but got error: {optimized.Error}");
        Assert.Equal(new[] { Decimal128.One }, optimized.Value.ToHostAtoms());

        var snapshot = diagnostics.GetSnapshot();
        Assert.Equal(1, snapshot.DirectRangeFusionHits);
        Assert.Equal(0, snapshot.DirectRangeFusionFallbacks);
    }

    [Theory]
    [InlineData("range(1.00, 3.000)", "1 2 3")]
    [InlineData("range(-0.0, 2)", "0 1 2")]
    [InlineData("range(2.0, -0.0)", "2 1 0")]
    [InlineData("range(-1.00, -3.0)", "-1 -2 -3")]
    [InlineData("range(1e1, 12)", "10 11 12")]
    [InlineData("range(0.5 + 0.5, 3)", "1 2 3")]
    [InlineData("range(-0.0, -0)", "0")]
    [InlineData("range(1e34 - 1, 1e34)", "9999999999999999999999999999999999 10000000000000000000000000000000000")]
    [InlineData("range(1e34, 1e34 - 1)", "10000000000000000000000000000000000 9999999999999999999999999999999999")]
    [InlineData("range(-1e34, -1e34 + 1)", "-10000000000000000000000000000000000 -9999999999999999999999999999999999")]
    [InlineData("range(-1e34 + 1, -1e34)", "-9999999999999999999999999999999999 -10000000000000000000000000000000000")]
    public async Task PipelineCallbacks_ObserveCanonicalAtoms_BeforeAnyFormatting(string range, string expectedAtoms)
    {
        var expected = expectedAtoms.Split(' ').Select(N).ToArray();
        var seen = new List<Decimal128>();
        var operations = HostOperations.Create(HostOperation.Create("Observe", (args, _) =>
        {
            seen.Add(Assert.IsType<Result.Atom>(args[0]).Value);
            return new Result.Atom(1);
        }, "x"));

        // Cover both direct-range spellings and fusion over a materialized property.
        foreach (var (pipeline, direct) in new[]
        {
            ($"{range}.filter(Keep).count", true),
            ($"count(filter({range}, Keep))", true),
            ($"R = {range}\nR.filter(Keep).count", false),
        })
        {
            var source = $"Keep(x) = Observe(x)\n{pipeline}";
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
            var ast = new Expr.AlgorithmExpr(parsed.Root);

            foreach (var optimize in new[] { false, true })
            {
                seen.Clear();
                var diagnostics = new SequencePipelineDiagnostics();
                var run = Evaluator.RunCountedObserved(ast,
                    enableOptimizations: optimize, sequenceDiagnostics: diagnostics, hostOperations: operations);
                AssertObservation(run.Result);
                var snapshot = diagnostics.GetSnapshot();
                Assert.Equal(optimize ? 1 : 0, snapshot.FilterCountFusionHits);
                Assert.Equal(optimize && direct ? 1 : 0, snapshot.DirectRangeFusionHits);
            }

            seen.Clear();
            var twin = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(ast,
                zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache(),
                hostOperations: operations));
            AssertObservation(twin.Result);

            void AssertObservation(EvalResult<Evaluator.CountedResult> result)
            {
                Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
                Assert.Equal(1, result.Value.EmittedCount);
                Assert.Equal(new[] { (Decimal128)expected.Length }, result.Value.Value.ToHostAtoms());
                Assert.Equal(expected, seen);
                AssertCanonicalIntegers(seen, source);
            }
        }
    }

    // ── The ±1e34 endpoints require exponent 1 ───────────────────────────────

    [Theory]
    [InlineData("range(1e34, 1e34)", "10000000000000000000000000000000000")]
    [InlineData("range(10000000000000000000000000000000000, 1e34)", "10000000000000000000000000000000000")]
    [InlineData("range(-1e34, -1e34)", "-10000000000000000000000000000000000")]
    [InlineData("range(-10000000000000000000000000000000000, -1e34)", "-10000000000000000000000000000000000")]
    [InlineData("range(1e34 - 1, 1e34)", "9999999999999999999999999999999999 10000000000000000000000000000000000")]
    [InlineData("range(1e34, 1e34 - 1)", "10000000000000000000000000000000000 9999999999999999999999999999999999")]
    [InlineData("range(-1e34, -1e34 + 1)", "-10000000000000000000000000000000000 -9999999999999999999999999999999999")]
    [InlineData("range(-1e34 + 1, -1e34)", "-9999999999999999999999999999999999 -10000000000000000000000000000000000")]
    public async Task CeilingEndpoint_HasOneRepresentation_RegardlessOfSpelling(string source, string expectedAtoms)
    {
        var expected = expectedAtoms.Split(' ').Select(N).ToArray();
        var sync = Atoms(source);
        Assert.Equal(expected, sync);
        AssertCanonicalIntegers(sync, source);
        var twin = await TwinAtoms(source);
        Assert.Equal(expected, twin);
        AssertCanonicalIntegers(twin, source + " (async twin)");
    }

    // ── Singleton ranges: representation, value preservation, idempotence ───

    [Theory]
    [InlineData("1.0", "1", 0)]
    [InlineData("1.00", "1", 0)]
    [InlineData("1.000000000000000000000000000000000", "1", 0)]
    [InlineData("100e-2", "1", 0)]
    [InlineData("1e1", "10", 0)]
    [InlineData("1.5e1", "15", 0)]
    [InlineData("0e5", "0", 0)]
    [InlineData("0.0", "0", 0)]
    [InlineData("-0", "0", 0)]
    [InlineData("-0.0", "0", 0)]
    [InlineData("-3.0", "-3", 0)]
    [InlineData("1", "1", 0)]
    [InlineData("-7", "-7", 0)]
    [InlineData("1e33", "1000000000000000000000000000000000", 0)]
    [InlineData("9999999999999999999999999999999999", "9999999999999999999999999999999999", 0)]
    [InlineData("1e34", "10000000000000000000000000000000000", 1)]
    [InlineData("-1e34", "-10000000000000000000000000000000000", 1)]
    public void SingletonRange_PreservesValueAndCanonicalRepresentation_WhenReusedAsBounds(
        string spelling,
        string expectedText,
        int expectedQuantumExponent)
    {
        var written = N(spelling);
        var canonical = Assert.Single(Atoms($"range({spelling}, {spelling})"));

        Assert.Equal(written, canonical); // value-preserving (Decimal128 equality ignores quantum)
        // KatLang's canonical text, not the runtime's default format: `Decimal128.ToString`
        // switches to IEEE `to-scientific-string` notation once the exponent is
        // positive, which is exactly the `1e34` row below.
        Assert.Equal(expectedText, KatLang.Rendering.ValueTextRenderer.FormatNumberInvariant(canonical));
        Assert.Equal(expectedQuantumExponent, QuantumExponent(canonical));
        Assert.False(canonical == Decimal128.Zero && Decimal128.IsNegative(canonical), "negative zero survived");

        // Idempotent: a canonical bound is its own canonical form.
        var rerun = Evaluator.RunFlat(new Expr.Call(
            new Expr.Resolve("range"),
            new OutputBundle([new Expr.Num(canonical), new Expr.Num(canonical)])));
        Assert.False(rerun.IsError);
        var again = Assert.Single(rerun.Value);
        Assert.Equal(canonical, again);
        Assert.True(Decimal128.HaveSameQuantum(canonical, again));
        Assert.Equal(Decimal128.IsNegative(canonical), Decimal128.IsNegative(again));
    }

    [Fact]
    public void CanonicalizeIntegralRangeBound_FailsLoudForInexactOrUnrepresentableResults()
    {
        // This guard detects a value-changing conversion, not every out-of-domain
        // value. Range-domain rejection belongs to ValidateRangeBound.
        Assert.Throws<InvalidOperationException>(() => Evaluator.CanonicalizeIntegralRangeBound(N("1.5")));
        Assert.Throws<InvalidOperationException>(() => Evaluator.CanonicalizeIntegralRangeBound(Decimal128.NaN));
        Assert.Throws<InvalidOperationException>(() => Evaluator.CanonicalizeIntegralRangeBound(N("1e36")));
    }

    // ── Validation still runs first, with unchanged precedence and wording ────

    [Theory]
    [InlineData("range(1.0, 1.5)", "range stop must be an integer")]
    [InlineData("range(-1.5, 1.0)", "range start must be an integer")]
    [InlineData("range(1e-6176, 1.0)", "range start must be an integer")]
    [InlineData("range(1.0, Math.Sqrt(-1))", "range stop must be an integer")]
    [InlineData("range(1.5, 2e34)", "range start must be an integer")]
    [InlineData("range(2e34, 1.0)", "range start must not exceed 1e34 in magnitude")]
    [InlineData("range(1.0, 2e34)", "range stop must not exceed 1e34 in magnitude")]
    [InlineData("range(9e6144 * 10, 1.0)", "range start must be an integer")]
    public void Validation_PrecedesCanonicalization_WithUnchangedDiagnostics(string source, string expectedReason)
        => AssertEvalFailsWithIllegalInEval(source, expectedReason);

    [Fact]
    public void StringBound_StillReportsTypeMismatch()
    {
        var result = EvalFull("range('1', 2.0)");
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        Assert.IsType<EvalError.TypeMismatch>(error);
    }

    [Theory]
    [InlineData("1.00", "1.00")]
    [InlineData("0.5 + 0.5", "1.0")]
    [InlineData("-0.0", "-0.0")]
    [InlineData("[1.00, 2.00]:0.0", "1.00")]
    [InlineData("repeat({s}, 2.0, 1.00)", "1.00")]
    [InlineData("Lo = 1.00\nR = range(Lo, 3)\nR.count * 0 + Lo", "1.00")]
    public async Task UnrelatedValues_KeepTheirQuantumAndZeroSign(string source, string expectedSpelling)
    {
        var expected = N(expectedSpelling);
        foreach (var actual in new[] { Assert.Single(Atoms(source)), Assert.Single(await TwinAtoms(source)) })
        {
            Assert.Equal(expected, actual);
            Assert.True(Decimal128.HaveSameQuantum(expected, actual));
            Assert.Equal(Decimal128.IsNegative(expected), Decimal128.IsNegative(actual));
        }
    }

    [Fact]
    public async Task FilteringAllRangeElements_StillProducesAnEmptyList()
    {
        const string source = "Keep(x) = 0\nrange(-0.0, 2.0).filter(Keep)";
        var result = EvalFull(source);
        Assert.False(result.IsError);
        Assert.Empty(Assert.IsType<Result.ListValue>(result.Value).Items);
        Assert.Empty(await TwinAtoms(source));
    }
}
