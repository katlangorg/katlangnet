using System.Numerics;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Alias evaluation semantics: every alias observes the SAME canonical
/// implementation as its <c>Math.X</c> spelling — constants exactly, function
/// members bit-for-bit on representative inputs, structured errors by kind and
/// message, and the random members' validation and interval contracts.
/// </summary>
public class MathAliasEvaluationTests
{
    private static EvalResult<IReadOnlyList<Decimal128>> EvalFlat(string source)
        => Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));

    private static Decimal128 EvalSingle(string source)
    {
        var result = EvalFlat(source);
        if (result.IsError)
            Assert.Fail($"Expected success for `{source}` but got: {result.Error}");
        return Assert.Single(result.Value);
    }

    private static void AssertAliasAgreesWithCanonical(string aliasSource, string canonicalSource)
    {
        var canonical = EvalFlat(canonicalSource);
        if (canonical.IsError)
            Assert.Fail($"Canonical `{canonicalSource}` unexpectedly failed: {canonical.Error}");

        var alias = EvalFlat(aliasSource);
        if (alias.IsError)
            Assert.Fail($"Alias `{aliasSource}` unexpectedly failed: {alias.Error}");

        // Decimal128.Equals semantics (NaN is one value), matching the
        // language's own structural equality.
        Assert.Equal(canonical.Value, alias.Value);
    }

    // Deterministic function members: one representative call per member,
    // alias spelling vs canonical spelling, exact result equality (they share
    // one implementation, so results are identical bit patterns).
    [Theory]
    [InlineData("abs(-2.5)", "Math.Abs(-2.5)")]
    [InlineData("ceil(1.2)", "Math.Ceil(1.2)")]
    [InlineData("floor(1.8)", "Math.Floor(1.8)")]
    [InlineData("round(2.34567, 2)", "Math.Round(2.34567, 2)")]
    [InlineData("sign(-3)", "Math.Sign(-3)")]
    [InlineData("sqrt(2)", "Math.Sqrt(2)")]
    [InlineData("exp(0.5)", "Math.Exp(0.5)")]
    [InlineData("exp(-2)", "Math.Exp(-2)")]
    [InlineData("ln(2)", "Math.Ln(2)")]
    [InlineData("lg(1000)", "Math.Lg(1000)")]
    [InlineData("sin(1)", "Math.Sin(1)")]
    [InlineData("asin(0.5)", "Math.Asin(0.5)")]
    [InlineData("cos(0.123)", "Math.Cos(0.123)")]
    [InlineData("acos(0.5)", "Math.Acos(0.5)")]
    [InlineData("tan(1)", "Math.Tan(1)")]
    [InlineData("atan(1)", "Math.Atan(1)")]
    [InlineData("atan2(1, 2)", "Math.Atan2(1, 2)")]
    [InlineData("pow(2, 10)", "Math.Pow(2, 10)")]
    [InlineData("log(8, 2)", "Math.Log(8, 2)")]
    public void DeterministicFunctionAlias_AgreesWithCanonical(string aliasSource, string canonicalSource)
        => AssertAliasAgreesWithCanonical(aliasSource, canonicalSource);

    [Theory]
    [InlineData("abs(-2.5)", "2.5")]
    [InlineData("ceil(1.2)", "2")]
    [InlineData("floor(1.8)", "1")]
    [InlineData("round(2.345, 2)", "2.35")]
    [InlineData("sign(-3)", "-1")]
    [InlineData("sqrt(4)", "2")]
    [InlineData("exp(0)", "1")]
    [InlineData("ln(1)", "0")]
    [InlineData("lg(1000)", "3")]
    [InlineData("sin(0)", "0")]
    [InlineData("asin(0)", "0")]
    [InlineData("cos(0)", "1")]
    [InlineData("acos(1)", "0")]
    [InlineData("tan(0)", "0")]
    [InlineData("atan(0)", "0")]
    [InlineData("atan2(0, 1)", "0")]
    [InlineData("pow(2, 10)", "1024")]
    [InlineData("log(8, 2)", "3")]
    public void DeterministicAliases_HaveIndependentKnownAnswers(string source, string expected)
        => Assert.Equal(
            Decimal128.Parse(expected, System.Globalization.CultureInfo.InvariantCulture),
            EvalSingle(source));

    [Fact]
    public void PiAlias_IsExactlyTheCanonicalConstant()
    {
        Assert.Equal(EvalSingle("Math.Pi"), EvalSingle("pi"));
        Assert.Equal(Decimal128.Zero, EvalSingle("pi - Math.Pi"));
        Assert.Equal(EvalSingle("Math.Sin(Math.Pi / 2)"), EvalSingle("sin(pi / 2)"));
    }

    [Fact]
    public void PiAlias_PropertyStyleAndExplicitCallAgree()
    {
        // The `A` vs `A()` distinction only controls the zero-argument cache;
        // both spellings observe the same constant.
        Assert.Equal(EvalSingle("pi"), EvalSingle("pi()"));
    }

    [Fact]
    public void ExpAliasAndCanonical_MatchDecimal128ExpDirectly()
    {
        // Math.Exp is wired directly to Decimal128.Exp — never through double,
        // System.Math, Pow, or a stored constant — so the language result IS
        // the oracle's value for representative positive and negative inputs.
        // exp(0) = 1 exactly.
        foreach (var (source, input) in new (string Source, string Input)[]
        {
            ("0", "0"),
            ("-0", "-0"),
            ("1", "1"),
            ("0.5", "0.5"),
            ("-1", "-1"),
            ("-2.25", "-2.25"),
            ("10", "10"),
        })
        {
            var oracle = Decimal128.Exp(
                Decimal128.Parse(input, System.Globalization.CultureInfo.InvariantCulture));
            Assert.Equal(oracle, EvalSingle($"Math.Exp({source})"));
            Assert.Equal(oracle, EvalSingle($"exp({source})"));
        }

        Assert.Equal(Decimal128.One, EvalSingle("Math.Exp(0)"));
        Assert.Equal(Decimal128.One, EvalSingle("exp(0)"));
    }

    [Fact]
    public void RemovedEulerConstant_IsNoLongerAvailable()
    {
        // The replacement is intentional and alias-free: `Math.E` has no
        // structural member and no lexical fallback (`E` is a free name), and
        // bare `e` is an ordinary identifier again — both surface as ordinary
        // unresolved implicit parameters, never as a retained constant.
        var canonicalError = SourceProvenance.ParseValid("Math.E")
            .ExpectEvaluationError<EvalError.UnresolvedImplicitParams>();
        Assert.Equal(["E"], canonicalError.ParamNames);
        Assert.Null(Assert.Single(canonicalError.InferredImplicitParameters!).SuggestedName);

        var aliasError = SourceProvenance.ParseValid("e")
            .ExpectEvaluationError<EvalError.UnresolvedImplicitParams>();
        Assert.Equal(["e"], aliasError.ParamNames);
        Assert.Null(Assert.Single(aliasError.InferredImplicitParameters!).SuggestedName);

        var expressionError = SourceProvenance.ParseValid("e + 1")
            .ExpectEvaluationError<EvalError.UnresolvedImplicitParams>();
        Assert.Equal(["e"], expressionError.ParamNames);
    }

    [Fact]
    public void PiAlias_PreservesPropertyCacheVersusExplicitCallSemantics()
    {
        var propertyCache = new RunScopedZeroArgPropertyResultCache();
        var propertyResult = Evaluator.Run(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid("pi\npi").Root),
            propertyCache);
        Assert.False(propertyResult.IsError);
        var propertySnapshot = propertyCache.GetSnapshot();
        Assert.Equal(2, propertySnapshot.TotalRequests);
        Assert.Equal(1, propertySnapshot.Hits);
        Assert.Equal(1, propertySnapshot.Misses);
        Assert.Equal(1, propertySnapshot.Stores);

        var explicitCallCache = new RunScopedZeroArgPropertyResultCache();
        var explicitCallResult = Evaluator.Run(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid("pi()\npi()").Root),
            explicitCallCache);
        Assert.False(explicitCallResult.IsError);
        Assert.Equal(0, explicitCallCache.GetSnapshot().TotalRequests);
    }

    [Fact]
    public void GoalPrograms_EvaluateThroughCanonicalImplementations()
    {
        AssertAliasAgreesWithCanonical("cos(0.123)", "Math.Cos(0.123)");
        AssertAliasAgreesWithCanonical("sin(pi / 2)", "Math.Sin(Math.Pi / 2)");
        AssertAliasAgreesWithCanonical("round(sqrt(2), 10)", "Math.Round(Math.Sqrt(2), 10)");
        Assert.Equal(Decimal128.One, EvalSingle("sin(pi / 2)"));
    }

    [Theory]
    [InlineData("sin(1, 2)", "sin(x)", 1, 2)]
    [InlineData("exp(1, 2)", "exp(x)", 1, 2)]
    [InlineData("round(2)", "round(x, y)", 2, 1)]
    [InlineData("atan2(1)", "atan2(y, x)", 2, 1)]
    [InlineData("log(8)", "log(x, y)", 2, 1)]
    [InlineData("random(0)", "random(start, end)", 2, 1)]
    [InlineData("randomInt(0)", "randomInt(start, end)", 2, 1)]
    [InlineData("pi(1)", "pi", 0, 1)]
    public void AliasArity_IsTheCanonicalMemberArity(
        string source, string expectedSignature, int expectedArity, int actualArity)
    {
        var error = SourceProvenance.ParseValid(source).ExpectEvaluationError<EvalError.ArityMismatch>();
        Assert.Equal(expectedArity, error.Expected);
        Assert.Equal(actualArity, error.Actual);
        Assert.Equal(expectedSignature, error.Signature?.DisplayText);
    }

    [Fact]
    public void DomainBehavior_AgreesWithCanonical()
    {
        // IEEE domain results are ordinary values, identical across spellings.
        Assert.True(Decimal128.IsNaN(EvalSingle("sqrt(-1)")));
        Assert.True(Decimal128.IsNaN(EvalSingle("Math.Sqrt(-1)")));
        Assert.True(Decimal128.IsNegativeInfinity(EvalSingle("ln(0)")));
        Assert.True(Decimal128.IsNegativeInfinity(EvalSingle("Math.Ln(0)")));
        Assert.True(Decimal128.IsPositiveInfinity(EvalSingle("exp(20000)")));
        Assert.True(Decimal128.IsPositiveInfinity(EvalSingle("Math.Exp(20000)")));
        AssertAliasAgreesWithCanonical("asin(2)", "Math.Asin(2)");
    }

    [Fact]
    public void Exp_PropagatesIeeeNonFiniteInputs()
    {
        // Overflow produces +Infinity; applying Exp to +Infinity keeps it.
        Assert.True(Decimal128.IsPositiveInfinity(EvalSingle("Math.Exp(Math.Exp(20000))")));
        Assert.True(Decimal128.IsPositiveInfinity(EvalSingle("exp(exp(20000))")));

        // Ln(0) supplies -Infinity and Sqrt(-1) supplies NaN without requiring
        // host-only literals for the special values.
        Assert.Equal(Decimal128.Zero, EvalSingle("Math.Exp(Math.Ln(0))"));
        Assert.Equal(Decimal128.Zero, EvalSingle("exp(ln(0))"));
        Assert.True(Decimal128.IsNaN(EvalSingle("Math.Exp(Math.Sqrt(-1))")));
        Assert.True(Decimal128.IsNaN(EvalSingle("exp(sqrt(-1))")));
    }

    [Fact]
    public void PowAlias_StaysAlignedWithCanonicalPowAndOperator()
    {
        var viaOperator = EvalSingle("2 ^ 0.5");
        Assert.Equal(viaOperator, EvalSingle("Math.Pow(2, 0.5)"));
        Assert.Equal(viaOperator, EvalSingle("pow(2, 0.5)"));

        // The shared implementation includes the zero-base error rule.
        var aliasError = SourceProvenance.ParseValid("pow(0, -2)").ExpectEvaluationError<EvalError.IllegalInEval>();
        var canonicalError = SourceProvenance.ParseValid("Math.Pow(0, -2)").ExpectEvaluationError<EvalError.IllegalInEval>();
        Assert.Equal(canonicalError.Reason, aliasError.Reason);
    }

    [Theory]
    [InlineData("random(5, 1)", "Math.Random(5, 1)")]
    [InlineData("random(1, 1)", "Math.Random(1, 1)")]
    [InlineData("randomInt(0.5, 2)", "Math.RandomInt(0.5, 2)")]
    [InlineData("randomInt(3, 2)", "Math.RandomInt(3, 2)")]
    public void RandomAliases_PreserveCanonicalValidation(string aliasSource, string canonicalSource)
    {
        var aliasError = SourceProvenance.ParseValid(aliasSource).ExpectEvaluationError<EvalError.IllegalInEval>();
        var canonicalError = SourceProvenance.ParseValid(canonicalSource).ExpectEvaluationError<EvalError.IllegalInEval>();
        Assert.Equal(canonicalError.Reason, aliasError.Reason);
    }

    [Fact]
    public void RandomAliases_DrawWithinTheCanonicalHalfOpenInterval()
    {
        // Interval contracts only — no equality assertions between independent
        // random draws.
        var random = EvalSingle("random(0, 1)");
        Assert.True(random >= 0 && random < 1);

        var randomInt = EvalSingle("randomInt(0, 3)");
        Assert.True(Decimal128.IsInteger(randomInt));
        Assert.True(randomInt >= 0 && randomInt < 3);
    }
}
