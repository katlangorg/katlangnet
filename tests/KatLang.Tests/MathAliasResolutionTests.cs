using System.Numerics;
using System.Text;

namespace KatLang.Tests;

/// <summary>
/// Alias name-resolution and elaboration semantics: aliases are ORDINARY
/// synthetic prelude properties under ownership-first lookup — shadowed by
/// local properties, explicit and captured parameters, never inferred as
/// implicit parameters, eligible for lexical dot fallback — and their calls
/// share the canonical Math members' strict-value implicit lifting, bare
/// callable lifting, and sibling dependency ordering.
/// </summary>
public class MathAliasResolutionTests
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

        Assert.Equal(canonical.Value, alias.Value);
    }

    private static IReadOnlyList<string> ElaboratedPropertyParams(string source, string propertyName)
    {
        var root = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid(source).Root);
        return Assert.Single(root.Properties, property => property.Name == propertyName).Value.Params;
    }

    [Fact]
    public void BareAliasReference_LiftsLikeCanonicalMathMember()
    {
        // `K = cos` infers K(radians) exactly like `K = Math.Cos` — the lifted
        // signature carries the member's declared parameter names.
        Assert.Equal(["radians"], ElaboratedPropertyParams("K = cos\nK(0)", "K"));
        Assert.Equal(["radians"], ElaboratedPropertyParams("K = Math.Cos\nK(0)", "K"));
        AssertAliasAgreesWithCanonical("K = cos\nK(0)", "K = Math.Cos\nK(0)");

        Assert.Equal(["x"], ElaboratedPropertyParams("K = exp\nK(1)", "K"));
        Assert.Equal(["x"], ElaboratedPropertyParams("K = Math.Exp\nK(1)", "K"));
        AssertAliasAgreesWithCanonical("K = exp\nK(1)", "K = Math.Exp\nK(1)");

        Assert.Equal(["y", "x"], ElaboratedPropertyParams("K = atan2\nK(1, 2)", "K"));
        AssertAliasAgreesWithCanonical("K = atan2\nK(1, 2)", "K = Math.Atan2\nK(1, 2)");

        // A bare alias at ROOT output lifts too, exactly like bare `Math.Abs`:
        // both leave the run with the same unresolved implicit parameter.
        var aliasError = SourceProvenance.ParseValid("abs").ExpectEvaluationError<EvalError.UnresolvedImplicitParams>();
        var canonicalError = SourceProvenance.ParseValid("Math.Abs").ExpectEvaluationError<EvalError.UnresolvedImplicitParams>();
        Assert.Equal(canonicalError.ParamNames, aliasError.ParamNames);
    }

    [Fact]
    public void AliasCallArguments_AreStrictValuePositions_LikeCanonical()
    {
        // `sin(F)` and `Math.Sin(F)` perform IDENTICAL strict-value implicit
        // lifting: F's implicit parameter x lifts into G's signature.
        const string aliasSource = "F = x + 1\nG = sin(F)\nG(0.5)";
        const string canonicalSource = "F = x + 1\nG = Math.Sin(F)\nG(0.5)";

        Assert.Equal(["x"], ElaboratedPropertyParams(aliasSource, "G"));
        Assert.Equal(["x"], ElaboratedPropertyParams(canonicalSource, "G"));
        AssertAliasAgreesWithCanonical(aliasSource, canonicalSource);
        Assert.Equal(EvalSingle("Math.Sin(1.5)"), EvalSingle(aliasSource));
    }

    [Fact]
    public void LocallyShadowedMath_DoesNotAcquireCanonicalStrictValueFacts()
    {
        // The receiver spelling alone is insufficient: this `Math` is the
        // user's ordinary structural container, and its Sin consumes the bare
        // higher-order F reference. Treating the argument as builtin-strict
        // would instead lift F(x) and leave Value spuriously parameterized.
        const string source = """
            Value = Math.Sin(F)
            F = x + 1
            Math = { Sin(g) = g(10) }
            Value
            """;

        Assert.Empty(ElaboratedPropertyParams(source, "Value"));
        Assert.Equal(11, EvalSingle(source));
    }

    [Fact]
    public void SiblingDependencyOrdering_WorksThroughAliasCalls()
    {
        // B is declared AFTER A, so A's strict-value argument processing must
        // wait for B's augmented signature — the same ordering the canonical
        // dot spelling gets.
        const string aliasSource = "A = sin(B)\nB = x + 1\nA(0)";
        const string canonicalSource = "A = Math.Sin(B)\nB = x + 1\nA(0)";

        Assert.Equal(["x"], ElaboratedPropertyParams(aliasSource, "A"));
        AssertAliasAgreesWithCanonical(aliasSource, canonicalSource);
        Assert.Equal(EvalSingle("Math.Sin(1)"), EvalSingle(aliasSource));
    }

    [Fact]
    public void LocalProperty_ShadowsAlias()
    {
        Assert.Equal(30, EvalSingle("sin(x) = x * 10\nsin(3)"));
        Assert.Equal(30, EvalSingle("exp(x) = x * 10\nexp(3)"));
        Assert.Equal(4, EvalSingle("pi = 3\npi + 1"));

        // Ancestor property shadowing: the user's `sin` stays an ordinary
        // NEUTRAL callable inside nested scopes — its argument is not
        // Math-lifted merely because the text is `sin`.
        Assert.Equal(30, EvalSingle("sin(x) = x * 10\nInner = { sin(3) }\nInner"));
    }

    [Fact]
    public void UserDefinedAliasName_KeepsNeutralHigherOrderArguments()
    {
        // A user-defined `sin` receiving a parameterized bare reference keeps
        // it a higher-order algorithm reference (neutral argument), which
        // Math-strict lifting would destroy.
        const string source = """
            F = x + 1
            sin(g) = g(10)
            sin(F)
            """;
        Assert.Equal(11, EvalSingle(source));
    }

    [Fact]
    public void ExplicitParameter_ShadowsAlias()
    {
        Assert.Equal(42, EvalSingle("F(sin) = sin\nF(42)"));
        Assert.Equal(7, EvalSingle("F(pi) = pi + 2\nF(5)"));
        Assert.Equal(8, EvalSingle("F(round) = round + 3\nF(5)"));
        Assert.Equal(6, EvalSingle("F(exp) = exp + 1\nF(5)"));
        Assert.Equal(6, EvalSingle("F(e) = e + 1\nF(5)"));
    }

    [Fact]
    public void CapturedAncestorParameter_ShadowsAlias()
    {
        // The nested brace scope captures the OUTER parameter; the prelude
        // alias (the scope chain's root) never outranks a nearer parameter.
        Assert.Equal(9, EvalSingle("F(sin) = {sin * 3}\nF(3)"));
        Assert.Equal(8, EvalSingle("F(round) = {round + 3}\nF(5)"));
        Assert.Equal(6, EvalSingle("F(pi) = {pi + 1}\nF(5)"));
    }

    [Theory]
    [InlineData("F(sum) = {sum + 1}\nF(5)", 6)]
    [InlineData("F(Math) = {Math + 1}\nF(5)", 6)]
    [InlineData("F(load) = {load + 1}\nF(5)", 6)]
    public void ExplicitAndCapturedParameters_ShadowEveryPreludeValueKind(
        string source,
        int expected)
        => Assert.Equal(expected, EvalSingle(source));

    [Fact]
    public void ExplicitAndCapturedParameter_ShadowsConfiguredHostOperation()
    {
        var calls = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create(
                "HostValue",
                (_, _) =>
                {
                    Interlocked.Increment(ref calls);
                    return new Result.Atom(100);
                })),
        };

        var result = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("F(HostValue) = {HostValue + 1}\nF(5)", options));
        Assert.Equal("6", result.ToDisplayString());
        Assert.Equal(0, calls);
    }

    [Fact]
    public void DeconstructionBindings_ShadowAliases()
        => Assert.Equal(5, EvalSingle("pi, sqrt = (2, 3)\npi + sqrt"));

    [Fact]
    public void AliasNames_AreNotInferredAsImplicitParameters()
    {
        foreach (var source in new[] { "cos(1)", "pi", "exp(1)", "sin(pi / 2)" })
        {
            var provenance = SourceProvenance.ParseValid(source);
            Assert.Empty(provenance.Root.Params);
        }

        // The documented compatibility effect: `F = pi + 1` means Math.Pi + 1
        // instead of inferring `pi` as a parameter; `F(pi) = pi + 1` still
        // requests the parameter explicitly.
        Assert.Empty(ElaboratedPropertyParams("F = pi + 1\nF", "F"));
        Assert.Equal(EvalSingle("Math.Pi + 1"), EvalSingle("F = pi + 1\nF"));
        Assert.Equal(["pi"], ElaboratedPropertyParams("F(pi) = pi + 1\nF(1)", "F"));

        // The REMOVED `e` binding is ordinary vocabulary again: a free `e` is
        // an implicit parameter exactly like any other unresolved name.
        Assert.Equal(["e"], SourceProvenance.ParseValid("e + 1").Root.Params);
        Assert.Equal(["E"], SourceProvenance.ParseValid("Math.E").Root.Params);
    }

    [Fact]
    public void AliasTypoSuggestion_IsUniqueAndResolutionConsistent()
    {
        var error = SourceProvenance.ParseValid("sni")
            .ExpectEvaluationError<EvalError.UnresolvedImplicitParams>();
        var note = Assert.Single(error.InferredImplicitParameters!);

        Assert.Equal("sni", note.Name);
        Assert.Equal("sin", note.SuggestedName);
    }

    [Fact]
    public void LexicalDotFallback_ReachesAliases()
    {
        // `x.cos` uses the ordinary lexical dot fallback as `cos(x)` when
        // structural lookup misses — on stored values and on parameters alike.
        Assert.Equal(EvalSingle("Math.Cos(0.5)"), EvalSingle("v = 0.5\nv.cos"));
        Assert.Equal(EvalSingle("Math.Cos(0.5)"), EvalSingle("F = x.cos\nF(0.5)"));
        Assert.Equal(EvalSingle("Math.Atan2(1, 2)"), EvalSingle("F = y.atan2(2)\nF(1)"));
        Assert.Equal(EvalSingle("Math.Exp(0.5)"), EvalSingle("F = x.exp\nF(0.5)"));
    }

    [Fact]
    public void MathLowercaseMember_StaysInvalid()
    {
        // `Math` has no lowercase members. `Math.cos(1)` falls through
        // structural lookup to the ordinary lexical fallback — the alias — and
        // fails on the receiver-injected arity, never silently computing.
        var arityError = SourceProvenance.ParseValid("Math.cos(1)").ExpectEvaluationError<EvalError.ArityMismatch>();
        Assert.Equal(1, arityError.Expected);
        Assert.Equal(2, arityError.Actual);

        // Property-style `Math.cos` equally stays an error, and it is an error
        // about what the program actually wrote: the fallback is `cos(Math)`,
        // whose argument binds on the algorithm channel only, so the wrapper's
        // declared-argument read demands the `Math` module's value and reports
        // that it has no output. (It used to report `Unknown name: radians` —
        // the wrapper's own internal parameter — because that read stopped
        // before the algorithm tier.)
        SourceProvenance.ParseValid("Math.cos").ExpectEvaluationError<EvalError.MissingOutput>();
    }

    [Fact]
    public void OpenMath_StillExposesCanonicalPascalCaseNames()
    {
        Assert.Equal(1, EvalSingle("open Math\nCos(0)"));
        Assert.Equal(EvalSingle("Math.Pi"), EvalSingle("open Math\nPi"));
        Assert.Equal(EvalSingle("Math.Exp(1)"), EvalSingle("open Math\nExp(1)"));

        // The aliases keep working alongside an explicit `open Math`.
        var both = EvalFlat("open Math\ncos(0), Cos(0)");
        Assert.False(both.IsError);
        Assert.Equal([Decimal128.One, Decimal128.One], both.Value);
    }

    [Fact]
    public void OpenedProvider_DoesNotOverrideDirectPreludeAlias()
    {
        // Direct-beats-open: the prelude's alias is a DIRECT property of the
        // scope chain's root, so an open-provided `sin` is never selected...
        const string shadowAttempt = """
            open Lib
            Lib = { public sin(x) = 42 }
            sin(0)
            """;
        Assert.Equal(0, EvalSingle(shadowAttempt));

        // ...while the provider's member stays reachable structurally.
        Assert.Equal(42, EvalSingle("Lib = { public sin(x) = 42 }\nLib.sin(0)"));
    }

    [Fact]
    public void AliasInsideConditionalBranchBody_ResolvesLikeAnyPreludeName()
    {
        // Branch bodies forbid implicit parameters; a resolvable prelude alias
        // is an ordinary visible name there.
        Assert.Equal(1, EvalSingle("F(0) = cos(0)\nF(n) = n\nF(0)"));
    }

    [Fact]
    public void NestedScopeAndConditionalBody_KeepAliasResolutionAndShadowing()
    {
        Assert.Equal(
            EvalSingle("Math.Sin(1)"),
            EvalSingle("Outer = { F = x + 1\nG = sin(F)\nG(0) }\nOuter"));

        Assert.Equal(
            30,
            EvalSingle("sin(x) = x * 10\nChoice(0) = sin(3)\nChoice(n) = n\nChoice(0)"));
    }

    [Fact]
    public void RecursivePropertyNamedLikeAlias_RemainsAnOrdinaryUserCallable()
        => Assert.Equal(3, EvalSingle("sin(0) = 0\nsin(n) = sin(n - 1) + 1\nsin(3)"));

    [Fact]
    public void CanonicalAndAliasBareReferences_DeduplicateByCanonicalCallableIdentity()
    {
        const string source = "K = Math.Atan2, atan2\nK(1, 2)";
        Assert.Equal(["y", "x"], ElaboratedPropertyParams(source, "K"));

        var result = EvalFlat(source);
        Assert.False(result.IsError);
        Assert.Equal(2, result.Value.Count);
        Assert.Equal(result.Value[0], result.Value[1]);
    }

    [Fact]
    public void GraceOnAliasDotFallback_UsesOrdinaryOccurrenceOrdering()
    {
        const string source = "K = y~.atan2(x)\nK(2, 1)";
        Assert.Equal(["x", "y"], ElaboratedPropertyParams(source, "K"));
        Assert.Equal(EvalSingle("Math.Atan2(1, 2)"), EvalSingle(source));
    }

    [Fact]
    public void BareAliasInNeutralArgumentPosition_StaysAlgorithmReference()
    {
        // Ordinary call arguments are NEUTRAL: a bare alias survives as a
        // higher-order algorithm reference, exactly like any bare callable.
        Assert.Equal(1, EvalSingle("Apply(f, v) = f(v)\nApply(cos, 0)"));
    }

    [Fact]
    public void FlatCallbackPosition_AliasAgreesWithCanonicalBareReference()
    {
        // Native-call wrapper bodies read their argument names through the
        // counted-first dual-view lookup (the same order as Expr.Param), so a
        // Math member works DIRECTLY as a flat callback reference — identically
        // through the alias spelling and the canonical BARE spelling (via
        // `open Math`), and identically to the explicit user-property wrapper.
        AssertAliasAgreesWithCanonical("map([1, -2], abs)", "open Math\nmap([1, -2], Abs)");
        Assert.Equal(new Decimal128[] { 1m, 2m }, EvalFlat("map([1, -2], abs)").Value);
        Assert.Equal(EvalFlat("map([1, -2], Wrap)\nWrap(v) = Math.Abs(v)").Value, EvalFlat("map([1, -2], abs)").Value);
    }

    [Fact]
    public void FlatCallbackPosition_QualifiedCanonicalMemberAgreesWithAlias()
    {
        var alias = EvalFlat("map([1, -2], abs)");
        var qualified = EvalFlat("map([1, -2], Math.Abs)");

        Assert.False(alias.IsError);
        Assert.False(qualified.IsError);
        Assert.Equal(alias.Value, qualified.Value);
    }

    [Fact]
    public void FlatCallbackPosition_QualifiedNativeGate_DoesNotReinterpretUserDefinedMath()
    {
        // The qualified native exception requires an actual runtime NativeCall
        // wrapper. A source-defined Math property keeps the same general dotted
        // zero-parameter algorithm identity as any other user module.
        var result = EvalFlat("Math = { public Abs(x) = x * 10 }\nmap([1, -2], Math.Abs)");

        var error = result.Error;
        while (error is EvalError.WithContext(_, var inner))
            error = inner;
        var arity = Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.Equal(0, arity.Expected);
        Assert.Equal(1, arity.Actual);
    }

    [Fact]
    public void WideAliasConsumerElaboration_AllocationGrowsLinearly()
    {
        // A previous draft materialized the growing ancestor-name set inside
        // every leaf dependency-graph build. Doubling a wide flat scope then
        // grew allocation by about 3.71x. The binding-aware predicate must stay
        // a shared O(1) lookup, so parse + front-end allocation remains linear.
        _ = Parser.Parse(WideAliasConsumerSource(256));
        var baseAllocation = MeasureParseAllocation(1_000);
        var doubleAllocation = MeasureParseAllocation(2_000);
        var ratio = (double)doubleAllocation / baseAllocation;

        Assert.True(
            ratio < 3.0,
            $"wide alias-consumer parse allocation grew {ratio:F2}x over N " +
            $"(expected ~2x linear; the materialized-ancestor-set path was ~3.71x). " +
            $"N={baseAllocation} bytes, 2N={doubleAllocation} bytes.");
    }

    private static long MeasureParseAllocation(int count)
    {
        var source = WideAliasConsumerSource(count);
        _ = Parser.Parse(source);
        var before = GC.GetAllocatedBytesForCurrentThread();
        _ = Parser.Parse(source);
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    private static string WideAliasConsumerSource(int count)
    {
        var source = new StringBuilder(count * 18);
        for (var i = 0; i < count; i++)
            source.Append("P").Append(i).Append(" = sin(0)\n");
        source.Append("P0");
        return source.ToString();
    }
}
