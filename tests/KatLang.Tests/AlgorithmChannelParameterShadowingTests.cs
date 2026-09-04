using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// A user call binds each parameter on the value channel, the algorithm channel,
/// or both, and the callee then inherits the CALLER's value environment so a
/// nested property can still read an ancestor-owned parameter. A parameter bound
/// ONLY on the algorithm channel contributes no value binding, so without
/// <c>Evaluator.ShadowValEnv</c> (Lean <c>ValEnv.shadow</c>) a same-named binding
/// inherited from the caller answered every value-position read of that
/// parameter.
///
/// <para>That was observable two ways, both fixed here: the callee silently
/// computed with an unrelated caller value instead of failing, and WHICH caller
/// parameter names happened to collide with a callee's parameter names became
/// observable — including the internal parameter names of the synthesized Math
/// wrappers (<c>x</c>, <c>value</c>, <c>digits</c>, ...).</para>
///
/// <para>The native-wrapper side of the same defect is
/// <see cref="NativeArgumentValueDemandTests"/>: a wrapper body's declared
/// argument read omitted the algorithm tier entirely, so once the value
/// environment was shadowed it reported <c>Unknown name</c> for the wrapper's own
/// parameter.</para>
/// </summary>
public class AlgorithmChannelParameterShadowingTests
{
    // ── The caller's same-named value is never visible in the callee ─────────

    /// <summary>
    /// Flat fixed binding. <c>A</c> is parameterized, so <c>G(A)</c> binds
    /// <c>x</c> on the algorithm channel only; reading <c>x</c> in value position
    /// must reach that binding (the ordinary zero-argument value demand of a
    /// one-parameter callable), never the caller's own <c>x = 7</c>.
    /// </summary>
    [Fact]
    public void FlatFixedCall_AlgorithmOnlyParameter_DoesNotReadCallersSameNamedValue()
    {
        AssertEvalFailsWithArityMismatch(
            """
            A = q + 1
            G(x) = x + 1
            F(x) = G(A)
            F(7)
            """,
            expected: 1,
            actual: 0);
    }

    /// <summary>
    /// The colliding caller parameter name is the ONLY difference from the case
    /// above, and it must not change the outcome — that equality is the property
    /// the leak violated.
    /// </summary>
    [Fact]
    public void FlatFixedCall_AlgorithmOnlyParameter_OutcomeIsIndependentOfCallerParameterName()
    {
        var colliding = GetEvalError(
            """
            A = q + 1
            G(x) = x + 1
            F(x) = G(A)
            F(7)
            """);
        var distinct = GetEvalError(
            """
            A = q + 1
            G(x) = x + 1
            F(zz) = G(A)
            F(7)
            """);

        Assert.NotNull(colliding);
        Assert.NotNull(distinct);
        var collidingArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(colliding));
        var distinctArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(distinct));
        Assert.Equal(distinctArity.Expected, collidingArity.Expected);
        Assert.Equal(distinctArity.Actual, collidingArity.Actual);
    }

    /// <summary>
    /// Patterned binding (a sequence-value parameter pattern makes the callee
    /// patterned) takes the same rule for its fixed capture.
    /// </summary>
    [Fact]
    public void PatternedCall_AlgorithmOnlyParameter_DoesNotReadCallersSameNamedValue()
    {
        AssertEvalFailsWithArityMismatch(
            """
            A = q + 1
            P(x, (a, b)) = x + a
            F(x) = P(A, (1, 2))
            F(7)
            """,
            expected: 1,
            actual: 0);
    }

    /// <summary>
    /// Item-supply binding (a top-level collecting parameter) takes the same rule
    /// for its fixed prefix capture.
    /// </summary>
    [Fact]
    public void CollectingCall_AlgorithmOnlyParameter_DoesNotReadCallersSameNamedValue()
    {
        AssertEvalFailsWithArityMismatch(
            """
            A = q + 1
            C(x, *rest) = x + 1
            F(x) = C(A, 5)
            F(7)
            """,
            expected: 1,
            actual: 0);
    }

    /// <summary>
    /// A builtin passed as an argument binds the same way, so the caller's value
    /// cannot answer for it either.
    /// </summary>
    [Fact]
    public void FlatFixedCall_BuiltinArgument_DoesNotReadCallersSameNamedValue()
    {
        AssertEvalFails(
            """
            G(x) = x + 1
            F(x) = G(sin)
            F(7)
            """);
    }

    /// <summary>
    /// A failed eager value view is not permission to consult the caller's same-named value.
    /// Demanding the callee parameter reaches the bound zero-parameter algorithm and surfaces
    /// its own failure.
    /// </summary>
    [Fact]
    public void FlatFixedCall_FailedValueView_SurfacesDivisionByZero()
    {
        var error = GetEvalError(
            """
            Broken = 1 / 0
            G(x) = x
            F(x) = G(Broken)
            F(7)
            """);

        Assert.NotNull(error);
        Assert.IsType<EvalError.DivByZero>(Innermost(error));
    }

    [Fact]
    public void FlatFixedCall_FailedConditionalValueView_SurfacesNoMatchingBranch()
    {
        var error = GetEvalError(
            """
            Choice(0) = 1
            Choice(n) = 2
            G(x) = x
            F(x) = G(Choice)
            F(7)
            """);

        Assert.NotNull(error);
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error));
    }

    [Fact]
    public void FlatFixedCall_FailedEmptyAlgorithmValueView_SurfacesMissingOutput()
    {
        var error = GetEvalError(
            """
            Empty = {
            }
            G(x) = x
            F(x) = G(Empty)
            F(7)
            """);

        Assert.NotNull(error);
        Assert.IsType<EvalError.MissingOutput>(Innermost(error));
    }

    // ── Shadowing removes ONLY the callee's own parameter names ──────────────

    /// <summary>
    /// The inherited value environment is what lets a nested property read an
    /// ancestor-owned parameter; shadowing must not break that.
    /// </summary>
    [Fact]
    public void NestedProperty_StillReadsAncestorOwnedParameter()
    {
        AssertEval(
            """
            Outer(v) = Inner
              Inner = v + 1
            Outer(7)
            """,
            8);
    }

    /// <summary>
    /// A parameter bound on BOTH channels keeps its value view: a zero-parameter
    /// property argument supplies a value and an algorithm, and the value tier
    /// still answers.
    /// </summary>
    [Fact]
    public void FlatFixedCall_DualChannelArgument_KeepsItsValueView()
    {
        AssertEval(
            """
            Z = 41
            G(x) = x + 1
            F(x) = G(Z)
            F(7)
            """,
            42);
    }

    /// <summary>
    /// An ordinary value argument is unaffected: the callee's parameter shadows
    /// the caller's same-named binding exactly as its own value binding always
    /// did.
    /// </summary>
    [Fact]
    public void FlatFixedCall_ValueArgument_ShadowsCallersSameNamedValue()
    {
        AssertEval(
            """
            G(x) = x + 1
            F(x) = G(100)
            F(7)
            """,
            101);
    }

    /// <summary>
    /// A higher-order callable argument is still invocable by name inside the
    /// callee — shadowing removes the value tier's stale answer, not the
    /// algorithm binding.
    /// </summary>
    [Fact]
    public void FlatFixedCall_AlgorithmOnlyParameter_RemainsCallableByName()
    {
        AssertEval(
            """
            A = q + 1
            G(x) = x(10)
            F(x) = G(A)
            F(7)
            """,
            11);
    }
}
