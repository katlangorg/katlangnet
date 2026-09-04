using KatLang.Runtime;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// A Math member (and every host operation) is an ordinary
/// <see cref="Algorithm.User"/> wrapper whose body is an
/// <see cref="Expr.NativeCall"/> naming the wrapper's own parameters. Reading
/// one of those declared arguments is therefore exactly the
/// <see cref="Expr.Param"/> value read — counted parameter environment, then
/// value environment, then the algorithm binding.
///
/// <para>The read used to stop after the value environment ("native arguments
/// are always value bindings"), which is false: an argument whose value
/// evaluation fails still binds on the ALGORITHM channel. That produced
/// <c>Unknown name: x</c> — the wrapper's OWN parameter name, an internal
/// spelling the user never wrote — for every such argument, and (before the
/// value environment was shadowed at binding, see
/// <see cref="AlgorithmChannelParameterShadowingTests"/>) let a same-named
/// caller value be handed to the native instead.</para>
/// </summary>
public class NativeArgumentValueDemandTests
{
    private static EvalError InnermostError(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");
        return Innermost(result.Error);
    }

    /// <summary>
    /// Innermost evaluator error for a source the FRONT END now rejects, evaluated from its
    /// elaborated tree directly.
    ///
    /// <para>Sources whose registry-proven strict-value position references a callable a
    /// CLOSED explicit parameter list cannot forward to are diagnosed before evaluation
    /// (<see cref="ClosedListStrictValueDiagnosticTests"/>). That does not retire the
    /// evaluator guarantee — it layers on top of it — and a host may evaluate an AST without
    /// front-end checking at all (<c>Evaluator.Run*</c> takes host-built trees as-is). So
    /// this asserts the rejection, then bypasses checking exactly as such a host would, to
    /// keep the runtime behavior independently pinned: the value demand of the bound
    /// argument, never an ambient caller value and never the wrapper's own parameter
    /// name.</para>
    /// </summary>
    private static EvalError InnermostErrorBypassingFrontEndRejection(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.True(
            parsed.HasErrors,
            "This source is expected to be rejected by the closed-list strict-value diagnostic; "
            + "if it now parses cleanly, use InnermostError instead." + Environment.NewLine + source);

        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");
        return Innermost(result.Error);
    }

    private static EvalError.ArityMismatch AssertZeroArgumentValueDemand(string source)
    {
        var arity = Assert.IsType<EvalError.ArityMismatch>(InnermostErrorBypassingFrontEndRejection(source));
        Assert.Equal(0, arity.Actual);
        return arity;
    }

    // ── The algorithm tier is reached, and never `Unknown name` ──────────────

    /// <summary>
    /// A parameterized property as a Math member argument reports the ordinary
    /// zero-argument value demand arity error, exactly as the grouped spelling
    /// <c>Math.Abs((A))</c> — which forces the value channel — already did. The
    /// enclosing algorithm has an EXPLICIT parameter list, so front-end implicit
    /// lifting cannot absorb <c>A</c>'s inferred <c>q</c> and the reference
    /// reaches the evaluator (the unenclosed spelling is
    /// <see cref="ParameterizedArgument_AtRoot_LiftsTheInferredParameter"/>).
    /// The parameter name here also collides with <c>Math.Abs</c>'s declared
    /// argument name <c>x</c> — the headline leak, which used to evaluate to
    /// the caller's <c>x</c> instead of failing.
    /// </summary>
    [Fact]
    public void ParameterizedArgument_ReportsZeroArgumentValueDemandArityMismatch()
    {
        var arity = AssertZeroArgumentValueDemand(
            """
            A = q + 1
            F(x) = Math.Abs(A)
            F(7)
            """);
        Assert.Equal(1, arity.Expected);
        var provenance = Assert.Single(arity.InferredImplicitParameters!);
        Assert.Equal("q", provenance.Name);
        Assert.NotNull(provenance.Span);
    }

    /// <summary>
    /// Control for the case above, and unchanged by this fix: at root, a Math
    /// member argument is a value-demanding position, so the front end lifts
    /// <c>A</c>'s inferred <c>q</c> into the root's implicit parameters and the
    /// run reports the unresolved implicit parameter instead of ever reaching
    /// the wrapper's argument read.
    /// </summary>
    [Fact]
    public void ParameterizedArgument_AtRoot_LiftsTheInferredParameter()
    {
        Assert.IsType<EvalError.UnresolvedImplicitParams>(InnermostError(
            """
            A = q + 1
            Math.Abs(A)
            """));
    }

    /// <summary>
    /// A caller parameter name that does NOT collide with the wrapper's declared
    /// argument name must produce the same failure — that equality is the
    /// property the leak violated.
    /// </summary>
    [Fact]
    public void ParameterizedArgument_OutcomeIsIndependentOfCallerParameterName()
    {
        var colliding = InnermostErrorBypassingFrontEndRejection(
            """
            A = q + 1
            F(x) = Math.Abs(A)
            F(7)
            """);
        var distinct = InnermostErrorBypassingFrontEndRejection(
            """
            A = q + 1
            F(zz) = Math.Abs(A)
            F(7)
            """);

        var collidingArity = Assert.IsType<EvalError.ArityMismatch>(colliding);
        var distinctArity = Assert.IsType<EvalError.ArityMismatch>(distinct);
        Assert.Equal(distinctArity.Expected, collidingArity.Expected);
        Assert.Equal(distinctArity.Actual, collidingArity.Actual);
    }

    /// <summary>
    /// A neutral argument slot reaches the same binding without any front-end
    /// value lifting, so the fix must cover it too.
    /// </summary>
    [Fact]
    public void ParameterizedArgument_ThroughNeutralArgumentSlot_StillFails()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Id(v) = v
            A = q + 1
            F(x) = Id(Math.Abs(A))
            F(7)
            """,
            expected: 1,
            actual: 0);
    }

    /// <summary>
    /// A binary Math member's declared argument names (<c>value</c>,
    /// <c>digits</c>) are reached the same way.
    /// </summary>
    [Fact]
    public void ParameterizedArgument_BinaryMathMember_StillFails()
    {
        var arity = AssertZeroArgumentValueDemand(
            """
            A = q + 1
            F(x) = Math.Round(A, 2)
            F(7)
            """);
        Assert.Equal(1, arity.Expected);
    }

    /// <summary>
    /// A zero-parameter property whose own body fails surfaces ITS error, exactly
    /// as an ordinary user callee's parameter read does — not <c>Unknown name</c>.
    /// </summary>
    [Fact]
    public void ZeroParameterArgumentWithFailingBody_SurfacesThatBodysError()
    {
        Assert.IsType<EvalError.DivByZero>(InnermostError(
            """
            Z = 1 / 0
            Math.Abs(Z)
            """));
    }

    /// <summary>
    /// A clause family has no value with zero arguments, so the ordinary
    /// conditional value-access error surfaces.
    /// </summary>
    [Fact]
    public void ConditionalFamilyArgument_ReportsNoMatchingBranch()
    {
        Assert.IsType<EvalError.NoMatchingBranch>(InnermostError(
            """
            C(0) = 1
            C(n) = 2
            Math.Abs(C)
            """));
    }

    /// <summary>
    /// A builtin argument reports the builtin's own arity failure rather than the
    /// wrapper parameter name.
    /// </summary>
    [Fact]
    public void BuiltinArgument_ReportsTheBuiltinsArityFailure()
    {
        Assert.IsType<EvalError.ArityMismatch>(InnermostError("Math.Abs(count)"));
    }

    /// <summary>
    /// No native-argument failure may name the wrapper's declared parameter as an
    /// UNKNOWN name — that spelling never appears in the user's program. Sources the
    /// closed-list strict-value diagnostic now rejects are covered too, evaluated past that
    /// rejection: the runtime guarantee has to hold for a host that never ran the front end.
    /// </summary>
    [Theory]
    [InlineData("A = q + 1\nMath.Abs(A)")]
    [InlineData("A = q + 1\nF(x) = Math.Abs(A)\nF(7)")]
    [InlineData("A = q + 1\nF(zz) = Math.Round(A, 2)\nF(7)")]
    [InlineData("Z = 1 / 0\nMath.Abs(Z)")]
    [InlineData("C(0) = 1\nC(n) = 2\nMath.Abs(C)")]
    [InlineData("Math.Abs(count)")]
    public void NativeArgumentFailure_NeverReportsTheWrapperParameterAsAnUnknownName(string source)
    {
        // These rows deliberately MIX front-end-accepted and front-end-rejected sources: the
        // property under test is "however this fails, it must not fail by naming the
        // wrapper's own parameter", which must hold on both sides of the front-end boundary.
        // So the rejection is not asserted here — the elaborated tree is evaluated either way.
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var innermost = Innermost(result.Error);
        Assert.False(
            innermost is EvalError.UnknownName,
            $"Native argument failure leaked the wrapper's own parameter name: {KatLangError.FromEvalError(innermost).Message}");
    }

    // ── Ordinary native argument reads are unchanged ─────────────────────────

    [Fact]
    public void ValueArgument_EvaluatesNormally()
        => AssertEval("Math.Abs(0 - 3)", 3);

    [Fact]
    public void ZeroParameterPropertyArgument_EvaluatesNormally()
        => AssertEval("V = 0 - 5\nMath.Abs(V)", 5);

    [Fact]
    public void ParameterBoundArgument_EvaluatesNormally()
        => AssertEval("F(x) = Math.Abs(x)\nF(0 - 9)", 9);

    /// <summary>
    /// The counted tier still wins for a flat-callback invocation, so a native
    /// used directly as a callback reads its callback-bound argument (the
    /// established <c>map(abs)</c> behavior).
    /// </summary>
    [Fact]
    public void NativeAsFlatCallback_ReadsItsCallbackBoundArgument()
        => AssertEvalSequenceModes("[0 - 1, 0 - 2, 0 - 3].map(abs).sum", 6);

    [Fact]
    public void QualifiedNativeAsFlatCallback_ReadsItsCallbackBoundArgument()
        => AssertEvalSequenceModes("[0 - 1, 0 - 2, 0 - 3].map(Math.Abs).sum", 6);

    /// <summary>
    /// A native used as a callback while an ambient value shares the wrapper's
    /// declared argument name still reads the callback-bound argument — the
    /// counted-first rule this suite's predecessor established, re-pinned here
    /// because the read is now the full three-tier parameter read.
    /// </summary>
    [Fact]
    public void NativeAsFlatCallback_IgnoresAnAmbientSameNamedValue()
        => AssertEvalSequenceModes("F(x) = [0 - 1, 0 - 2, 0 - 3].map(abs).sum\nF(100)", 6);
}
