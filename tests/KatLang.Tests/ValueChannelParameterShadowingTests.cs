using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// The mirror image of <see cref="AlgorithmChannelParameterShadowingTests"/> (K4-03).
/// A callee's algorithm environment is its own algorithm bindings prepended to the
/// CALLER's, which is what lets a nested call still invoke an ancestor-owned callable
/// parameter. A parameter bound ONLY on the value channel contributes no algorithm
/// binding, so without <c>Evaluator.ShadowAlgEnv</c> (Lean <c>AlgEnv.shadow</c>, applied
/// at every binding site through <c>ShadowInheritedParameterEnvironments</c> / Lean
/// <c>EvalCtx.bindParameters</c>) a same-named callable inherited from the caller
/// answered every call-position read of that parameter: <c>Inner(f) = f(2)</c> called as
/// <c>Inner(5)</c> inside <c>Apply(f)</c> invoked the caller's <c>f</c> and returned
/// <c>3</c>, where the standalone <c>Inner(5)</c> fails as not-callable.
///
/// <para>Every test asserts the OBSERVABLE rule — a bound parameter owns its name on
/// every channel — through the public evaluation surface, once per independently
/// implemented binding path: flat fixed, patterned, and collecting user calls,
/// clause-family binders, the sequence-builtin callbacks, generic and planned loop
/// steps, the async twin family, and the nested-scope, dot-fallback, and forwarding
/// consumers of the algorithm channel.</para>
/// </summary>
public class ValueChannelParameterShadowingTests
{
    /// <summary>
    /// <c>Apply(f)</c> receives the callable <c>Inc</c> under the name <c>f</c>; the body
    /// then binds a callee parameter named <c>f</c> to a VALUE and reads it in call
    /// position.
    /// </summary>
    private static string InsideApply(string body)
        => "Inc(x) = x + 1\n\nApply(f) = {\n" + body + "}\n\nApply(Inc)\n";

    private const string FlatBody = "    Inner(f) = f(2)\n    Inner(5)\n";
    private const string BinderBody = "    Inner(0) = 0\n    Inner(f) = f(2)\n    Inner(5)\n";
    private const string MapBody = "    Inner(f) = f(2)\n    [5].map(Inner)\n";
    private const string RepeatBody = "    Step(f) = f(2)\n    repeat(Step, 1, 5)\n";
    private const string WhileBody = "    Step(f) = f(2), 0\n    while(Step, 5)\n";
    private const string NestedCallBody = "    Inner(f) = {\n        Local(y) = f(y)\n        Local(2)\n    }\n    Inner(5)\n";
    private const string DotFallbackBody = "    Inner(f) = 2.f\n    Inner(5)\n";

    public static TheoryData<string, string> ValueBoundCallPositionRows()
    {
        var rows = new TheoryData<string, string>();
        rows.Add("flat fixed call", InsideApply(FlatBody));
        rows.Add("patterned call", InsideApply("    Inner(f, (a, b)) = f(2)\n    Inner(5, (1, 2))\n"));
        rows.Add("collecting call", InsideApply("    Inner(f, *rest) = f(2)\n    Inner(5, 1)\n"));
        rows.Add("clause-family binder", InsideApply(BinderBody));
        rows.Add("map callback", InsideApply(MapBody));
        rows.Add("filter callback", InsideApply("    Inner(f) = f(2) == 3\n    [5].filter(Inner)\n"));
        rows.Add("reduce callback", InsideApply("    Step(acc, f) = f(2)\n    reduce([5], Step, 0)\n"));
        rows.Add("repeat step", InsideApply(RepeatBody));
        rows.Add("while step", InsideApply(WhileBody));
        rows.Add("nested call frame", InsideApply(NestedCallBody));
        rows.Add("nested zero-parameter property", InsideApply("    Inner(f) = {\n        Local = f(2)\n        Local\n    }\n    Inner(5)\n"));
        rows.Add("lexical dot-call fallback", InsideApply(DotFallbackBody));
        return rows;
    }

    // ── The caller's same-named callable is never visible in the callee ──────

    /// <summary>
    /// Every binding path: a parameter bound to the value <c>5</c> is not callable,
    /// and the enclosing <c>f = Inc</c> can never answer in its place.
    /// </summary>
    [Theory]
    [MemberData(nameof(ValueBoundCallPositionRows))]
    public void ValueBoundParameter_IsNotCallable_EvenWhenTheCallerHoldsACallableUnderThatName(string path, string source)
    {
        var error = GetEvalError(source);
        Assert.True(error is not null, $"{path}: the program must fail instead of invoking the caller's callable");
        var notCallable = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(error!));
        Assert.Equal("param(f)", notCallable.Description);
    }

    public static TheoryData<string, string, string> StandaloneControlRows()
    {
        var rows = new TheoryData<string, string, string>();
        rows.Add("flat fixed call", InsideApply(FlatBody), "Inner(f) = f(2)\nInner(5)\n");
        rows.Add("clause-family binder", InsideApply(BinderBody), "Inner(0) = 0\nInner(f) = f(2)\nInner(5)\n");
        rows.Add("map callback", InsideApply(MapBody), "Inner(f) = f(2)\n[5].map(Inner)\n");
        rows.Add("repeat step", InsideApply(RepeatBody), "Step(f) = f(2)\nrepeat(Step, 1, 5)\n");
        rows.Add("nested call frame", InsideApply(NestedCallBody), "Inner(f) = {\n    Local(y) = f(y)\n    Local(2)\n}\nInner(5)\n");
        rows.Add("lexical dot-call fallback", InsideApply(DotFallbackBody), "Inner(f) = 2.f\nInner(5)\n");
        return rows;
    }

    /// <summary>
    /// The enclosing algorithm's parameter name is the ONLY difference between the two
    /// programs, and it changes nothing — that equality is the property the leak
    /// violated (the enclosed program returned <c>3</c> while the standalone failed).
    /// </summary>
    [Theory]
    [MemberData(nameof(StandaloneControlRows))]
    public void ValueBoundParameter_OutcomeIsIndependentOfTheEnclosingCallable(string path, string enclosed, string standalone)
    {
        var enclosedError = GetEvalError(enclosed);
        var standaloneError = GetEvalError(standalone);
        Assert.True(enclosedError is not null && standaloneError is not null, $"{path}: both programs must fail");

        var enclosedInnermost = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(enclosedError!));
        var standaloneInnermost = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(standaloneError!));
        Assert.Equal(standaloneInnermost.Description, enclosedInnermost.Description);
    }

    /// <summary>
    /// Generic and planned loop strategies bind the step's state parameters through
    /// different code (<c>PrepareGenericLoopStep</c> and the planned loop's step
    /// context); both must shadow the algorithm tier.
    /// </summary>
    [Theory]
    [InlineData(RepeatBody)]
    [InlineData(WhileBody)]
    public void LoopStep_ValueBoundParameter_IsNotCallableUnderEitherLoopStrategy(string body)
    {
        var source = InsideApply(body);
        foreach (var enableLoopOptimization in new[] { false, true })
        {
            var result = EvalFull(source, enableLoopOptimization);
            Assert.True(result.IsError, $"loop optimization {enableLoopOptimization}: the program must fail");
            var notCallable = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(result.Error));
            Assert.Equal("param(f)", notCallable.Description);
        }
    }

    /// <summary>
    /// The async twin family re-implements the flat-fixed binder, the conditional call
    /// core, and the loop-step iteration; every row must reach the synchronous outcome
    /// through the twin path.
    /// </summary>
    [Theory]
    [MemberData(nameof(ValueBoundCallPositionRows))]
    public async Task ValueBoundParameter_AsyncTwinMatchesTheSynchronousOutcome(string path, string source)
    {
        var ast = AsyncEvaluationHarness.Ast(source);
        var sync = Evaluator.RunCounted(ast);

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var async = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(ast, cache));

        Assert.True("err notAnAlgorithm" == AsyncEvaluationHarness.NeutralOf(sync), $"{path}: sync outcome was {AsyncEvaluationHarness.NeutralOf(sync)}");
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        Assert.Equal(0, cache.SyncAccesses);
    }

    /// <summary>
    /// Forwarding the value-bound parameter as an argument offers only its value view:
    /// the receiving parameter binds on the value channel alone and is not callable
    /// either, so the caller's callable cannot re-enter through a second call.
    /// </summary>
    [Fact]
    public void ForwardedValueBoundParameter_BindsTheReceivingParameterOnTheValueChannelOnly()
    {
        var error = GetEvalError(InsideApply("    Pass(g) = g(1)\n    Inner(f) = Pass(f)\n    Inner(5)\n"));

        Assert.NotNull(error);
        var notCallable = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(error));
        Assert.Equal("param(g)", notCallable.Description);
    }

    // ── The mirror direction keeps working ───────────────────────────────────

    /// <summary>
    /// An algorithm-only inner binding still hides the caller's same-named VALUE: the
    /// value read is the zero-argument value demand of <c>Inc</c>, never <c>6</c>.
    /// </summary>
    [Fact]
    public void AlgorithmBoundParameter_StillHidesTheCallersSameNamedValue()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Inc(x) = x + 1

            Outer(f) = {
                Inner(f) = f + 1
                Inner(Inc)
            }

            Outer(5)
            """,
            expected: 1,
            actual: 0);
    }

    // ── Shadowing removes ONLY the callee's own parameter names ──────────────

    /// <summary>
    /// The inherited algorithm environment is what lets a nested call invoke an
    /// ancestor-owned callable; a callee that declares no <c>f</c> keeps seeing it.
    /// </summary>
    [Fact]
    public void NestedCall_StillInvokesTheAncestorOwnedCallable()
    {
        AssertEval(InsideApply("    Inner(x) = f(x)\n    Inner(5)\n"), 6);
    }

    [Fact]
    public void Callback_StillInvokesTheAncestorOwnedCallable()
    {
        AssertEval(InsideApply("    Inner(x) = f(x)\n    [5].map(Inner)\n"), 6);
    }

    /// <summary>
    /// A parameter bound on BOTH channels keeps its own callable view: the callee's own
    /// algorithm binding is prepended and wins over the shadowed ancestor binding.
    /// </summary>
    [Fact]
    public void DualChannelArgument_KeepsItsOwnCallableView()
    {
        AssertEval(InsideApply("    Z = 41\n    Inner(f) = f()\n    Inner(Z)\n"), 41);
    }

    /// <summary>
    /// The value channel is untouched: reading the value-bound parameter as a value
    /// still yields the argument bound at this call.
    /// </summary>
    [Fact]
    public void ValueBoundParameter_ReadInValuePosition_IsUnchanged()
    {
        AssertEval(InsideApply("    Inner(f) = f + 1\n    Inner(5)\n"), 6);
    }
}
