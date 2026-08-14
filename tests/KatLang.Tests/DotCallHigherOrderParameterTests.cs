namespace KatLang.Tests;

/// <summary>
/// Focused regression matrix for the higher-order lexical dot-call parameter
/// law: after structural member lookup fails, <c>receiver.F(args...)</c>
/// resolves <c>F</c> with the SAME callable resolution as the plain callee
/// <c>F(receiver, args...)</c> — including algorithm-valued parameters. The
/// front-end decides the member's lexical-fallback identity ONCE
/// (<c>ParameterDetector</c> rewrites <c>Expr.DotCall.LexicalFallback</c>
/// from <c>Resolve</c> to <c>Param</c> by the same rule as a bare callee
/// name: a parameter of the current algorithm always binds as a parameter; a
/// captured ancestor parameter binds unless a visible non-builtin lexical
/// declaration shadows it), and the evaluator CONSUMES that stored decision
/// through canonical <c>ResolveAlg</c>. Structural lookup precedence, the
/// receiver segment rule, sequence-builtin dot dispatch for lexical member
/// names, and plain/counted parity all stay intact. Lean: `Expr.dotMember`
/// (CoreTests `higherOrderDot*` guards); Grace composition coverage lives in
/// <c>GraceDotCompositionTests</c>.
/// </summary>
public class DotCallHigherOrderParameterTests
{
    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result Seq(params Result[] items) => new Result.SequenceValue(items);

    private static Result List(params Result[] items) => new Result.ListValue(items);

    /// <summary>
    /// STRICT-SOURCE: requires a clean front end, then evaluates through both
    /// the plain and the counted evaluator entry points and asserts they agree
    /// on the same value before returning it.
    /// </summary>
    private static Result Evaluate(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        var expr = new Expr.AlgorithmExpr(provenance.Root);

        var plain = Evaluator.Run(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");

        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");

        Assert.True(
            Result.ValueComparer.Equals(plain.Value, counted.Value.Value),
            $"Plain/counted divergence: {plain.Value} vs {counted.Value.Value}");
        return plain.Value;
    }

    private static void AssertResult(string source, Result expected)
    {
        var actual = Evaluate(source);
        Assert.True(
            Result.ValueComparer.Equals(expected, actual),
            $"Expected {expected} but got {actual}{Environment.NewLine}Source:{Environment.NewLine}{source}");
    }

    /// <summary>
    /// STRICT-SOURCE error harness: requires a clean front end, asserts BOTH
    /// evaluator entry points fail, and returns the plain innermost error
    /// after checking the counted innermost error has the same shape.
    /// </summary>
    private static EvalError AssertBothEvaluatorsFail(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        var expr = new Expr.AlgorithmExpr(provenance.Root);

        var plain = Evaluator.Run(expr);
        Assert.True(plain.IsError, $"Expected plain evaluation error but got: {(plain.IsError ? null : plain.Value)}");

        var counted = Evaluator.RunCounted(expr);
        Assert.True(counted.IsError, $"Expected counted evaluation error but got: {(counted.IsError ? null : counted.Value.Value)}");

        var plainInner = Innermost(plain.Error);
        var countedInner = Innermost(counted.Error);
        Assert.Equal(plainInner.GetType(), countedInner.GetType());
        return plainInner;
    }

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext withContext ? Innermost(withContext.Inner) : error;

    // ── A. The core law: t(a) and a.t agree on algorithm-valued parameters ──

    [Fact]
    public void PlainCall_HigherOrderParameter_Control()
        => AssertResult(
            """
            K(a, t) = t(a)
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void DotMember_ResolvesLocalHigherOrderParameter()
        => AssertResult(
            """
            K(a, t) = a.t
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void DotMember_ResolvesCapturedParameterInNestedScope()
        // The brace body owns a scope with no parameters of its own; `t` is a
        // captured ancestor parameter witnessed by its environment binding and
        // unshadowed by any lexical declaration.
        => AssertResult(
            """
            K(a, t) = {a.t}
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void DotMember_ParameterChannelUnderLiftedReceiverWrapper()
        // The inner `a.t` evaluates inside the algorithm-position lift of the
        // outer dot target; the parameter channel still applies there.
        => AssertResult(
            """
            K(a, t) = a.t.string
            K(7, {a+1})
            """,
            Str("8"));

    [Fact]
    public void DotMember_ExtraArgumentsFollowInjectedReceiver()
        => AssertResult(
            """
            K(a, t) = a.t(5)
            K(7, {a+b})
            """,
            Atom(12));

    [Fact]
    public void LexicalFallback_RootScopeMatchesDirectCall()
        => AssertResult(
            """
            t(a) = a + 1
            Dot(a) = a.t
            Direct(a) = t(a)
            Dot(7)
            Direct(7)
            """,
            Seq(Atom(8), Atom(8)));

    [Fact]
    public void LexicalFallback_ImmediateParentScopeMatchesDirectCall()
        => AssertResult(
            """
            Outer = {
                t(a) = a + 2
                Dot(a) = a.t
                Direct(a) = t(a)
                Dot(7)
                Direct(7)
            }
            Outer
            """,
            Seq(Atom(9), Atom(9)));

    [Fact]
    public void LexicalFallback_GrandparentScopeAndNearerShadowMatchDirectCall()
        => AssertResult(
            """
            t(a) = a + 100
            Outer = {
                t(a) = a + 10
                Inner = {
                    Dot(a) = a.t
                    Direct(a) = t(a)
                    Dot(7)
                    Direct(7)
                }
                Inner
            }
            Outer
            """,
            Seq(Atom(17), Atom(17)));

    [Fact]
    public void LexicalFallback_OpenedCallableMatchesDirectCall()
        => AssertResult(
            """
            Lib = {
                public t(a) = a + 3
            }
            Outer = {
                open Lib
                Dot(a) = a.t
                Direct(a) = t(a)
                Dot(7)
                Direct(7)
            }
            Outer
            """,
            Seq(Atom(10), Atom(10)));

    [Fact]
    public void LexicalFallback_AmbiguousOpenMatchesDirectCallError()
    {
        const string declarations =
            """
            A = {
                public Pick(a) = 1
            }
            B = {
                public Pick(a) = 2
            }
            Outer = {
                open A, B
            """;

        var dotError = Assert.IsType<EvalError.AmbiguousOpen>(AssertBothEvaluatorsFail(
            declarations +
            """

                7.Pick
            }
            Outer
            """));
        var directError = Assert.IsType<EvalError.AmbiguousOpen>(AssertBothEvaluatorsFail(
            declarations +
            """

                Pick(7)
            }
            Outer
            """));

        Assert.Equal(directError.Name, dotError.Name);
        Assert.Equal(directError.Providers, dotError.Providers);
    }

    [Fact]
    public void PlainCall_ExtraArguments_Control()
        => AssertResult(
            """
            K(a, t) = t(a, 5)
            K(7, {a+b})
            """,
            Atom(12));

    // ── B. Error parity: value-bound parameter fails like the plain callee ──

    [Fact]
    public void ValueBoundParameter_DotMemberFailsWithCanonicalParamError()
    {
        var error = AssertBothEvaluatorsFail(
            """
            K(a, t) = a.t
            K(7, 5)
            """);
        var notAnAlgorithm = Assert.IsType<EvalError.NotAnAlgorithm>(error);
        Assert.Equal("param(t)", notAnAlgorithm.Description);
    }

    [Fact]
    public void ValueBoundParameter_PlainCallFailsWithSameParamError()
    {
        var error = AssertBothEvaluatorsFail(
            """
            K(a, t) = t(a)
            K(7, 5)
            """);
        var notAnAlgorithm = Assert.IsType<EvalError.NotAnAlgorithm>(error);
        Assert.Equal("param(t)", notAnAlgorithm.Description);
    }

    [Fact]
    public void CaptureArgument_SuppressesCallableIdentityInBothSpellings()
    {
        // `(Inc)` is a capture: the algorithm channel sees only a
        // zero-parameter value thunk, so both spellings fail evaluating the
        // thunk's bare `Inc` output row identically.
        var dotError = AssertBothEvaluatorsFail(
            """
            Inc(x) = x + 1
            K(a, t) = a.t
            K(7, (Inc))
            """);
        var plainError = AssertBothEvaluatorsFail(
            """
            Inc(x) = x + 1
            K(a, t) = t(a)
            K(7, (Inc))
            """);
        Assert.IsType<EvalError.ArityMismatch>(dotError);
        Assert.IsType<EvalError.ArityMismatch>(plainError);
    }

    // ── C. Precedence: structural lookup, local parameters, shadowing ───────

    [Fact]
    public void StructuralLookup_StillWinsOverParameterChannel()
        // Structural member lookup on the resolved receiver has priority; the
        // same-name parameter `V` is never consulted.
        => AssertResult(
            """
            Obj = {public V = 42}
            K(a, V) = a.V
            K(Obj, {a+1})
            """,
            Atom(42));

    [Fact]
    public void StructuralLookup_PlainDotAccessUnchanged()
        => AssertResult(
            """
            Obj = {public V = 42}
            Obj.V
            """,
            Atom(42));

    [Fact]
    public void LexicalDotCall_NonParameterMemberUnchanged()
        => AssertResult(
            """
            Add(x, y) = x + y
            3.Add(4)
            """,
            Atom(7));

    [Fact]
    public void LocalParameter_WinsOverSameNameVisibleProperty()
        // A parameter of the CURRENT algorithm shadows the lexical property,
        // exactly as the bare callee name `t` does in `t(a)`.
        => AssertResult(
            """
            t = 5
            K(a, t) = a.t
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void LocalParameter_PlainCallControl()
        => AssertResult(
            """
            t = 5
            K(a, t) = t(a)
            K(7, {a+1})
            """,
            Atom(8));

    [Fact]
    public void VisibleProperty_ShadowsNonLocalParameterBinding()
    {
        // Inside G, `t` is NOT a parameter; the visible property `t = 5` wins
        // over the dynamically visible binding of the enclosing K invocation,
        // so the fallback stays lexical: calling the zero-parameter property
        // with the injected receiver is an arity mismatch — exactly like the
        // plain form `t(x)` written in G's body.
        var dotError = AssertBothEvaluatorsFail(
            """
            t = 5
            G(x) = x.t
            K(a, t) = G(a)
            K(7, {a+1})
            """);
        var plainError = AssertBothEvaluatorsFail(
            """
            t = 5
            G(x) = t(x)
            K(a, t) = G(a)
            K(7, {a+1})
            """);
        var dotMismatch = Assert.IsType<EvalError.ArityMismatch>(dotError);
        var plainMismatch = Assert.IsType<EvalError.ArityMismatch>(plainError);
        Assert.Equal(0, dotMismatch.Expected);
        Assert.Equal(1, dotMismatch.Actual);
        Assert.Equal(0, plainMismatch.Expected);
        Assert.Equal(1, plainMismatch.Actual);
    }

    // ── D. Builtin-named parameters and sequence-builtin dispatch ───────────

    [Fact]
    public void BuiltinBoundParameter_TakesParameterChannelInBothSpellings()
    {
        // `t` is bound to builtin `count`; both spellings call it with the
        // receiver as ONE ordinary collection argument (plain-call boundary,
        // not the sequence-builtin dot-receiver view).
        AssertResult(
            """
            K(a, t) = a.t
            K((1, 2, 3), count)
            """,
            Atom(3));
        AssertResult(
            """
            K(a, t) = t(a)
            K((1, 2, 3), count)
            """,
            Atom(3));
    }

    [Fact]
    public void SequenceBuiltinDotReceiver_UnchangedForNonParameterNames()
        => AssertResult("(1, 2, 3).count", Atom(3));

    [Fact]
    public void CollectingCallee_ParameterChannelKeepsReceiverSegmentRule()
    {
        // A named parameter receiver supplies its value-boundary count (one
        // item), so the collecting callee collects one slot in both spellings.
        AssertResult(
            """
            Collect(*items) = items
            K(a, t) = a.t
            K((1, 2), Collect)
            """,
            List(Seq(Atom(1), Atom(2))));
        AssertResult(
            """
            Collect(*items) = items
            K(a, t) = t(a)
            K((1, 2), Collect)
            """,
            List(Seq(Atom(1), Atom(2))));
    }

    // ── E. Optimizer coherence: fusion must observe the parameter channel ───

    [Fact]
    public void FilterCountFusion_SuppressedWhenCountIsParameterBound()
        // A fused pipeline would produce 2; the parameter channel must win
        // and call the bound algorithm with the filtered list instead.
        => AssertResult(
            """
            C(a) = 99
            K(xs, count) = xs.filter({a > 1}).count
            K((1, 2, 3), C)
            """,
            Atom(99));

    [Fact]
    public void FilterCountFusion_UnchangedWithoutParameterBinding()
        => AssertResult(
            """
            K(xs) = xs.filter({a > 1}).count
            K((1, 2, 3))
            """,
            Atom(2));

    [Fact]
    public void FilterCountFusion_SuppressedWhenFilterIsParameterBound()
    {
        // Non-fused resolution calls the one-parameter bound algorithm with
        // receiver + predicate (two arguments); fusion would produce 2.
        var error = AssertBothEvaluatorsFail(
            """
            C(a) = 99
            K(xs, filter) = xs.filter({a > 1}).count
            K((1, 2, 3), C)
            """);
        var mismatch = Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.Equal(1, mismatch.Expected);
        Assert.Equal(2, mismatch.Actual);
    }

    // ── F. Counted evaluation contexts ──────────────────────────────────────

    [Fact]
    public void ReduceInitialAccumulator_AcceptsDotParameterResult()
        => AssertResult(
            """
            K(a, t) = a.t
            reduce((1, 2, 3), {a + b}, K(7, {a+1}))
            """,
            Atom(14));
}
