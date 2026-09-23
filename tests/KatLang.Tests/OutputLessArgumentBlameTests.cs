using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// F5 — A WRITTEN VALUE ARGUMENT THAT PRODUCES NO OUTPUT IS DIAGNOSED AT THAT ARGUMENT.
///
/// <para>Four situations that look alike in the final argument count and are NOT the
/// same thing:</para>
/// <list type="number">
/// <item>no argument was written — an arity failure before anything is evaluated
/// (<c>F()</c>, <c>count()</c>);</item>
/// <item>an ordinary value argument was written and its expression produced no output
/// — the argument's own failure (<c>F({ })</c>, <c>count({ })</c>,
/// <c>Coll({ })</c>);</item>
/// <item>an argument produced a legitimate EMPTY VALUE — one ordinary value
/// (<c>F([])</c>, <c>F(())</c>, <c>count([])</c>);</item>
/// <item>an explicit SPREAD legitimately supplied zero items — a legal supply
/// (<c>Coll(Empty*)</c>).</item>
/// </list>
///
/// <para>Before this fix, case 2 was reported through whichever frame happened to
/// enclose it: <c>count({ })</c> read "Cannot call 'count' because it has no defined
/// output", blaming a builtin that is perfectly well formed and describing the program
/// as though the source had been the argumentless <c>count()</c>; <c>Coll({ })</c>
/// blamed <c>Coll</c>; <c>(1, 2, 3).take({ })</c> blamed the receiver expression. The
/// blame now belongs to the written argument, through the ONE
/// <c>Evaluator.BlameWrittenArgumentForMissingOutput</c> — the unnamed half of the rule
/// a NAMED argument already got from <see cref="PropertyEvaluationContext"/> /
/// <see cref="ParameterEvaluationContext"/>.</para>
///
/// <para>C#-ONLY: the structured error kind and payload are unchanged (the innermost
/// error is still <see cref="EvalError.MissingOutput"/>, and
/// <see cref="KatLangError.Code"/> is still
/// <see cref="KatLangErrorCode.MissingOutput"/>), values and emitted counts are
/// unchanged, and Lean's <c>errCategory</c> discards <c>withContext</c> outright, so no
/// Lean guard can observe a context frame. The one public-surface addition is
/// <see cref="ArgumentEvaluationContext"/> itself, which MUST be public because
/// <see cref="ErrorContext"/> is consumer-exhaustive — <see cref="EvalError"/> is the one
/// closed root that deliberately keeps a non-public variant
/// (<c>ClosedHierarchyContractTests.HierarchyWithAnInternalVariant_IsNeverExhaustiveForAConsumer</c>).</para>
/// </summary>
public class OutputLessArgumentBlameTests
{
    private const string Collector = "Coll(*xs) = xs";
    private const string Fixed1 = "F(x) = x";
    private const string Fixed2 = "F(x, y) = x + y";
    private const string Fixed3 = "F(x, y, z) = x + y + z";

    // ── 1. The four situations are four different outcomes ──────────────────

    /// <summary>
    /// An OMITTED argument never reaches argument evaluation at all: the binder's arity
    /// check rejects it first, at the whole call.
    /// </summary>
    [Theory]
    [InlineData(Fixed1 + "\nF()")]
    [InlineData("count()")]
    [InlineData("sum()")]
    public void OmittedArgument_IsAnArityFailure_NotAnArgumentFailure(string source)
    {
        var error = AssertEvalError(source);
        Assert.IsType<EvalError.ArityMismatch>(Innermost(error));

        var message = KatLangError.FromEvalError(error).Message;
        Assert.Contains("was called with 0 arguments", message, StringComparison.Ordinal);
        Assert.DoesNotContain("no defined output", message, StringComparison.Ordinal);
    }

    /// <summary>
    /// A WRITTEN argument whose expression produced no output is blamed at that
    /// argument, in every receiver shape that demands its value.
    /// </summary>
    [Theory]
    [InlineData(Collector + "\nColl({ })", "Coll", "{...}")]
    [InlineData("P((x, *rest)) = [x, rest]\nP({ })", "P", "{...}")]
    [InlineData("P(x, *rest, x) = x\nP(1, { }, 2)", "P", "{...}")]
    [InlineData("count({ })", "count", "{...}")]
    [InlineData("sum({ })", "sum", "{...}")]
    [InlineData("atoms({ })", "atoms", "{...}")]
    [InlineData("range({ }, 3)", "range", "{...}")]
    [InlineData("if({ }, 1, 2)", "if", "{...}")]
    [InlineData("take((1, 2, 3), { })", "take", "{...}")]
    [InlineData("sum(({ }, 1))", "sum", "({...}, 1)")]
    [InlineData(Fixed1 + "\nF(1 + { })", "F", "(1 + {...})")]
    public void WrittenOutputLessArgument_IsBlamedAtTheArgument_NeverAtTheCallee(
        string source,
        string callee,
        string expectedArgumentDescription)
    {
        var error = AssertEvalError(source);
        Assert.IsType<EvalError.MissingOutput>(Innermost(error));
        Assert.Equal(KatLangErrorCode.MissingOutput, KatLangError.FromEvalError(error).Code);

        var argument = AssertArgumentBlame(error);
        Assert.Equal(expectedArgumentDescription, argument.ArgumentDescription);

        var message = KatLangError.FromEvalError(error).Message;
        Assert.Contains($"The argument `{expectedArgumentDescription}` has no defined output", message, StringComparison.Ordinal);
        Assert.DoesNotContain($"Cannot call '{callee}'", message, StringComparison.Ordinal);
        // Never the argumentless spelling of the same call.
        Assert.DoesNotContain("was called with 0 arguments", message, StringComparison.Ordinal);
    }

    /// <summary>
    /// A legitimate EMPTY VALUE is a value. Zero output values and one empty value are
    /// different things, and an empty list, an empty sequence, and an empty string all
    /// stay ordinary arguments.
    /// </summary>
    [Theory]
    [InlineData(Fixed1 + "\nF([])", "[]")]
    [InlineData(Fixed1 + "\nF(())", "()")]
    [InlineData("count([])", "0")]
    [InlineData("count(())", "0")]
    [InlineData(Collector + "\nColl([])", "[[]]")]
    [InlineData(Collector + "\nColl(())", "[]")]
    public void LegitimateEmptyValueArgument_IsOneOrdinaryArgument(string source, string expectedDisplay)
        => Assert.Equal(expectedDisplay, AssertEvalSuccessDisplay(source));

    /// <summary>
    /// An empty STRING is a value too, and the empty value an argument carries is
    /// preserved structurally — zero output values and one empty value stay different.
    /// </summary>
    [Fact]
    public void EmptyStringArgument_IsOneOrdinaryArgument()
    {
        var result = EvalFull(Fixed1 + "\nF('')");
        Assert.False(result.IsError);
        Assert.Equal(new Result.Str(string.Empty), result.Value);
        Assert.Equal(1, result.Value.ValueCount());
    }

    /// <summary>
    /// An explicit SPREAD that legitimately opens to zero items is a legal supply, not a
    /// missing output — the collector accepts it exactly as it accepts <c>Coll()</c>.
    /// A spread operand that has no output at all is its own, different error
    /// (<see cref="EvalError.SpreadMissingOutput"/>), never the argument blame.
    /// </summary>
    [Fact]
    public void ExplicitSpreadSupplyingZeroItems_IsALegalSupply_NotAnOutputLessArgument()
    {
        Assert.Equal("[]", AssertEvalSuccessDisplay("Empty = ()\n" + Collector + "\nColl(Empty*)"));
        Assert.Equal("[]", AssertEvalSuccessDisplay(Collector + "\nColl(()*)"));
        Assert.Equal("[]", AssertEvalSuccessDisplay(Collector + "\nColl([]*)"));

        var spreadError = AssertEvalError(Collector + "\nColl({ }*)");
        Assert.IsType<EvalError.SpreadMissingOutput>(Innermost(spreadError));
        Assert.Null(FindArgumentBlame(spreadError));
        Assert.Contains(
            "Cannot spread because the spread operand has no defined output",
            KatLangError.FromEvalError(spreadError).Message,
            StringComparison.Ordinal);
    }

    // ── 2. Fixed arity: F() and F({ }) are not the same diagnosis ───────────

    /// <summary>
    /// The whole point of F5: an omitted argument and a written output-less argument must
    /// stay distinguishable in kind, in context, in span, and in wording.
    /// </summary>
    [Fact]
    public void FixedArity_OmittedAndOutputLessArguments_AreDistinctDiagnoses()
    {
        var omitted = AssertEvalError(Fixed1 + "\nF()");
        var written = AssertEvalError(Fixed1 + "\nF({ })");

        Assert.IsType<EvalError.ArityMismatch>(Innermost(omitted));
        Assert.IsType<EvalError.MissingOutput>(Innermost(written));
        Assert.NotEqual(omitted.Code, written.Code);

        var omittedMessage = KatLangError.FromEvalError(omitted).Message;
        var writtenMessage = KatLangError.FromEvalError(written).Message;
        Assert.NotEqual(omittedMessage, writtenMessage);
        Assert.Contains("expects 1 argument, but was called with 0 arguments", omittedMessage, StringComparison.Ordinal);

        // A FIXED parameter binds the argument on the algorithm channel and demands it
        // only when the body reads it, so the failure is reported through that parameter
        // — naming the argument the caller has to change, never the callee.
        var parameter = AssertContext<ParameterEvaluationContext>(written);
        Assert.Equal("x", parameter.ParameterName);
        Assert.Contains("Parameter 'x' has no defined output", writtenMessage, StringComparison.Ordinal);
        Assert.Contains("the argument bound to it", writtenMessage, StringComparison.Ordinal);
        Assert.DoesNotContain("Cannot call 'F'", writtenMessage, StringComparison.Ordinal);
    }

    /// <summary>
    /// A callee that genuinely has no output of its own KEEPS the callee blame — that
    /// message is correct there, and F5 must not disarm it.
    /// </summary>
    [Theory]
    [InlineData("F = { A = 1 }\nF()")]
    [InlineData("F = { A = 1 }\nF(1)")]
    public void CalleeWithNoOutputOfItsOwn_IsStillBlamedAsTheCallee(string source)
    {
        var error = AssertEvalError(source);
        Assert.IsType<EvalError.MissingOutput>(Innermost(error));
        Assert.Null(FindArgumentBlame(error));
        Assert.Contains(
            "Cannot call 'F' because it has no defined output",
            KatLangError.FromEvalError(error).Message,
            StringComparison.Ordinal);
    }

    // ── 3. Collectors: zero supplied items is not "produced no output" ──────

    /// <summary>
    /// A collector legally accepts zero supplied items, which is exactly why it must not
    /// swallow an ordinary written argument that produced none: <c>Coll({ })</c> is not
    /// <c>Coll()</c>, and the distinction cannot be decided from the final supplied-item
    /// count — only from slot provenance.
    /// </summary>
    [Fact]
    public void Collector_OutputLessWrittenArgument_DoesNotCollapseToTheZeroSupplyCall()
    {
        Assert.Equal("[]", AssertEvalSuccessDisplay(Collector + "\nColl()"));

        var error = AssertEvalError(Collector + "\nColl({ })");
        Assert.IsType<EvalError.MissingOutput>(Innermost(error));
        Assert.Equal("{...}", AssertArgumentBlame(error).ArgumentDescription);
    }

    /// <summary>
    /// The collector's own binding is unaffected: only the failing slot is blamed, and
    /// only where a VALUE is demanded. A collector that never reads its capture still
    /// collects it, so the failure still surfaces.
    /// </summary>
    [Theory]
    [InlineData(Collector + "\nColl(1, { }, 3)")]
    [InlineData("Coll(*xs) = 1\nColl({ })")]
    [InlineData("F(*xs, z) = z\nF({ }, 2)")]
    public void Collector_BlamesTheWrittenSlot_WhateverTheSurroundingSupply(string source)
        => Assert.Equal("{...}", AssertArgumentBlame(AssertEvalError(source)).ArgumentDescription);

    // ── 4. Builtins: value slots only, never callback slots ─────────────────

    /// <summary>
    /// A CALLBACK slot receives an algorithm and is never value-demanded, so F5 does not
    /// turn a higher-order argument into a value demand. The block reaches the callback
    /// contract exactly as before.
    /// </summary>
    [Theory]
    [InlineData("map((1, 2, 3), { })")]
    [InlineData("filter((1, 2, 3), { })")]
    [InlineData("reduce((1, 2, 3), {}, 0)")]
    [InlineData("repeat({}, 1, 0)")]
    [InlineData("while({}, 0)")]
    public void CallbackSlot_IsNotValueDemanded_ByTheArgumentBlame(string source)
    {
        var error = AssertEvalError(source);
        Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Null(FindArgumentBlame(error));
    }

    /// <summary>
    /// A real algorithm-valued callback still passes as an algorithm.
    /// </summary>
    [Fact]
    public void AlgorithmValuedCallback_StillPassesAsAnAlgorithm()
    {
        Assert.Equal("[2, 4, 6]", AssertEvalSuccessDisplay("Double(v) = v * 2\nmap((1, 2, 3), Double)"));
        Assert.Equal("[]", AssertEvalSuccessDisplay("Only(*xs) = xs\nmap((), Only)"));
    }

    /// <summary>
    /// An UNSELECTED branch is never demanded, so an output-less one is not an error.
    /// </summary>
    [Fact]
    public void UnselectedConditionalBranch_IsNeverDemanded()
    {
        Assert.Equal("1", AssertEvalSuccessDisplay("if(true, 1, { })"));
        Assert.Equal("2", AssertEvalSuccessDisplay("if(false, { }, 2)"));
    }

    /// <summary>
    /// A SELECTED branch that produces no output is blamed as the written argument it is
    /// — and a named one keeps the established property blame.
    /// </summary>
    [Fact]
    public void SelectedConditionalBranch_WithoutOutput_BlamesTheWrittenBranch()
    {
        Assert.Equal("{...}", AssertArgumentBlame(AssertEvalError("if(true, { }, 2)")).ArgumentDescription);

        var named = AssertEvalError("NoOut = { }\nif(true, NoOut, 2)");
        Assert.Null(FindArgumentBlame(named));
        Assert.Equal("NoOut", AssertContext<PropertyEvaluationContext>(named).PropertyName);
    }

    // ── 5. Which argument is blamed ─────────────────────────────────────────

    /// <summary>
    /// First, second, and middle output-less arguments are each identified precisely. A
    /// FIXED parameter list identifies the argument by the parameter it was bound to; a
    /// collector identifies it by the span of the written slot. Neither ever attaches
    /// another argument's identity.
    /// </summary>
    [Theory]
    [InlineData(Fixed2 + "\nF({ }, 2)", "x")]
    [InlineData(Fixed2 + "\nF(1, { })", "y")]
    [InlineData(Fixed3 + "\nF({ }, 2, 3)", "x")]
    [InlineData(Fixed3 + "\nF(1, { }, 3)", "y")]
    [InlineData(Fixed3 + "\nF(1, 2, { })", "z")]
    public void FixedParameters_BlameTheParameterOfTheOutputLessArgument(string source, string expectedParameter)
        => Assert.Equal(expectedParameter, AssertContext<ParameterEvaluationContext>(AssertEvalError(source)).ParameterName);

    /// <summary>
    /// Collector slots are identified by SPAN: the blame is positioned at the written
    /// argument that failed, never at an earlier or later one.
    /// </summary>
    [Theory]
    [InlineData("Coll({ }, 2, 3)")]
    [InlineData("Coll(1, { }, 3)")]
    [InlineData("Coll(1, 2, { })")]
    public void CollectorSlots_AreBlamedAtTheirOwnSpan(string call)
    {
        var source = Collector + "\n" + call;
        var error = AssertEvalError(source);
        AssertArgumentBlame(error);
        Assert.Equal(SpanOfFirstBlockOn(source, line: 2), error.Span);
    }

    // ── 6. Nested calls keep their frames ───────────────────────────────────

    /// <summary>
    /// Genuine user-written call frames are preserved outermost-to-innermost and the
    /// innermost written argument keeps the blame; the outer call never turns into a
    /// generic arity mismatch, and no synthetic frame appears.
    /// </summary>
    [Fact]
    public void NestedCalls_KeepTheirFramesAndBlameTheInnermostWrittenArgument()
    {
        var error = AssertEvalError("count(take((1, 2), { }))");
        var frames = Contexts(error);
        Assert.Equal(["count", "take"], frames.OfType<CallContext>().Select(c => c.CalleeDescription));
        Assert.Equal("{...}", AssertArgumentBlame(error).ArgumentDescription);

        var message = KatLangError.FromEvalError(error).Message;
        Assert.StartsWith("while evaluating call to count: while evaluating call to take: The argument", message, StringComparison.Ordinal);

        // A user callee nested inside a user callee keeps both frames too.
        var userError = AssertEvalError("Inner(a) = a\nOuter(b) = b\nOuter(Inner({ }))");
        Assert.Equal(["Outer", "Inner"], Contexts(userError).OfType<CallContext>().Select(c => c.CalleeDescription));
        Assert.Equal("a", AssertContext<ParameterEvaluationContext>(userError).ParameterName);
    }

    // ── 7. Dotted calls ─────────────────────────────────────────────────────

    /// <summary>
    /// DOT-CALL PASSES A VALUE: the receiver is an ordinary leading argument, so an
    /// output-less RECEIVER is blamed as the argument it is, and an output-less written
    /// ARGUMENT after the receiver is blamed as itself. The receiver is never
    /// reinterpreted as an implicit spread.
    /// </summary>
    [Fact]
    public void DottedCall_BlamesTheFailingSourceExpression_ReceiverOrWrittenArgument()
    {
        // A written argument of a dotted builtin call.
        var argument = AssertEvalError("(1, 2, 3).take({ })");
        Assert.Equal("{...}", AssertArgumentBlame(argument).ArgumentDescription);
        Assert.Equal("take", AssertContext<DotCallContext>(argument).PropertyName);

        // The RECEIVER itself. `{ }.count` is `count({ })`, so the receiver is the
        // written argument that produced nothing.
        var receiver = AssertEvalError("{ }.count");
        Assert.Equal("{...}", AssertArgumentBlame(receiver).ArgumentDescription);
        Assert.Equal("{...}", AssertContext<DotCallContext>(receiver).ReceiverDescription);
        Assert.Equal(new SourceSpan(new SourcePosition(1, 1), new SourcePosition(1, 4)), receiver.Span);

        // A NAMED receiver keeps the established property blame.
        var named = AssertEvalError("NoOut = { }\nNoOut.count");
        Assert.Null(FindArgumentBlame(named));
        Assert.Equal("NoOut", AssertContext<PropertyEvaluationContext>(named).PropertyName);

        // A user extension callee binds the receiver as an ordinary fixed parameter.
        var extension = AssertEvalError("F(r, x) = r + x\n5.F({ })");
        Assert.Equal("x", AssertContext<ParameterEvaluationContext>(extension).ParameterName);
    }

    // ── 8. Evaluation order, exactly-once, and laziness ─────────────────────

    /// <summary>
    /// Argument slots still evaluate left to right, and a slot that failed is RETAINED
    /// rather than raised — an argument nobody demands is not an error at all — so later
    /// slots still run. The blame is produced where the failure is finally demanded, and
    /// nothing is re-evaluated to discover it.
    /// </summary>
    [Fact]
    public void ArgumentEvaluation_StaysLeftToRight_AndNothingIsReEvaluatedForTheBlame()
    {
        // Ordering: the earlier argument ran, the later one still ran (retained failure).
        var (orderedError, ordered) = RunWithEffects(Collector + "\nColl(effect(1), { }, effect(3))");
        Assert.NotNull(orderedError);
        Assert.Equal(["1", "3"], ordered);
        AssertArgumentBlame(orderedError);

        // The failing argument is evaluated EXACTLY ONCE: discovering its provenance
        // never invokes its body again.
        var (onceError, once) = RunWithEffects(Collector + "\nColl(if(effect(1) == 1, { }, 2))");
        Assert.NotNull(onceError);
        Assert.Equal(["1"], once);
        AssertArgumentBlame(onceError);

        var (builtinError, builtinEffects) = RunWithEffects("take(effect(1), { })");
        Assert.NotNull(builtinError);
        Assert.Equal(["1"], builtinEffects);
        AssertArgumentBlame(builtinError);
    }

    /// <summary>
    /// Laziness is untouched: an output-less argument bound to a parameter the callee
    /// never reads is not an error at all, so the blame rule can never fire eagerly.
    /// </summary>
    [Fact]
    public void UndemandedOutputLessArgument_IsNotAnError()
    {
        Assert.Equal("1", AssertEvalSuccessDisplay("F(x, y) = x\nF(1, { })"));
        Assert.Equal("1", AssertEvalSuccessDisplay("F(x) = 1\nF({ })"));

        // Retention needs an algorithm channel; a NAME has one, so the slot is evaluated
        // once during assembly (left to right) and its failure is simply never demanded.
        var (error, effects) = RunWithEffects("P = if(effect(9) == 9, { }, 2)\nF(x, y) = x\nF(1, P)");
        Assert.Null(error);
        Assert.Equal(["9"], effects);
    }

    /// <summary>
    /// CHARACTERIZATION, deliberately unchanged by F5: a FIXED parameter binds its
    /// argument on the algorithm channel and drops the retained non-resource-limit value
    /// error, so the demand inside the callee re-derives it — which re-runs an effectful
    /// argument body. That is the pre-existing consequence of the lazy binding and of
    /// "failed properties are never cached", not of the blame rule; changing it would
    /// change observable host-effect counts, so this fix leaves it exactly as it was.
    /// </summary>
    [Fact]
    public void FixedParameterDemand_ReDerivesTheArgument_AsBefore()
    {
        var (error, effects) = RunWithEffects("P = if(effect(1) == 1, { }, 2)\n" + Fixed1 + "\nF(P)");
        Assert.NotNull(error);
        Assert.Equal(["1", "1"], effects);

        // The collector and builtin paths surface the RETAINED failure instead, so they
        // evaluate it once.
        var (collectorError, collectorEffects) = RunWithEffects("P = if(effect(1) == 1, { }, 2)\n" + Collector + "\nColl(P)");
        Assert.NotNull(collectorError);
        Assert.Equal(["1"], collectorEffects);
    }

    /// <summary>
    /// The zero-argument property cache is untouched: a successful property read is still
    /// shared across argument slots, and a failed one is still not stored.
    /// </summary>
    [Fact]
    public void ZeroArgumentPropertyCache_IsUnchanged()
    {
        var (error, effects) = RunWithEffects("P = effect(7)\nF(a, b) = a + b\nF(P, P)");
        Assert.Null(error);
        Assert.Equal(["7"], effects);
    }

    // ── 9. Named arguments keep the established blame ───────────────────────

    /// <summary>
    /// A NAME occurrence makes its own blame decision while it is evaluated, so the
    /// argument context never displaces the property or parameter blame.
    /// </summary>
    [Theory]
    [InlineData("L = { }\nsum(L)", "L")]
    [InlineData("L = { }\ncount(L)", "L")]
    [InlineData("L = { }\n" + Collector + "\nColl(L)", "L")]
    [InlineData("L = { }\nif(true, L, 2)", "L")]
    public void NamedOutputLessArgument_KeepsThePropertyBlame(string source, string propertyName)
    {
        var error = AssertEvalError(source);
        Assert.Null(FindArgumentBlame(error));
        Assert.Equal(propertyName, AssertContext<PropertyEvaluationContext>(error).PropertyName);
        Assert.Contains(
            $"Property '{propertyName}' has no defined output",
            KatLangError.FromEvalError(error).Message,
            StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("G(a) = sum(a)\nG({ })")]
    [InlineData("G(a) = count(a)\nG({ })")]
    [InlineData("G(a) = a.string\nG({ })")]
    public void OutputLessArgumentReadThroughAParameter_KeepsTheParameterBlame(string source)
    {
        var error = AssertEvalError(source);
        Assert.Null(FindArgumentBlame(error));
        Assert.Equal("a", AssertContext<ParameterEvaluationContext>(error).ParameterName);
    }

    // ── 10. F2 and F3 invariants survive ────────────────────────────────────

    /// <summary>
    /// F2: a location is a real half-open span or it is absent. The argument blame is
    /// positioned at the written argument, never at a fabricated <c>[0:0]</c>.
    /// </summary>
    [Theory]
    [InlineData("count({ })", 1, 7, 10)]
    [InlineData("sum({ })", 1, 5, 8)]
    [InlineData("if({ }, 1, 2)", 1, 4, 7)]
    public void ArgumentBlame_CarriesTheWrittenArgumentSpan(string source, int line, int startColumn, int endColumn)
    {
        var error = AssertEvalError(source);
        AssertArgumentBlame(error);
        Assert.Equal(
            new SourceSpan(new SourcePosition(line, startColumn), new SourcePosition(line, endColumn)),
            error.Span);
    }

    /// <summary>
    /// F3: the parser's synthetic assignment-deconstruction plumbing stays diagnostically
    /// transparent. Its hoisted right-hand-side source is a NAME the evaluator
    /// deliberately leaves unattributed so the failure reaches the written target — the
    /// argument blame must not claim it and reveal <c>$deconstruct$N</c>.
    /// </summary>
    [Theory]
    [InlineData("x, y = { }\nx")]
    [InlineData("x, y = { }\ny")]
    [InlineData("x, *y = { }\nx")]
    public void SyntheticDeconstructionPlumbing_StaysTransparent(string source)
    {
        var error = AssertEvalError(source);
        Assert.IsType<EvalError.MissingOutput>(Innermost(error));
        Assert.Null(FindArgumentBlame(error));

        var message = KatLangError.FromEvalError(error).Message;
        Assert.DoesNotContain("$deconstruct$", message, StringComparison.Ordinal);
        Assert.DoesNotContain("{...}", message, StringComparison.Ordinal);
        Assert.DoesNotContain("argument", message, StringComparison.Ordinal);
    }

    /// <summary>
    /// The deconstruction assignment renders exactly like the ordinary assignment control
    /// it mirrors, as F3 settled.
    /// </summary>
    [Fact]
    public void DeconstructionMissingOutput_MatchesTheOrdinaryAssignmentControl()
    {
        var deconstruction = KatLangError.FromEvalError(AssertEvalError("x, y = { }\nx")).Message;
        var ordinary = KatLangError.FromEvalError(AssertEvalError("x = { }\nx")).Message;
        Assert.Equal(ordinary, deconstruction);
    }

    // ── 11. Sync, async, generic, and optimized agree ───────────────────────

    /// <summary>
    /// The async twins assemble arguments through the mirrored path, so code, span, and
    /// rendered message agree with the sync evaluator.
    /// </summary>
    [Theory]
    [InlineData("count({ })")]
    [InlineData("take((1, 2, 3), { })")]
    [InlineData(Collector + "\nColl(1, { }, 3)")]
    [InlineData(Fixed1 + "\nF({ })")]
    [InlineData(Fixed3 + "\nF(1, { }, 3)")]
    [InlineData("(1, 2, 3).take({ })")]
    [InlineData("{ }.count")]
    [InlineData("x, y = { }\nx")]
    public async Task SyncAndAsyncEvaluation_ProduceTheSameBlame(string source)
    {
        var ast = new Expr.AlgorithmExpr(ParseValidRoot(source));
        var sync = Evaluator.Run(ast);
        var async = await Evaluator.RunAsync(ast, new Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache());

        Assert.True(sync.IsError);
        Assert.True(async.IsError);
        AssertSameDiagnosis(sync.Error, async.Error);
    }

    /// <summary>
    /// A genuinely SUSPENDING host operation before the output-less argument does not
    /// change the blame: the run really suspends, resumes, and reports the same argument.
    /// </summary>
    [Theory]
    [InlineData("Coll(*xs) = xs\nColl(Held(), { })")]
    [InlineData("take(Held(), { })")]
    [InlineData("P(a, (x, y)) = x\nP(Held(), { })")]
    [InlineData("F(0, x) = x\nF(a, b) = a + b\nF(Held(), { })")]
    [InlineData("Step(v, acc) = v + acc\nreduce(Held(), Step, { })")]
    public async Task SuspendedRun_ProducesTheSameArgumentBlame(string source)
    {
        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var invocations = 0;

        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Held", async (_, _) =>
                {
                    Interlocked.Increment(ref invocations);
                    reached.TrySetResult();
                    return await gate.Task;
                })),
        };

        var run = KatLangEngine.RunAsync(source, options);

        var arrived = await Task.WhenAny(reached.Task, Task.Delay(TimeSpan.FromSeconds(45)));
        Assert.Same(reached.Task, arrived);
        Assert.False(run.IsCompleted);

        gate.TrySetResult(new Result.Atom(5));
        var completed = await Task.WhenAny(run, Task.Delay(TimeSpan.FromSeconds(45)));
        Assert.Same(run, completed);

        var failure = Assert.IsType<RunResult.EvalFailure>(await run);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.MissingOutput, error.Code);
        Assert.Contains("The argument `{...}` has no defined output", error.Message, StringComparison.Ordinal);
        Assert.Equal(1, Volatile.Read(ref invocations));
        var sync = KatLangEngine.Run(source, new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Held", (_, _) => new Result.Atom(5))),
        });
        Assert.NotNull(error.Source);
        var syncError = Assert.Single(Assert.IsType<RunResult.EvalFailure>(sync).Errors).Source;
        Assert.NotNull(syncError);
        AssertSameDiagnosis(syncError, error.Source);
    }

    /// <summary>
    /// The loop and sequence-pipeline optimizers never disagree with the generic
    /// strategy about which argument is blamed.
    /// </summary>
    [Theory]
    [InlineData("count({ })")]
    [InlineData("take((1, 2, 3), { })")]
    [InlineData(Collector + "\nColl(1, { }, 3)")]
    [InlineData("map((1, 2, 3), { })")]
    [InlineData("S = (1, 2, 3)\nS.filter({ }).count")]
    [InlineData("Step(s) = s + 1\nrepeat(Step, 3, { })")]
    public void GenericAndOptimizedExecution_ProduceTheSameBlame(string source)
    {
        var generic = EvalFull(source, enableLoopOptimization: false, enableSequencePipelineOptimization: false);
        var optimized = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: true);

        Assert.True(generic.IsError);
        Assert.True(optimized.IsError);
        AssertSameDiagnosis(generic.Error, optimized.Error);
    }

    // ── 12. Host-built ASTs follow the same rule ────────────────────────────

    /// <summary>
    /// The rule depends on SEMANTIC provenance — a written argument slot demanded for its
    /// value — not on anything the parser records, so a host-built call reports exactly
    /// like the parsed one.
    /// </summary>
    [Fact]
    public void HostBuiltCall_WithAnOutputLessArgument_IsBlamedAtTheArgument()
    {
        var outputLess = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], []));

        // count({ }) — a builtin value slot.
        var builtinCall = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [],
            [new Expr.Call(new Expr.Resolve("count"), new OutputBundle([outputLess]))]));
        var builtinError = AssertError(Evaluator.Run(builtinCall));
        Assert.Null(builtinError.Span);
        Assert.IsType<EvalError.MissingOutput>(Innermost(builtinError));
        Assert.Equal("{...}", AssertArgumentBlame(builtinError).ArgumentDescription);

        // Coll({ }) — a user collector.
        var collector = new Property("Coll", new Algorithm.User(
            null,
            [new CaptureParameterPattern("xs", Kind: ParameterKind.Collecting)],
            [],
            [],
            [new Expr.Param("xs")]));
        var userCall = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [collector],
            [new Expr.Call(new Expr.Resolve("Coll"), new OutputBundle([outputLess]))]));
        var userError = AssertError(Evaluator.Run(userCall));
        Assert.Null(userError.Span);
        Assert.IsType<EvalError.MissingOutput>(Innermost(userError));
        Assert.Equal("{...}", AssertArgumentBlame(userError).ArgumentDescription);

        // The same host-built collector still accepts a legitimate zero supply.
        var zeroSupply = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [collector],
            [new Expr.Call(new Expr.Resolve("Coll"), OutputBundle.Empty)]));
        var ok = Evaluator.Run(zeroSupply);
        Assert.False(ok.IsError);
        Assert.Equal(new Result.ListValue([]), ok.Value);
    }

    // Hostile review: binding shapes, actual strategy dispatch, and cancellation.

    [Theory]
    [InlineData("F(x, *xs) = xs\nF(1, {})")]
    [InlineData("F(x, *xs, z) = xs\nF(1, {}, 3)")]
    [InlineData("Coll(*xs) = xs\n(1, 2).Coll({})")]
    [InlineData("Obj = { public Coll(*xs) = xs }\nObj.Coll({})")]
    [InlineData("F((x, y)) = x\nF({})")]
    [InlineData("F((x, *rest)) = rest\nF({})")]
    [InlineData("F((x, y), *rest) = x\nF({}, 3)")]
    [InlineData("F(0) = 0\nF(x) = x\nF({})")]
    [InlineData("F((0, y)) = y\nF((x, y)) = x\nF({})")]
    [InlineData("Step(s) = s + 1\nrepeat(Step, {}, 0)")]
    [InlineData("Step(s) = s + 1\nrepeat(Step, 1, {})")]
    [InlineData("Step(s) = s, false\nwhile(Step, {})")]
    [InlineData("Step(v, acc) = v + acc\nreduce([1], Step, {})")]
    [InlineData("Coll(*xs) = xs\nColl({}:0)")]
    [InlineData("Coll(*xs) = xs\nColl([1, {}])")]
    [InlineData("Coll(*xs) = xs\nColl((1, {}))")]
    public async Task ValueDemandPaths_RetainWrittenSource_InBothTwins(string source)
    {
        var error = AssertEvalError(source);
        Assert.IsType<EvalError.MissingOutput>(Innermost(error));
        AssertArgumentBlame(error);
        Assert.NotNull(error.Span);
        var asyncResult = await Evaluator.RunAsync(new Expr.AlgorithmExpr(ParseValidRoot(source)),
            new Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache());
        AssertSameDiagnosis(error, AssertError(asyncResult));
    }

    [Fact]
    public void MultipleMissingSlots_KeepFirstDemandedSlot_AndSuffixesStayLazy()
    {
        var source = Collector + "\nColl({}, { A = 2 }, {})";
        var error = AssertEvalError(source);
        Assert.Equal(SpanOfFirstBlockOn(source, 2), error.Span);
        AssertArgumentBlame(error);
        Assert.Equal("[1]", AssertEvalSuccessDisplay("F(*xs, z) = xs\nF(1, {})"));
        var suffix = AssertEvalError("F(*xs, z) = z\nF(1, {})");
        Assert.Equal("z", AssertContext<ParameterEvaluationContext>(suffix).ParameterName);
        Assert.Equal("7", AssertEvalSuccessDisplay("F((0, y)) = y\nF((x, y)) = x\nF((0, 7))"));
        Assert.Equal("[]", AssertEvalSuccessDisplay("Only(*xs) = xs\nOnly"));
    }

    [Theory]
    [InlineData("if(true, effect(1), if(effect(2) == 2, {}, 0))", "1")]
    [InlineData("if(false, if(effect(1) == 1, {}, 0), effect(2))", "2")]
    public void ConditionalLaziness_IsProvedByEffects(string source, string selected)
    {
        var (error, effects) = RunWithEffects(source);
        Assert.Null(error);
        Assert.Equal([selected], effects);
    }

    [Fact]
    public async Task CancellationDuringArgumentAssembly_StaysCancellation_AndStopsLaterEffects()
    {
        using var cancellation = new CancellationTokenSource();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = new List<string>();
        var run = KatLangEngine.RunAsync("Coll(*xs) = xs\nColl(Held(), {}, Later())", new RunOptions
        {
            EvaluationCancellationToken = cancellation.Token,
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Held", async (_, token) =>
                {
                    calls.Add("Held");
                    reached.SetResult();
                    Assert.Equal(cancellation.Token, token);
                    return await gate.Task;
                }),
                HostOperation.Create("Later", (_, _) => { calls.Add("Later"); return new Result.Atom(3); })),
        });
        await reached.Task.WaitAsync(TimeSpan.FromSeconds(30));
        Assert.False(run.IsCompleted);
        cancellation.Cancel();
        gate.SetResult(new Result.Atom(1));
        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => run.WaitAsync(TimeSpan.FromSeconds(30)));
        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(["Held"], calls);
    }

    [Theory]
    [InlineData("Step(s) = if(true, {}, s)\nrepeat(Step, 1, 0)")]
    [InlineData("Step(s) = if({}, s, s)\nrepeat(Step, 1, 0)")]
    [InlineData("Step(s) = if(false, s, 1 + {})\nrepeat(Step, 1, 0)")]
    [InlineData("Coll(*xs) = xs\nStep(s) = Coll({})\nrepeat(Step, 1, 0)")]
    public void PlannedLoop_ArgumentFailure_HasGenericBlame(string source)
    {
        var (generic, genericStats, _) = LoopDiagnosticParityAssertions.RunObserved(source, false);
        var (planned, plannedStats, _) = LoopDiagnosticParityAssertions.RunObserved(source, true);
        Assert.Equal(0, genericStats.OptimizedLoopHits);
        Assert.Equal(1, plannedStats.OptimizedLoopHits);
        // The loop is optimized, but a missing-output block is not a scalar plan.
        // Its output expression must reach the generic fallback inside that loop.
        Assert.True(plannedStats.PlannedExpressionFallbacks > 0);
        AssertArgumentBlame(AssertError(generic));
        AssertSameDiagnosis(generic.Error, AssertError(planned));
        Assert.Equal(LoopDiagnosticParityAssertions.DescribeErrorTree(generic.Error),
            LoopDiagnosticParityAssertions.DescribeErrorTree(planned.Error));
    }

    [Theory]
    [InlineData("P(x) = true\ncount(filter({}, P))", 0, true)]
    [InlineData("P(x) = true\n{}.filter(P).count", 0, false)]
    [InlineData("P(x) = count({}) == x\ncount(filter(range(1, 2), P))", 1, false)]
    [InlineData("P(x) = count({}) == x\n(1, 2).filter(P).count", 1, false)]
    public void FusedPipeline_ArgumentFailure_HasGenericBlame(string source, int fusionHits, bool fallback)
    {
        var diagnostics = new Optimizations.Sequences.SequencePipelineDiagnostics();
        var ast = new Expr.AlgorithmExpr(ParseValidRoot(source));
        var generic = EvalFull(source, enableLoopOptimization: false, enableSequencePipelineOptimization: false);
        var optimized = Evaluator.Run(ast, new Evaluation.Caching.RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true, loopDiagnostics: null,
            enableSequencePipelineOptimization: true, sequenceDiagnostics: diagnostics);
        var stats = diagnostics.GetSnapshot();
        Assert.Equal(fusionHits, stats.FilterCountFusionHits);
        if (fallback)
            Assert.True(stats.FilterCountFusionFallbacks > 0);
        else if (fusionHits == 0)
        {
            // Recognition committed; source preparation failed before ExecuteFilterCount.
            Assert.Equal(0, stats.FilterCountFusionFallbacks);
            Assert.Equal(1, stats.DirectRangeFusionFallbacks);
        }
        AssertArgumentBlame(AssertError(generic));
        AssertSameDiagnosis(generic.Error, AssertError(optimized));
    }

    [Fact]
    public void ArgumentDescriptions_AreBoundedDeterministic_AndKeepUnicodePairs()
    {
        // The block fails before the large tail is evaluated, but naming the capture
        // must still bound traversal and avoid splitting a UTF-16 surrogate pair.
        var prefix = "({...}, '";
        var text = new string('a', 511 - prefix.Length) + "\U0001F680" + new string('z', 2000);
        var source = "count(({}, '" + text + "'))";
        var first = AssertArgumentBlame(AssertEvalError(source)).ArgumentDescription;
        var second = AssertArgumentBlame(AssertEvalError(source)).ArgumentDescription;
        Assert.Equal(prefix + new string('a', 511 - prefix.Length) + "…", first);
        Assert.Equal(first, second);
        Assert.DoesNotContain(first, char.IsSurrogate);
        var wide = "count(({}, " + string.Join(", ", Enumerable.Repeat("1", 10000)) + "))";
        var wideName = AssertArgumentBlame(AssertEvalError(wide)).ArgumentDescription;
        Assert.True(wideName.Length <= 513);
        Assert.EndsWith("…", wideName, StringComparison.Ordinal);
    }

    [Fact]
    public async Task ImportedCollector_BlamesTheCallersArgumentCoordinates()
    {
        const string source = "open 'https://example.test/library'\nColl({})";
        var run = await KatLangEngine.RunAsync(source, new RunOptions
        {
            AllowedHosts = ["example.test"],
            DownloadCode = (_, _) => ValueTask.FromResult("# Imported declaration\n\npublic Coll(*xs) = xs"),
        });
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(run).Errors).Source;
        Assert.NotNull(error);
        AssertArgumentBlame(error);
        Assert.Equal(new SourceSpan(new SourcePosition(2, 6), new SourcePosition(2, 8)), error.Span);
    }

    [Fact]
    public void GroupedPatternBesideCollector_KeepsF4ArityFacts()
    {
        const string declaration = "G((a, b), *rest) = a";
        var algorithm = Assert.Single(ParseValidRoot(declaration).Properties).Value;
        var facts = CallableSignature.FromAlgorithm("G", algorithm).ArityFacts;
        Assert.Equal(1, facts.MinTopLevelArgumentCount);
        Assert.Null(facts.MaxTopLevelArgumentCount);
        var missing = Assert.IsType<EvalError.ArityMismatch>(Innermost(AssertEvalError(declaration + "\nG()")));
        Assert.Equal(1, missing.Expected);
        Assert.Equal(0, missing.Actual);
        Assert.Equal("1", AssertEvalSuccessDisplay(declaration + "\nG((1, 2), 3, 4)"));
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static EvalError AssertEvalError(string source)
        => AssertError(EvalFull(source));

    private static EvalError AssertError(EvalResult<Result> result)
    {
        if (!result.IsError)
            Assert.Fail($"Expected an evaluation error but the run succeeded with: {result.Value}");
        return result.Error;
    }

    private static string AssertEvalSuccessDisplay(string source)
    {
        var run = KatLangEngine.Run(source);
        if (run is not RunResult.Success success)
            Assert.Fail($"Expected success but got: {run.ToDisplayString()}");
        else
            return success.ToDisplayString();

        throw new InvalidOperationException("unreachable");
    }

    private static IReadOnlyList<ErrorContext> Contexts(EvalError error)
    {
        var contexts = new List<ErrorContext>();
        for (var current = error; current is EvalError.WithContext context; current = context.Inner)
            contexts.Add(context.ErrorContext);
        return contexts;
    }

    private static ArgumentEvaluationContext? FindArgumentBlame(EvalError error)
        => Contexts(error).OfType<ArgumentEvaluationContext>().FirstOrDefault();

    private static ArgumentEvaluationContext AssertArgumentBlame(EvalError error)
    {
        var argument = FindArgumentBlame(error);
        Assert.True(argument is not null, $"Expected an ArgumentEvaluationContext, but the chain was: {error}");
        return argument!;
    }

    private static TContext AssertContext<TContext>(EvalError error) where TContext : ErrorContext
    {
        var context = Contexts(error).OfType<TContext>().FirstOrDefault();
        Assert.True(context is not null, $"Expected a {typeof(TContext).Name}, but the chain was: {error}");
        return context!;
    }

    private static void AssertSameDiagnosis(EvalError left, EvalError right)
    {
        Assert.Equal(left.Code, right.Code);
        Assert.Equal(left.Span, right.Span);
        Assert.Equal(KatLangError.FromEvalError(left).Message, KatLangError.FromEvalError(right).Message);
        Assert.Equal(
            Contexts(left).Select(c => c.ToLegacyString()),
            Contexts(right).Select(c => c.ToLegacyString()));
        Assert.Equal(LoopDiagnosticParityAssertions.DescribeErrorTree(left),
            LoopDiagnosticParityAssertions.DescribeErrorTree(right));
    }

    /// <summary>
    /// The span of the first brace block written on <paramref name="line"/>, used to pin
    /// which written slot the blame was positioned at.
    /// </summary>
    private static SourceSpan SpanOfFirstBlockOn(string source, int line)
    {
        var text = source.Split('\n')[line - 1];
        var start = text.IndexOf('{');
        var end = text.IndexOf('}', start);
        Assert.True(start >= 0 && end > start, $"No brace block on line {line} of: {source}");
        return new SourceSpan(new SourcePosition(line, start + 1), new SourcePosition(line, end + 2));
    }

    /// <summary>
    /// Runs <paramref name="source"/> with a deterministic <c>effect(tag)</c> host
    /// operation that records its argument, returning the failure (if any) and the
    /// recorded effect order.
    /// </summary>
    private static (EvalError? Error, IReadOnlyList<string> Effects) RunWithEffects(string source)
    {
        var effects = new List<string>();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("effect", (values, _) =>
                {
                    effects.Add(values[0] is Result.Atom(var number) ? number.ToString() : values[0].ToString()!);
                    return values[0];
                }, "tag")),
        };

        var run = KatLangEngine.Run(source, options);
        return run switch
        {
            RunResult.EvalFailure failure => (failure.Errors[0].Source, effects),
            RunResult.ParseFailure parseFailure => throw new InvalidOperationException(
                "Effect probe source must parse cleanly: " + parseFailure.Errors[0].Message),
            RunResult.Success => (null, effects),
            _ => throw new InvalidOperationException("Effect probe must produce a value or evaluation error: " + run),
        };
    }
}
