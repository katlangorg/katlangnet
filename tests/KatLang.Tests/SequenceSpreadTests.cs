namespace KatLang.Tests;

public class SequenceSpreadTests
{
    private static EvalResult<IReadOnlyList<decimal>> Eval(string source)
    {
        var parseResult = Parser.Parse(source);
        if (parseResult.HasErrors)
        {
            var message = string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message));
            Assert.Fail($"Expected parse success but got diagnostics:{Environment.NewLine}{message}");
        }

        return Evaluator.RunFlat(new Expr.Block(parseResult.Root));
    }

    private static EvalResult<Result> EvalFull(string source)
    {
        var parseResult = Parser.Parse(source);
        if (parseResult.HasErrors)
        {
            var message = string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message));
            Assert.Fail($"Expected parse success but got diagnostics:{Environment.NewLine}{message}");
        }

        return Evaluator.Run(new Expr.Block(parseResult.Root));
    }

    private static void AssertEval(string source, params decimal[] expected)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal(expected, result.Value);
    }

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext(_, var inner) ? Innermost(inner) : error;

    private static void AssertArityFailure(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        Assert.True(
            Innermost(result.Error) is EvalError.ArityMismatch or EvalError.BadArity,
            $"Expected arity-shaped failure but got: {result.Error}");
    }

    private static void AssertEvaluationFailure(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");
    }

    private static void AssertParseFailure(string source)
    {
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);
    }

    [Fact]
    public void BasicSequenceSpread_MultiOutputPropertySpreadsFixedCallArguments()
        => AssertEval(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair...)
            """,
            30m);

    [Fact]
    public void BasicSequenceSpread_SequenceValueSpreadsSequenceValueItems()
        => AssertEval(
            """
            Pair = (10, 20)
            Add(x, y) = x + y
            Add(Pair...)
            """,
            30m);

    [Fact]
    public void NormalCallArgument_DoesNotImplicitlySpreadMultiOutputProperty()
        => AssertArityFailure(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair)
            """);

    [Fact]
    public void NormalCallArgument_DotCallMultiOutputDoesNotSpreadByItself()
        => AssertArityFailure(
            """
            Pair = (10, 20)
            Add(x, y) = x + y
            Add(Pair.atoms)
            """);

    [Fact]
    public void PartialSequenceSpread_SpreadsTailArguments()
        => AssertEval(
            """
            Tail = 2, 3
            Use(a, b, c) = a + b + c
            Use(1, Tail...)
            """,
            6m);

    [Fact]
    public void MultipleSequenceSpreadSegments_SpreadAroundNormalArgument()
        => AssertEval(
            """
            Head = 1, 2
            Tail = 4, 5
            Use(a, b, c, d, e) = a + b + c + d + e
            Use(Head..., 3, Tail...)
            """,
            15m);

    [Fact]
    public void LineEndingPostfixEllipsis_DoesNotContinueSequenceSpreadForFixedCall()
        // Inside the open call-argument list a newline separates slots, so the
        // call sees two argument slots `A...` and `A` — not a continued spread
        // A...A and not four call arguments.
        => AssertArityFailure(
            """
            A = 1, 2
            Sum4(a, b, c, d) = a + b + c + d
            Sum4(A...
            A)
            """);

    [Fact]
    public void LineEndingPostfixEllipsisWithExplicitComma_KeepsNextLineAsSeparateArgument()
        => AssertEval(
            """
            A = 1, 2
            Use(a, b, c) = a + b + c.count
            Use(A...,
            A)
            """,
            5m);

    [Fact]
    public void OrdinaryCompleteExpressionsAcrossNewlines_DoNotBecomeCallArguments()
        // Inside the open call-argument list a newline separates slots, so this
        // is the two-argument call Shape(A, A).
        => AssertEval(
            """
            A = 1, 2
            Shape(first, second) = first.count, second.count
            Shape(A
            A)
            """,
            2m,
            2m);

    [Fact]
    public void LeadingEllipsisContinuation_IsParseError()
        => AssertParseFailure(
            """
            A = 1, 2
            Sum4(a, b, c, d) = a + b + c + d
            Sum4(A
            ...A)
            """);

    // A postfix spread never consumes a following binary operator, so an opened
    // item supply cannot be a binary operand. `A... == A...` is a parse error
    // rather than an elementwise comparison — structural `==`/`!=` operate on whole
    // values, never on opened item supplies. Compare regrouped values with `(A...) == A`.
    [Fact]
    public void PostfixEllipsisFollowedByEqualityOperator_IsParseError()
        => AssertParseFailure(
            """
            A = 1, 2
            A... == A...
            """);

    [Fact]
    public void CallEndingAfterInnerPostfixEllipsis_FollowingLineStartsSeparateOutput()
        => AssertEval(
            """
            A = 1, 2
            F(x, y) = x + y
            F(A...)
            9
            """,
            3m,
            9m);

    [Fact]
    public void CallEndingAfterInnerPostfixEllipsisWithTrailingComment_FollowingLineStartsSeparateOutput()
        => AssertEval(
            """
            A = 1, 2
            F(x, y) = x + y
            F(A...) // the line ends with the call, not the inner ellipsis
            9
            """,
            3m,
            9m);

    [Fact]
    public void ParenthesizedPostfixEllipsis_FollowingLineStartsSeparateOutput()
    {
        var result = EvalFull(
            """
            A = 1, 2
            (A...)
            9
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Equal(2, outer.Items.Count);

        var spread = Assert.IsType<Result.SequenceValue>(outer.Items[0]);
        Assert.Equal(
            [1m, 2m],
            spread.Items.Select(static item => Assert.IsType<Result.Atom>(item).Value).ToArray());
        Assert.Equal(9m, Assert.IsType<Result.Atom>(outer.Items[1]).Value);
    }

    // `Values...7` is not a binary spread: `...` is postfix and takes no right
    // operand, so it parses as the expression list `Values..., 7` = three slots
    // [10, 20, 7], bound by the item-supply matcher (sum 37).
    [Theory]
    [InlineData("Sum(Values...7)")]
    [InlineData("Sum(Values ...7)")]
    public void PostfixSpreadThenJoinInsideCall_BindsItemSupply(string call)
        => AssertEval(
            $$"""
            Values = 10, 20
            Sum(values...) = values.sum
            {{call}}
            """,
            37m);

    [Fact]
    public void VariadicSuffixBinding_CommaSeparatedSpreadSegmentBindsByDeconstruction()
        // Sum(values..., val) is a comma deconstruction parameter list. Values...
        // spreads into [10, 20] and 7 fills the suffix, so the variadic captures
        // [10, 20] (sum 30) and val binds 7: 30 + 7 = 37.
        => AssertEval(
            """
            Values = 10, 20
            Sum(values..., val) = values.sum + val
            Sum(Values..., 7)
            """,
            37m);

    [Fact]
    public void VariadicSuffixBinding_NormalArgumentSpreadsOnlyVariadicSlot()
        => AssertEval(
            """
            Values = 10, 20
            Sum(values..., val) = values.sum + val
            Sum(Values, 7)
            """,
            37m);

    [Fact]
    public void VariadicSuffixBinding_NormalArgumentPreservesSingleGroupedValue()
        // One grouped sequence-value argument is not implicitly opened for a
        // mixed variadic call; val receives the sequence value and the numeric
        // body fails. Use Values... to open it explicitly.
        => AssertEvaluationFailure(
            """
            Values = 10, 20
            Sum(values..., val) = values.sum + val
            Sum(Values)
            """);

    [Fact]
    public void VariadicSuffixBinding_DotCallReceiverPreservesSingleGroupedValue()
        => AssertEvaluationFailure(
            """
            Values = 10, 20
            Sum(values..., val) = values.sum + val
            Values.Sum
            """);

    [Fact]
    public void VariadicSuffixBinding_DotCallReceiverWithSuffixSpreadsVariadicSlot()
        => AssertEval(
            """
            Values = 10, 20
            Sum(values..., val) = values.sum + val
            Values.Sum(7)
            """,
            37m);

    [Fact]
    public void VariadicSuffixBinding_ExplicitSpreadCanSatisfySuffixWhenSlotCountMatches()
        => AssertEval(
            """
            Values = 10, 20
            Sum(values..., val) = values.sum + val
            Sum(Values...)
            """,
            30m);

    [Fact]
    public void StrictVariadicSequenceSlot_QmeanNormalCallSucceeds()
        => AssertEval(
            """
            Vector = range(1, 10)
            Qmean(args...) = Math.Sqrt(args.map{x * x}.sum / args.count)
            Qmean(Vector) == Math.Sqrt(385 / 10)
            """,
            1m);

    [Fact]
    public void StrictVariadicSequenceSlot_QmeanDotCallMatchesNormalCall()
        => AssertEval(
            """
            Vector = range(1, 10)
            Qmean(args...) = Math.Sqrt(args.map{x * x}.sum / args.count)
            Vector.Qmean() == Qmean(Vector)
            """,
            1m);

    [Fact]
    public void StrictVariadicSequenceSlot_MultiOutputPropertySpreadsSequenceValue()
        => AssertEval(
            """
            Values = 10, 20
            Count(args...) = args.count
            Count(Values)
            """,
            2m);

    [Fact]
    public void StrictVariadicSequenceSlot_VisibleGroupCountsSequenceItems()
        => AssertEval(
            """
            Pair = (10, 20)
            Count(args...) = args.count
            Count(Pair)
            """,
            2m);

    [Fact]
    public void StrictVariadicSequenceSlot_DotCallVisibleGroupCountsSequenceItems()
        => AssertEval(
            """
            Pair = (10, 20)
            Count(args...) = args.count
            Pair.Count()
            """,
            2m);

    [Fact]
    public void FlatFixedCall_DotCallReceiverDoesNotImplicitlySpreadMultiOutputProperty()
        => AssertArityFailure(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Pair.Add
            """);

    [Fact]
    public void VariadicParameterForwarding_DirectCallSpreadsCompatibleVariadicSlot()
        => AssertEval(
            """
            CountItem(values..., item) = values.filter{value == item}.count
            Use(values...) = CountItem(values, 1)
            Use((1, 1, 2, 4, 4))
            """,
            2m);

    [Fact]
    public void VariadicParameterForwarding_CallbackBodySpreadsCompatibleVariadicSlot()
        => AssertEval(
            """
            CountItem(values..., item) = values.filter{value == item}.count

            Mode(values...) = {
                Freqs = values.distinct.map{CountItem(values, candidate)}
                Freqs
            }

            Mode((1, 1, 2, 4, 4))
            """,
            2m, 1m, 2m);

    [Fact]
    public void VariadicParameterForwarding_FullModeExampleSpreadsCompatibleVariadicSlot()
        => AssertEval(
            """
            CountItem(values..., item) = values.filter{value == item}.count

            Mode(values...) = {
                Freqs = values.distinct.map{CountItem(values, candidate)}
                MaxFreq = Freqs.max

                values.distinct.filter{CountItem(values, candidate) == MaxFreq}
            }

            Mode((1, 1, 2, 4, 4))
            """,
            1m, 4m);

    [Fact]
    public void VariadicParameterForwarding_NonVariadicCalleeStillReceivesOneSequenceValue()
        => AssertEval(
            """
            Collect(list) = list.count
            Use(values...) = Collect(values)
            Use((10, 20, 30))
            """,
            3m);

    [Fact]
    public void VariadicParameterForwarding_CompatibleTopLevelVariadicCalleeReceivesStream()
        => AssertEval(
            """
            Collect(list...) = list.count
            Use(values...) = Collect(values)
            Use((10, 20, 30))
            """,
            3m);

    [Fact]
    public void VariadicParameterForwarding_TopLevelCaptureStillSpreadsCompatibleVariadicSlot()
        => AssertEval(
            """
            CountItems(items...) = items.count
            Use(values...) = CountItems(values)
            Use((1, 2, 3))
            """,
            3m);

    [Fact]
    public void VariadicParameterForwarding_SequenceValueVariadicPatternKeepsSequenceValueBindingBehavior()
        => AssertEval(
            """
            CountSequenceValue((values...)) = values.count
            Use(values...) = CountSequenceValue(values)
            Use((10, 20, 30))
            """,
            3m);

    [Fact]
    public void VariadicParameterForwarding_SequenceValueVariadicCaptureSpreadsCompatibleVariadicSlot()
        => AssertEval(
            """
            FindNext(history..., pre1, pre2) = history.count + pre1 + pre2
            YSStep((history...), pre2, pre1) = FindNext(history, pre1, pre2)
            YSStep((1, 2, 3), 2, 3)
            """,
            8m);

    [Fact]
    public void VariadicParameterForwarding_SequenceValueCaptureStillSpreadsCompatibleVariadicSlot()
        => AssertEval(
            """
            CountItems(items...) = items.count
            Use((history...)) = CountItems(history)
            Use((1, 2, 3))
            """,
            3m);

    [Fact]
    public void SequenceValueVariadicCalleeBoundary_DoesNotUseFlatSlotSpread()
        => AssertEval(
            """
            CountSequenceValue((items...)) = items.count
            Pair = 10, 20
            CountSequenceValue(Pair)
            """,
            2m);

    [Fact]
    public void VariadicParameterForwarding_SequenceValueVariadicCaptureForwardsByProvenanceNotName()
        => AssertEval(
            """
            CountItems(items..., last) = items.count + last
            Use((history...), last) = CountItems(history, last)
            Use((10, 20, 30), 7)
            """,
            10m);

    [Fact]
    public void VariadicParameterForwarding_SequenceValueVariadicCaptureKeepsNonVariadicCalleeBoundary()
        => AssertEval(
            """
            Collect(list) = list.count
            Use((history...), marker) = Collect(history)
            Use((10, 20, 30), 99)
            """,
            3m);

    [Fact]
    public void VariadicParameterForwarding_SequenceValueVariadicCaptureOnlyExpandsInTargetVariadicSlot()
        => AssertEval(
            """
            TakeLast(first..., last) = first.count
            Use((history...), marker) = TakeLast(0, history)
            Use((10, 20, 30), 99)
            """,
            1m);

    [Fact]
    public void VariadicParameterForwarding_LoopStepSequenceValueVariadicCaptureSpreadsCompatibleVariadicSlot()
        => AssertEval(
            """
            FindNext(history..., pre1, pre2) = history.count + pre1 + pre2
            YSStep((history...), pre2, pre1) = FindNext(history, pre1, pre2), pre1, pre2
            YSStep.repeat(1, (1, 2, 3), 2, 3):0
            """,
            8m);

    [Fact]
    public void SequenceBuiltin_NormalArgumentContributesSequenceItems()
        => AssertEval(
            """
            Values = 10, 20
            count(Values)
            """,
            2m);

    [Fact]
    public void SequenceBuiltin_ExplicitSpreadJoinsItemSupply()
        // A rest-shaped builtin consumes an item supply like a user variadic, so explicit
        // spread opens its items into the same supply (it no longer over-supplies).
        => AssertEval(
            """
            Values = 10, 20
            count(Values...)
            """,
            2m);

    [Fact]
    public void SequenceBuiltin_NumericNormalArgumentConsumesSequenceValue()
        => AssertEval(
            """
            Values = 10, 20
            sum(Values)
            """,
            30m);

    [Fact]
    public void SequenceBuiltin_NumericExplicitSpreadJoinsItemSupply()
        => AssertEval(
            """
            Values = 10, 20
            sum(Values...)
            """,
            30m);

    [Fact]
    public void FixedBuiltin_ExplicitSpreadProvidesArguments()
        => AssertEval(
            """
            Bounds = 1, 3
            range(Bounds...)
            """,
            1m, 2m, 3m);

    [Fact]
    public void NonCallResultContext_CommaPreservesNestedBlockBoundary()
    {
        var result = EvalFull(
            """
            A = 1, { 2, 3 }
            A
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Equal(2, group.Items.Count);
        Assert.Equal(1m, Assert.IsType<Result.Atom>(group.Items[0]).Value);
        var nested = Assert.IsType<Result.SequenceValue>(group.Items[1]);
        Assert.Equal([2m, 3m], nested.Items.Select(static item => Assert.IsType<Result.Atom>(item).Value).ToArray());
    }

    [Theory]
    [InlineData("A = 1...{ 2, 3 }")]
    [InlineData("A = 1 ... { 2, 3 }")]
    public void NonCallResultContext_SequenceSpreadSpreadsNestedBlockOutput(string definition)
        => AssertEval(
            $$"""
            {{definition}}
            A
            """,
            1m, 2m, 3m);

    // `(Values...)` spreads the receiver into the item supply, so `Sum(values...)`
    // binds [10, 20] and sums to 30.
    [Fact]
    public void DotCall_ExplicitSequenceSpreadReceiverBindsItemSupply()
        => AssertEval(
            """
            Values = 10, 20
            Sum(values...) = values.sum
            Output = (Values...).Sum
            """,
            30m);

    [Theory]
    [InlineData("(Values...7).Sum")]
    [InlineData("(Values ...7).Sum")]
    public void DotCall_SequenceSpreadReceiverBindsTopLevelVariadicFirstParameter(string call)
        => AssertEval(
            $$"""
            Values = 10, 20
            Sum(values...) = values.sum
            Output = {{call}}
            """,
            call.Contains('7', StringComparison.Ordinal) ? 37m : 30m);

    // `(Pair...)` spreads the receiver items into the item supply, so
    // `Sum(values...)` binds [10, 20] and sums to 30.
    [Fact]
    public void DotCall_GroupSequenceSpreadReceiverBindsItemSupply()
        => AssertEval(
            """
            Pair = (10, 20)
            Sum(values...) = values.sum
            Output = (Pair...).Sum
            """,
            30m);

    [Theory]
    [InlineData("(Pair...7).Sum", 37)]
    public void DotCall_GroupSequenceSpreadReceiverBindsTopLevelVariadicFirstParameter(string call, decimal expected)
        => AssertEval(
            $$"""
            Pair = (10, 20)
            Sum(values...) = values.sum
            Output = {{call}}
            """,
            expected);

    [Fact]
    public void DotCall_SequenceSpreadReceiverDoesNotSpreadIntoFixedParameters()
        => AssertArityFailure(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Output = (Pair...).Add
            """);

    [Fact]
    public void SemicolonSyntax_ReportsUnsupportedExpressionSeparator()
    {
        var parseResult = Parser.ParseSyntax("1; 2");

        Assert.True(parseResult.HasErrors);
        Assert.Contains(parseResult.Diagnostics, diagnostic => diagnostic.Message.Contains("Semicolon is not supported as an expression separator", StringComparison.Ordinal));
    }

    [Fact]
    public void PostfixSequenceSpreadInsideSequenceValueArgument_SpreadsImmediateExpressionOnly()
    {
        AssertEval(
            """
            a = 1
            b = 2, 3
            X(values...) = values.count

            X((a, b...))
            """,
            3m);

        AssertEval(
            """
            a = 1
            b = 2, 3
            X(values...) = values.count

            X((a, (b...)))
            """,
            2m);
    }

    // ── Empty spread (zero-item) and the spread-vs-variadic-capture distinction ──

    [Fact]
    public void SequenceSpread_PreferredSemantics_OpensSequenceValueIntoSlots()
    {
        AssertEval("(1, 2, 3)...", 1m, 2m, 3m); // contributes 1, 2, 3
        AssertEval("(1)...", 1m);               // contributes 1
        AssertEval("()...");                    // contributes zero items
    }

    [Fact]
    public void SequenceSpread_OfEmpty_ContributesZeroItemsInContext()
        => AssertEval("1, ()..., 2", 1m, 2m);

    [Fact]
    public void SequenceSpread_VersusVariadicCapture_AreDistinct()
    {
        // Definition side: `values...` is a VARIADIC (rest) CAPTURE — NOT a spread.
        // A named sequence value is still supplied as one call argument; the rest-only
        // capture plus the builtin `sum(values)` can display the same result as an
        // explicit spread, so fixed and mixed signatures are the boundary proof.
        const string variadicDef = """
            Sum(values...) = sum(values)
            Vals = (1, 2, 3)
            Sum(Vals)
            """;
        AssertEval(variadicDef, 6m);

        var defRoot = Parser.ParseSyntax(variadicDef).Root;
        var sum = Assert.IsType<Algorithm.User>(defRoot.Properties.Single(property => property.Name == "Sum").Value);
        var capture = Assert.IsType<CaptureParameterPattern>(Assert.Single(sum.ParameterPatterns));
        Assert.Equal(ParameterKind.Variadic, capture.Kind);

        // Use site: `Pair...` is a SPREAD expression (Expr.SequenceSpread) that opens
        // a multi-output into a fixed-arity call's argument slots.
        const string useSiteSpread = """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair...)
            """;
        AssertEval(useSiteSpread, 30m);

        var useRoot = Parser.ParseSyntax(useSiteSpread).Root;
        var call = Assert.IsType<Expr.Call>(useRoot.Output[^1]);
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args.Output));
        Assert.Equal("Pair", Assert.IsType<Expr.Resolve>(spread.Operand).Name);
    }
}
