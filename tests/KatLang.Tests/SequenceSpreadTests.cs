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
            Add(Pair.spread)
            """,
            30m);

    [Fact]
    public void BasicSequenceSpread_SequenceValueSpreadsSequenceValueItems()
        => AssertEval(
            """
            Pair = (10, 20)
            Add(x, y) = x + y
            Add(Pair.spread)
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
            Use(1, Tail.spread)
            """,
            6m);

    [Fact]
    public void MultipleSequenceSpreadSegments_SpreadAroundNormalArgument()
        => AssertEval(
            """
            Head = 1, 2
            Tail = 4, 5
            Use(a, b, c, d, e) = a + b + c + d + e
            Use(Head.spread, 3, Tail.spread)
            """,
            15m);

    [Fact]
    public void LineEndingPostfixEllipsis_DoesNotContinueSequenceSpreadForFixedCall()
        // Inside the open call-argument list a newline separates slots, so the
        // call sees two argument slots `A.spread` and `A` — not a continued spread
        // A.spread A and not four call arguments.
        => AssertArityFailure(
            """
            A = 1, 2
            Sum4(a, b, c, d) = a + b + c + d
            Sum4(A.spread
            A)
            """);

    [Fact]
    public void LineEndingPostfixEllipsisWithExplicitComma_KeepsNextLineAsSeparateArgument()
        => AssertEval(
            """
            A = 1, 2
            Use(a, b, c) = a + b + c.count
            Use(A.spread,
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
            A...)
            """);

    // A spread expression never consumes a following binary operator, so an opened
    // item supply cannot be a binary operand. `A.spread == A.spread` is a parse error
    // rather than an elementwise comparison — structural `==`/`!=` operate on whole
    // values, never on opened item supplies. Compare regrouped values with `(A.spread) == A`.
    [Fact]
    public void PostfixEllipsisFollowedByEqualityOperator_IsParseError()
        => AssertParseFailure(
            """
            A = 1, 2
            A.spread == A.spread
            """);

    [Fact]
    public void CallEndingAfterInnerPostfixEllipsis_FollowingLineStartsSeparateOutput()
        => AssertEval(
            """
            A = 1, 2
            F(x, y) = x + y
            F(A.spread)
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
            F(A.spread) // the line ends with the call, not the inner ellipsis
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
            (A.spread)
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

    // `Values.spread 7` is not a binary spread: a spread expression takes no
    // right operand, so it parses as the expression list `Values.spread, 7` =
    // three slots [10, 20, 7], bound by the item-supply matcher (sum 37).
    // Same-line whitespace before `.spread` stays a postfix continuation.
    [Theory]
    [InlineData("Sum(Values.spread 7)")]
    [InlineData("Sum(Values .spread 7)")]
    [InlineData("Sum(spread(Values) 7)")]
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
        // Sum(values..., val) is a comma deconstruction parameter list. Values.spread
        // spreads into [10, 20] and 7 fills the suffix, so the variadic captures
        // [10, 20] (sum 30) and val binds 7: 30 + 7 = 37.
        => AssertEval(
            """
            Values = 10, 20
            Sum(values..., val) = values.sum + val
            Sum(Values.spread, 7)
            """,
            37m);

    [Fact]
    public void VariadicSuffixBinding_NormalArgumentIsOneCollectedItem()
        // The plain argument is one supplied slot: the variadic parameter collects the
        // one-element list [(10, 20)], so the numeric `.sum` fails on the
        // sequence-valued element. The spread segment form above supplies
        // the items.
        => AssertEvaluationFailure(
            """
            Values = 10, 20
            Sum(values..., val) = values.sum + val
            Sum(Values, 7)
            """);

    [Fact]
    public void VariadicSuffixBinding_NormalArgumentPreservesSingleGroupedValue()
        // One grouped sequence-value argument is not implicitly opened for a
        // mixed variadic call; val receives the sequence value and the numeric
        // body fails. Use Values.spread to spread it explicitly.
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
    public void VariadicSuffixBinding_DotCallReceiverWithSuffixIsOneCollectedItem()
        // The receiver is one leading argument (Sum(Values, 7)), so the variadic parameter
        // collects [(10, 20)] and the numeric body fails exactly like the
        // canonical call above.
        => AssertEvaluationFailure(
            """
            Values = 10, 20
            Sum(values..., val) = values.sum + val
            Values.Sum(7)
            """);

    [Fact]
    public void VariadicSuffixBinding_ExplicitSpreadCanSatisfySuffixWhenSlotCountMatches()
        => AssertEval(
            """
            Values = 10, 20
            Sum(values..., val) = values.sum + val
            Sum(Values.spread)
            """,
            30m);

    [Fact]
    public void SingleVariadic_QmeanSpreadCallSucceedsWhileGroupedCallFails()
    {
        // Vector is the exact list [1..10]. The plain call collects it as one
        // non-numeric element, so the numeric body fails; explicit spread
        // supplies the ten items.
        AssertEvaluationFailure(
            """
            Vector = range(1, 10)
            Qmean(args...) = Math.Sqrt(args.map{x * x}.sum / args.count)
            Qmean(Vector)
            """);

        AssertEval(
            """
            Vector = range(1, 10)
            Qmean(args...) = Math.Sqrt(args.map{x * x}.sum / args.count)
            Qmean(Vector.spread) == Math.Sqrt(385 / 10)
            """,
            1m);
    }

    [Fact]
    public void SingleVariadic_QmeanSpreadDotCallMatchesSpreadCall()
        => AssertEval(
            """
            Vector = range(1, 10)
            Qmean(args...) = Math.Sqrt(args.map{x * x}.sum / args.count)
            (Vector.spread).Qmean() == Qmean(Vector.spread)
            """,
            1m);

    [Fact]
    public void SingleVariadic_MultiOutputPropertyIsOneCollectedItem()
        => AssertEval(
            """
            Values = 10, 20
            Count(args...) = args.count
            Count(Values)
            """,
            1m);

    [Fact]
    public void SingleVariadic_VisibleGroupIsOneCollectedItem()
        => AssertEval(
            """
            Pair = (10, 20)
            Count(args...) = args.count
            Count(Pair)
            """,
            1m);

    [Fact]
    public void SingleVariadic_DotCallVisibleGroupIsOneCollectedItem()
        => AssertEval(
            """
            Pair = (10, 20)
            Count(args...) = args.count
            Pair.Count()
            """,
            1m);

    [Fact]
    public void FlatFixedCall_DotCallReceiverDoesNotImplicitlySpreadMultiOutputProperty()
        => AssertArityFailure(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Pair.Add
            """);

    [Fact]
    public void VariadicParameterForwarding_DirectCallForwardsStreamWithExplicitSpread()
        // Forwarding a collected list's ITEMS is explicit spread at the forwarding
        // call (and the root call supplies the stream by spreading too); a bare
        // `CountItem(values, 1)` would pass the whole collected list as one
        // argument.
        => AssertEval(
            """
            CountItem(values..., item) = values.filter{value == item}.count
            Use(values...) = CountItem(values.spread, 1)
            Use((1, 1, 2, 4, 4).spread)
            """,
            2m);

    [Fact]
    public void VariadicParameterForwarding_CallbackBodyForwardsStreamWithExplicitSpread()
        => AssertEval(
            """
            CountItem(values..., item) = values.filter{value == item}.count

            Mode(values...) = {
                Freqs = values.distinct.map{CountItem(values.spread, candidate)}
                Freqs
            }

            Mode((1, 1, 2, 4, 4).spread)
            """,
            2m, 1m, 2m);

    [Fact]
    public void VariadicParameterForwarding_FullModeExampleForwardsStreamWithExplicitSpread()
        => AssertEval(
            """
            CountItem(values..., item) = values.filter{value == item}.count

            Mode(values...) = {
                Freqs = values.distinct.map{CountItem(values.spread, candidate)}
                MaxFreq = Freqs.max

                values.distinct.filter{CountItem(values.spread, candidate) == MaxFreq}
            }

            Mode((1, 1, 2, 4, 4).spread)
            """,
            1m, 4m);

    [Fact]
    public void VariadicParameterForwarding_NonVariadicCalleeReceivesOneListValue()
        // Passing the collected list bare hands the callee the whole collected
        // list as ONE argument; the fixed parameter's collection view then
        // counts its three elements.
        => AssertEval(
            """
            Collect(list) = list.count
            Use(values...) = Collect(values)
            Use((10, 20, 30).spread)
            """,
            3m);

    [Fact]
    public void VariadicParameterForwarding_TopLevelVariadicCalleeReceivesStreamViaSpread()
        => AssertEval(
            """
            Collect(list...) = list.count
            Use(values...) = Collect(values.spread)
            Use((10, 20, 30).spread)
            """,
            3m);

    [Fact]
    public void VariadicParameterForwarding_TopLevelCaptureRoundTripsThroughSpread()
        // Round trip: the callee's variadic parameter re-collects exactly the caller's items.
        => AssertEval(
            """
            CountItems(items...) = items.count
            Use(values...) = CountItems(values.spread)
            Use((1, 2, 3).spread)
            """,
            3m);

    [Fact]
    public void VariadicParameterForwarding_SequenceValueVariadicPatternOpensForwardedList()
        // The pattern callee wants ONE grouped value, so the collected list is
        // passed bare and the sequence-value pattern opens its one boundary.
        => AssertEval(
            """
            CountSequenceValue((values...)) = values.count
            Use(values...) = CountSequenceValue(values)
            Use((10, 20, 30).spread)
            """,
            3m);

    [Fact]
    public void VariadicParameterForwarding_SequenceValueVariadicCaptureForwardsStreamWithExplicitSpread()
        => AssertEval(
            """
            FindNext(history..., pre1, pre2) = history.count + pre1 + pre2
            YSStep((history...), pre2, pre1) = FindNext(history.spread, pre1, pre2)
            YSStep((1, 2, 3), 2, 3)
            """,
            8m);

    [Fact]
    public void VariadicParameterForwarding_SequenceValueCaptureForwardsStreamWithExplicitSpread()
        => AssertEval(
            """
            CountItems(items...) = items.count
            Use((history...)) = CountItems(history.spread)
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
    public void VariadicParameterForwarding_ExplicitSpreadForwardsRegardlessOfName()
        // Explicit spread forwards the capture's items whatever the callee's
        // parameter is called — no name matching is involved.
        => AssertEval(
            """
            CountItems(items..., last) = items.count + last
            Use((history...), last) = CountItems(history.spread, last)
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
    public void VariadicParameterForwarding_LoopStepSequenceValueVariadicCaptureForwardsStreamWithExplicitSpread()
        => AssertEval(
            """
            FindNext(history..., pre1, pre2) = history.count + pre1 + pre2
            YSStep((history...), pre2, pre1) = FindNext(history.spread, pre1, pre2), pre1, pre2
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
    public void SequenceBuiltin_SpreadFollowsOrdinaryFixedArity()
    {
        // Spread has only its ordinary meaning: `Values.spread` opens to two
        // argument slots, over-supplying the fixed count(collection) — an
        // ordinary arity error. Grouping the spread back into one collection
        // argument is the valid rewrite.
        AssertArityFailure(
            """
            Values = 10, 20
            count(Values.spread)
            """);
        AssertEval(
            """
            Values = 10, 20
            count((Values.spread))
            """,
            2m);
    }

    [Fact]
    public void SequenceBuiltin_NumericNormalArgumentConsumesSequenceValue()
        => AssertEval(
            """
            Values = 10, 20
            sum(Values)
            """,
            30m);

    [Fact]
    public void SequenceBuiltin_NumericSpreadFollowsOrdinaryFixedArity()
    {
        // Same rule for the numeric reducers: sum(Values.spread) supplies two
        // arguments to the fixed sum(collection); the grouped form is valid.
        AssertArityFailure(
            """
            Values = 10, 20
            sum(Values.spread)
            """);
        AssertEval(
            """
            Values = 10, 20
            sum((Values.spread))
            """,
            30m);
    }

    [Fact]
    public void FixedBuiltin_ExplicitSpreadProvidesArguments()
        => AssertEval(
            """
            Bounds = 1, 3
            range(Bounds.spread)
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
    [InlineData("A = 1.spread, { 2, 3 }")]
    [InlineData("A = spread(1), { 2, 3 }")]
    public void NonCallResultContext_SequenceSpreadSpreadsNestedBlockOutput(string definition)
        => AssertEval(
            $$"""
            {{definition}}
            A
            """,
            1m, 2m, 3m);

    // `(Values.spread)` spreads the receiver into the item supply, so `Sum(values.spread)`
    // binds [10, 20] and sums to 30.
    [Fact]
    public void DotCall_ExplicitSequenceSpreadReceiverBindsItemSupply()
        => AssertEval(
            """
            Values = 10, 20
            Sum(values...) = values.sum
            Output = (Values.spread).Sum
            """,
            30m);

    // `(Values.spread 7)` materializes ONE sequence value (10, 20, 7): unlike the lone
    // `(Values.spread)` spread receiver it is an ordinary grouped receiver, so the
    // variadic parameter collects [(10, 20, 7)] and the numeric body fails. Re-spreading the
    // group — `((Values.spread 7).spread)` — supplies the items.
    [Theory]
    [InlineData("(Values.spread 7).Sum")]
    [InlineData("(spread(Values) 7).Sum")]
    public void DotCall_SpreadJoinGroupReceiver_IsOneCollectedItem(string call)
        => AssertEvaluationFailure(
            $$"""
            Values = 10, 20
            Sum(values...) = values.sum
            Output = {{call}}
            """);

    [Fact]
    public void DotCall_RespreadSpreadJoinGroupReceiver_SuppliesItems()
        => AssertEval(
            """
            Values = 10, 20
            Sum(values...) = values.sum
            Output = ((Values.spread 7).spread).Sum
            """,
            37m);

    // `(Pair.spread)` spreads the receiver items into the item supply, so
    // `Sum(values.spread)` binds [10, 20] and sums to 30.
    [Fact]
    public void DotCall_GroupSequenceSpreadReceiverBindsItemSupply()
        => AssertEval(
            """
            Pair = (10, 20)
            Sum(values...) = values.sum
            Output = (Pair.spread).Sum
            """,
            30m);

    [Fact]
    public void DotCall_GroupSpreadJoinReceiver_IsOneCollectedItem()
    {
        // Same rule for a sequence-valued source: `(Pair.spread 7)` is one grouped
        // receiver argument, so the variadic parameter collects [(10, 20, 7)] and the numeric
        // body fails; re-spreading the group supplies the items.
        AssertEvaluationFailure(
            """
            Pair = (10, 20)
            Sum(values...) = values.sum
            Output = (Pair.spread 7).Sum
            """);

        AssertEval(
            """
            Pair = (10, 20)
            Sum(values...) = values.sum
            Output = ((Pair.spread 7).spread).Sum
            """,
            37m);
    }

    [Fact]
    public void DotCall_SequenceSpreadReceiverDoesNotSpreadIntoFixedParameters()
        => AssertArityFailure(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Output = (Pair.spread).Add
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
        // The inner `.spread` binds to `b` only: `(a, b.spread)` is (1, 2, 3) while
        // `(a, (b.spread))` is (1, (2, 3)). Spreading the outer group at the call
        // exposes the distinct item counts through the collecting binding.
        AssertEval(
            """
            a = 1
            b = 2, 3
            X(values...) = values.count

            X((a, b.spread).spread)
            """,
            3m);

        AssertEval(
            """
            a = 1
            b = 2, 3
            X(values...) = values.count

            X((a, (b.spread)).spread)
            """,
            2m);
    }

    // ── Empty spread (zero-item) and the spread-vs-variadic-capture distinction ──

    [Fact]
    public void SequenceSpread_PreferredSemantics_OpensSequenceValueIntoSlots()
    {
        AssertEval("(1, 2, 3).spread", 1m, 2m, 3m); // contributes 1, 2, 3
        AssertEval("(1).spread", 1m);               // contributes 1
        AssertEval("().spread");                    // contributes zero items
    }

    [Fact]
    public void SequenceSpread_OfEmpty_ContributesZeroItemsInContext()
        => AssertEval("1, ().spread, 2", 1m, 2m);

    [Fact]
    public void SequenceSpread_VersusVariadicCapture_AreDistinct()
    {
        // Definition side: `values...` is a VARIADIC PARAMETER — NOT a spread.
        // The call-site spread supplies Vals's items as the collected list
        // [1, 2, 3]; a bare `Sum(Vals)` would collect [(1, 2, 3)] whose element
        // is non-numeric.
        const string variadicDef = """
            Sum(values...) = sum(values)
            Vals = (1, 2, 3)
            Sum(Vals.spread)
            """;
        AssertEval(variadicDef, 6m);

        var defRoot = Parser.ParseSyntax(variadicDef).Root;
        var sum = Assert.IsType<Algorithm.User>(defRoot.Properties.Single(property => property.Name == "Sum").Value);
        var capture = Assert.IsType<CaptureParameterPattern>(Assert.Single(sum.ParameterPatterns));
        Assert.Equal(ParameterKind.Variadic, capture.Kind);

        // Use site: `Pair.spread` is a SPREAD expression (Expr.SequenceSpread) that opens
        // a multi-output into a fixed-arity call's argument slots.
        const string useSiteSpread = """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair.spread)
            """;
        AssertEval(useSiteSpread, 30m);

        var useRoot = Parser.ParseSyntax(useSiteSpread).Root;
        var call = Assert.IsType<Expr.Call>(useRoot.Output[^1]);
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args.Output));
        Assert.Equal("Pair", Assert.IsType<Expr.Resolve>(spread.Operand).Name);
    }
}
