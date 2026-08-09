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

        return Evaluator.RunFlat(new Expr.AlgorithmExpr(parseResult.Root));
    }

    private static EvalResult<Result> EvalFull(string source)
    {
        var parseResult = Parser.Parse(source);
        if (parseResult.HasErrors)
        {
            var message = string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message));
            Assert.Fail($"Expected parse success but got diagnostics:{Environment.NewLine}{message}");
        }

        return Evaluator.Run(new Expr.AlgorithmExpr(parseResult.Root));
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
            Add(Pair*)
            """,
            30m);

    [Fact]
    public void BasicSequenceSpread_SequenceValueSpreadsSequenceValueItems()
        => AssertEval(
            """
            Pair = (10, 20)
            Add(x, y) = x + y
            Add(Pair*)
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
            Use(1, Tail*)
            """,
            6m);

    [Fact]
    public void MultipleSequenceSpreadSegments_SpreadAroundNormalArgument()
        => AssertEval(
            """
            Head = 1, 2
            Tail = 4, 5
            Use(a, b, c, d, e) = a + b + c + d + e
            Use(Head*, 3, Tail*)
            """,
            15m);

    [Fact]
    public void LineEndingAttachedStar_DoesNotContinueSequenceSpreadForFixedCall()
        // A line-ending attached `A*` is a spread; inside the open
        // call-argument list the newline separates slots, so the call sees the
        // two argument slots `A*` and `A` — three supplied arguments after
        // spreading, not four.
        => AssertArityFailure(
            """
            A = 1, 2
            Sum4(a, b, c, d) = a + b + c + d
            Sum4(A*
            A)
            """);

    [Fact]
    public void LineEndingSpreadWithExplicitComma_KeepsNextLineAsSeparateArgument()
        => AssertEval(
            """
            A = 1, 2
            Use(a, b, c) = a + b + c.count
            Use(A*,
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

    // A spread expression is never a binary operand: `A* == A*` is a targeted
    // misplaced-spread parse error rather than an elementwise comparison —
    // structural `==`/`!=` operate on whole values, never on opened item
    // supplies. Compare regrouped values with `(A*) == A`.
    [Fact]
    public void SpreadFollowedByEqualityOperator_IsParseError()
        => AssertParseFailure(
            """
            A = 1, 2
            A* == A*
            """);

    [Fact]
    public void CallEndingAfterInnerSpread_FollowingLineStartsSeparateOutput()
        => AssertEval(
            """
            A = 1, 2
            F(x, y) = x + y
            F(A*)
            9
            """,
            3m,
            9m);

    [Fact]
    public void CallEndingAfterInnerSpreadWithTrailingComment_FollowingLineStartsSeparateOutput()
        => AssertEval(
            """
            A = 1, 2
            F(x, y) = x + y
            F(A*) # the line ends with the call, not the inner spread marker
            9
            """,
            3m,
            9m);

    [Fact]
    public void ParenthesizedSpread_FollowingLineStartsSeparateOutput()
    {
        var result = EvalFull(
            """
            A = 1, 2
            (A*)
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

    // `Values* 7` would be multiplication (a same-line right operand after the
    // star), so the spread-plus-item supply needs the explicit comma:
    // `Sum(Values*, 7)` is the expression list of three slots [10, 20, 7],
    // bound by the item-supply matcher (sum 37).
    [Fact]
    public void SpreadThenCommaSlotInsideCall_BindsItemSupply()
        => AssertEval(
            """
            Values = 10, 20
            Sum(*values) = values.sum
            Sum(Values*, 7)
            """,
            37m);

    [Fact]
    public void VariadicSuffixBinding_CommaSeparatedSpreadSegmentBindsByDeconstruction()
        // Sum(*values, val) is a comma deconstruction parameter list. Values*
        // spreads into [10, 20] and 7 fills the suffix, so the collecting
        // parameter captures [10, 20] (sum 30) and val binds 7: 30 + 7 = 37.
        => AssertEval(
            """
            Values = 10, 20
            Sum(*values, val) = values.sum + val
            Sum(Values*, 7)
            """,
            37m);

    [Fact]
    public void VariadicSuffixBinding_NormalArgumentIsOneCollectedItem()
        // The plain argument is one supplied slot: the collecting parameter
        // collects the one-element list [(10, 20)], so the numeric `.sum`
        // fails on the sequence-valued element. The spread segment form above
        // supplies the items.
        => AssertEvaluationFailure(
            """
            Values = 10, 20
            Sum(*values, val) = values.sum + val
            Sum(Values, 7)
            """);

    [Fact]
    public void VariadicSuffixBinding_NormalArgumentPreservesSingleGroupedValue()
        // One grouped sequence-value argument is not implicitly opened for a
        // mixed variadic call; val receives the sequence value and the numeric
        // body fails. Use Values* to spread it explicitly.
        => AssertEvaluationFailure(
            """
            Values = 10, 20
            Sum(*values, val) = values.sum + val
            Sum(Values)
            """);

    [Fact]
    public void VariadicSuffixBinding_DotCallReceiverPreservesSingleGroupedValue()
        => AssertEvaluationFailure(
            """
            Values = 10, 20
            Sum(*values, val) = values.sum + val
            Values.Sum
            """);

    [Fact]
    public void VariadicSuffixBinding_DotCallReceiverWithSuffixIsOneCollectedItem()
        // The receiver is one leading argument (Sum(Values, 7)), so the
        // collecting parameter collects [(10, 20)] and the numeric body fails
        // exactly like the canonical call above.
        => AssertEvaluationFailure(
            """
            Values = 10, 20
            Sum(*values, val) = values.sum + val
            Values.Sum(7)
            """);

    [Fact]
    public void VariadicSuffixBinding_ExplicitSpreadCanSatisfySuffixWhenSlotCountMatches()
        => AssertEval(
            """
            Values = 10, 20
            Sum(*values, val) = values.sum + val
            Sum(Values*)
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
            Qmean(*args) = Math.Sqrt(args.map{x * x}.sum / args.count)
            Qmean(Vector)
            """);

        AssertEval(
            """
            Vector = range(1, 10)
            Qmean(*args) = Math.Sqrt(args.map{x * x}.sum / args.count)
            Qmean(Vector*) == Math.Sqrt(385 / 10)
            """,
            1m);
    }

    [Fact]
    public void SingleVariadic_QmeanSpreadDotCallMatchesSpreadCall()
        => AssertEval(
            """
            Vector = range(1, 10)
            Qmean(*args) = Math.Sqrt(args.map{x * x}.sum / args.count)
            (Vector*).Qmean() == Qmean(Vector*)
            """,
            1m);

    [Fact]
    public void SingleVariadic_MultiOutputPropertyIsOneCollectedItem()
        => AssertEval(
            """
            Values = 10, 20
            Count(*args) = args.count
            Count(Values)
            """,
            1m);

    [Fact]
    public void SingleVariadic_VisibleGroupIsOneCollectedItem()
        => AssertEval(
            """
            Pair = (10, 20)
            Count(*args) = args.count
            Count(Pair)
            """,
            1m);

    [Fact]
    public void SingleVariadic_DotCallVisibleGroupIsOneCollectedItem()
        => AssertEval(
            """
            Pair = (10, 20)
            Count(*args) = args.count
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
    public void CollectingParameterForwarding_DirectCallForwardsStreamWithExplicitSpread()
        // Forwarding a collected list's ITEMS is explicit spread at the forwarding
        // call (and the root call supplies the stream by spreading too); a bare
        // `CountItem(values, 1)` would pass the whole collected list as one
        // argument.
        => AssertEval(
            """
            CountItem(*values, item) = values.filter{value == item}.count
            Use(*values) = CountItem(values*, 1)
            Use((1, 1, 2, 4, 4)*)
            """,
            2m);

    [Fact]
    public void CollectingParameterForwarding_CallbackBodyForwardsStreamWithExplicitSpread()
        => AssertEval(
            """
            CountItem(*values, item) = values.filter{value == item}.count

            Mode(*values) = {
                Freqs = values.distinct.map{CountItem(values*, candidate)}
                Freqs
            }

            Mode((1, 1, 2, 4, 4)*)
            """,
            2m, 1m, 2m);

    [Fact]
    public void CollectingParameterForwarding_FullModeExampleForwardsStreamWithExplicitSpread()
        => AssertEval(
            """
            CountItem(*values, item) = values.filter{value == item}.count

            Mode(*values) = {
                Freqs = values.distinct.map{CountItem(values*, candidate)}
                MaxFreq = Freqs.max

                values.distinct.filter{CountItem(values*, candidate) == MaxFreq}
            }

            Mode((1, 1, 2, 4, 4)*)
            """,
            1m, 4m);

    [Fact]
    public void CollectingParameterForwarding_NonVariadicCalleeReceivesOneListValue()
        // Passing the collected list bare hands the callee the whole collected
        // list as ONE argument; the fixed parameter's collection view then
        // counts its three elements.
        => AssertEval(
            """
            Collect(list) = list.count
            Use(*values) = Collect(values)
            Use((10, 20, 30)*)
            """,
            3m);

    [Fact]
    public void CollectingParameterForwarding_TopLevelVariadicCalleeReceivesStreamViaSpread()
        => AssertEval(
            """
            Collect(*list) = list.count
            Use(*values) = Collect(values*)
            Use((10, 20, 30)*)
            """,
            3m);

    [Fact]
    public void CollectingParameterForwarding_TopLevelCaptureRoundTripsThroughSpread()
        // Round trip: the callee's collecting parameter re-collects exactly the
        // caller's items.
        => AssertEval(
            """
            CountItems(*items) = items.count
            Use(*values) = CountItems(values*)
            Use((1, 2, 3)*)
            """,
            3m);

    [Fact]
    public void CollectingParameterForwarding_SequenceValueVariadicPatternOpensForwardedList()
        // The pattern callee wants ONE grouped value, so the collected list is
        // passed bare and the sequence-value pattern opens its one boundary.
        => AssertEval(
            """
            CountSequenceValue((*values)) = values.count
            Use(*values) = CountSequenceValue(values)
            Use((10, 20, 30)*)
            """,
            3m);

    [Fact]
    public void CollectingParameterForwarding_SequenceValueCollectingCaptureForwardsStreamWithExplicitSpread()
        => AssertEval(
            """
            FindNext(*history, pre1, pre2) = history.count + pre1 + pre2
            YSStep((*history), pre2, pre1) = FindNext(history*, pre1, pre2)
            YSStep((1, 2, 3), 2, 3)
            """,
            8m);

    [Fact]
    public void CollectingParameterForwarding_SequenceValueCaptureForwardsStreamWithExplicitSpread()
        => AssertEval(
            """
            CountItems(*items) = items.count
            Use((*history)) = CountItems(history*)
            Use((1, 2, 3))
            """,
            3m);

    [Fact]
    public void SequenceValueVariadicCalleeBoundary_DoesNotUseFlatSlotSpread()
        => AssertEval(
            """
            CountSequenceValue((*items)) = items.count
            Pair = 10, 20
            CountSequenceValue(Pair)
            """,
            2m);

    [Fact]
    public void CollectingParameterForwarding_ExplicitSpreadForwardsRegardlessOfName()
        // Explicit spread forwards the capture's items whatever the callee's
        // parameter is called — no name matching is involved.
        => AssertEval(
            """
            CountItems(*items, last) = items.count + last
            Use((*history), last) = CountItems(history*, last)
            Use((10, 20, 30), 7)
            """,
            10m);

    [Fact]
    public void CollectingParameterForwarding_SequenceValueCollectingCaptureKeepsNonVariadicCalleeBoundary()
        => AssertEval(
            """
            Collect(list) = list.count
            Use((*history), marker) = Collect(history)
            Use((10, 20, 30), 99)
            """,
            3m);

    [Fact]
    public void CollectingParameterForwarding_SequenceValueCollectingCaptureOnlyExpandsInTargetVariadicSlot()
        => AssertEval(
            """
            TakeLast(*first, last) = first.count
            Use((*history), marker) = TakeLast(0, history)
            Use((10, 20, 30), 99)
            """,
            1m);

    [Fact]
    public void CollectingParameterForwarding_LoopStepSequenceValueCollectingCaptureForwardsStreamWithExplicitSpread()
        => AssertEval(
            """
            FindNext(*history, pre1, pre2) = history.count + pre1 + pre2
            YSStep((*history), pre2, pre1) = FindNext(history*, pre1, pre2), pre1, pre2
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
        // Spread has only its ordinary meaning: `Values*` opens to two
        // argument slots, over-supplying the fixed count(collection) — an
        // ordinary arity error. Grouping the spread back into one collection
        // argument is the valid rewrite.
        AssertArityFailure(
            """
            Values = 10, 20
            count(Values*)
            """);
        AssertEval(
            """
            Values = 10, 20
            count((Values*))
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
        // Same rule for the numeric reducers: sum(Values*) supplies two
        // arguments to the fixed sum(collection); the grouped form is valid.
        AssertArityFailure(
            """
            Values = 10, 20
            sum(Values*)
            """);
        AssertEval(
            """
            Values = 10, 20
            sum((Values*))
            """,
            30m);
    }

    [Fact]
    public void FixedBuiltin_ExplicitSpreadProvidesArguments()
        => AssertEval(
            """
            Bounds = 1, 3
            range(Bounds*)
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

    [Fact]
    public void NonCallResultContext_SequenceSpreadSpreadsNestedBlockOutput()
        => AssertEval(
            """
            A = 1*, { 2, 3 }
            A
            """,
            1m, 2m, 3m);

    // `(Values*).Sum` is the parenthesized spread receiver: the receiver's
    // items feed the leading flat collecting parameter, so `values` collects
    // [10, 20] and sums to 30.
    [Fact]
    public void DotCall_ExplicitSequenceSpreadReceiverBindsItemSupply()
        => AssertEval(
            """
            Values = 10, 20
            Sum(*values) = values.sum
            (Values*).Sum
            """,
            30m);

    // `(Values*, 7)` materializes ONE sequence value (10, 20, 7): unlike the
    // lone `(Values*)` spread receiver it is an ordinary grouped receiver, so
    // the collecting parameter collects [(10, 20, 7)] and the numeric body
    // fails. Re-spreading the group — `((Values*, 7)*)` — supplies the items.
    // (`Values* 7` without the comma would be multiplication.)
    [Fact]
    public void DotCall_SpreadJoinGroupReceiver_IsOneCollectedItem()
        => AssertEvaluationFailure(
            """
            Values = 10, 20
            Sum(*values) = values.sum
            (Values*, 7).Sum
            """);

    [Fact]
    public void DotCall_RespreadSpreadJoinGroupReceiver_SuppliesItems()
        => AssertEval(
            """
            Values = 10, 20
            Sum(*values) = values.sum
            ((Values*, 7)*).Sum
            """,
            37m);

    // `(Pair*)` spreads the receiver items into the item supply, so the
    // collecting parameter binds [10, 20] and sums to 30.
    [Fact]
    public void DotCall_GroupSequenceSpreadReceiverBindsItemSupply()
        => AssertEval(
            """
            Pair = (10, 20)
            Sum(*values) = values.sum
            (Pair*).Sum
            """,
            30m);

    [Fact]
    public void DotCall_GroupSpreadJoinReceiver_IsOneCollectedItem()
    {
        // Same rule for a sequence-valued source: `(Pair*, 7)` is one grouped
        // receiver argument, so the collecting parameter collects
        // [(10, 20, 7)] and the numeric body fails; re-spreading the group
        // supplies the items.
        AssertEvaluationFailure(
            """
            Pair = (10, 20)
            Sum(*values) = values.sum
            (Pair*, 7).Sum
            """);

        AssertEval(
            """
            Pair = (10, 20)
            Sum(*values) = values.sum
            ((Pair*, 7)*).Sum
            """,
            37m);
    }

    [Fact]
    public void DotCall_SequenceSpreadReceiverDoesNotSpreadIntoFixedParameters()
        => AssertArityFailure(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            (Pair*).Add
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
        // The inner `*` binds to `b` only: `(a, b*)` is (1, 2, 3) while
        // `(a, (b*))` is (1, (2, 3)). Spreading the outer group at the call
        // exposes the distinct item counts through the collecting binding.
        AssertEval(
            """
            a = 1
            b = 2, 3
            X(*values) = values.count

            X((a, b*)*)
            """,
            3m);

        AssertEval(
            """
            a = 1
            b = 2, 3
            X(*values) = values.count

            X((a, (b*))*)
            """,
            2m);
    }

    // ── Empty spread (zero-item) and the spread-vs-collecting-capture distinction ──

    [Fact]
    public void SequenceSpread_PreferredSemantics_OpensSequenceValueIntoSlots()
    {
        AssertEval("(1, 2, 3)*", 1m, 2m, 3m); // contributes 1, 2, 3
        AssertEval("(1)*", 1m);               // contributes 1
        AssertEval("()*");                    // contributes zero items
    }

    [Fact]
    public void SequenceSpread_OfEmpty_ContributesZeroItemsInContext()
        => AssertEval("1, ()*, 2", 1m, 2m);

    [Fact]
    public void SequenceSpread_VersusCollectingCapture_AreDistinct()
    {
        // Definition side: `*values` is a COLLECTING PARAMETER — NOT a spread.
        // The call-site spread supplies Vals's items as the collected list
        // [1, 2, 3]; a bare `Sum(Vals)` would collect [(1, 2, 3)] whose element
        // is non-numeric.
        const string collectingDef = """
            Sum(*values) = sum(values)
            Vals = (1, 2, 3)
            Sum(Vals*)
            """;
        AssertEval(collectingDef, 6m);

        var defRoot = SourceProvenance.ParseSyntaxValidRoot(collectingDef);
        var sum = Assert.IsType<Algorithm.User>(defRoot.Properties.Single(property => property.Name == "Sum").Value);
        var capture = Assert.IsType<CaptureParameterPattern>(Assert.Single(sum.ParameterPatterns));
        Assert.Equal(ParameterKind.Collecting, capture.Kind);

        // Use site: `Pair*` is a SPREAD expression (Expr.SequenceSpread) that
        // opens a multi-output into a fixed-arity call's argument slots.
        const string useSiteSpread = """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair*)
            """;
        AssertEval(useSiteSpread, 30m);

        var useRoot = SourceProvenance.ParseSyntaxValidRoot(useSiteSpread);
        var call = Assert.IsType<Expr.Call>(useRoot.Output[^1]);
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args));
        Assert.Equal("Pair", Assert.IsType<Expr.Resolve>(spread.Operand).Name);
    }
}
