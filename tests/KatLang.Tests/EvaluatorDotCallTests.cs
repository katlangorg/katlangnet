using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorDotCallTests
{
    private static string YellowstoneSource(string finalExpression) =>
        $$"""
          GcdStep = b~, a mod b, a mod b != 0
          Gcd = GcdStep.while(a, b):1

          FindNext(*history, pre1, pre2) = {
              IsYSCandidate = not history.contains(candidate) and
                  Gcd(candidate, pre1) == 1 and Gcd(candidate, pre2) != 1
              FindStep = candidate + 1, not IsYSCandidate
              FindStep.while(1):0
          }
          YSStep((*history), pre2, pre1) = {
              Next = FindNext(history*, pre1, pre2)
              (history*, Next), pre1, Next
          }
          {{finalExpression}}
          """;

    [Fact]
    public void Eval_SequenceReceiverBoundary_NamedPropertyOutputsPreserveEmittedSlots()
    {
        AssertEval(
            """
            A = 1, 2, 3
            A.take(2)
            """,
            1,
            2);

        AssertEval(
            """
            A = 1, 2, 3
            A.count
            """,
            3);
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_NamedSequenceValuePropertyIsSequenceValue()
    {
        AssertEval(
            """
            A = (1, 2, 3)
            A.count
            """,
            3);

        var takeResult = EvalFull(
            """
            A = (1, 2, 3)
            A.take(2)
            """);

        if (takeResult.IsError)
            Assert.Fail($"Expected success but got error: {takeResult.Error}");

        AssertEval(
            """
            A = (1, 2, 3)
            A.take(2)
            """,
            1,
            2);
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_SequenceSpreadPropertyExposesSpreadSlots()
        => AssertEval(
            """
            A = 1*, 2*, 3
            A.take(2)
            """,
            1,
            2);

    [Fact]
    public void Eval_SequenceSpread_NamedSequenceValueOperandPreservesEmittedBoundary()
    {
        var result = EvalFull(
            """
            A = (1, 2)
            A*, 3
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertSequenceValueAtoms(result.Value, 1, 2, 3);
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_UserCallsPreserveEmittedSlots()
    {
        AssertEval(
            """
            F(x) = x, x + 1, x + 2
            F(1).count
            F(1).take(2)
            """,
            3,
            1,
            2);

        AssertEval(
            """
            G(x) = (x, x + 1, x + 2)
            G(1).count
            """,
            3);
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_ConditionalBranchesPreserveEmittedSlots()
    {
        AssertEval(
            """
            ChooseMulti(1) = 1, 2, 3
            ChooseMulti(x) = 4, 5, 6
            ChooseSequenceValue(1) = (1, 2, 3)
            ChooseSequenceValue(x) = (4, 5, 6)
            ChooseMulti(1).take(2)
            ChooseSequenceValue(1).count
            """,
            1,
            2,
            3);
    }

    [Fact]
    public void Eval_ParenthesizedSequenceSpread_PropertyEmitsOneSequenceValueResult()
    {
        var source = """
            A = 1, 2
            B = 3, 4
            Test = (A*, B)
            Test.count
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_ParenthesizedSequenceSpread_VariadicCallArgumentIsOneSequenceValue()
    {
        // `(A*, B)` materializes one sequence value (1, 2, (3, 4)), which the
        // call supplies as one argument: the collecting parameter collects [that value].
        var source = """
            A = 1, 2
            B = 3, 4
            F(*values) = values.count
            F((A*, B))
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_BareSequenceSpread_AdjacentExpressionBindsItemSupply()
    {
        // A*, B is three slots (1, 2, (3, 4)); F(*values) collects them as one
        // exact list of count 3.
        var source = """
            A = 1, 2
            B = 3, 4
            F(*values) = values.count
            F(A*, B)
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_UserDefinedVariadicDotCallReceiver_CountsTheReceiverAsOneItem()
    {
        // Dot-call passes a value: the receiver is the ONE leading argument of
        // `CountItems((1, 2))`, so the collecting parameter collects the one
        // sequence value, [(1, 2)]. Only the spread marker opens the receiver:
        // `(1, 2)*.CountItems` is `CountItems(1, 2)` and collects [1, 2].
        var source = """
            CountItems(*items) = items.count
            (1, 2).CountItems
            """;

        AssertEval(source, 1);
        AssertEval("CountItems(*items) = items.count\n(1, 2)*.CountItems", 2);
        AssertEval("CountItems(*items) = items.count\nCountItems((1, 2))", 1);
    }

    [Fact]
    public void Eval_UserDefinedVariadicDotCallReceiver_SpreadReceiverBindsItemsForBody()
    {
        // The fluent spread receiver supplies the receiver's items as ordinary
        // argument slots — `(1, 2)*.Mean` is `Mean(1, 2)` — so the collecting
        // parameter collects [1, 2] and the numeric body works. The
        // parenthesized spread `((1, 2)*)` is a CAPTURE receiver instead: one
        // sequence value, collected as [(1, 2)], whose sum is not numeric.
        var source = """
            Mean(*vector) = vector.sum
            (1, 2)*.Mean
            """;

        AssertEval(source, 3);
        AssertEvalFails("Mean(*vector) = vector.sum\n((1, 2)*).Mean");
    }

    [Fact]
    public void Eval_UserDefinedVariadicDotCallReceiver_PreservesSingleGroupedValueBeforeSuffixAllocation()
    {
        // The receiver is the only supplied argument of `Sum(Values)`: the
        // fixed suffix `last` binds it (the sequence (10, 20)), the collecting
        // parameter collects [], and the numeric body fails. Spread the
        // receiver — `Values*.Sum`, i.e. `Sum(Values*)` — to supply separate slots.
        var source = """
            Values = 10, 20
            Sum(*values, last) = values.sum + last
            Values.Sum
            """;

        AssertEvalFails(source);
    }

    // Dot-call receiver law: dot-call passes a value. For extension-call
    // fallback, `R.F(args)` assembles exactly the argument slots of
    // `F(R, args)`: the receiver is ONE ordinary leading argument whatever its
    // shape (a named property, an inline group `(1, 2, 3)`, a brace block, a
    // capture of a spread `(Values*)`, a selection, a call result), it never
    // satisfies arity by its item count, and a collecting parameter collects
    // it as ONE item. Only the spread marker opens a receiver: the fluent
    // `Values*.F(args)` is `F(Values*, args)`, whose spread items are ordinary
    // slots. Lean: CoreTests dot-call receiver guards.

    [Fact]
    public void Eval_SequenceValueReceiver_LeadingFlatVariadic_IsOneReceiverArgument()
    {
        // The receiver is the one leading argument of `NItems(Pair)`, so the
        // collecting parameter collects the one-element list [(10, 20)] — for
        // a named property, an inline group, or a brace-block receiver alike.
        var source = """
            NItems(*values) = values.count
            Pair = (10, 20)
            Pair.NItems
            """;

        AssertEval(source, 1);
        AssertEval("NItems(*values) = values.count\n(10, 20).NItems", 1);
        AssertEval("NItems(*values) = values.count\n{10, 20}.NItems", 1);
    }

    [Fact]
    public void Eval_SequenceValueReceiverSpread_FluentSpreadSuppliesSlots_CaptureIsOneValue()
    {
        // The fluent spread `Pair*.NItems` is `NItems(Pair*)`: the two spread
        // items are ordinary slots, collected as [10, 20] (count 2). The
        // parenthesized `(Pair*)` is a CAPTURE receiver — one sequence value
        // (10, 20) — so `(Pair*).NItems` is `NItems((Pair*))` and collects
        // [(10, 20)] (count 1).
        const string define = "NItems(*values) = values.count\nPair = (10, 20)\n";

        AssertEval(define + "Pair*.NItems", 2);
        AssertEval(define + "NItems(Pair*)", 2);
        AssertEval(define + "(Pair*).NItems", 1);
        AssertEval(define + "NItems((Pair*))", 1);
    }

    [Fact]
    public void Eval_SequenceValueReceiver_LeadingFlatVariadicWithSuffix_IsOneReceiverArgument()
    {
        // Two supplied arguments: the receiver and 99. The suffix binds 99 from
        // the back and the collecting parameter collects the one-element list [(10, 20)].
        var source = """
            BeforeLastCount(*values, last) = values.count
            Pair = (10, 20)
            Pair.BeforeLastCount(99)
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_SequenceValueReceiverSpreadWithSuffix_FluentSpreadSuppliesSlots_CaptureIsOneValue()
    {
        // `Pair*.BeforeLastCount(99)` is `BeforeLastCount(10, 20, 99)`: the
        // fixed suffix `last` binds 99 from the back and the collecting
        // parameter collects [10, 20] (count 2). The capture `(Pair*)` is one
        // value, so `(Pair*).BeforeLastCount(99)` collects [(10, 20)] (count 1).
        const string define = "BeforeLastCount(*values, last) = values.count\nPair = (10, 20)\n";

        AssertEval(define + "Pair*.BeforeLastCount(99)", 2);
        AssertEval(define + "BeforeLastCount(Pair*, 99)", 2);
        AssertEval(define + "(Pair*).BeforeLastCount(99)", 1);
        AssertEval(define + "BeforeLastCount((Pair*), 99)", 1);
    }

    [Fact]
    public void Eval_SequenceValueArgument_CanonicalCall_MatchesSequenceValueReceiverDotCall()
    {
        // Canonical-call twin of the dot-call above: Pair is one argument, so
        // the collecting parameter collects [(10, 20)] — count 1, matching Pair.BeforeLastCount(99).
        var source = """
            BeforeLastCount(*values, last) = values.count
            Pair = (10, 20)
            BeforeLastCount(Pair, 99)
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_SequenceValueSpreadArgument_CanonicalCall_OverSuppliesVariadicByDeconstruction()
    {
        // Canonical-call twin: Pair* spreads into [10, 20] and 99 fills the
        // suffix, so the deconstruction matcher captures [10, 20] (count 2).
        var source = """
            BeforeLastCount(*values, last) = values.count
            Pair = (10, 20)
            BeforeLastCount(Pair*, 99)
            """;

        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_MultiOutputReceiver_DotCallMatchesCanonicalCalls()
    {
        // Each dot-call agrees with its canonical-call twin: the receiver is
        // the one written argument (the collector collects [(10, 20)], count
        // 1), the fluent spread receiver supplies the two spread slots (count
        // 2), and the capture of the spread is again one written value.
        var define = """
            NItems(*values) = values.count
            Values = 10, 20

            """;
        AssertEval(define + "Values.NItems", 1);
        AssertEval(define + "NItems(Values)", 1);
        AssertEval(define + "Values*.NItems", 2);
        AssertEval(define + "NItems(Values*)", 2);
        AssertEval(define + "(Values*).NItems", 1);
        AssertEval(define + "NItems((Values*))", 1);
    }

    [Fact]
    public void Eval_MultiOutputReceiverWithSuffix_DotCallMatchesCanonicalCalls()
    {
        var define = """
            BeforeLastCount(*values, last) = values.count
            Values = 10, 20

            """;
        // Each dot-call agrees with its canonical-call twin: the ordinary forms
        // pass one sequence value plus the suffix (the collector collects
        // [(10, 20)], count 1); the fluent spread forms supply the two spread
        // slots before the suffix (count 2); the capture of the spread is one
        // value again (count 1).
        AssertEval(define + "Values.BeforeLastCount(99)", 1);
        AssertEval(define + "BeforeLastCount(Values, 99)", 1);
        AssertEval(define + "Values*.BeforeLastCount(99)", 2);
        AssertEval(define + "BeforeLastCount(Values*, 99)", 2);
        AssertEval(define + "(Values*).BeforeLastCount(99)", 1);
        AssertEval(define + "BeforeLastCount((Values*), 99)", 1);
    }

    [Fact]
    public void Eval_OrdinaryMultiOutputArgument_PreservesSingleGroupedValueAtSuffixAllocation()
    {
        // Sum(*values, last) receives Values as one argument. `last` receives
        // the sequence value, so the numeric body fails unless Values* is used.
        var source = """
            Sum(*values, last) = values.sum + last
            Values = 10, 20
            Sum(Values)
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_CapturedSpreadReceiver_IsOneValueAtSuffixAllocation()
    {
        // Spread supplies 10 and 20 as separate slots, so `last` binds 20 and
        // the collecting parameter collects [10] — in the direct call and in
        // the fluent dotted spelling alike. The CAPTURED spread `(Values*)` is
        // one value: with no other arguments the fixed suffix `last` takes it
        // (the sequence (10, 20)), the collector collects [], and the numeric
        // body fails — exactly as the written `Sum((Values*))` fails.
        var define = """
            Sum(*values, last) = values.sum + last
            Values = 10, 20

            """;
        AssertEval(define + "Sum(Values*)", 30);
        AssertEval(define + "Values*.Sum", 30);

        foreach (var captured in new[] { "(Values*).Sum", "Sum((Values*))" })
        {
            var receiverResult = EvalFull(define + captured);
            Assert.True(receiverResult.IsError, $"Expected failure but got: {(receiverResult.IsOk ? receiverResult.Value : null)}");
            Assert.IsType<EvalError.TypeMismatch>(Innermost(receiverResult.Error));
        }
    }

    [Fact]
    public void Eval_UserDefinedNonVariadicDotCallReceiver_PassesCanonicalSequenceArgument()
    {
        var source = """
            CountOne(value) = value.count
            (1, 2).CountOne
            """;

        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_ParenthesizedSequenceSpread_DirectDotCallReceiverExpandsOneLayer()
    {
        var source = """
            A = 1, 2
            B = 3, 4
            (A*, B).count
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_DoubleParenthesizedSequenceSpread_DotCallReceiverPreservesNestedLayer()
    {
        var source = """
            A = 1, 2
            B = 3, 4
            ((A*, B)).count
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Count_WrapperMultiOutputBoundary_CountsExpandedTopLevelItems()
    {
        var source = """
            Values = 1, 2, 3
            count(Values)
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Count_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            count(Data:0)
            (Data:0).count
            """;

        AssertEval(source, 5, 5);
    }

    [Fact]
    public void Eval_Count_ProjectedExpressionAndNamedProjectionAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            Projected = Data:0
            count(Data:0)
            count(Projected)
            """;

        AssertEval(source, 5, 5);
    }

    // Direct-consumer regressions for variadic-style top-level binding.

    [Fact]
    public void Eval_SequenceBoundaryLaw_NumericDirectConsumersExpandCommaSeparatedNamedSources()
    {
        var dataSource = "Data = 3, 4, 5, 6\n";

        AssertEval(dataSource + "sum(Data)", 18);
        AssertEval(dataSource + "sum((Data*, 8))", 26);

        AssertEval(dataSource + "min(Data)", 3);
        AssertEval(dataSource + "min((Data*, 8))", 3);

        AssertEval(dataSource + "max(Data)", 6);
        AssertEval(dataSource + "max((Data*, 8))", 8);

        AssertEval(dataSource + "avg(Data)", 4.5m);
        AssertEval(dataSource + "avg((Data*, 8))", 5.2m);
    }

    [Fact]
    public void Eval_SequenceBoundaryLaw_SlicingDistinctAndOrderingExpandCommaSeparatedNamedSources()
    {
        var dataSource = "Data = 3, 4, 5, 6\n";

        AssertEval(dataSource + "skip(Data, 1)", 4, 5, 6);
        AssertEval(dataSource + "skip((Data*, 8), 1)", 4, 5, 6, 8);

        AssertEval(dataSource + "count(distinct(Data))", 4);
        AssertEval(dataSource + "count(distinct((Data*, 4)))", 4);

        AssertEval(dataSource + "orderDesc(Data)", 6, 5, 4, 3);
        AssertEval(dataSource + "orderDesc((Data*, 8))", 8, 6, 5, 4, 3);
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_WhileReceiverCountsFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Step(a, b) = a + 1, b + 1, false
            Step.while(1, 2).count
            """,
            2);

    [Fact]
    public void Eval_SequenceReceiverBoundary_WhileSequenceValueStateSlotCountsOneItem()
        => AssertEvalLoopModes(
            """
            Step(x) = (x, x + 1), false
            Step.while(1).count
            """,
            1);

    [Fact]
    public void Eval_SequenceReceiverBoundary_RepeatReceiverCountsFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Step(a, b) = a + 1, b + 1
            Step.repeat(1, 1, 2).count
            """,
            2);

    [Fact]
    public void Eval_SequenceReceiverBoundary_RepeatSequenceValueStateSlotCountsOneItem()
        => AssertEvalLoopModes(
            """
            Step(x) = (x, x + 1)
            Step.repeat(1, 1).count
            """,
            2);

    [Fact]
    public void Eval_SequenceReceiverBoundary_RepeatReceiverTakeTrimsFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Step(a, b) = a + 1, b + 1
            Step.repeat(1, 1, 2).take(1)
            """,
            2);

    [Fact]
    public void Eval_SequenceReceiverBoundary_YellowstoneSequenceValueHistorySelectionReturnsHistory()
    {
        var expectedPrefix = new Decimal128[]
        {
            1, 2, 3, 4, 9, 8, 15, 14, 5, 6,
            25, 12, 35, 16, 7, 10, 21, 20, 27, 22,
            39, 11, 13, 33, 26, 45, 28, 51, 32, 17
        };

        AssertEval(
            YellowstoneSource("YSStep.repeat(27, (1, 2, 3), 2, 3):0"),
            expectedPrefix);
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_YellowstoneWithoutTakeKeepsHelperStateSlots()
    {
        AssertEvalResultLoopModes(
            YellowstoneSource("YSStep.repeat(27, (1, 2, 3), 2, 3)"),
            Result.FromItems([
                ResultFromAtoms(
                    1, 2, 3, 4, 9, 8, 15, 14, 5, 6,
                    25, 12, 35, 16, 7, 10, 21, 20, 27, 22,
                    39, 11, 13, 33, 26, 45, 28, 51, 32, 17),
                new Result.Atom(32),
                new Result.Atom(17),
            ]));
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_YellowstoneSequenceValueHistoryPassedWhole()
    {
        // `history` holds one grouped sequence value, which is exactly the one
        // collection argument contains(collection, item) expects — the wrapper
        // passes it whole and the collection view opens the lone boundary.
        var expectedHistory = new Decimal128[]
        {
            1, 2, 3, 4, 9, 8, 15, 14, 5, 6,
            25, 12, 35, 16, 7, 10, 21, 20, 27, 22,
            39, 11, 13, 33, 26, 45, 28, 51, 32, 17
        };

        var source = """
            GcdStep = b, ~a mod b, a mod b != 0
            Gcd = GcdStep.while(a, b):1

            FindNext(history, pre1, pre2) = {
                IsYSCandidate(candidate) = not contains(history, candidate) and
                    Gcd(candidate, pre1) == 1 and Gcd(candidate, pre2) != 1
                FindStep = candidate + 1, not IsYSCandidate(candidate)
                FindStep.while(1):0
            }

            YSStep(history, pre2, pre1) = {
                Next = FindNext(history, pre1, pre2)
                (history*, Next), pre1, Next
            }
            """;

        AssertEvalResultLoopModes(
            source + "\nYSStep.repeat(27, (1, 2, 3), 2, 3)",
            Result.FromItems([
                ResultFromAtoms(expectedHistory),
                new Result.Atom(32),
                new Result.Atom(17),
            ]));

        AssertEvalLoopModes(
            source + "\nYSStep.repeat(27, (1, 2, 3), 2, 3):0",
            expectedHistory);
    }

    // -- Sequence builtin dot-call regression sweep --------------------------

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Count_ExplicitReceiverSweep()
        => AssertEval(
            """
            Values = 1, 2, 3
            SequenceValue = (1, 2, 3)
            Data = (3, 1, 2), (9, 8, 7)
            Values.count
            count(Values)
            SequenceValue.count
            count(SequenceValue)
            (Data:0).count
            count(Data:0)
            """,
            3,
            3,
            3,
            3,
            3,
            3);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Contains_ExplicitReceiverSweep()
        => AssertEvalBools(
            """
            Values = 1, 2, 3
            SequenceValue = (1, 2, 3)
            Data = (3, 1, 2), (9, 8, 7)
            Values.contains(2)
            contains(Values, 2)
            SequenceValue.contains(2)
            SequenceValue.contains((1, 2, 3))
            (Data:0).contains(2)
            contains(Data:0, 2)
            """,
            true,
            true,
            true,
            false,
            true,
            true);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_OrderAndOrderDesc_ProjectionSweep()
        => AssertEval(
            """
            Values = 3, 1, 2
            Data = (3, 1, 2), (9, 8, 7)
            Values.order
            Values.orderDesc
            (Data:0).order
            order(Data:0)
            (Data:0).orderDesc
            orderDesc(Data:0)
            """,
            1,
            2,
            3,
            3,
            2,
            1,
            1,
            2,
            3,
            1,
            2,
            3,
            3,
            2,
            1,
            3,
            2,
            1);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_OrderAndOrderDesc_MultiOutputHelpersMatchPlainCall()
    {
        AssertEval(
            """
            Values = 3, 1, 2
            order(Values)
            orderDesc(Values)
            """,
            1,
            2,
            3,
            3,
            2,
            1);

        AssertEval(
            """
            SequenceValue = (3, 1, 2)
            SequenceValue.order
            """,
            1,
            2,
            3);

        AssertEval(
            """
            SequenceValue = (3, 1, 2)
            SequenceValue.orderDesc
            """,
            3,
            2,
            1);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_FirstAndLast_ProjectionSweep()
        => AssertEval(
            """
            Values = 5, 6, 7
            Data = (9, 8, 7), (3, 2, 1)
            Values.first
            Values.last
            (Data:0).first
            first(Data:0)
            (Data:0).last
            last(Data:0)
            """,
            5,
            7,
            9,
            9,
            7,
            7);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_FirstAndLast_SequenceValueReceiversAgreeWithPlainCall()
    {
        AssertEval(
            """
            SequenceValue = (5, 6, 7)
            SequenceValue.first
            first(SequenceValue)
            SequenceValue.last
            last(SequenceValue)
            """,
            5,
            5,
            7,
            7);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Distinct_ProjectionSweep()
        => AssertEval(
            """
            Values = 1, 2, 1, 3
            Data = (1, 2, 1, 3), (9, 8, 9)
            Values.distinct
            (Data:0).distinct
            distinct(Data:0)
            """,
            1,
            2,
            3,
            1,
            2,
            3,
            1,
            2,
            3);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Distinct_SequenceValueReceiversAgreeWithPlainCall()
    {
        AssertEval(
            """
            SequenceValue = (1, 2, 1, 3)
            SequenceValue.distinct
            distinct(SequenceValue)
            """,
            1,
            2,
            3,
            1,
            2,
            3);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_TakeAndSkip_ExplicitReceiverSweep()
        => AssertEval(
            """
            Values = 1, 2, 3
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            Values.take(2)
            take(Values, 2)
            Values.skip(1)
            skip(Values, 1)
            (Data:0).take(2)
            take(Data:0, 2)
            (Data:0).skip(2)
            skip(Data:0, 2)
            """,
            1,
            2,
            1,
            2,
            2,
            3,
            2,
            3,
            7,
            6,
            7,
            6,
            4,
            2,
            1,
            4,
            2,
            1);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_TakeAndSkip_SequenceValueReceiversAgreeWithPlainCall()
    {
        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.take(2)
            take(SequenceValue, 2)
            """,
            1,
            2,
            1,
            2);

        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.skip(1)
            skip(SequenceValue, 1)
            """,
            2,
            3,
            2,
            3);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_InlineReceiver_StripsOneOuterBlockLayer()
        => AssertEval(
            """
            Add = x + total
            AddOne = x + 1
            IsLarge = x > 1
            (1, 2, 3).count
            if((1, 2, 3).contains(2), 1, 0)
            (3, 1, 2).order
            (5, 6, 7).first
            (5, 6, 7).last
            (1, 2, 1, 3).distinct
            (1, 2, 3).take(2)
            (1, 2, 3).skip(1)
            (10, 4, 7).min
            {10, 4, 7}.max
            {3, 5, 3}.sum
            (10, 4, 7).avg
            (1, 2, 3).map(AddOne)
            {1, 2, 3, 4}.filter(IsLarge)
            (1, 2, 3).reduce(Add, 0)
            """,
            3,
            1,
            1,
            2,
            3,
            5,
            7,
            1,
            2,
            3,
            1,
            2,
            2,
            3,
            4,
            10,
            11,
            7,
            2,
            3,
            4,
            2,
            3,
            4,
            6);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_NumericAggregations_ProjectionSweep()
        => AssertEval(
            """
            Values = 1, 2, 3
            Data = (3, 1, 2), (9, 8, 7)
            Values.sum
            Values.avg
            Values.min
            Values.max
            (Data:0).sum
            sum(Data:0)
            (Data:0).avg
            avg(Data:0)
            (Data:0).min
            min(Data:0)
            (Data:0).max
            max(Data:0)
            """,
            6,
            2,
            1,
            3,
            6,
            6,
            2,
            2,
            1,
            1,
            3,
            3);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_NumericAggregations_MultiOutputHelpersMatchPlainCall()
    {
        AssertEval(
            """
            Values = 1, 2, 3
            sum(Values)
            avg(Values)
            min(Values)
            max(Values)
            """,
            6,
            2,
            1,
            3);

        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.sum
            """,
            6);

        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.avg
            """,
            2);

        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.min
            """,
            1);

        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.max
            """,
            3);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Map_ExplicitReceiverSweep()
        => AssertEval(
            """
            ItemCount(x) = x.count
            AddOne = x + 1
            Items = (1, 2, 3), 7
            SequenceValue = (1, 2, 3)
            Data = (1, 2, 3), (4, 5, 6)
            Items.map(ItemCount)
            map(Items, ItemCount)
            SequenceValue.map(ItemCount)
            map(SequenceValue, ItemCount)
            (Data:0).map(AddOne)
            map(Data:0, AddOne)
            """,
            3,
            1,
            3,
            1,
            1,
            1,
            1,
            1,
            1,
            1,
            2,
            3,
            4,
            2,
            3,
            4);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Filter_ExplicitReceiverSweep()
        => AssertEval(
            """
            KeepCountThree(x) = x.count == 3
            IsLarge = x > 1
            Items = (1, 2, 3), (4, 5, 6), 7
            SequenceValue = (1, 2, 3)
            Data = (1, 2, 3), (4, 5, 6)
            Items.filter(KeepCountThree).count
            filter(Items, KeepCountThree).count
            SequenceValue.filter(KeepCountThree).count
            filter(SequenceValue, KeepCountThree).count
            (Data:0).filter(IsLarge).count
            filter(Data:0, IsLarge).count
            """,
            2,
            2,
            0,
            0,
            2,
            2);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Reduce_ExplicitReceiverSweep()
        => AssertEval(
            """
            AddItemCount(item, acc) = item.count + acc
            Add = x + total
            Items = (1, 2, 3), 7
            SequenceValue = (1, 2, 3)
            Data = (1, 2, 3), (4, 5, 6)
            Items.reduce(AddItemCount, 0)
            reduce(Items, AddItemCount, 0)
            SequenceValue.reduce(AddItemCount, 0)
            reduce(SequenceValue, AddItemCount, 0)
            (Data:0).reduce(Add, 0)
            reduce(Data:0, Add, 0)
            """,
            4,
            4,
            3,
            3,
            6,
            6);

    // â”€â”€ Extension call (dot-call) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_DotCall_LexicalSingleParam()
    {
        // Lean: resolveAlg on literal fails â†’ use algorithm target instead
        var source = """
            Inc = x + 1
            V = 5
            V.Inc
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_DotCall_LexicalWithArgs()
    {
        // Lean: resolveAlg on literal fails â†’ use algorithm target instead
        var source = """
            Add = a + b
            V = 3
            V.Add(4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_DotCall_Chaining()
    {
        // Lean: resolveAlg on literal fails â†’ use algorithm target instead
        var source = """
            Inc = x + 1
            Double = x * 2
            V = 3
            V.Inc.Double
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_StructuralProperty()
    {
        // 0-param structural property â†’ value access (navigation only)
        var source = """
            X = { Inc = x + 1
            5 }
            X.Inc(5)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_DotCall_StructuralProperty_NoArgs_Fails()
    {
        // Structural property with params but no args â†’ arity mismatch
        // (navigation only: no receiver injection for structural properties)
        var source = """
            X = { Inc = x + 1
            5 }
            X.Inc
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_StructuralWithArgs()
    {
        // Navigation only: all args must be provided explicitly (no receiver injection)
        var source = """
            X = { Add = a + b
            5 }
            X.Add(5, 10)
            """;
        AssertEval(source, 15);
    }

    [Fact]
    public void Eval_DotCall_StructuralNoReceiverInjection()
    {
        // Confirm receiver value is NOT injected as first arg.
        // X has output 42, but F gets args directly: a=10, b=20 â†’ 30 (not 42+10=52)
        var source = """
            X = { F = a + b
            42 }
            X.F(10, 20)
            """;
        AssertEval(source, 30);
    }

    [Fact]
    public void Eval_DotCall_LexicalFallback_ReceiverIsLeft()
    {
        // Num.Double: receiver=Num (left), name=Double (right)
        // Lexical fallback: call Double(Num) -> x=3, x*2=6
        var source = """
            Num = 3
            Double = x * 2
            Num.Double
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_DotCall_MissingProperty_UsesKatLangFacingMessage()
    {
        var source = ClosedMemberProbe(
            """
            Lib = {
                A = 1
            }

            """,
            "Lib.B");

        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var callContext = Assert.IsType<EvalError.WithContext>(result.Error);
        var contextual = Assert.IsType<EvalError.WithContext>(callContext.Inner);
        var dotContext = Assert.IsType<DotCallContext>(contextual.ErrorContext);
        Assert.Equal("Lib", dotContext.ReceiverDescription);
        Assert.Equal("B", dotContext.PropertyName);
        var unresolved = Assert.IsType<EvalError.UnknownName>(contextual.Inner);
        Assert.Equal("B", unresolved.Name);

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.DoesNotContain("dotCall", formatted);
        Assert.DoesNotContain("Unknown name: B", formatted);
        Assert.Contains("Property 'B' was not found on `Lib`", formatted);
        Assert.Contains("visible algorithm or property named 'B'", formatted);
        Assert.Contains("`Lib` as the first argument", formatted);
    }

    [Fact]
    public void Eval_DotCall_MissingProperty_OnExpression_RendersReceiver()
    {
        var result = EvalFull(ClosedMemberProbe("", "(2 + 3).B"));
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("`(2 + 3)`", formatted);
        Assert.Contains("Property 'B' was not found", formatted);
    }

    [Fact]
    public void Eval_DotCall_LexicalFallback_WithVisibleName_StillWorks()
    {
        var source = """
            B = x + 1
            5.B
            """;

        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_UnknownName_OutsideDotCall_RemainsPlain()
    {
        var formatted = KatLangError.FromEvalError(new EvalError.UnknownName("B")).Message;
        Assert.Equal("Unknown name: B", formatted);
    }

    [Fact]
    public void Eval_DotCall_ReversedReceiver_ProducesError()
    {
        // Double.Num: receiver=Double (parameterised), name=Num (0-param)
        // Lexical fallback: call Num(Double) -> Num has 0 params, 1 arg -> ArityMismatch
        var source = """
            Num = 3
            Double = x * 2
            Double.Num
            """;
        AssertEvalFails(source);
        var err = GetEvalError(source);
        Assert.IsType<EvalError.WithContext>(err);
        var inner = ((EvalError.WithContext)err!).Inner;
        Assert.IsType<EvalError.ArityMismatch>(inner);
        var arity = (EvalError.ArityMismatch)inner;
        Assert.Equal(0, arity.Expected); // Num has 0 params
        Assert.Equal(1, arity.Actual);   // 1 arg (the receiver Double)
    }

    [Fact]
    public void Eval_DotCall_WithArgs_LexicalFallback()
    {
        // V.Add(4): receiver=V, name=Add -> call Add(V, 4) -> a=3, b=4, a+b=7
        var source = """
            Add = a + b
            V = 3
            V.Add(4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_NormalCallPreservesSequenceValueArgumentBoundary()
    {
        AssertEval(
            """
            F = a + b
            F(3, 7)
            """,
            10);

        AssertEvalFailsWithArityMismatch(
            """
            F = a + b
            F((3, 7))
            """,
            expected: 2,
            actual: 1);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_ScalarReceiverWithExplicitArgStillWorks()
    {
        var source = """
            F = a + b
            (3).F(7)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_MultiOutputReceiverDoesNotSpread()
    {
        var source = """
            F = a + b
            (3, 7).F
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_EmptyArgsDoNotSpreadMultiOutputReceiver()
    {
        var source = """
            F = a + b
            (3, 7).F()
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_CountedPathDoesNotSpreadMultiOutputReceiver()
    {
        var source = """
            F = a + b
            ((3, 7).F).count
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_OneParamReceivesSequenceValueReceiver()
    {
        var result = EvalFull(
            """
            G = x
            (3, 7).G
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        AssertSequenceValueAtoms(result.Value, 3, 7);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_FinalExplicitSequenceValueArgDoesNotUnpack()
    {
        var source = """
            H = a + b + c
            (3).H((4, 5))
            """;

        AssertEvalFailsWithArityMismatch(source, expected: 3, actual: 2);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_SequenceBuiltinsStillExpandReceiverContent()
    {
        AssertEval("(3, 7).sum", 10);
        AssertEval("(3, 7).count", 2);
        AssertEval("(3, 7).first", 3);
        AssertEval("(3, 7).last", 7);
    }

    [Fact]
    public void Eval_DotCall_StructuralProperty_ArityMismatch_Propagated()
    {
        // X.Inc: Inc has params but no args -> ArityMismatch propagated through dotCall
        var source = """
            X = { Inc = x + 1
            5 }
            X.Inc
            """;
        AssertEvalFails(source);
        var err = GetEvalError(source);
        Assert.IsType<EvalError.WithContext>(err);
        var inner = ((EvalError.WithContext)err!).Inner;
        Assert.IsType<EvalError.ArityMismatch>(inner);
    }
    // â”€â”€ Division, mod, power â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    // ── Extension properties on arbitrary receiver expressions ───────────────

    [Fact]
    public void Eval_DotCall_IntegerLiteral_Receiver()
    {
        // 5.Square → Square(5) → n*n = 25
        var source = """
            Square = n * n
            5.Square
            """;
        AssertEval(source, 25);
    }

    [Fact]
    public void Eval_DotCall_ParenExpr_Receiver()
    {
        // (2 + 3).Square → Square(5) → n*n = 25
        var source = """
            Square = n * n
            (2 + 3).Square
            """;
        AssertEval(source, 25);
    }

    [Fact]
    public void Eval_DotCall_ArbitraryExprReceiver_AlgorithmReceiver_StillWorks()
    {
        // A = 5; A.Square → Square(5) → 25 (existing behavior preserved)
        var source = """
            Square = n * n
            A = 5
            A.Square
            """;
        AssertEval(source, 25);
    }

    [Fact]
    public void Eval_DotCall_IntegerLiteral_Receiver_WithArgs()
    {
        // 5.Add(3) → Add(5, 3) → a+b = 8
        var source = """
            Add = a + b
            5.Add(3)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_ParenExpr_Receiver_WithArgs()
    {
        // (2 + 3).Add(7) → Add(5, 7) → a+b = 12
        var source = """
            Add = a + b
            (2 + 3).Add(7)
            """;
        AssertEval(source, 12);
    }

    [Fact]
    public void Eval_DotCall_NumberLiteralReceiver()
    {
        var source = """
            Add = a + b
            2.Add(6)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_ParenExprReceiver()
    {
        var source = """
            Add = a + b
            (2).Add(6)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_SameLineItemAfterDefinitionBody_IsAParseError()
    {
        // SYN-07A: `2.Add(6)` after the body `a + b` on the same line is
        // rejected (never silently a second body slot, never a root row), so no
        // evaluator outcome exists; on its own line it is the root row.
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError("Add = a + b 2.Add(6)"));
        Assert.Equal(DiagnosticCode.UnseparatedSameLineItem, diagnostic.Code);
        AssertEval("Add = a + b\n2.Add(6)", 8);
    }

    [Fact]
    public void Eval_DotCall_DecimalLiteral_Receiver()
    {
        // 2.0.Double → Double(2.0) → x*2 = 4.0
        var source = """
            Double = x * 2
            2.0.Double
            """;
        AssertEval(source, 4.0m);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_MultiOutputPropertyReceiverDoesNotUnpack()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Pair.Add
            """,
            expected: 2,
            actual: 1);
    }

    [Fact]
    public void Eval_GracePrefix_ReordersParams()
    {
        // Without grace: F(a,b) where a=first-appearance â†’ a=2, b=3
        // F = b + ~a * 10 â†’ params [a, b] (a moved left)
        // F(2, 3) â†’ a=2, b=3 â†’ 3 + 2*10 = 23
        var source = """
            F = b + ~a * 10
            F(2, 3)
            """;
        AssertEval(source, 23);
    }

    [Fact]
    public void Eval_GracePostfix_ReordersParams()
    {
        // F = a~ + b â†’ first-appearance [a, b], a~ moves right â†’ params [b, a]
        // F(2, 3) â†’ b=2, a=3 â†’ 3 + 2 = 5
        var source = """
            F = a~ + b
            F(2, 3)
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_NoGrace_Baseline()
    {
        // Without grace: F(a,b), a=first â†’ a=2, b=3 â†’ 2 + 3*10 = 32
        var source = """
            F = a + b * 10
            F(2, 3)
            """;
        AssertEval(source, 32);
    }

    [Fact]
    public void Eval_GraceWithImplicitArgs()
    {
        // F = b + ~a â†’ params [a, b]
        // G uses F implicitly: G = F + 1
        // G(2, 3) â†’ F(2,3) + 1 â†’ (3 + 2) + 1 = 6
        var source = """
            F = b + ~a
            G = F + 1
            G(2, 3)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_GraceDoublePrefixThreeParams()
    {
        // F = c + b + ~~a â†’ first-appearance [c, b, a], ~~a moves a 2 left â†’ [a, c, b]
        // F(1, 2, 3) â†’ a=1, c=2, b=3 â†’ 2 + 3 + 1 = 6
        var source = """
            F = c + b + ~~a
            F(1, 2, 3)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_DotCallReceiver_RemainsCanonicalOneArgument()
    {
        // The named property receiver is a value boundary supplying one item,
        // so the collecting parameter collects [(1, 2, 3)].
        AssertEval(
            """
            Seq = (1, 2, 3)
            Sum(*values) = values.count
            Seq.Sum()
            """,
            1m);

        AssertEvalFailsWithArityMismatch(
            """
            Pair = (1, 2)
            Add(a, b) = a + b
            Pair.Add()
            """,
            expected: 2,
            actual: 1);
    }
}
