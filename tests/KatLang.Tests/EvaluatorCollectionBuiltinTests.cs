using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorCollectionBuiltinTests
{
    private static void AssertBuiltinFailureWithExactContext(string source, string expectedContext)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains(expectedContext, formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(expectedContext, contexts);
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertBuiltinFailureWithContext(string source, string expectedContext)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains(expectedContext, formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains(expectedContext));
        Assert.IsType<EvalError.BadArity>(error);
    }

    // ── Range builtin ────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Range_AscendingInclusive()
        => AssertEval("range(1, 10)", 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);

    [Fact]
    public void Eval_Range_DescendingInclusive()
        => AssertEval("range(10, 1)", 10, 9, 8, 7, 6, 5, 4, 3, 2, 1);

    [Fact]
    public void Eval_Range_SingletonWhenEqual()
        => AssertEval("range(5, 5)", 5);

    [Fact]
    public void Eval_Range_NegativeToPositive()
        => AssertEval("range(-2, 2)", -2, -1, 0, 1, 2);

    [Fact]
    public void Eval_Range_NonIntegerStart_Fails()
        => AssertEvalFailsWithIllegalInEval("range(1.5, 5)", "range start must be an integer");

    [Fact]
    public void Eval_Range_NonIntegerStop_Fails()
        => AssertEvalFailsWithIllegalInEval("range(1, 5.2)", "range stop must be an integer");

    [Fact]
    public void Eval_Range_SequenceSpread_PreservesOrdering()
        => AssertEval("range(3, 1)*, 0", 3, 2, 1, 0);

    // ── Order builtins ──────────────────────────────────────────────────────

    [Fact]
    public void Eval_Order_DirectCallMultiArgs_SortsAscending()
        => AssertEval("order((3, 4, 2, 1, 3, 3))", 1, 2, 3, 3, 3, 4);

    [Fact]
    public void Eval_Order_WrapperMultiOutputArg_ExpandsTopLevelItems()
    {
        var source = """
            Values = 3, 4, 2, 1, 3, 3
            order(Values)
            """;

        AssertEval(source, 1, 2, 3, 3, 3, 4);
    }

    [Fact]
    public void Eval_Order_SingleSequenceValueArg_SortsSequenceItems()
        => AssertEval("order((3, 4, 2, 1, 3, 3))", 1, 2, 3, 3, 3, 4);

    [Fact]
    public void Eval_Order_ProjectedSelection_PlainAndDotCallAgree()
        => AssertEval(
            """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            order(Data:0)
            (Data:0).order
            """,
            1,
            2,
            4,
            6,
            7,
            1,
            2,
            4,
            6,
            7);

    [Fact]
    public void Eval_Order_DirectCallMixedArgs_ExpandsRangeTopLevelItems()
        => AssertEval("order((3, 4, range(1, 5)*, 7))", 1, 2, 3, 3, 4, 4, 5, 7);

    [Fact]
    public void Eval_Order_DotCallReceiverAsSingleSource_SortsRangeItems()
        => AssertEval("range(5, 1).order", 1, 2, 3, 4, 5);

    [Fact]
    public void Eval_Order_DotCall_InlineParenReceiver_PreservesBoundary()
        => AssertEval("(3, 5, 3, 6, 3).order", 3, 3, 3, 5, 6);

    [Fact]
    public void Eval_Order_DoubleParenReceiver_DotCallSortsSequenceItems()
        => AssertEval("((3, 5, 3, 6, 3)).order", 3, 3, 3, 5, 6);

    [Fact]
    public void Eval_Order_UnsupportedElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "order((1, 'hello'))",
            "order expects each collection element to be a single numeric value; item 1 was string value \"hello\"");

    [Fact]
    public void Eval_Order_SequenceValueMultiArgs_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "order(((1, 2), (3, 4)))",
            "order expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_OrderDesc_DirectCallMultiArgs_SortsDescending()
        => AssertEval("orderDesc((3, 4, 2, 1, 3, 3))", 4, 3, 3, 3, 2, 1);

    [Fact]
    public void Eval_OrderDesc_WrapperMultiOutputArg_ExpandsTopLevelItems()
    {
        var source = """
            Values = 3, 4, 2, 1, 3, 3
            orderDesc(Values)
            """;

        AssertEval(source, 4, 3, 3, 3, 2, 1);
    }

    [Fact]
    public void Eval_OrderDesc_SingleSequenceValueArg_SortsSequenceItems()
        => AssertEval("orderDesc((3, 4, 2, 1, 3, 3))", 4, 3, 3, 3, 2, 1);

    [Fact]
    public void Eval_OrderDesc_SequenceValueMultiArgs_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "orderDesc(((1, 2), (3, 4)))",
            "orderDesc expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Order_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "order((1, (2, 3)))",
            "order expects each collection element to be a single numeric value; item 1 was sequence value");

    [Fact]
    public void Eval_OrderDesc_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "orderDesc((1, (2, 3)))",
            "orderDesc expects each collection element to be a single numeric value; item 1 was sequence value");

    // ── Count builtin ────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Count_OrdinaryBuiltinCall_CountsRangeTopLevelItems()
        => AssertEval("count(range(1, 5))", 5);

    [Fact]
    public void Eval_Count_DotCall_CountsRangeTopLevelItems()
        => AssertEval("range(1, 5).count", 5);

    [Fact]
    public void Eval_Count_DotCall_EmptyFilterReceiver_ReturnsZero()
        => AssertEval("(1, 5, 3).filter{ n mod 2 == 0 }.count", 0);

    [Fact]
    public void Eval_Filter_DotCallTrailingBlockSpacing_ReturnsEquivalentResults()
    {
        AssertEval("(1, 2, 3, 4).filter{ n > 2 }.count", 2);
        AssertEval("(1, 2, 3, 4).filter { n > 2 }.count", 2);
    }

    [Fact]
    public void Eval_Count_DotCall_EmptyFilterReceiverWithNamedPredicate_ReturnsZero()
    {
        var source = """
            IsEven = n mod 2 == 0
            (1, 5, 3).filter(IsEven).count
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_Count_EmptySequence_ReturnsZero()
        => AssertEval("count(())", 0);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_EmptyFilterReceiver_RespectsEmptyPolicies()
    {
        AssertEval("(1, 5, 3).filter{ n mod 2 == 0 }.sum", 0);
        AssertBuiltinFailureWithExactContext(
            "(1, 5, 3).filter{ n mod 2 == 0 }.first",
            "first requires a non-empty collection");
        AssertBuiltinFailureWithExactContext(
            "(1, 5, 3).filter{ n mod 2 == 0 }.last",
            "last requires a non-empty collection");
    }

    [Fact]
    public void Eval_EmptySequence_IsEmptySequenceValue()
        => AssertEvalEmptyOutput("()");

    [Fact]
    public void Eval_EmptySequence_AndNestedEmpty_CanonicalizeToSameValue()
    {
        var empty = Assert.IsType<Result.SequenceValue>(EvalFull("()").Value);
        Assert.Empty(empty.Items);

        var nested = Assert.IsType<Result.SequenceValue>(EvalFull("(())").Value);
        Assert.Empty(nested.Items);

        var deeper = Assert.IsType<Result.SequenceValue>(EvalFull("((()))").Value);
        Assert.Empty(deeper.Items);
    }

    [Fact]
    public void Eval_EmptySequence_CountsAsZeroItems()
    {
        AssertEval("()");
        AssertEval("().count", 0);
        AssertEval("count(())", 0);
    }

    [Fact]
    public void Eval_NestedEmptySequence_CanonicalizesToZeroItems()
    {
        AssertEval("(()).count", 0);
        AssertEval("count((()))", 0);
        AssertEval("A = ()\nA.count", 0);
        AssertEval("A = (())\nA.count", 0);
    }

    // ── Collection builtins return exact immutable list values: kept items stay
    //    exact list elements (a one-element list [item] is NEVER erased to the
    //    item), and zero kept items form the empty list [] ──

    [Fact]
    public void Eval_Filter_NestedEmptyInput_CanonicalizesToEmptyList()
        => AssertEvalCounted(
            """
            AlwaysTrue(x) = 1
            filter((()), AlwaysTrue)
            """,
            1,
            ListValue());

    [Fact]
    public void Eval_Count_FilterNestedEmptyInput_CountsZeroItems()
        => AssertEval(
            """
            AlwaysTrue(x) = 1
            count(filter((()), AlwaysTrue))
            """,
            0);

    [Fact]
    public void Eval_Take_SingleSequenceValueItem_StaysExactListElement()
        => AssertEvalCounted("take(((1, 2), (3, 4)), 1)", 1, ListValue(SequenceValue(Atom(1), Atom(2))));

    [Fact]
    public void Eval_Skip_SingleSequenceValueItem_StaysExactListElement()
        => AssertEvalCounted("skip(((1, 2), (3, 4)), 1)", 1, ListValue(SequenceValue(Atom(3), Atom(4))));

    [Fact]
    public void Eval_Distinct_SingleSequenceValueItem_StaysExactListElement()
        => AssertEvalCounted("distinct(((1, 2), (1, 2)))", 1, ListValue(SequenceValue(Atom(1), Atom(2))));

    [Fact]
    public void Eval_Filter_KeepsSingleNonEmptySequenceValueItem_StaysExactListElement()
    {
        // Filtering a two-item collection down to one kept sequence-valued item
        // keeps that item as an exact list element: the result is [(1, 2)] —
        // no singleton erasure ever applies to list structure.
        var result = EvalFull(
            """
            KeepFirstPair(pair) = pair:0 == 1
            filter(((1, 2), (3, 4)), KeepFirstPair)
            """);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m]);
    }

    [Fact]
    public void Eval_Take_SingleKeptItem_ReproAgreesAcrossObservations()
    {
        // T is the exact list [(1, 2)]: display, count(T), T.count, equality, and
        // indexing all observe the same one-element list value. Lists are not
        // equal to sequences, and `:` indexing selects the stored element
        // exactly (T:0 is the kept `(1, 2)` element, projected one level like
        // any selected sequence element).
        AssertEvalCounted("T = take(((1, 2), (3, 4)), 1)\nT", 1, ListValue(SequenceValue(Atom(1), Atom(2))));
        AssertEval("T = take(((1, 2), (3, 4)), 1)\ncount(T)", 1);
        AssertEval("T = take(((1, 2), (3, 4)), 1)\nT.count", 1);
        AssertEval("T = take(((1, 2), (3, 4)), 1)\nT == (1, 2)", 0);
        AssertEval("T = take(((1, 2), (3, 4)), 1)\nT == ((1, 2))", 0);
        AssertEval("T = take(((1, 2), (3, 4)), 1)\nT == [(1, 2)]", 1);
        AssertEvalCounted("T = take(((1, 2), (3, 4)), 1)\nT:0", 2, SequenceValue(Atom(1), Atom(2)));
    }

    [Fact]
    public void Eval_Distinct_SingleKeptEmptyItem_StaysExactListElement()
    {
        // distinct(((), ())) dedups the collection's two equal `()` items to one
        // kept item; the kept `()` stays an exact list element, so the result is
        // [()] (one element, count 1) and is NOT equal to the empty sequence `()`.
        AssertEvalCounted("distinct(((), ()))", 1, ListValue(SequenceValue()));
        AssertEval("count(distinct(((), ())))", 1);
        AssertEval("distinct(((), ())) == ()", 0);

        // The old bare two-argument form over-supplies the fixed
        // distinct(collection) signature.
        AssertEvalFailsWithArityMismatch("distinct((), ())", expected: 1, actual: 2);
    }

    [Fact]
    public void Eval_Take_MultipleEmptyItems_PreservesSiblingBoundaries()
    {
        // Kept empty-sequence items stay exact list elements with their sibling
        // boundaries preserved raw: take(((), ()), 2) is [(), ()] — never
        // collapsed or dropped.
        AssertEvalCounted("take(((), ()), 2)", 1, ListValue(SequenceValue(), SequenceValue()));
        AssertEval("count(take(((), ()), 2))", 2);
        AssertEvalCounted("distinct(((), (), 1))", 1, ListValue(SequenceValue(), Atom(1)));

        // The old bare form supplied the empty items as separate arguments —
        // now an ordinary arity error against take(collection, count).
        AssertEvalFailsWithArityMismatch("take((), (), 2)", expected: 2, actual: 3);
    }

    [Fact]
    public void Eval_Filter_SingleKeptEmptyItem_StaysExactListElement()
    {
        // Filtering down to exactly one kept `()` item returns the exact list
        // [()]: one visible output slot whose one element is the empty sequence.
        AssertEvalCounted(
            """
            KeepEmpty(x) = x.count == 0
            filter(((), 1), KeepEmpty)
            """,
            1,
            ListValue(SequenceValue()));
        AssertEval(
            """
            KeepEmpty(x) = x.count == 0
            count(filter(((), 1), KeepEmpty))
            """,
            1);

        // The old bare three-argument form over-supplies the fixed
        // filter(collection, predicate) signature.
        AssertEvalFailsWithArityMismatch(
            """
            KeepEmpty(x) = x.count == 0
            filter((), 1, KeepEmpty)
            """,
            expected: 2,
            actual: 3);
    }

    [Fact]
    public void Eval_Count_DescendingRange_CountsTopLevelItems()
        => AssertEval("count(range(5, 1))", 5);

    [Fact]
    public void Eval_Count_SequenceValueElements_CountsSequenceItems()
        => AssertEval("count(((1, 2), (3, 4)))", 2);

    [Fact]
    public void Eval_Count_SingleAtomicInput_ReturnsOne()
        => AssertEval("count(5)", 1);

    [Fact]
    public void Eval_Count_StringInput_ReturnsOne()
        => AssertEval("count('hello')", 1);

    [Fact]
    public void Eval_Count_DirectCallMultiArgs_CountsTopLevelItems()
        => AssertEval("count((1, 7))", 2);

    [Fact]
    public void Eval_Count_DirectCallMixedArgs_CountsExpandedTopLevelItems()
        => AssertEval("count((3, 4, range(1, 5)*, 7))", 8);

    [Fact]
    public void Eval_Count_SingleSequenceValueArg_CountsSequenceItems()
        => AssertEval("count((1, 7))", 2);

    [Fact]
    public void Eval_Count_SequenceValueMultiArgs_CountTopLevelGroups()
        => AssertEval("count(((1, 2), (3, 4)))", 2);

    [Fact]
    public void Eval_Count_InlineParenReceiver_DotCallDestructuresSequence()
        => AssertEval("(1, 7).count", 2);

    // ── Contains builtin ─────────────────────────────────────────────────────

    [Fact]
    public void Eval_Contains_OrdinaryBuiltinCall_SearchesExpandedRangeTopLevelItems()
        => AssertEval("contains(range(1, 5), 3)", 1);

    [Fact]
    public void Eval_Contains_OrdinaryBuiltinCall_DoesNotTreatRangeAsOneSequenceValue()
        => AssertEval("contains(range(1, 5), (1, 2, 3, 4, 5))", 0);

    [Fact]
    public void Eval_Contains_DotCall_MatchesPlainCallReceiverSemantics()
        => AssertEval("range(1, 5).contains(4)", 1);

    [Fact]
    public void Eval_Contains_DirectCallMixedArgs_SearchesExpandedRangeTopLevelItems()
        => AssertEval("contains((3, 4, range(1, 5)*, 7), 5)", 1);

    [Fact]
    public void Eval_Contains_DirectCallMixedArgs_DoesNotMatchExpandedRangeAsSequenceValue()
        => AssertEval("contains((3, 4, range(1, 5)*, 7), (1, 2, 3, 4, 5))", 0);

    [Fact]
    public void Eval_Contains_SequenceValueItem_UsesOrdinaryValueEquality()
        => AssertEval("contains((1, 2), 1)", 1);

    [Fact]
    public void Eval_Contains_DoesNotSearchInsideNestedSequenceValueMembers()
        => AssertEval("contains(((1, 2), (3, 4)), (1, 2))", 1);

    [Fact]
    public void Eval_Contains_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            contains(Data:0, 4)
            (Data:0).contains(4)
            """;

        AssertEval(source, 1, 1);
    }

    [Fact]
    public void Eval_Contains_MultiOutputSearchedItem_UsesFinalTopLevelItemAsSuffix()
    {
        var source = """
            Item = 1, 2
            contains((1, 2), Item)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_Contains_OneArgument_IsArityError()
    {
        // contains(collection, item) is fixed two-argument, so contains(1) is
        // an ordinary arity error. Searching nothing is spelled with an
        // explicit empty collection argument and finds nothing.
        AssertEvalFailsWithArityMismatch("contains(1)", expected: 2, actual: 1);
        AssertEval("contains((), 2)", 0m);
    }

    // ── First/last builtins ────────────────────────────────────────────────

    [Fact]
    public void Eval_First_OrdinaryBuiltinCall_ReturnsFirstExpandedRangeItem()
        => AssertEval("first(range(1, 5))", 1);

    [Fact]
    public void Eval_Last_OrdinaryBuiltinCall_ReturnsLastExpandedRangeItem()
        => AssertEval("last(range(1, 5))", 5);

    [Fact]
    public void Eval_First_DotCall_ReturnsFirstExpandedRangeItem()
        => AssertEval("range(1, 5).first", 1);

    [Fact]
    public void Eval_Last_DotCall_ReturnsLastExpandedRangeItem()
        => AssertEval("range(1, 5).last", 5);

    [Fact]
    public void Eval_First_DirectCallMultiResult_Shorthand_ReturnsFirstOutput()
        => AssertEval("first((1, 2, 3))", 1);

    [Fact]
    public void Eval_Last_DirectCallMultiResult_Shorthand_ReturnsLastOutput()
        => AssertEval("last((1, 2, 3))", 3);

    [Fact]
    public void Eval_First_SingleSequenceValueArg_ReturnsFirstSequenceItem()
        => AssertEval("first((1, 2))", 1);

    [Fact]
    public void Eval_First_MultiArgSequenceValueInputs_PreservesFirstGroup()
    {
        var result = EvalFull("first(((1, 2), (3, 4)))");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertSequenceValueAtoms(result.Value, 1, 2);
    }

    [Fact]
    public void Eval_Last_SingleSequenceValueArg_ReturnsLastSequenceItem()
        => AssertEval("last((1, 2))", 2);

    [Fact]
    public void Eval_Last_MultiArgSequenceValueInputs_PreservesLastGroup()
    {
        var result = EvalFull("last(((1, 2), (3, 4)))");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertSequenceValueAtoms(result.Value, 3, 4);
    }

    [Fact]
    public void Eval_First_PropertyOutput_PreservesBoundaryItem()
    {
        var source = """
            Values = 4, 5, 6
            Head = Values.first
            Head
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Last_IntermediateProperty_PreservesBoundaryItem()
    {
        var source = """
            Values = 4, 5, 6
            Tail = Values.last
            Tail
            """;

        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_First_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            first(Data:0)
            (Data:0).first
            """;

        AssertEval(source, 7, 7);
    }

    [Fact]
    public void Eval_Last_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            last(Data:0)
            (Data:0).last
            """;

        AssertEval(source, 1, 1);
    }

    [Fact]
    public void Eval_First_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(4, 5, 6).first", 4);

    [Fact]
    public void Eval_Last_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(4, 5, 6).last", 6);

    // ── Distinct builtin ───────────────────────────────────────────────────

    [Fact]
    public void Eval_Distinct_OrdinaryBuiltinCall_RemovesLaterDuplicatesPreservingFirstOccurrence()
        => AssertEval("distinct((3, 1, 3, 2, 1, 2))", 3, 1, 2);

    [Fact]
    public void Eval_Distinct_DotCall_PreservesNamedBoundaryItem()
    {
        var source = """
            Values = 3, 1, 3, 2, 1, 2
            Values.distinct
            """;

        AssertEval(source, 3, 1, 2);
    }

    [Fact]
    public void Eval_Distinct_AllEqualInput_ReturnsSingleValue()
        => AssertEval("distinct((4, 4, 4, 4))", 4);

    [Fact]
    public void Eval_Distinct_AlreadyDistinctInput_PreservesOrder()
        => AssertEval("distinct((1, 2, 3))", 1, 2, 3);

    [Fact]
    public void Eval_Distinct_SequenceValueItems_RemoveDuplicateGroupsByValue()
    {
        var result = EvalFull("distinct(((1, 2), (1, 2), (3, 4)))");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Distinct_SequenceValueWrapperOutput_PreservesSingleSequenceValueItem()
    {
        var source = """
            Values = ((1, 2), (1, 2), (3, 4))
            distinct(Values)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Distinct_MultiOutputWrapper_DeduplicatesExpandedTopLevelItems()
    {
        var source = """
            Values = (1, 2), (1, 2), (3, 4)
            distinct(Values)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Distinct_InlineParenReceiver_DotCallPreservesBoundaryItem()
        => AssertEval("(1, 2, 1, 3).distinct", 1, 2, 3);

    [Fact]
    public void Eval_Distinct_SequenceValueReceiver_DotCallDeduplicatesSequenceItems()
    {
        var source = """
            Values = (1, 2, 1, 3)
            Values.distinct
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertEval(source, 1, 2, 3);
    }

    // ── Take/skip builtins ────────────────────────────────────────────────

    [Fact]
    public void Eval_Take_OrdinaryBuiltinCall_ReturnsLeadingItems()
        => AssertEval("take((1, 2, 3, 4, 5), 3)", 1, 2, 3);

    [Fact]
    public void Eval_Skip_OrdinaryBuiltinCall_ReturnsRemainingItems()
        => AssertEval("skip((1, 2, 3, 4, 5), 3)", 4, 5);

    [Fact]
    public void Eval_Take_DotCall_ReturnsExpandedRangeItems()
        => AssertEval("range(1, 5).take(3)", 1, 2, 3);

    [Fact]
    public void Eval_Take_DotCall_RepeatReceiverUsesFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Step(a, b) = a + 1, b + 10
            Step.repeat(3, 0, 0).take(1)
            """,
            3);

    [Fact]
    public void Eval_Take_DotCall_VariadicRepeatReceiverUsesExpandedFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Grow(*history, tail) = (history*, tail + 1), tail + 1
            Grow.repeat(3, 1, 2).take(4)
            """,
            1,
            3,
            4,
            5,
            5);

    [Fact]
    public void Eval_Take_DotCall_WhileReceiverUsesFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Step(a, b) = a + 1, b + 10, a < 2
            Step.while(0, 0).take(1)
            """,
            2);

    [Fact]
    public void Eval_Skip_DotCallReceiverAsSingleSource_SkipsExpandedRangeItems()
        => AssertEval("range(1, 5).skip(3)", 4, 5);

    [Fact]
    public void Eval_Take_InlineParenReceiver_DotCallPreservesBoundaryItem()
        => AssertEval("(1, 2, 3).take(2)", 1, 2);

    [Fact]
    public void Eval_Skip_InlineParenReceiver_DotCallDropsBoundaryItem()
        => AssertEval("(1, 2, 3).skip(1)", 2, 3);

    [Fact]
    public void Eval_Take_SequenceValueReceiver_DotCallTakesSequencePrefix()
    {
        var source = """
            Values = (1, 2, 3)
            Values.take(2)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertEval(source, 1, 2);
    }

    [Fact]
    public void Eval_Skip_SequenceValueReceiver_DotCallSkipsSequencePrefix()
    {
        var source = """
            Values = (1, 2, 3)
            Values.skip(1)
            """;

        AssertEval(source, 2, 3);
    }

    [Fact]
    public void Eval_Take_ZeroCount_ReturnsEmpty()
        => AssertEval("take((1, 2, 3), 0)");

    [Fact]
    public void Eval_Skip_ZeroCount_ReturnsOriginalSequence()
        => AssertEval("skip((1, 2, 3), 0)", 1, 2, 3);

    [Fact]
    public void Eval_Take_NegativeCount_ReturnsEmpty()
        => AssertEval("take((1, 2, 3), -2)");

    [Fact]
    public void Eval_Skip_NegativeCount_ReturnsOriginalSequence()
        => AssertEval("skip((1, 2, 3), -2)", 1, 2, 3);

    [Fact]
    public void Eval_Take_CountLargerThanLength_ReturnsWholeSequence()
        => AssertEval("take((1, 2, 3), 10)", 1, 2, 3);

    [Fact]
    public void Eval_Skip_CountLargerThanLength_ReturnsEmpty()
        => AssertEval("skip((1, 2, 3), 10)");

    [Fact]
    public void Eval_Take_SequenceValueItems_KeepsFirstGroupAsExactListElement()
    {
        var result = EvalFull("take(((1, 2), (3, 4)), 1)");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // The one kept sequence-valued item stays an exact list element: the
        // result is [(1, 2)] (first(...) still selects the item itself).
        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m]);
    }

    [Fact]
    public void Eval_Skip_SequenceValueItems_KeepsSecondGroupAsExactListElement()
    {
        var result = EvalFull("skip(((1, 2), (3, 4)), 1)");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // The one remaining sequence-valued item stays an exact list element:
        // the result is [(3, 4)] (last(...) still selects the item itself).
        AssertListOfSequenceValueAtoms(result.Value, [3m, 4m]);
    }

    [Fact]
    public void Eval_Take_SequenceValueWrapperOutput_PreservesSingleSequenceValueItem()
    {
        var source = """
            Values = (1, 2, 3)
            take(Values, 1)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Take_MultiOutputWrapper_KeepsExpandedTopLevelPrefix()
    {
        var source = """
            Values = 1, 2, 3
            take(Values, 1)
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Skip_SequenceValueWrapperOutput_ReturnsEmptyAfterSkippingSingleSequenceValueItem()
    {
        var source = """
            Values = (1, 2, 3)
            skip(Values, 1)
            """;

        AssertEval(source, 2, 3);
    }

    [Fact]
    public void Eval_Skip_MultiOutputWrapper_DropsExpandedTopLevelPrefix()
    {
        var source = """
            Values = 1, 2, 3
            skip(Values, 1)
            """;

        AssertEval(source, 2, 3);
    }

    [Fact]
    public void Eval_Take_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            take(Data:0, 2)
            (Data:0).take(2)
            """;

        AssertEval(source, 7, 6, 7, 6);
    }

    [Fact]
    public void Eval_Skip_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            skip(Data:0, 2)
            (Data:0).skip(2)
            """;

        AssertEval(source, 4, 2, 1, 4, 2, 1);
    }

    [Fact]
    public void Eval_Take_EmptyCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithContext(
            "take((1, 2), take(1, 0))",
            "take count must be exactly one whole-number value");

    [Fact]
    public void Eval_Take_SequenceValueCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "take((3, 4), (1, 2))",
            "take count must be exactly one whole-number value");

    [Fact]
    public void Eval_Take_FractionalCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithContext(
            "take((1, 2), 1.5)",
            "take count must be exactly one whole-number value");

    [Fact]
    public void Eval_Skip_StringCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "skip((1, 2), 'hello')",
            "skip count must be exactly one whole-number value");

    [Fact]
    public void Eval_Skip_SpreadArguments_FollowOrdinaryFixedArity()
    {
        // Spread has only its ordinary meaning: `Bad*` opens to two argument
        // slots, so skip((3, 4), Bad*) supplies three arguments to the fixed
        // skip(collection, count) signature — an ordinary arity error.
        var source = """
            Bad = 1, 2
            skip((3, 4), Bad*)
            """;

        AssertEvalFailsWithArityMismatch(source, expected: 2, actual: 3);
    }

    // ── Min builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Min_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("min(range(1, 5))", 1);

    [Fact]
    public void Eval_Min_DotCallReceiverAsSingleSource_ExpandsRangeItems()
        => AssertEval("range(1, 5).min", 1);

    [Fact]
    public void Eval_Min_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            min(Data:0)
            (Data:0).min
            """;

        AssertEval(source, 1, 1);
    }

    [Fact]
    public void Eval_Min_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(10, 4, 7).min", 4);

    [Fact]
    public void Eval_Min_SequenceValueReceiver_DotCallFindsMinimum()
    {
        var source = """
            Values = (10, 4, 7)
            Values.min
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Min_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("min(5)", 5);

    [Fact]
    public void Eval_Min_DirectCallMultiArgs_FindsMinimum()
        => AssertEval("min((10, 4, 7))", 4);

    [Fact]
    public void Eval_Min_SequenceValueElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "min(((1, 2), (3, 4)))",
            "min expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Min_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "min('hello')",
            "min expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Min_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "min((1, (2, 3)))",
            "min expects each collection element to be a single numeric value; item 1 was sequence value");

    // ── Max builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Max_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("max(range(1, 5))", 5);

    [Fact]
    public void Eval_Max_DotCallReceiverAsSingleSource_ExpandsRangeItems()
        => AssertEval("range(1, 5).max", 5);

    [Fact]
    public void Eval_Max_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            max(Data:0)
            (Data:0).max
            """;

        AssertEval(source, 7, 7);
    }

    [Fact]
    public void Eval_Max_InlineBraceReceiver_DotCallPreservesBoundary()
        => AssertEval("{10, 4, 7}.max", 10);

    [Fact]
    public void Eval_Max_SequenceValueReceiver_DotCallFindsMaximum()
    {
        var source = """
            Values = (10, 4, 7)
            Values.max
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Max_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("max(5)", 5);

    [Fact]
    public void Eval_Max_DirectCallMultiArgs_FindsMaximum()
        => AssertEval("max((10, 4, 7))", 10);

    [Fact]
    public void Eval_Max_SequenceValueElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "max(((1, 2), (3, 4)))",
            "max expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Max_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "max('hello')",
            "max expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Max_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "max((1, (2, 3)))",
            "max expects each collection element to be a single numeric value; item 1 was sequence value");

    // ── Sum builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Sum_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("sum(range(1, 5))", 15);

    [Fact]
    public void Eval_Sum_OrdinaryBuiltinCall_ExpandsLargeRangeTopLevelItems()
        => AssertEval("sum(range(1, 100))", 5050);

    [Fact]
    public void Eval_Sum_WrapperBoundToRange_ExpandsTopLevelItems()
    {
        var source = """
            P = range(1, 100)
            sum(P)
            """;

        AssertEval(source, 5050);
    }

    [Fact]
    public void Eval_Sum_DotCallReceiverAsSingleSource_ExpandsRangeItems()
        => AssertEval("range(1, 5).sum", 15);

    [Fact]
    public void Eval_Sum_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            sum(Data:0)
            (Data:0).sum
            """;

        AssertEval(source, 20, 20);
    }

    [Fact]
    public void Eval_Sum_InlineBraceReceiver_DotCallPreservesBoundary()
        => AssertEval("{3, 5, 3}.sum", 11);

    [Fact]
    public void Eval_Sum_SequenceValueReceiver_DotCallSumsSequenceItems()
    {
        var source = """
            Values = (10, 20, 30)
            Values.sum
            """;

        AssertEval(source, 60);
    }

    [Fact]
    public void Eval_Sum_NestedSequenceValueReceiver_DotCallPreservesNestedSequenceValues()
        => AssertBuiltinFailureWithExactContext(
            "((1, 2), (3, 4)).sum",
            "sum expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Sum_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("sum(5)", 5);

    [Fact]
    public void Eval_Sum_DirectCallMultiArgs_AddsValues()
        => AssertEval("sum((10, 20, 30))", 60);

    [Fact]
    public void Eval_Sum_SequenceValueElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "sum(((1, 2), (3, 4)))",
            "sum expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Sum_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "sum('hello')",
            "sum expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Sum_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "sum((1, (2, 3)))",
            "sum expects each collection element to be a single numeric value; item 1 was sequence value");

    [Fact]
    public void Eval_Sum_ProjectedNestedSequenceValueSelection_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            sum(A:0)
            """,
            "sum expects each collection element to be a single numeric value; item 0 was sequence value");

    // ── Avg builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Avg_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("avg(range(1, 5))", 3);

    [Fact]
    public void Eval_Avg_DotCallReceiverAsSingleSource_ExpandsRangeItems()
        => AssertEval("range(1, 5).avg", 3);

    [Fact]
    public void Eval_Avg_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            avg(Data:0)
            (Data:0).avg
            """;

        AssertEval(source, 4, 4);
    }

    [Fact]
    public void Eval_Avg_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(10, 4, 7).avg", 7);

    [Fact]
    public void Eval_Avg_SequenceValueReceiver_DotCallAveragesSequenceItems()
    {
        var source = """
            Values = (10, 20, 30)
            Values.avg
            """;

        AssertEval(source, 20);
    }

    [Fact]
    public void Eval_Avg_NonExactPositiveMean_ReturnsDecimalMean()
        => AssertEval("avg((1, 2))", 1.5m);

    [Fact]
    public void Eval_Avg_NonExactNegativeMean_ReturnsDecimalMean()
        => AssertEval("avg((-1, -2))", -1.5m);

    [Fact]
    public void Eval_Avg_NegativeMeanTowardZero_ReturnsDecimalMean()
        => AssertEval("avg((-1, 0))", -0.5m);

    [Fact]
    public void Eval_Avg_ExactMultiArgMean_ReturnsInteger()
        => AssertEval("avg((1, 2, 3))", 2);

    [Fact]
    public void Eval_Avg_FractionalMeanViaSumOverCount_KeepsDecimal()
        => AssertEval("sum((-1, -2)) / count((-1, -2))", -1.5m);

    [Fact]
    public void Eval_Avg_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("avg(5)", 5);

    [Fact]
    public void Eval_Avg_DirectCallMultiArgs_ComputesMean()
        => AssertEval("avg((10, 20, 30))", 20);

    [Fact]
    public void Eval_Avg_SequenceValueElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "avg(((1, 2), (3, 4)))",
            "avg expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Avg_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "avg('hello')",
            "avg expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Avg_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "avg((1, (2, 3)))",
            "avg expects each collection element to be a single numeric value; item 1 was sequence value");

    [Fact]
    public void Eval_Sum_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 20, 30
            sum(Values)
            """;

        AssertEval(source, 60);
    }

    [Fact]
    public void Eval_Min_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 4, 7
            min(Values)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Max_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 4, 7
            max(Values)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Avg_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 20, 30
            avg(Values)
            """;

        AssertEval(source, 20);
    }
}
