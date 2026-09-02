using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorSequenceCallbackTests
{
    private static void AssertFilterPredicateShapeFails(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("filter predicate must return exactly one atomic numeric value", formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("filter predicate must return exactly one atomic numeric value"));
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertReduceStepShapeFails(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("reduce step must return a single accumulator value", formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("reduce step must return a single accumulator value"));
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertMapTransformShapeFails(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("map transform must return a single element", formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("map transform must return a single element"));
        Assert.IsType<EvalError.BadArity>(error);
    }

    // ── Filter builtin ───────────────────────────────────────────────────────

    [Fact]
    public void Eval_Filter_DirectCallMultiArgs_KeepsMatchingItems()
    {
        var source = """
            IsEven = x mod 2 == 0
            filter((1, 2, 3, 4, 5, 6), IsEven)
            """;
        AssertEval(source, 2, 4, 6);
    }

    // Variadic-style top-level binding contract.

    [Fact]
    public void Eval_Filter_BoundaryLaw_CommaSeparatedRangeSourceExpandsTopLevelItems()
    {
        var source = """
            IsEven = x mod 2 == 0
            filter((range(3, 6)*, 8), IsEven)
            """;

        AssertEval(source, 4, 6, 8);
    }

    [Fact]
    public void Eval_Filter_BoundaryLaw_NamedMultiOutputSingleSourceExpands()
    {
        var source = """
            IsEven = x mod 2 == 0
            Data = 3, 4, 5, 6
            filter(Data, IsEven)
            """;

        AssertEval(source, 4, 6);
    }

    [Fact]
    public void Eval_Filter_BoundaryLaw_DotCallReceiverExpandsAsSingleSource()
    {
        var source = """
            IsEven = x mod 2 == 0
            Data = 3, 4, 5, 6
            Data.filter(IsEven)
            """;

        AssertEval(source, 4, 6);
    }

    [Fact]
    public void Eval_Filter_BoundaryLaw_CommaSeparatedNamedMultiOutputExpandsTopLevelItems()
    {
        var source = """
            IsEven = x mod 2 == 0
            Data = 3, 4, 5, 6
            filter((Data*, 8), IsEven)
            """;

        AssertEval(source, 4, 6, 8);
    }

    [Fact]
    public void Eval_Filter_RangeArgument_IteratesEmittedItemsForPredicate()
    {
        var source = """
            KeepWholeRange((a, b, c, d, e)) = 1
            KeepWholeRange(x) = 0
            filter(range(1, 5), KeepWholeRange)
            """;

        AssertEval(source);
    }

    [Fact]
    public void Eval_Filter_DirectCallMixedArgs_ExpandsRangeTopLevelItemsForPredicate()
    {
        var source = """
            KeepWideRange((a, b, c, d)) = 1
            KeepWideRange(x) = 0
            filter(((1, 2), range(3, 6)*), KeepWideRange)
            """;

        AssertEval(source);
    }

    [Fact]
    public void Eval_Filter_SequenceValueElements_ArePreservedWhole()
    {
        var source = """
            KeepPair = pair:0 mod 2 == 0
            filter(((1, 10), (2, 20), (3, 30), (4, 40)), KeepPair)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // The kept pairs stay whole sequence values, held as exact list elements.
        AssertListOfSequenceValueAtoms(result.Value, [2m, 20m], [4m, 40m]);
    }

    [Fact]
    public void Eval_Filter_MultiOutputPredicate_FailsWithContext()
    {
        var source = """
            Bad(x) = 0, 999
            filter((1, 2, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_SequenceValuePredicateResult_FailsWithContext()
    {
        var source = """
            Bad(x) = (1, 0)
            filter((1, 2, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_EmptyPredicateResult_FailsWithContext()
    {
        var source = """
            Bad(x) = take(1, 0)
            filter((1, 2, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_StringPredicateResult_FailsWithContext()
    {
        var source = """
            Bad(x) = x.string
            filter((1, 2, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_ArityMismatch_FollowsBuiltinConvention()
    {
        // filter(collection, predicate) is an ordinary fixed-arity callable:
        // a zero-argument call is a plain arity error carrying the fixed
        // signature.
        var result = EvalFull("filter()");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            "Callable `filter(collection, predicate)` expects 2 arguments, but was called with 0 arguments.",
            formatted);

        var error = result.Error;
        while (error is EvalError.WithContext wc)
            error = wc.Inner;

        Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.False(error is EvalError.VariadicArityMismatch);
    }

    // ── Map builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Map_DirectCallMultiArgs_TransformsEachItem()
    {
        var source = """
            Double = x * 2
            map((1, 2, 3), Double)
            """;

        AssertEval(source, 2, 4, 6);
    }

    [Fact]
    public void Eval_Map_NativeCallbackReference_BindsCallbackArguments()
    {
        // A native-call wrapper (here the Math alias `abs`) works DIRECTLY as a
        // flat callback: its body reads the argument name counted-first, the
        // same dual-view order as Expr.Param, so it sees the callback-bound
        // element rather than failing with `Unknown name: x`.
        AssertEval("[1, -2].map(abs)", 1, 2);
    }

    [Fact]
    public void Eval_Map_NativeCallbackReference_IgnoresSameNamedAmbientValue()
    {
        // The regression that motivated counted-first lookup: an ambient value
        // named like the native's parameter (`x` here) must never be captured in
        // place of the callback-bound element. valEnv-only lookup returned
        // [5, 5] for this program.
        AssertEval("F(x) = [1, -2].map(abs)\nF(5)", 1, 2);
    }

    [Fact]
    public void Eval_Map_NativeCallbackReference_NonXParameterName_BindsElement()
    {
        // Same rule for a native whose parameter is not `x`: `sin(radians)`
        // maps the elements 0 and 1, ignoring the ambient `radians = 0.5`.
        var direct = Eval("sin(0), sin(1)");
        Assert.False(direct.IsError);
        var mapped = Eval("G(radians) = [0, 1].map(sin)\nG(0.5)");
        Assert.False(mapped.IsError);
        Assert.Equal(direct.Value, mapped.Value);
    }

    [Fact]
    public void Eval_Repeat_NativeStepReference_BindsLoopStateArgument()
    {
        // Loop steps bind their state through the same counted funnel as flat
        // callbacks, so a native-call wrapper works as a step reference too.
        AssertEval("repeat(abs, 2, -5)", 5);

        // The loop-step binder must also shadow a same-named counted binding
        // inherited from an enclosing callback before the native body runs.
        AssertEval("F(x) = repeat(abs, 2, -5)\n[99].map(F)", 5);
    }

    [Fact]
    public void Eval_Reduce_TwoParameterNativeCallbackReference_BindsBothArguments()
    {
        // Reduce supplies element then accumulator. Both callback-bound values
        // must beat the enclosing counted x/y bindings when pow's native body
        // looks up its two declared arguments: 2^1 = 2, then 3^2 = 9.
        AssertEval("F(x, y) = reduce([2, 3], pow, 1)\nF(100, 200)", 9);
    }

    [Fact]
    public void Eval_DirectNativeCall_ValEnvFallback_Unchanged()
    {
        // Direct calls bind the native's parameter into the value environment;
        // the counted-first lookup falls through to it unchanged.
        AssertEval("abs(-2)", 2);
        AssertEval("F(x) = abs(x)\nF(-3)", 3);
    }

    [Fact]
    public void Eval_DirectNativeCall_InsideCountedCallbackContext_BindsCallArgument()
    {
        // A direct native call inside a callback body must NOT read the
        // caller's counted binding: flat fixed binding shadows the callee's
        // parameter names out of the counted environment, so `abs(-2)` binds
        // x = -2 in the value environment even while a counted `x = 5` exists.
        AssertEval("K(x) = abs(-2)\n[5].map(K)", 2);
    }

    [Fact]
    public void Eval_Map_RangeArgument_IteratesEmittedItemsForHigherOrderIteration()
    {
        var source = """
            TopLevelItemCount(item) = item.count
            map(range(3, 6), TopLevelItemCount)
            """;

        AssertEval(source, 1, 1, 1, 1);
    }

    [Fact]
    public void Eval_Map_PreservesOriginalOrder()
    {
        var source = """
            Tag = x * 10 + 1
            map((5, 4, 3, 2, 1), Tag)
            """;

        AssertEval(source, 51, 41, 31, 21, 11);
    }

    [Fact]
    public void Eval_Map_RangeArgument_WithScalarTransform_MapsEachEmittedItem()
    {
        var source = """
            AddOne = x + 1
            map(range(1, 5), AddOne)
            """;

        AssertEval(source, 2, 3, 4, 5, 6);
    }

    [Fact]
    public void Eval_Map_DirectCallMixedArgs_ExpandsRangeTopLevelItems()
    {
        var source = """
            MarkSequenceValueRange((a, b, c)) = 1
            MarkSequenceValueRange(x) = 0
            map((1, range(2, 4)*), MarkSequenceValueRange)
            """;

        AssertEval(source, 0, 0, 0, 0);
    }

    [Fact]
    public void Eval_Map_SequenceValueElements_ArePassedWhole()
    {
        var source = """
            TakeValue = pair:1
            map(((1, 10), (2, 20), (3, 30)), TakeValue)
            """;

        AssertEval(source, 10, 20, 30);
    }

    [Fact]
    public void Eval_Map_SequenceValueTransformResult_IsAccepted()
    {
        var source = """
            PairWithSquare(x) = (x, x * x)
            map((1, 2, 3), PairWithSquare)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // Each mapped sequence value is one exact list element of the map result.
        AssertListOfSequenceValueAtoms(result.Value, [1m, 1m], [2m, 4m], [3m, 9m]);
    }

    [Fact]
    public void Eval_Map_EmptyTransformResult_FailsWithContext()
    {
        // A transform whose body is the truly empty result `()` still fails the
        // strict single-element contract. (A collection builtin like take(1, 0)
        // no longer produces this failure — it returns the empty list [], which
        // is one valid element; see the exact-list acceptance test below.)
        var source = """
            Bad(x) = ()
            map((1, 2, 3), Bad)
            """;

        AssertMapTransformShapeFails(source);
    }

    [Fact]
    public void Eval_Map_EmptyListTransformResult_IsOneMappedElementPerItem()
    {
        // take(1, 0) returns the exact empty list value [] — ONE valid mapped
        // element per item, so the transform succeeds with result [[], [], []].
        AssertEvalCounted(
            """
            EmptyList(x) = take(1, 0)
            map((1, 2, 3), EmptyList)
            """,
            1,
            ListValue(ListValue(), ListValue(), ListValue()));
    }

    [Fact]
    public void Eval_Map_MultiOutputTransformResult_FailsWithContext()
    {
        var source = """
            Bad(x) = x, x * x
            map((1, 2, 3), Bad)
            """;

        AssertMapTransformShapeFails(source);
    }

    // ── Reduce builtin ───────────────────────────────────────────────────────

    [Fact]
    public void Eval_Reduce_DirectCallMultiArgs_AddsLeftToRight()
    {
        var source = """
            Add = x + total
            reduce((1, 2, 3, 4), Add, 0)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Reduce_RangeArgument_IteratesEmittedItemsForHigherOrderIteration()
    {
        var source = """
            AddItemCount(item, acc) = item.count + acc
            reduce(range(3, 6), AddItemCount, 0)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Reduce_DirectCallMixedArgs_PreservesRangeBoundary()
    {
        var source = """
            AddItemCount(x, acc) = x.count + acc
            reduce(((1, 2), range(3, 4)*), AddItemCount, 0)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Reduce_DirectCallMixedArgs_ExpandsRangeTopLevelItemsForStep()
    {
        var source = """
            AddSequenceValueRange((a, b, c), acc) = acc + 100
            AddSequenceValueRange(x, acc) = acc + x
            reduce((1, range(2, 4)*), AddSequenceValueRange, 0)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Reduce_NamedMultiOutputArgument_IteratesEmittedItems()
    {
        var source = """
            Left = 3, 4, 2, 1, 3, 3
            Right = 4, 3, 5, 3, 9, 3

            CountMatchStep(element, tt) = {
                T = atoms(tt)
                (T.first, T:1 + if(element == T.first, 1, 0))
            }

            MatchCount = reduce(Right, CountMatchStep, (value, 0)):1
            SimilarityAt = value * MatchCount(value)
            Part2 = Left.map(SimilarityAt).sum
            Part2
            """;

        AssertEval(source, 31);
    }

    [Fact]
    public void Eval_Reduce_IsLeftToRight()
    {
        var source = """
            Digits = x + acc * 10
            reduce((1, 2, 3, 4), Digits, 0)
            """;

        AssertEval(source, 1234);
    }

    [Fact]
    public void Eval_Reduce_ArityMismatch_ReportsFixedThreeArgumentSignature()
    {
        // reduce(collection, reducer, initial) is an ordinary fixed-arity
        // callable: an under-supplied call is a plain arity error carrying the
        // fixed signature.
        var result = EvalFull(
            """
            Add = x + total
            reduce(1)
            """);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            "Callable `reduce(collection, reducer, initial)` expects 3 arguments, but was called with 1 argument.",
            formatted);

        var error = result.Error;
        while (error is EvalError.WithContext wc)
            error = wc.Inner;

        Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.False(error is EvalError.VariadicArityMismatch);

        // The old two-argument shape (collection + reducer, no initial) is the
        // same kind of plain arity error — no suffix binding, no hint.
        AssertEvalFailsWithArityMismatch("Add = x + total\nreduce((1, 2, 3), Add)", expected: 3, actual: 2);
    }

    [Fact]
    public void Eval_Reduce_ParameterizedInitialAccumulator_ReportsCallSiteWithHint()
    {
        // A fully supplied reduce(collection, reducer, initial) whose `initial`
        // argument is a parameterized algorithm cannot evaluate the starting
        // accumulator, so the call-site hint fires (rather than a generic
        // unknown-name error).
        var result = EvalFull("Add = x + total\nreduce((1, 2, 3), {a + b}, Add)");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error);
        Assert.Equal(2, formatted.StartLine);
        Assert.Equal(1, formatted.StartColumn);
        Assert.Contains("the last argument must be an initial accumulator value", formatted.Message);
        Assert.Contains("still needs 'x' and 'total'", formatted.Message);
        Assert.DoesNotContain("Unknown name: x", formatted.Message);
    }

    [Fact]
    public void Eval_Reduce_DotCallParameterizedInitialAccumulator_ReportsCallSiteWithHint()
    {
        var result = EvalFull(
            """
            Add = x + total
            Values = 1, 2, 3
            Values.reduce(Add)
            """);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error);
        Assert.Equal(3, formatted.StartLine);
        Assert.Equal(1, formatted.StartColumn);
        Assert.Contains("`reduce` is `reduce(collection, reducer, initial)`", formatted.Message);
        Assert.Contains("'x' and 'total'", formatted.Message);
        Assert.Contains("add an initial accumulator", formatted.Message);
        Assert.DoesNotContain("Unknown name: x", formatted.Message);
        Assert.DoesNotContain("Bad arity", formatted.Message);
    }

    [Fact]
    public void Eval_Reduce_DotCallOrdinaryValueWithMissingArgument_ReportsFixedArity()
    {
        // The missing-initial hint is specific to the common X.reduce(F)
        // mistake where F is visibly a parameterized reducer. An ordinary
        // value is not misdescribed as an unevaluable initial accumulator.
        var result = EvalFull("Values = 1, 2, 3\nValues.reduce(0)");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error);
        Assert.Equal(2, formatted.StartLine);
        Assert.Equal(1, formatted.StartColumn);
        Assert.Equal(
            "Callable `reduce(collection, reducer, initial)` expects 3 arguments, but was called with 2 arguments.",
            formatted.Message);
    }

    [Fact]
    public void Eval_Reduce_SequenceValueElements_ArePassedWhole()
    {
        var source = """
            TakeValue((tag, value), acc) = acc + value
            reduce(((1, 10), (2, 20), (3, 30)), TakeValue, 0)
            """;

        AssertEval(source, 60);
    }

    [Fact]
    public void Eval_Reduce_SequenceValueAccumulator_IsAccepted()
    {
        var source = """
            Stats(x, acc) = (x + acc:0, acc:1 + 1)
            reduce((1, 2, 3, 4), Stats, (0, 0))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Collection(
            group.Items,
            first => Assert.Equal(10m, Assert.IsType<Result.Atom>(first).Value),
            second => Assert.Equal(4m, Assert.IsType<Result.Atom>(second).Value));
    }

    [Fact]
    public void Eval_Reduce_VariadicAccumulatorState_FlattensNaturally()
    {
        var source = """
            Append(item, *history) = (history*, item)
            reduce((2, 3, 4), Append, 1)
            """;

        AssertEvalResultSequenceModes(source, ResultFromAtoms(1, 2, 3, 4));
    }

    [Fact]
    public void Eval_Reduce_ScalarReducerBehavior_RemainsUnchanged()
    {
        var source = """
            Sum(item, total) = total + item
            reduce((2, 3, 4), Sum, 1)
            """;

        AssertEvalSequenceModes(source, 10);
    }

    [Fact]
    public void Eval_Reduce_NonVariadicAccumulator_PreservesStructuralAccumulator()
    {
        var source = """
            Append(item, history) = (history*, item)
            reduce((2, 3, 4), Append, 1)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.SequenceValue>(result.Value);
        AssertSequenceValueAtoms(outer, 1, 2, 3, 4);
    }

    [Fact]
    public void Eval_Reduce_SequenceValueElements_AndSequenceValueAccumulator_ArePassedWhole()
    {
        var source = """
            TakeStats((tag, value), (sum, count)) = (sum + value, count + 1)
            reduce(((1, 10), (2, 20), (3, 30)), TakeStats, (0, 0))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Collection(
            group.Items,
            first => Assert.Equal(60m, Assert.IsType<Result.Atom>(first).Value),
            second => Assert.Equal(3m, Assert.IsType<Result.Atom>(second).Value));
    }

    [Fact]
    public void Eval_Reduce_SequenceValueReceiver_DotCall_ProjectsCurrentItemLikeSelection()
    {
        var source = """
            AddItemCount(item, acc) = item.count + acc
            Values = (1, 2, 3)
            Values.reduce(AddItemCount, 0)
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Reduce_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Add = x + total
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            reduce(Data:0, Add, 0)
            (Data:0).reduce(Add, 0)
            """;

        AssertEval(source, 20, 20);
    }

    [Fact]
    public void Eval_Reduce_CurrentItem_MatchesSelection_PlainAndDotCall()
    {
        var source = """
            Signature(current, acc) = acc * 100 + current.count * 10 + current.sum
            Items = (1, 2), (3, 4)
            (Items:0).count
            (Items:0).sum
            (Items:1).count
            (Items:1).sum
            Items.reduce(Signature, 0)
            reduce(((1, 2), (3, 4)), Signature, 0)
            """;

        AssertEval(source, 2, 3, 2, 7, 2327, 2327);
    }

    [Fact]
    public void Eval_Reduce_CurrentItem_ProjectsOneLevelOnly()
    {
        var source = """
            Signature(current, acc) = acc * 100 + current.count * 10 + (current:0).count
            Items = ((1, 2), (3, 4))
            (Items:0).count
            Items.reduce(Signature, 0)
            reduce(((1, 2), (3, 4)), Signature, 0)
            """;

        AssertEval(source, 2, 2121, 2121);
    }

    [Fact]
    public void Eval_Reduce_Accumulator_DoesNotAutoProject()
    {
        var source = """
            Signature(current, acc) = (acc:0 * 100 + current.count * 10 + acc.count, acc.count)
            Items = (1, 2), (3, 4)
            Items.reduce(Signature, (0, 9, 8))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertSequenceValueAtoms(result.Value, 2322m, 2m);
    }

    [Fact]
    public void Eval_Reduce_EmptyStepResult_FailsWithContext()
    {
        // A step whose body is the truly empty result `()` still fails the strict
        // single-accumulator contract. (A collection builtin like take(1, 0) no
        // longer produces this failure — it returns the empty list [], which is
        // one valid accumulator value; see the exact-list acceptance test below.)
        var source = """
            Bad(x, acc) = ()
            reduce((1, 2, 3), Bad, 0)
            """;

        AssertReduceStepShapeFails(source);
    }

    [Fact]
    public void Eval_Reduce_ListValuedStepResult_IsAcceptedAsAccumulator()
    {
        // take(a, 1) returns an exact list — ONE valid accumulator value per
        // step, so the final accumulator is the last step's list [3].
        AssertEvalCounted(
            """
            Step(a, acc) = take(a, 1)
            reduce((1, 2, 3), Step, 0)
            """,
            1,
            ListValue(Atom(3)));
    }

    [Fact]
    public void Eval_Reduce_MultiOutputStepResult_FailsWithContext()
    {
        var source = """
            Bad(x, acc) = acc, x
            reduce((1, 2, 3), Bad, 0)
            """;

        AssertReduceStepShapeFails(source);
    }

    // -- Callback runtime binding characterization -------------------------

    [Fact]
    public void Eval_Callback_TopLevelVariadicMap_CollectsOneElementSlotPerInvocation()
    {
        var source = """
            Count(*values) = values.count
            map((1, 2, 3), Count)
            """;

        // A single-variadic callback receives each iterated element as ONE collected
        // slot: values = [element], so values.count is 1 per invocation.
        AssertEvalSequenceModes(source, 1, 1, 1);

        // values.count cannot distinguish scalar binding (values = 7) from
        // list collection (values = [7]); the identity/equality forms below
        // pin the collected list kind exactly.
        var identity = EvalFull(
            """
            Collect(*values) = values
            map((7, 8), Collect)
            """);
        Assert.True(identity.IsOk, $"expected success: {(identity.IsError ? identity.Error.ToString() : "")}");
        var mapped = Assert.IsType<Result.ListValue>(identity.Value);
        Assert.Collection(
            mapped.Items,
            first =>
            {
                var collected = Assert.IsType<Result.ListValue>(first);
                Assert.Equal([new Result.Atom(7)], collected.Items, Result.ValueComparer);
            },
            second =>
            {
                var collected = Assert.IsType<Result.ListValue>(second);
                Assert.Equal([new Result.Atom(8)], collected.Items, Result.ValueComparer);
            });

        AssertEvalSequenceModes(
            """
            IsSingleSeven(*values) = values == [7]
            map((7, 8), IsSingleSeven)
            """,
            1, 0);
    }

    [Fact]
    public void Eval_Callback_TopLevelVariadicFilter_CollectsOneElementSlotPerInvocation()
    {
        var source = """
            One(*values) = values.count == 1
            filter((1, 2, 3), One)
            """;

        // Single-variadic predicate callbacks collect one element slot per
        // invocation, so values.count == 1 succeeds for every source item.
        AssertEvalSequenceModes(source, 1, 2, 3);

        // Kind-sensitive form: the predicate observes the collected LIST
        // [element], not the bare scalar (7 == [7] is false, [7] == [7] true).
        AssertEvalSequenceModes(
            """
            IsSingleSeven(*values) = values == [7]
            filter((7, 8), IsSingleSeven)
            """,
            7);
    }

    [Fact]
    public void Eval_Callback_TopLevelVariadicReduce_CollectsElementSlotBeforeAccumulator()
    {
        var source = """
            Step(*values, acc) = values.count * 10 + acc
            reduce((1, 2, 3), Step, 0)
            """;

        // A reducer collecting parameter in element position collects the projected item as
        // [element] each step; the accumulator stays a separate fixed slot.
        AssertEvalSequenceModes(source, 30);

        // Kind-sensitive form: the step observes the collected list [element].
        AssertEvalSequenceModes(
            """
            Step(*values, acc) = acc + (values == [3])
            reduce((1, 2, 3), Step, 0)
            """,
            1);
    }

    [Fact]
    public void Eval_Callback_FlatFixedArityFailure_PreservesCurrentDiagnosticShape()
    {
        var result = EvalFull(
            """
            NeedTwo(a, b) = a + b
            map((1, 2), NeedTwo)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("while evaluating map transform", formatted);
        Assert.DoesNotContain("NeedTwo", formatted);

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(2, arity.Expected);
        Assert.Equal(1, arity.Actual);
    }

    [Fact]
    public void Eval_Callback_SequenceValuePatternWrongShape_DoesNotFlattenScalarItems()
    {
        var result = EvalFull(
            """
            PairSum((x, y)) = x + y
            map((1, 2), PairSum)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("while evaluating map transform", formatted);

        Assert.IsType<EvalError.BadArity>(Innermost(result.Error));
    }

    [Fact]
    public void Eval_Callback_RepeatedSequenceValueBinderUsesEqualityConstraint()
    {
        AssertEvalSequenceModes(
            """
            Same((x, x)) = x
            map(((1, 1), (2, 2)), Same)
            """,
            1, 2);

        var result = EvalFull(
            """
            Same((x, x)) = x
            map((1, 2), Same)
            """);
        Assert.True(result.IsError);
        Assert.IsType<EvalError.BadArity>(Innermost(result.Error));
    }

    [Fact]
    public void Eval_Callback_RepeatedConditionalBinderFallsThrough()
    {
        AssertEvalSequenceModes(
            """
            Equal((x, x)) = 1
            Equal((x, y)) = 0
            map(((1, 1), (1, 2)), Equal)
            """,
            1, 0);
    }

    [Fact]
    public void Eval_Callback_ConditionalPredicateNoMatch_PreservesFilterDiagnosticShape()
    {
        var result = EvalFull(
            """
            Keep(0) = 1
            filter(1, Keep)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("while evaluating filter predicate for item 0: 1", formatted, StringComparison.Ordinal);

        var noMatch = Assert.IsType<EvalError.NoMatchingBranch>(Innermost(result.Error));
        Assert.Equal("filter predicate", noMatch.AlgorithmName);
    }

    [Fact]
    public void Eval_Callback_SequenceValueMapPatternWrongGroupArity_PreservesArityMismatch()
    {
        var result = EvalFull(
            """
            PairSum((x, y)) = x + y
            map(((1, 2, 3)), PairSum)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("while evaluating map transform", formatted, StringComparison.Ordinal);

        Assert.IsType<EvalError.BadArity>(Innermost(result.Error));
    }

    [Fact]
    public void Eval_Callback_DoesNotBindAlgorithmChannelForIteratedItems()
    {
        var result = EvalFull(
            """
            Thunk = 42
            Apply(f) = f()
            map(Thunk, Apply)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("while evaluating map transform", formatted, StringComparison.Ordinal);

        var notAlgorithm = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(result.Error));
        Assert.Equal("param(f)", notAlgorithm.Description);
    }

    [Fact]
    public void Eval_Callback_ConditionalPredicate_UsesConditionalCallbackPath()
    {
        var source = """
            Keep(0) = 0
            Keep(x) = 1
            filter((0, 1, 2), Keep)
            """;

        AssertEvalSequenceModes(source, 1, 2);
    }

    [Fact]
    public void Eval_Callback_BuiltinMapper_UsesCustomBuiltinCountedPath()
    {
        var source = """
            map(((1, 2), (3, 4, 5)), count)
            """;

        AssertEvalSequenceModes(source, 2, 3);
    }

    // ── Higher-order boundary regressions ───────────────────────────────────

    [Fact]
    public void Eval_Filter_InlineBraceReceiver_DotCallPreservesBoundary()
    {
        var source = """
            IsLarge = x > 1
            {1, 2, 3, 4}.filter(IsLarge)
            """;

        AssertEval(source, 2, 3, 4);
    }

    [Fact]
    public void Eval_Filter_SequenceValueReceiver_DotCallIteratesSequenceItems()
    {
        var source = """
            KeepSecondEven(pair) = pair:1 mod 2 == 0
            Values = (1, 2), (3, 5)
            Values.filter(KeepSecondEven)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // Only (1, 2) is kept; it stays an exact list element, so the result is
        // the exact list [(1, 2)].
        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m]);
    }

    [Fact]
    public void Eval_Map_InlineParenReceiver_DotCallPreservesBoundary()
    {
        var source = """
            AddOne = x + 1
            (1, 2, 3).map(AddOne)
            """;

        AssertEval(source, 2, 3, 4);
    }

    [Fact]
    public void Eval_Map_RecursiveCallback_UsesCurrentValueBinding()
    {
        var source = """
            Factorial = if(n == 0, 1, Factorial(n - 1) * n)
            (0, 1, 2, 3, 4).map(Factorial)
            """;

        AssertEval(source, 1, 1, 2, 6, 24);
    }

    [Fact]
    public void Eval_Reduce_InlineParenReceiver_DotCall_UsesTopLevelItems()
    {
        var source = """
            Add = x + total
            (1, 2, 3).reduce(Add, 0)
            """;

        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_Map_SequenceValueReceiver_DotCall_ProjectsCallbackItemLikeSelection()
    {
        var source = """
            TakeFirst(x) = x:0
            Values = (1, 2, 3)
            Values.map(TakeFirst)
            """;

        AssertEval(source, 1, 2, 3);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_UsesReceiverTopLevelItemsAndProjectedCallbackCounts()
    {
        var source = """
            Items = range(1, 3), 7
            Items.count
            (Items:0).count
            (Items:1).count
            Items.map{x.count}
            """;

        AssertEval(source, 2, 3, 1, 3, 1);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_FilterAndSelectionUseProjectedCallbackItems()
    {
        var source = """
            Items = range(1, 3), 7
            Items.map{x:0}
            Items.filter{x.count == 3}.count
            """;

        // range(1, 3) is an exact list item bound whole to the callback param:
        // `x:0` selects its first stored element (1), while the scalar item 7
        // projects to itself, so the map materializes [1, 7]. filter keeps the
        // one list item whose opened count is 3, and .count reports the
        // kept-item count 1.
        AssertEval(source, 1, 7, 1);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_SequenceValueNamedReceiver_DoesNotAutoExpand()
    {
        var source = """
            TopLevelItemCount(item) = item.count
            AddTopLevelItemCount(item, acc) = item.count + acc
            Pairs = ((1, 2), (3, 4))
            Pairs.count
            Pairs.map(TopLevelItemCount)
            Pairs.reduce(AddTopLevelItemCount, 0)
            """;

        AssertEval(source, 2, 2, 2, 4);
    }

    [Fact]
    public void Eval_Map_CallbackItem_FirstProjectionMatchesSelection()
    {
        var source = """
            TakeFirst(report) = report:0
            map(((7, 6, 4, 2, 1), (1, 2, 7, 8, 9)), TakeFirst)
            """;

        AssertEval(source, 7, 1);
    }

    [Fact]
    public void Eval_Map_SequenceValuePairs_ProjectOneLevelOnly()
    {
        var source = """
            TakeFirst(x) = x:0
            map(((1, 2), (3, 4)), TakeFirst)
            """;

        AssertEval(source, 1, 3);
    }

    [Fact]
    public void Eval_Filter_PracticalSafeReportStyle_UsesProjectedCallbackReport()
    {
        var source = """
            IsSafe(report) =
                report:0 > report:(0 + 1) and
                report:1 > report:(1 + 1) and
                report:2 > report:(2 + 1) and
                report:3 > report:(3 + 1) and
                report:0 - report:(0 + 1) <= 3 and
                report:1 - report:(1 + 1) <= 3 and
                report:2 - report:(2 + 1) <= 3 and
                report:3 - report:(3 + 1) <= 3
            filter(((7, 6, 4, 2, 1), (1, 2, 7, 8, 9)), IsSafe)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // Only the first report is kept; it stays an exact list element, so the
        // result is the exact list [(7, 6, 4, 2, 1)].
        AssertListOfSequenceValueAtoms(result.Value, [7m, 6m, 4m, 2m, 1m]);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_IndexedSequenceValueReceiver_ProjectsOneLevel()
    {
        var source = """
            TopLevelItemCount(item) = item.count
            AddTopLevelItemCount(item, acc) = item.count + acc
            Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            (Bags:0).count
            (Bags:0).map(TopLevelItemCount)
            (Bags:0).reduce(AddTopLevelItemCount, 0)
            """;

        AssertEval(source, 2, 2, 2, 4);
    }

    // ── Uniform counted sequence extraction regressions ────────────────────

    [Fact]
    public void Eval_Filter_WrapperSequenceOutput_IteratesSequenceValueItems()
    {
        var source = """
            KeepSecondEven(pair) = pair:1 mod 2 == 0
            Values = (1, 2), (3, 5)
            filter(Values, KeepSecondEven)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // Only (1, 2) is kept; it stays an exact list element, so the result is
        // the exact list [(1, 2)].
        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m]);
    }

    [Fact]
    public void Eval_Map_WrapperSequenceOutput_MapsSequenceValueItems()
    {
        var source = """
            TakeValue(pair) = pair:1
            Values = ((1, 2), (3, 4))
            map(Values, TakeValue)
            """;

        AssertEval(source, 2, 4);
    }

    [Fact]
    public void Eval_Reduce_WrapperSingleSequenceValueOutput_FoldsWholeGroupOnce()
    {
        var source = """
            AddValue(pair, total) = total + pair:1
            Values = ((1, 2), (3, 4))
            reduce(Values, AddValue, 0)
            """;

        AssertEval(source, 6);
    }
}
