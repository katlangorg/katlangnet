using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorUserCallTests
{
    // â”€â”€ User-defined functions â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_UserFunction_SingleParam()
    {
        var source = """
            F = x + 1
            F(5)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_UserFunction_MultipleParams()
    {
        var source = """
            Add = a + b
            Add(3, 4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_UserFunction_WithBraces()
    {
        var source = """
            Double = x * 2
            Double{3}
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_UserFunction_ReturnsMultipleOutputs()
    {
        var source = """
            Swap = a, b
            Swap(1, 2)
            """;
        AssertEval(source, 1, 2);
    }

    [Fact]
    public void Eval_UserFunction_Chained()
    {
        var source = """
            F = x + 1
            F(F(1))
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_UserFunction_RecursiveProperty()
    {
        var source = """
            Numbers = 3, 5, 9
            Numbers:0
            """;
        AssertEval(source, 3);
    }

    // â”€â”€ Complex examples â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_SumExample_Returns24()
    {
        var source = """
            Numbers = 3, 5, 9, 1, 0, 6
            Add = a + 1, total + Numbers:a
            Sum = repeat(Add, (6), 0, 0) : 1
            Sum
            """;
        AssertEval(source, 24);
    }

    [Fact]
    public void Eval_Fibonacci()
    {
        var source = """
            Fib = a + b, a
            repeat(Fib, (10), 1, 0):0
            """;
        AssertEval(source, 89);
    }

    [Fact]
    public void Eval_ConditionalMax()
    {
        AssertEval("if(5 > 3, (5), (3))", 5);
        AssertEval("if(2 > 7, (2), (7))", 7);
    }

    // Spread

    [Fact]
    public void Eval_SequenceSpread_SpreadsReferencedResults()
    {
        var source = """
            A = 1, 2
            B = 3, 4
            atoms((A*, B))
            """;
        AssertEval(source, 1, 2, 3, 4);
    }

    [Fact]
    public void Eval_PlainFlatFixedUserCall_UsesExplicitParameters()
    {
        AssertEval(
            """
            Add(x, y) = x + y
            Add(2, 3)
            """,
            5);
    }

    [Fact]
    public void Eval_PlainFlatFixedUserCall_UsesImplicitParameters()
    {
        AssertEval(
            """
            Add = x + y
            Add(2, 3)
            """,
            5);
    }

    [Fact]
    public void Eval_Count_UserCallFlatFixedMirrorCountsCurrentOutputShape()
    {
        AssertEval(
            """
            Pair(x, y) = x, y
            Pair(2, 3).count
            """,
            2);
    }

    [Fact]
    public void Eval_PlainFlatFixedUserCall_PreservesAlgorithmValueDualBinding()
    {
        AssertEval(
            """
            Apply(f, x) = f(x)
            Double(n) = n * 2
            Apply(Double, 4)
            """,
            8);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_ArgumentExpressionsAreEvaluatedIndependently()
    {
        var result = EvalFull(
            """
            Use(a, b) = a + b
            Use(1, a)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(result.Error));
        Assert.Equal(["a"], unresolved.ParamNames);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_MultiOutputPropertyReferenceDoesNotUnpack()
    {
        var arity = AssertEvalFailsWithArityMismatch(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair)
            """,
            expected: 2,
            actual: 1);

        Assert.NotNull(arity.Signature);
        Assert.Equal("Add(x, y)", arity.Signature.DisplayText);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_ExplicitSpreadOpensMultiOutputPropertyReference()
    {
        AssertEval(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair*)
            """,
            30);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_DotCallMultiOutputDoesNotBecomeArgumentSpreading()
    {
        // A multi-output dot-call expression (here `.atoms`) is still ONE
        // argument expression in a flat fixed call; only an explicit spread marker opens it.
        AssertEvalFailsWithArityMismatch(
            """
            Pair = (10, 20)
            Add(x, y) = x + y
            Add(Pair.atoms)
            """,
            expected: 2,
            actual: 1);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_SeparateCommaArgumentsStillWork()
    {
        AssertEval(
            """
            Add(x, y) = x + y
            Add(10, 20)
            """,
            30);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_ExplicitIndexingStillWorks()
    {
        AssertEval(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair:0, Pair:1)
            """,
            30);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_MixedPrefixPlusMultiOutputExpressionDoesNotUnpack()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Tail = 2, 3
            Use(a, b, c) = a + b + c
            Use(1, Tail)
            """,
            expected: 3,
            actual: 2);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_ExplicitPropertyBodyBlockPreservesArgumentBoundary()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Tail = { 2, 3 }
            Use(a, b, c) = a + b + c
            Use(1, Tail)
            """,
            expected: 3,
            actual: 2);
    }

    [Fact]
    public void Eval_BlockBoundary_NestedBlockPreservesMultiOutputBoundary()
    {
        var result = EvalFull(
            """
            A = 1, { 2, 3 }
            A
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Equal(2, outer.Items.Count);
        AssertAtomValue(outer.Items[0], 1);
        AssertSequenceValueAtoms(outer.Items[1], 2, 3);
    }

    [Fact]
    public void Eval_BlockBoundary_ExplicitOuterPropertyBlockIsTransparent()
    {
        var result = EvalFull(
            """
            A = { 1, { 2, 3 } }
            A
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Equal(2, outer.Items.Count);
        AssertAtomValue(outer.Items[0], 1);
        AssertSequenceValueAtoms(outer.Items[1], 2, 3);
    }

    [Fact]
    public void Eval_BlockBoundary_SequenceSpreadExplicitlyFlattensNestedBlockOutput()
    {
        AssertEval(
            """
            A = 1*, { 2, 3 }
            A
            """,
            1,
            2,
            3);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_SequenceValueResolvableAsAlgorithmPreservesBoundary()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Pair = (2, 3)
            Use(x, y) = x + y
            Use(Pair)
            """,
            expected: 2,
            actual: 1);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_AlgorithmOnlyFinalArgumentWithRemainingParamsKeepsArityPayload()
    {
        var result = EvalFull(
            """
            Inc(x) = x + 1
            Use(f, x) = f(x)
            Use(Inc)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(1, arity.Expected);
        Assert.Equal(0, arity.Actual);
        Assert.NotNull(arity.Signature);
        Assert.Equal("Use(f, x)", arity.Signature.DisplayText);

        Assert.Contains(
            "Callable `Use(f, x)` expects 2 arguments, but was called with 0 arguments.",
            KatLangError.FromEvalError(result.Error).Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_FlatFixedUserCallInsideCallback_ShadowsOuterCountedCallbackParameter()
    {
        AssertEval(
            """
            Use(n) = n + 1
            Callback(n) = Use(n + 10)
            map((1, 2, 3), Callback)
            """,
            12, 13, 14);
    }

    [Fact]
    public void Eval_Count_UserCallFlatFixedRouteCountsCurrentOutputShape()
    {
        AssertEval(
            """
            F(x, y) = x, y
            F(1, 2).count
            """,
            2);
    }

    [Fact]
    public void Eval_Count_UserCallPatternedRouteCountsCurrentOutputShape()
    {
        AssertEval(
            """
            F((x, y)) = x, y
            F((1, 2)).count
            """,
            2);
    }

    [Fact]
    public void Eval_Count_UserCallFlatVariadicRouteCountsCurrentOutputShape()
    {
        // The grouped call collects one item, so the returned list is [(1, 2, 3)].
        AssertEval(
            """
            F(*xs) = xs
            F((1, 2, 3)).count
            """,
            1);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_CapturesAllItems()
    {
        // The spread supplies three argument slots; the collecting parameter collects [1, 2, 3].
        AssertEval(
            """
            CountValues(*values) = values.count
            CountValues((1, 2, 3)*)
            """,
            3);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_WithSuffixBindsSuffixFromBack()
    {
        AssertEval(
            """
            Scale(*items, factor) = items.map{n * factor}
            Scale((1, 2, 3)*, 10)
            """,
            10, 20, 30);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_WithAlgorithmSuffixPreservesAlgorithmChannel()
    {
        AssertEval(
            """
            Apply(*values, f) = f(values:0)
            Inc = a + 1
            Apply((10, 20)*, Inc)
            """,
            11);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_WithPrefixAndSuffixCapturesMiddleItems()
    {
        AssertEval(
            """
            F(prefix, *values, suffix) = prefix, values.count, suffix
            F(1, (2, 3)*, 4)
            """,
            1, 2, 4);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_WithSuffixReportsSameMinimumArityFailure()
    {
        var result = EvalFull(
            """
            Scale(*items, factor) = items.map{n * factor}
            Scale()
            """);

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.VariadicArityMismatch>(Innermost(result.Error));
        Assert.Equal(1, arity.ExpectedMinimum);
        Assert.Equal(0, arity.Actual);

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains(
            "Callable `Scale(*items, factor)` expects at least 1 item, but received 0 items.",
            formatted,
            StringComparison.Ordinal);
        Assert.NotNull(arity.Signature);
        Assert.Equal("Scale(*items, factor)", arity.Signature.DisplayText);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_WithPrefixAndSuffixReportsSignatureInMinimumArityFailure()
    {
        var result = EvalFull(
            """
            F(prefix, *values, suffix) = prefix*, values*, suffix
            F()
            """);

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.VariadicArityMismatch>(Innermost(result.Error));
        Assert.Equal(2, arity.ExpectedMinimum);
        Assert.Equal(0, arity.Actual);

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("F(prefix, *values, suffix)", formatted, StringComparison.Ordinal);
        Assert.Contains("expects at least 2 items", formatted, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_Count_UserCallDeconstructionRouteReportsSignatureInMinimumArityFailure()
    {
        // F(*xs, last) is a comma deconstruction parameter list. F() supplies no
        // items, so the matcher cannot bind the single fixed parameter `last`: it
        // needs at least 1 item, reported against the callable signature.
        var result = EvalFull(
            """
            F(*xs, last) = xs*, last
            F().count
            """);

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.VariadicArityMismatch>(Innermost(result.Error));
        Assert.Equal(1, arity.ExpectedMinimum);
        Assert.Equal(0, arity.Actual);

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("F(*xs, last)", formatted, StringComparison.Ordinal);
        Assert.Contains(
            "Callable `F(*xs, last)` expects at least 1 item, but received 0 items.",
            formatted,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_Count_UserCallPatternedPlusTopLevelVariadicRoutesAsPatterned()
    {
        AssertEval(
            """
            F((*inner), *outer) = inner*, outer
            F((1, 2), ((3, 4))).count
            """,
            3);
    }

    [Fact]
    public void Eval_SequenceValueParameter_HeadTailPatternBindsWithinOneSlot()
    {
        AssertEval(
            """
            F((head, *tail)) = head, tail.count
            F((1, 2, 3, 4))
            """,
            1, 3);
    }

    [Fact]
    public void Eval_SequenceValueParameter_FirstMiddleLastPatternBindsWithinOneSlot()
    {
        AssertEval(
            """
            F((first, *middle, last)) = first, middle.count, last
            F((1, 2, 3, 4, 5))
            """,
            1, 3, 5);
    }

    [Fact]
    public void Eval_SequenceValueParameter_VariadicWithSuffixInsideSequenceValueBindsWithinOneSlot()
    {
        AssertEval(
            """
            F((*history, pre2), pre1) = history.count, pre2, pre1
            F((1, 2, 3), 4)
            """,
            2, 3, 4);
    }

    [Fact]
    public void Eval_SequenceValueParameter_WithSuffixInsideSequenceValueRequiresSuffixValue()
    {
        var result = EvalFull(
            """
            F((*history, pre2), pre1) = history.count, pre2, pre1
            F((), 4)
            """);

        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_TopLevelCollectingParameter_GroupedArgumentIsOneCollectedItem()
    {
        // Contrast with the sequence-value pattern below: the top-level collecting parameter
        // collects the grouped argument as one list element ([(1, 2)], count 1),
        // while F((*xs), y) opens the same argument to count 2.
        AssertEval(
            """
            F(*xs, y) = xs.count, y
            F((1, 2), 3)
            """,
            1, 3);
    }

    [Fact]
    public void Eval_SequenceValueCollectingParameter_IsNotTopLevelCollecting()
    {
        AssertEval(
            """
            F((*xs), y) = xs.count, y
            F((1, 2), 3)
            """,
            2, 3);

        var result = EvalFull(
            """
            F((*xs), y) = xs.count, y
            F(1, 2, 3)
            """);

        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_NonVariadicSequenceValuePattern_DoesNotSpreadArbitraryGroup()
    {
        var result = EvalFull(
            """
            F((x)) = x
            F((1, 2, 3))
            """);

        Assert.True(result.IsError);
    }

    [Fact]
    public void VariadicUserProperty_MatchesBuiltinSumAndCount()
    {
        // The item-supplying call forms (spread argument, spread receiver)
        // feed the collecting parameter the items the builtins see.
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3
            Mean(*values) = values.sum / values.count
            Mean(Arg*), (Arg*).Mean
            """,
            2, 2);
    }

    [Fact]
    public void VariadicUserProperty_MatchesDirectBuiltinExpression()
    {
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3
            Mean(*values) = values.sum / values.count
            Direct = Arg.sum / Arg.count
            Mean(Arg*), Direct
            """,
            2, 2);
    }

    [Fact]
    public void VariadicUserProperty_PreservesNestedSequenceValuesLikeSequenceBuiltins()
    {
        AssertEvalSequenceModes(
            """
            Arg = (1, 2), (3, 4)
            CountViaVariadic(*values) = values.count
            CountViaVariadic(Arg*), (Arg*).CountViaVariadic, Arg.count
            """,
            2, 2, 2);
    }

    [Fact]
    public void VariadicUserProperty_DistinguishesAtomsRecursiveFlattening()
    {
        AssertEvalSequenceModes(
            """
            Arg = (1, 2), (3, 4)
            CountViaVariadic(*values) = values.count
            CountAtoms(*values) = atoms(values).count
            CountViaVariadic(Arg*), CountAtoms(Arg*)
            """,
            2, 4);
    }

    [Fact]
    public void VariadicUserProperty_MapWrapperMatchesBuiltinMap()
    {
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3
            Scale(*values, factor) = values.map{n * factor}
            (Arg*).Scale(10), Arg.map{n * 10}
            """,
            10, 20, 30, 10, 20, 30);
    }

    [Fact]
    public void VariadicUserProperty_FilterWrapperMatchesBuiltinFilter()
    {
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3, 4, 5
            KeepBetween(*values, minValue, maxValue) = values.filter{n >= minValue and n <= maxValue}
            (Arg*).KeepBetween(2, 4), Arg.filter{n >= 2 and n <= 4}
            """,
            2, 3, 4, 2, 3, 4);
    }

    [Fact]
    public void VariadicUserProperty_TakeWrapperMatchesBuiltinTake()
    {
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3, 4
            TakeFirst(*values, itemCount) = values.take(itemCount)
            (Arg*).TakeFirst(2), Arg.take(2)
            """,
            1, 2, 1, 2);
    }

    [Fact]
    public void VariadicUserProperty_SkipWrapperMatchesBuiltinSkip()
    {
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3, 4
            SkipFirst(*values, itemCount) = values.skip(itemCount)
            (Arg*).SkipFirst(2), Arg.skip(2)
            """,
            3, 4, 3, 4);
    }

    [Fact]
    public void OrdinaryParameter_RemainsStructuralAfterVariadicSupport()
    {
        // The fixed parameter binds the receiver value untouched (count 3 via
        // the collection view), while the collecting parameter collects the receiver
        // as one list element (count 1).
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3
            Ordinary(list) = list.count
            Variadic(*list) = list.count
            Arg.Ordinary, Arg.Variadic
            """,
            3, 1);
    }

    [Fact]
    public void SequenceBuiltins_PreserveNestedSequenceValuesAndDoNotBehaveLikeAtoms()
    {
        AssertEvalSequenceModes(
            """
            Arg = (1, 2), (3, 4)
            Arg.count, atoms(Arg).count
            """,
            2, 4);
    }
}
