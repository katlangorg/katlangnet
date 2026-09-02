using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorValueBoundaryTests
{
    // ── Property / call / builtin boundary arity = 1 ──────────────────────────
    // A property/call/builtin RESULT boundary always returns ONE value: a body or
    // collection that internally produces an item supply is observed by the caller
    // as one sequence value (emitted count 1). Only an explicit caller-site
    // `value*` slot contributes it back to the surrounding
    // item supply. This generalizes the
    // lexical property-access and `if`-branch behavior to every value boundary.
    // Lean: reCountValueBoundary.

    // User-defined variadic call: the collecting binding collects the supplied argument
    // slots as one exact immutable list value.
    [Fact]
    public void Eval_UserCall_VariadicReturn_IsOneListValue()
        => AssertEvalCounted("F(*a) = a\nF(5, 9)", 1, ListValue(Atom(5), Atom(9)));

    [Fact]
    public void Eval_UserCall_VariadicReturnWithBodySpread_IsOneSequenceValue()
        => AssertEvalCounted("F(*a) = a*\nF(5, 9)", 1, ResultFromAtoms(5, 9));

    // Body `a, 0`: the collecting capture stays grouped as a nested list value.
    [Fact]
    public void Eval_UserCall_VariadicCommaSlot_GroupsCaptureAsNestedValue()
        => AssertEvalCounted(
            "F(*a) = a, 0\nF(5, 9)",
            1,
            Result.FromItems([ListValue(Atom(5), Atom(9)), Atom(0)]));

    // Body `a*, 0`: the body spread flattens the capture into sibling slots, and
    // the boundary still returns the whole flat item supply as one value.
    [Fact]
    public void Eval_UserCall_VariadicBodySpreadThenSlot_IsOneFlatSequenceValue()
        => AssertEvalCounted("F(*a) = a*, 0\nF(5, 9)", 1, ResultFromAtoms(5, 9, 0));

    // Caller-site spread turns the returned value back into an item supply.
    [Fact]
    public void Eval_UserCall_CallerSpread_OpensReturnedValue()
        => AssertEvalCounted("F(*a) = a\nF(5, 9)*", 2, ResultFromAtoms(5, 9));

    // Explicit zero-arg call `X()` is a call boundary (unlike property access `X`)
    // and now also returns one value.
    [Fact]
    public void Eval_ExplicitZeroArgCall_IsOneSequenceValue()
        => AssertEvalCounted("X = 1, 2, 3\nX()", 1, ResultFromAtoms(1, 2, 3));

    // Regression: lexical zero-arg property access was already arity 1.
    [Fact]
    public void Eval_LexicalPropertyAccess_StaysOneSequenceValue()
        => AssertEvalCounted("X = 1, 2, 3\nX", 1, ResultFromAtoms(1, 2, 3));

    // Structural dot zero-arg access now matches lexical access (arity 1).
    [Fact]
    public void Eval_StructuralDotZeroArgAccess_IsOneSequenceValue()
        => AssertEvalCounted("M = {\n  Public P = 1, 2, 3\n  P\n}\nM.P", 1, ResultFromAtoms(1, 2, 3));

    // Internal variadic forwarding is unaffected: the body still sees the raw item
    // exact list, so collection builtins open it after binding and explicit
    // spread-forwarding re-spreads it at the caller-selected boundary.
    [Theory]
    [InlineData("F(*a) = sum(a)\nF(5, 9)", 14)]
    [InlineData("F(*a) = count(a)\nF(5, 9)", 2)]
    [InlineData("G(*a) = a*\nsum(G(5, 9))", 14)]
    [InlineData("F(*a) = a\nsum(F(5, 9))", 14)]
    public void Eval_VariadicForwarding_UsesCollectedListViews(string source, int expected)
        => AssertEval(source, expected);

    // Collection-producing builtins return one exact immutable list value;
    // spread opens it.
    [Theory]
    [InlineData("X = 3, 1, 2\nX.order", 1)]
    [InlineData("X = 1, 2, 3, 3\nX.distinct", 1)]
    public void Eval_CollectionBuiltin_IsOneExactListValue(string source, int expectedCount)
        => AssertEvalCounted(source, expectedCount, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void Eval_CollectionBuiltin_OrderSpread_OpensIntoItems()
        => AssertEvalCounted("X = 3, 1, 2\nX.order*", 3, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_CollectionBuiltin_Take_IsOneExactListValue()
        => AssertEvalCounted("X = 1, 2, 3\nX.take(2)", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void Eval_CollectionBuiltin_TakeSpread_OpensIntoItems()
        => AssertEvalCounted("X = 1, 2, 3\nX.take(2)*", 2, ResultFromAtoms(1, 2));

    [Fact]
    public void Eval_CollectionBuiltin_Skip_IsOneExactListValue()
        => AssertEvalCounted("X = 1, 2, 3\nX.skip(1)", 1, ListValue(Atom(2), Atom(3)));

    [Fact]
    public void Eval_CollectionBuiltin_Filter_IsOneExactListValue()
        => AssertEvalCounted("IsBig = x > 1\nX = 1, 2, 3\nX.filter(IsBig)", 1, ListValue(Atom(2), Atom(3)));

    [Fact]
    public void Eval_CollectionBuiltin_Map_IsOneExactListValue()
        => AssertEvalCounted("Double = x * 2\nX = 1, 2, 3\nX.map(Double)", 1, ListValue(Atom(2), Atom(4), Atom(6)));

    [Fact]
    public void Eval_CollectionBuiltin_Range_IsOneExactListValue()
        => AssertEvalCounted("range(1, 3)", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void Eval_CollectionBuiltin_RangeSpread_OpensIntoItems()
        => AssertEvalCounted("range(1, 3)*", 3, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_CollectionBuiltin_Atoms_IsOneExactListValue()
        => AssertEvalCounted("atoms((1, (2, 3)))", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void Eval_CollectionBuiltin_OrderDesc_IsOneExactListValue()
        => AssertEvalCounted("X = 3, 1, 2\nX.orderDesc", 1, ListValue(Atom(3), Atom(2), Atom(1)));

    [Fact]
    public void Eval_CollectionBuiltin_OrderDescSpread_OpensIntoItems()
        => AssertEvalCounted("X = 3, 1, 2\nX.orderDesc*", 3, ResultFromAtoms(3, 2, 1));

    [Fact]
    public void Eval_CollectionBuiltin_DistinctSpread_OpensIntoItems()
        => AssertEvalCounted("X = 1, 1, 2, 3\nX.distinct*", 3, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_CollectionBuiltin_SkipSpread_OpensIntoItems()
        => AssertEvalCounted("X = 1, 2, 3\nX.skip(1)*", 2, ResultFromAtoms(2, 3));

    [Fact]
    public void Eval_CollectionBuiltin_FilterSpread_OpensIntoItems()
        => AssertEvalCounted("IsBig = x > 1\nX = 1, 2, 3\nX.filter(IsBig)*", 2, ResultFromAtoms(2, 3));

    [Fact]
    public void Eval_CollectionBuiltin_MapSpread_OpensIntoItems()
        => AssertEvalCounted("Double = x * 2\nX = 1, 2, 3\nX.map(Double)*", 3, ResultFromAtoms(2, 4, 6));

    [Fact]
    public void Eval_CollectionBuiltin_AtomsSpread_OpensIntoItems()
        => AssertEvalCounted("atoms((1, (2, 3)))*", 3, ResultFromAtoms(1, 2, 3));

    // A collection-builtin result fed into another sequence builtin is still
    // opened by singleton-boundary normalization (value-based, not count-based).
    [Theory]
    [InlineData("sum(range(1, 4))", 10)]
    [InlineData("X = 3, 1, 2\nsum(X.order)", 6)]
    public void Eval_CollectionBuiltin_ResultStillConsumedByBuiltin(string source, int expected)
        => AssertEval(source, expected);

    // Chaining a collection builtin onto a collection builtin still works: the
    // lone list result is opened as the collection input of the next builtin.
    [Fact]
    public void Eval_CollectionBuiltin_ChainedOrder_IsOneExactListValue()
        => AssertEvalCounted("X = 3, 1, 2\nX.order.order", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    // Regression: scalar/reduction builtins were already arity 1 and are unchanged.
    [Fact]
    public void Eval_ScalarReduction_Sum_StaysOneValue()
        => AssertEvalCounted("X = 1, 2, 3\nX.sum", 1, Atom(6));

    [Fact]
    public void Eval_Reduce_StaysOneAccumulatorValue()
        => AssertEvalCounted("Add = x + total\nreduce((1, 2, 3, 4), Add, 0)", 1, Atom(10));

    // Regression: a map transform that emits more than one value is still rejected;
    // the boundary rule must NOT silently turn it into one sequence-valued element.
    [Fact]
    public void Eval_Map_MultiOutputCallback_StillRejected()
        => AssertEvalFails("Pair = x, x * 10\n(1, 2, 3).map(Pair)");

    // Regression: root output is NOT a call boundary and stays multi-output.
    [Fact]
    public void Eval_RootOutput_StaysMultiOutput()
        => AssertEvalCounted("1, 2, 3", 3, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_RootOutput_Spread_StaysMultiOutput()
        => AssertEvalCounted("X = 1, 2, 3\nX*", 3, ResultFromAtoms(1, 2, 3));

    // Regression: while/repeat intentionally preserve multi-slot loop state and are
    // NOT collapsed by the boundary rule.
    [Fact]
    public void Eval_Repeat_MultiSlotLoopState_StaysMultiSlot()
        => AssertEvalCounted("repeat({a + 1, b + a}, 3, 0, 0)", 2, ResultFromAtoms(3, 3));

    // Regression: redundant empty-sequence nesting is canonicalized before the
    // public boundary is observed.
    [Fact]
    public void Eval_Boundary_CanonicalizesNestedEmptySequence()
        => AssertEvalCounted("F = (())\nF", 1, SequenceValue());

    [Fact]
    public void Eval_Boundary_PreservesSingletonSequenceValue()
        => AssertEvalCounted("F = ((1, 2))\nF", 1, SequenceValue(Atom(1), Atom(2)));

    [Fact]
    public void Eval_ParenSubExpr_FirstArg_Works()
    {
        var source = """
            F = a + b
            F((1 + 2) mod 2, 10)
            """;
        AssertEval(source, 11);
    }

    [Fact]
    public void Eval_DoubleParens_IsOrdinaryGrouping()
    {
        var source = """
            X = ((1 + 2))
            X
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Atoms_FlattensGroups()
        => AssertEval("atoms(((1, 2), (3, 4)))", 1, 2, 3, 4);

    [Fact]
    public void Eval_Atoms_SingleValue()
        => AssertEval("atoms((5))", 5);

    [Fact]
    public void Eval_Content_NoLongerResolvesAsBuiltin()
    {
        // `content` was removed as a builtin; it now behaves like any other
        // unresolved callable/identifier unless the user defines it.
        AssertEvalFails("content(1)");
        AssertEvalFails("content((1, 2, 3))");
    }

    [Fact]
    public void Eval_Content_UserDefinedCallable_IsNotReserved()
        => AssertEval(
            """
            content(x) = x + 1
            content(1)
            """,
            2);

    [Fact]
    public void Eval_Spread_MultiOutputProperty_OpensIntoOutput()
        => AssertEval(
            """
            X = 1, 2, 3
            X*
            """,
            1, 2, 3);

    [Fact]
    public void Eval_Spread_SequenceValueProperty_OpensIntoOutput()
        => AssertEval(
            """
            X = (1, 2, 3)
            X*
            """,
            1, 2, 3);
}
