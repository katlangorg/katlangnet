namespace KatLang.Tests;

/// <summary>
/// After Aspect 2, a builtin whose public signature is rest-shaped (`sum(values...)`,
/// `contains(values..., item)`) consumes an item supply exactly like a user-defined
/// variadic: item-supply binding opens a single grouped sequence boundary where required
/// (it does not repeatedly normalize nested sequence structure), the rest captures the
/// collection, suffix parameters bind from the back, and multiple sibling grouped values
/// are preserved rather than flattened. These tests pin that symmetry through the same
/// shared item-supply binding the user-call path uses.
/// </summary>
public class BuiltinItemSupplyBindingTests
{
    private static decimal[] Atoms(string source)
        => KatLangEngine.EvaluateToAtoms(source).ToArray();

    private static void AssertAtoms(string source, params decimal[] expected)
        => Assert.Equal(expected, Atoms(source));

    private static bool Fails(string source)
        => KatLangEngine.Run(source).IsFailure;

    // ───────────────────────── Rest-only collection builtins ─────────────────────

    [Fact]
    public void Sum_ConsumesItemSupply_InlineGroupedAndNestedAllAgree()
    {
        AssertAtoms("sum()", 0);
        AssertAtoms("sum(3, 4, 2, 1, 3, 3)", 16);
        AssertAtoms("sum((3, 4, 2, 1, 3, 3))", 16);
        AssertAtoms("sum(((3, 4, 2, 1, 3, 3)))", 16);
    }

    [Fact]
    public void RestOnlyBuiltins_AcceptInlineItemSupply()
    {
        AssertAtoms("count(3, 4, 2, 1, 3, 3)", 6);
        AssertAtoms("min(3, 4, 2, 1, 3, 3)", 1);
        AssertAtoms("max(3, 4, 2, 1, 3, 3)", 4);
        AssertAtoms("avg(3, 4, 2, 1, 3, 3)", 16m / 6m);
        AssertAtoms("order(3, 4, 2, 1, 3, 3)", 1, 2, 3, 3, 3, 4);
        AssertAtoms("distinct(3, 4, 2, 1, 3, 3)", 3, 4, 2, 1);
        AssertAtoms("first(1, 2, 3)", 1);
        AssertAtoms("last(1, 2, 3)", 3);
    }

    [Fact]
    public void Builtin_MatchesUserVariadicWithSameParameterShape()
    {
        // The shared item-supply binder makes the builtin and an equivalent user variadic agree.
        AssertAtoms("G(values...) = values.sum\nG(3, 4, 2, 1, 3, 3)", 16);
        AssertAtoms("sum(3, 4, 2, 1, 3, 3)", 16);
    }

    // ───────────────────────── Sibling preservation ─────────────────────────────

    [Fact]
    public void SiblingGroupedValues_AreNotFlattened()
    {
        // sum(A, B) keeps two grouped values, so the SingleNumeric constraint rejects them
        // rather than silently flattening to sum(1, 2, 3, 4) = 10.
        Assert.True(Fails("A = 1, 2\nB = 3, 4\nsum(A, B)"));
    }

    [Fact]
    public void ExplicitSpread_OpensSiblingsIntoOneItemSupply()
        => AssertAtoms("A = 1, 2\nB = 3, 4\nsum(A..., B...)", 10);

    // ───────────────────────── Suffix builtins ──────────────────────────────────

    [Fact]
    public void Contains_BindsCollectionAsRestAndItemAsSuffix()
    {
        AssertAtoms("contains(1, 2, 3, 2)", 1);
        // A grouped collection is opened by singleton-boundary normalization, so the
        // explicit-group form agrees with the inline form above.
        AssertAtoms("contains((1, 2, 3), 2)", 1);
        AssertAtoms("Data = 1, 2, 3\ncontains(Data, 2)", 1);
        AssertAtoms("Data = 1, 2, 3\ncontains(Data..., 2)", 1);
        AssertAtoms("contains(1, 2, 3, 9)", 0);
    }

    [Fact]
    public void Take_BindsCollectionAsRestAndCountAsSuffix()
    {
        AssertAtoms("take(1, 2, 3, 2)", 1, 2);
        AssertAtoms("take((1, 2, 3), 2)", 1, 2);
    }

    [Fact]
    public void Map_InlineAndGroupedCollectionsAgree()
    {
        AssertAtoms("Double = n * 2\nmap(1, 2, 3, Double)", 2, 4, 6);
        AssertAtoms("Double = n * 2\nmap((1, 2, 3), Double)", 2, 4, 6);
    }

    [Fact]
    public void SuffixAndCallbackBuiltins_InlineAndGroupedCollectionsAgree()
    {
        // The rest captures the collection and the suffix(es) (count / predicate / reducer +
        // initial) bind from the back, so inline and grouped collection forms agree. Callback
        // execution stays a separate phase after the top-level arguments are bound.
        AssertAtoms("skip(1, 2, 3, 1)", 2, 3);
        AssertAtoms("skip((1, 2, 3), 1)", 2, 3);

        AssertAtoms("IsEven = x mod 2 == 0\nfilter(1, 2, 3, 4, IsEven)", 2, 4);
        AssertAtoms("IsEven = x mod 2 == 0\nfilter((1, 2, 3, 4), IsEven)", 2, 4);

        AssertAtoms("Add = x + total\nreduce(1, 2, 3, Add, 0)", 6);
        AssertAtoms("Add = x + total\nreduce((1, 2, 3), Add, 0)", 6);
    }

    [Fact]
    public void FirstLast_SiblingGroupedValues_AreReturnedWhole()
    {
        // Two grouped siblings are preserved, so first/last return the first/last group whole:
        // first(A, B) is (1, 2) (atoms 1, 2), not the flattened scalar 1.
        AssertAtoms("A = 1, 2\nB = 3, 4\nfirst(A, B)", 1, 2);
        AssertAtoms("A = 1, 2\nB = 3, 4\nlast(A, B)", 3, 4);
    }

    [Fact]
    public void Reduce_SiblingsPreserved_OpenedConcatenates()
    {
        // reduce(values..., reducer, initial): a grouped collection is opened, so Values.reduce
        // over (1, 2, 3) folds three items.
        AssertAtoms("Add = x + total\nValues = (1, 2, 3)\nValues.reduce(Add, 0)", 6);
        // Multiple sibling grouped values are preserved (not flattened to four numbers), so a
        // numeric reducer rejects them; opening them with `...` folds all four.
        Assert.True(Fails("Add = x + total\nA = 1, 2\nB = 3, 4\nreduce(A, B, Add, 0)"));
        AssertAtoms("Add = x + total\nA = 1, 2\nB = 3, 4\nreduce(A..., B..., Add, 0)", 10);
    }
}
