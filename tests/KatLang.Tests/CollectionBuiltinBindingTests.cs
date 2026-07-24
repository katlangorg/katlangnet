namespace KatLang.Tests;

/// <summary>
/// Collection builtins are ordinary fixed-arity callables: exactly one
/// `collection` parameter plus fixed control parameters (`sum(collection)`,
/// `contains(collection, item)`, `reduce(collection, reducer, initial)`).
/// Argument boundaries are never altered before binding; only AFTER binding
/// does the bound collection value open one outer sequence or list boundary
/// (a scalar is a one-item collection). Inline multi-item calls such as
/// `sum(1, 2, 3)` are therefore ordinary arity errors, and the supported
/// rewrite is the grouped twin `sum((1, 2, 3))`.
/// </summary>
public class CollectionBuiltinBindingTests
{
    private static decimal[] Atoms(string source)
        => KatLangEngine.EvaluateToAtoms(source).ToArray();

    private static void AssertAtoms(string source, params decimal[] expected)
        => Assert.Equal(expected, Atoms(source));

    private static void AssertArityError(string source, string signatureDisplay)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result.IsFailure, $"Expected arity failure but got: {result.ToDisplayString()}");
        Assert.Contains(
            $"Callable `{signatureDisplay}` expects",
            result.ToDisplayString(),
            StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("count()", "count(collection)", 1, 0, 1)]
    [InlineData("count(1, 2, 3)", "count(collection)", 1, 3, 1)]
    [InlineData("count([1, 2, 3]...)", "count(collection)", 1, 3, 1)]
    [InlineData("take([1, 2, 3])", "take(collection, count)", 2, 1, 1)]
    [InlineData("take((1, 2, 3))", "take(collection, count)", 2, 1, 1)]
    [InlineData("take([1, 2, 3]..., 2)", "take(collection, count)", 2, 4, 1)]
    [InlineData("F(x) = x\nmap(1, 2, 3, F)", "map(collection, mapper)", 2, 4, 2)]
    [InlineData("P(x) = x\nfilter(1, 2, 3, P)", "filter(collection, predicate)", 2, 4, 2)]
    [InlineData("contains(1, 2, 3, 2)", "contains(collection, item)", 2, 4, 1)]
    [InlineData("F(x, acc) = x + acc\nreduce(2, 3, 4, F, 1)", "reduce(collection, reducer, initial)", 3, 5, 2)]
    public void InvalidDirectAndSpreadForms_ReportExactFixedArityAtCallSite(
        string source,
        string signatureDisplay,
        int expected,
        int actual,
        int expectedLine)
    {
        var eval = Evaluator.Run(new Expr.Block(Parser.Parse(source).Root));
        Assert.True(eval.IsError, "Expected an arity failure.");

        var error = eval.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var arity = Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.Equal(expected, arity.Expected);
        Assert.Equal(actual, arity.Actual);
        Assert.Equal(signatureDisplay, arity.Signature?.DisplayText);

        var run = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var diagnostic = Assert.Single(run.Errors);
        Assert.Equal(expectedLine, diagnostic.StartLine);
        Assert.Equal(1, diagnostic.StartColumn);
    }

    // ───────────────────────── Single-collection builtins ───────────────────────

    [Fact]
    public void Sum_TakesOneCollectionArgument()
    {
        // Absence of an argument is never an empty collection: `sum(())` is 0,
        // while `sum()` and inline multi-item calls are ordinary arity errors.
        AssertArityError("sum()", "sum(collection)");
        AssertAtoms("sum(())", 0);
        AssertArityError("sum(3, 4, 2, 1, 3, 3)", "sum(collection)");
        AssertAtoms("sum((3, 4, 2, 1, 3, 3))", 16);
        // Redundant sequence grouping canonicalizes, so extra parentheses
        // still supply the same one collection argument.
        AssertAtoms("sum(((3, 4, 2, 1, 3, 3)))", 16);
    }

    [Fact]
    public void SingleCollectionBuiltins_RejectInlineMultiItemCalls()
    {
        AssertArityError("count(3, 4, 2, 1, 3, 3)", "count(collection)");
        AssertArityError("min(3, 4, 2, 1, 3, 3)", "min(collection)");
        AssertArityError("max(3, 4, 2, 1, 3, 3)", "max(collection)");
        AssertArityError("avg(3, 4, 2, 1, 3, 3)", "avg(collection)");
        AssertArityError("order(3, 4, 2, 1, 3, 3)", "order(collection)");
        AssertArityError("distinct(3, 4, 2, 1, 3, 3)", "distinct(collection)");
        AssertArityError("first(1, 2, 3)", "first(collection)");
        AssertArityError("last(1, 2, 3)", "last(collection)");
    }

    [Fact]
    public void SingleCollectionBuiltins_AcceptTheGroupedTwin()
    {
        AssertAtoms("count((3, 4, 2, 1, 3, 3))", 6);
        AssertAtoms("min((3, 4, 2, 1, 3, 3))", 1);
        AssertAtoms("max((3, 4, 2, 1, 3, 3))", 4);
        AssertAtoms("avg((3, 4, 2, 1, 3, 3))", 16m / 6m);
        AssertAtoms("order((3, 4, 2, 1, 3, 3))", 1, 2, 3, 3, 3, 4);
        AssertAtoms("distinct((3, 4, 2, 1, 3, 3))", 3, 4, 2, 1);
        AssertAtoms("first((1, 2, 3))", 1);
        AssertAtoms("last((1, 2, 3))", 3);
    }

    [Fact]
    public void UserVariadic_ForwardsCapturedValueAsOneCollectionArgument()
    {
        // A user-defined variadic collects the argument stream as ONE exact
        // list value, so forwarding it (`values.sum`) binds the single
        // `collection` parameter. The builtin itself has no variadic shape:
        // the equivalent inline call is an arity error.
        AssertAtoms("G(...values) = values.sum\nG(3, 4, 2, 1, 3, 3)", 16);
        AssertArityError("sum(3, 4, 2, 1, 3, 3)", "sum(collection)");
    }

    // ───────────────────────── Sibling and spread arguments ─────────────────────

    [Fact]
    public void SiblingGroupedValues_AreTwoArguments_NotOneCollection()
        // sum(A, B) supplies two arguments to the one-collection signature.
        => AssertArityError("A = 1, 2\nB = 3, 4\nsum(A, B)", "sum(collection)");

    [Fact]
    public void SpreadArguments_CountAsOrdinarySlots_GroupedSpreadConcatenates()
    {
        // Spread has only its ordinary meaning: `sum(A..., B...)` supplies
        // four argument slots, an arity error.
        AssertArityError("A = 1, 2\nB = 3, 4\nsum(A..., B...)", "sum(collection)");
        // The concatenation rewrite groups the spreads into ONE
        // sequence-value collection argument.
        AssertAtoms("A = 1, 2\nB = 3, 4\nsum((A..., B...))", 10);
    }

    // ───────────────────────── Control-parameter builtins ───────────────────────

    [Fact]
    public void Contains_TakesCollectionAndItemPositionally()
    {
        AssertArityError("contains(1, 2, 3, 2)", "contains(collection, item)");
        AssertAtoms("contains((1, 2, 3), 2)", 1);
        AssertAtoms("Data = 1, 2, 3\ncontains(Data, 2)", 1);
        // Spreading the stored collection supplies its items as ordinary
        // argument slots, overflowing the two-argument signature.
        AssertArityError("Data = 1, 2, 3\ncontains(Data..., 2)", "contains(collection, item)");
        AssertAtoms("contains((1, 2, 3), 9)", 0);
    }

    [Fact]
    public void Take_TakesCollectionAndCount()
    {
        AssertArityError("take(1, 2, 3, 2)", "take(collection, count)");
        AssertAtoms("take((1, 2, 3), 2)", 1, 2);
    }

    [Fact]
    public void Map_TakesCollectionAndMapper()
    {
        AssertArityError("Double = n * 2\nmap(1, 2, 3, Double)", "map(collection, mapper)");
        AssertAtoms("Double = n * 2\nmap((1, 2, 3), Double)", 2, 4, 6);
    }

    [Fact]
    public void ControlAndCallbackBuiltins_RequireOneGroupedCollection()
    {
        // Callback execution stays a separate phase after the fixed top-level
        // arguments are bound.
        AssertArityError("skip(1, 2, 3, 1)", "skip(collection, count)");
        AssertAtoms("skip((1, 2, 3), 1)", 2, 3);

        AssertArityError("IsEven = x mod 2 == 0\nfilter(1, 2, 3, 4, IsEven)", "filter(collection, predicate)");
        AssertAtoms("IsEven = x mod 2 == 0\nfilter((1, 2, 3, 4), IsEven)", 2, 4);

        AssertArityError("Add = x + total\nreduce(1, 2, 3, Add, 0)", "reduce(collection, reducer, initial)");
        AssertAtoms("Add = x + total\nreduce((1, 2, 3), Add, 0)", 6);
    }

    // ───────────────────────── Grouped items stay whole ──────────────────────────

    [Fact]
    public void FirstLast_GroupedSiblings_StayWholeItemsInsideOneCollection()
    {
        // Two sibling arguments are an arity error; grouped into one
        // collection they stay two whole items, so first/last return a
        // group whole: first((A, B)) is (1, 2), not the flattened scalar 1.
        AssertArityError("A = 1, 2\nB = 3, 4\nfirst(A, B)", "first(collection)");
        AssertArityError("A = 1, 2\nB = 3, 4\nlast(A, B)", "last(collection)");
        AssertAtoms("A = 1, 2\nB = 3, 4\nfirst((A, B))", 1, 2);
        AssertAtoms("A = 1, 2\nB = 3, 4\nlast((A, B))", 3, 4);
    }

    [Fact]
    public void Reduce_DotReceiverFillsCollection_SpreadFormsNeedRegrouping()
    {
        // The dot receiver binds the `collection` parameter, so the dot form
        // passes exactly the remaining control arguments.
        AssertAtoms("Add = x + total\nValues = (1, 2, 3)\nValues.reduce(Add, 0)", 6);
        // Sibling or spread collection arguments overflow the fixed arity...
        AssertArityError(
            "Add = x + total\nA = 1, 2\nB = 3, 4\nreduce(A, B, Add, 0)",
            "reduce(collection, reducer, initial)");
        AssertArityError(
            "Add = x + total\nA = 1, 2\nB = 3, 4\nreduce(A..., B..., Add, 0)",
            "reduce(collection, reducer, initial)");
        // ...and the concatenation rewrite groups them into one collection.
        AssertAtoms("Add = x + total\nA = 1, 2\nB = 3, 4\nreduce((A..., B...), Add, 0)", 10);
    }
}
