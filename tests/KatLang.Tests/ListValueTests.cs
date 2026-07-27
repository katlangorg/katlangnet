namespace KatLang.Tests;

/// <summary>
/// Exact immutable list values (<c>[]</c> syntax): construction, display,
/// equality, spread, calls, capture, deconstruction, collecting binding, and the
/// builtin collection view (lone lists open one boundary; collection-producing
/// builtins return exact lists). Lean parity: the list cases in CoreTests.lean
/// and the list bridge laws in KatLangArityLaws.lean.
/// </summary>
public class ListValueTests
{
    private static decimal[] Atoms(string source) => KatLangEngine.EvaluateToAtoms(source).ToArray();

    private static void AssertAtoms(string source, params decimal[] expected) => Assert.Equal(expected, Atoms(source));

    private static bool Fails(string source) => KatLangEngine.Run(source).IsFailure;

    private static void AssertArityFailure(string source, string signatureDisplay)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result.IsFailure, $"Expected arity failure but got: {result.ToDisplayString()}");
        Assert.Contains(
            $"Callable `{signatureDisplay}` expects",
            result.ToDisplayString(),
            StringComparison.Ordinal);
    }

    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString();
    }

    private static void AssertDisplay(string source, string expected) => Assert.Equal(expected, Display(source));

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result SequenceValue(params Result[] items) => new Result.SequenceValue(items);

    private static Result ListValue(params Result[] items) => new Result.ListValue(items);

    [Fact]
    public void TruthAndHostAtomViews_RemainDistinctForLists()
    {
        // Three atom views: ToAtoms (truth testing) keeps lists opaque, while
        // LanguageAtoms (the atoms builtin's collector) and ToHostAtoms (host
        // projection) both open them — separate contracts that agree on
        // numeric content (Lean: languageAtoms_eq_hostAtoms).
        var value = ListValue(Atom(1), SequenceValue(Atom(2), Atom(3)), ListValue(Atom(4)));

        Assert.Empty(value.ToAtoms());
        Assert.Equal([1m, 2m, 3m, 4m], value.LanguageAtoms());
        Assert.Equal([1m, 2m, 3m, 4m], value.ToHostAtoms());
        Assert.Equal([1m, 2m, 3m], KatLangEngine.EvaluateToAtoms("range(1, 3)"));
    }

    private static void AssertEvalCounted(string source, int expectedEmittedCount, Result expectedValue)
    {
        var parseResult = Parser.Parse(source);
        if (parseResult.HasErrors)
        {
            var message = string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message));
            Assert.Fail($"Expected parse success but got diagnostics:{Environment.NewLine}{message}");
        }

        var result = Evaluator.RunCounted(new Expr.Block(parseResult.Root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal(expectedEmittedCount, result.Value.EmittedCount);
        Assert.True(
            Result.ValueComparer.Equals(expectedValue, result.Value.Value),
            $"Expected {expectedValue} but got {result.Value.Value}");
    }

    // ── Construction and display ─────────────────────────────────────────────

    [Theory]
    [InlineData("[]", "[]")]
    [InlineData("[1]", "[1]")]
    [InlineData("[1, 2, 3]", "[1, 2, 3]")]
    [InlineData("[[1, 2], [3, 4]]", "[[1, 2], [3, 4]]")]
    [InlineData("[[]]", "[[]]")]
    [InlineData("[[[]]]", "[[[]]]")]
    [InlineData("[()]", "[()]")]
    [InlineData("[(1, 2)]", "[(1, 2)]")]
    [InlineData("[(), []]", "[(), []]")]
    [InlineData("[(())]", "[()]")]
    public void ListLiteral_Displays_WithBrackets(string source, string expected)
        => AssertDisplay(source, expected);

    [Fact]
    public void ListLiteral_EvaluatesToOneListValue()
        => AssertEvalCounted("[1, 2, 3]", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void EmptyList_IsOneVisibleValue()
        => AssertEvalCounted("[]", 1, ListValue());

    [Fact]
    public void SingletonList_IsNotNormalizedAway()
        => AssertEvalCounted("[7]", 1, ListValue(Atom(7)));

    [Fact]
    public void NestedSingletonLists_PreserveEveryBoundary()
        => AssertEvalCounted("[[7]]", 1, ListValue(ListValue(Atom(7))));

    [Fact]
    public void ListLiteral_KeepsVisibleEmptySequenceElements()
        => AssertEvalCounted("[1, (), 2]", 1, ListValue(Atom(1), SequenceValue(), Atom(2)));

    [Fact]
    public void ListLiteral_AdjacencyElementsSeparate()
        => AssertEvalCounted("[1 2 3]", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void ListLiteral_SpansPhysicalLinesInsideOpenBracket()
        => AssertEvalCounted("[1,\n2,\n3]", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void ListLiteral_MultilineAdjacencyElements()
        => AssertEvalCounted("[1\n2]", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void BracketAfterExpression_IsAdjacency_NeverIndexing()
        // `A[1]` is the two output rows `A, [1]`, exactly like `2 (3)` is `2, 3`.
        => AssertEvalCounted("A = 5\nA[1]", 2, SequenceValue(Atom(5), ListValue(Atom(1))));

    [Fact]
    public void ListDisplay_RoundTripsThroughParser()
    {
        var display = Display("[[1, 2], (), [()], 3]");
        AssertDisplay(display, display);
    }

    // ── Exactness and equality ───────────────────────────────────────────────

    [Theory]
    [InlineData("[7] == 7", 0)]
    [InlineData("[7] != 7", 1)]
    [InlineData("[[1, 2]] == [1, 2]", 0)]
    [InlineData("[[]] == []", 0)]
    [InlineData("[] == ()", 0)]
    [InlineData("[] != ()", 1)]
    [InlineData("[1, 2] == (1, 2)", 0)]
    [InlineData("[[1, 2]] == ((1, 2))", 0)]
    [InlineData("[1, 2] == [1, 2]", 1)]
    [InlineData("[[1], [2, 3]] == [[1], [2, 3]]", 1)]
    [InlineData("[1, [2]] == [1, 2]", 0)]
    [InlineData("[1, [2]] != [1, 2]", 1)]
    [InlineData("[] == []", 1)]
    [InlineData("['a', 'b'] == ['a', 'b']", 1)]
    [InlineData("['a'] == 'a'", 0)]
    public void ListEquality_IsStructuralAndKindExact(string source, decimal expected)
        => AssertAtoms(source, expected);

    [Fact]
    public void RedundantSequenceBoundary_AroundList_StillCanonicalizes()
        => AssertAtoms("([1, 2]) == [1, 2]", 1);

    [Fact]
    public void RedundantSequenceBoundary_AroundList_YieldsTheListValue()
        => AssertEvalCounted("([1, 2])", 1, ListValue(Atom(1), Atom(2)));

    // ── Lists are opaque to numeric contexts ─────────────────────────────────

    [Fact]
    public void List_DoesNotCoerceToNumber_EvenSingleton()
        => Assert.True(Fails("[5] + 1"));

    [Fact]
    public void EmptyList_IsNotTransparentInArithmetic()
    {
        // `() > 1` passes through, but `[]` is an exact value and type-errors.
        AssertAtoms("() > 1", 1);
        Assert.True(Fails("[] > 1"));
    }

    [Fact]
    public void List_InIfCondition_Fails()
        => Assert.True(Fails("if([1], 1, 2)"));

    // ── Spread ───────────────────────────────────────────────────────────────

    [Fact]
    public void Spread_OpensOneListBoundary()
        => AssertEvalCounted("A = [1, 2, 3]\nB = A...\nB", 1, SequenceValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void Spread_EmptyList_CapturesEmptySequence()
        // The capture is the empty sequence value; at root output the
        // non-spread row stays one VISIBLE `()` slot (visible-empty rule).
        => AssertEvalCounted("A = []\nB = A...\nB", 1, SequenceValue());

    [Fact]
    public void Spread_SingletonList_CapturesItem()
        => AssertEvalCounted("A = [7]\nB = A...\nB", 1, Atom(7));

    [Fact]
    public void Spread_NestedList_OpensExactlyOneBoundary()
        => AssertEvalCounted("A = [[7]]\nB = A...\nB", 1, ListValue(Atom(7)));

    [Fact]
    public void Spread_ListLiteral_Directly()
        => AssertEvalCounted("[1, 2, 3]...", 3, SequenceValue(Atom(1), Atom(2), Atom(3)))
        ;

    [Fact]
    public void Spread_Scalar_StillSuppliesItself()
        => AssertAtoms("7...", 7);

    [Fact]
    public void Spread_ListContainingSequence_KeepsSequenceItem()
        // Spread supplies the sequence item; the single-name CAPTURE boundary
        // then singleton-collapses, so B stores (1, 2).
        => AssertEvalCounted("A = [(1, 2)]\nB = A...\nB", 1, SequenceValue(Atom(1), Atom(2)));

    [Fact]
    public void StackedSpread_OpensOneListBoundaryPerLayer()
    {
        // Each written `...` opens exactly one boundary, so the stacked form
        // agrees with the value-boundary-separated form.
        AssertEvalCounted("A = [[7]]\nA......", 1, Atom(7));
        AssertEvalCounted("A = [[7]]\n(A...)...", 1, Atom(7));
        AssertEvalCounted("A = [[1, 2]]\nA......", 2, SequenceValue(Atom(1), Atom(2)));
        // Extra layers on a sequence value stay fixed points (unchanged
        // pre-list behavior).
        AssertEvalCounted("A = (1, 2)\nA......", 2, SequenceValue(Atom(1), Atom(2)));
    }

    // ── Spread inside list literals ──────────────────────────────────────────

    [Fact]
    public void ListLiteral_SpreadOfSequenceProperty()
        => AssertEvalCounted("A = 1, 2, 3\n[A...]", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void ListLiteral_SpreadBetweenFixedElements()
        => AssertEvalCounted("A = 1, 2, 3\n[0, A..., 4]", 1,
            ListValue(Atom(0), Atom(1), Atom(2), Atom(3), Atom(4)));

    [Fact]
    public void ListLiteral_NonSpreadListsStaySingleElements()
        => AssertEvalCounted("A = [1, 2]\nB = [3, 4]\n[A, B]", 1,
            ListValue(ListValue(Atom(1), Atom(2)), ListValue(Atom(3), Atom(4))));

    [Fact]
    public void ListLiteral_SpreadLists_ConcatenatesElements()
        => AssertEvalCounted("A = [1, 2]\nB = [3, 4]\n[A..., B...]", 1,
            ListValue(Atom(1), Atom(2), Atom(3), Atom(4)));

    [Fact]
    public void ListLiteral_MixedSpreadAndNonSpread()
        => AssertEvalCounted("A = [1, 2]\nB = [3, 4]\n[A, B...]", 1,
            ListValue(ListValue(Atom(1), Atom(2)), Atom(3), Atom(4)));

    [Fact]
    public void ListLiteral_EmptyListSpread_ContributesNoElements()
        => AssertEvalCounted("[1, []..., 2]", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void ListLiteral_EmptySequenceSpread_ContributesNoElements()
        => AssertEvalCounted("[1, ()..., 2]", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void ListLiteral_SequenceElementStaysOneElement()
        => AssertEvalCounted("[(1, 2)]", 1, ListValue(SequenceValue(Atom(1), Atom(2))));

    // ── Calls preserve list boundaries ───────────────────────────────────────

    [Fact]
    public void Call_ListWithoutSpread_IsOneArgument()
        => AssertAtoms("F(x) = 9\nF([1, 2, 3])", 9);

    [Fact]
    public void Call_ListWithSpread_SuppliesElements()
        => AssertAtoms("F(a, b, c) = a + b + c\nF([1, 2, 3]...)", 6);

    [Fact]
    public void Call_ListWithoutSpread_DoesNotSatisfyFixedArity()
        => Assert.True(Fails("F(a, b, c) = a + b + c\nF([1, 2, 3])"));

    [Fact]
    public void Call_ThroughVariable_PreservesBoundary()
    {
        AssertAtoms("F(x) = 9\nA = [1, 2, 3]\nF(A)", 9);
        AssertAtoms("F(a, b, c) = a + b + c\nA = [1, 2, 3]\nF(A...)", 6);
    }

    [Fact]
    public void Call_FixedParameter_ReceivesTheListValue()
        => AssertEvalCounted("F(x) = x\nF([1, 2])", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void Call_EmptyListSpread_SuppliesZeroArguments()
    {
        // Zero arguments reach the callee: a fixed one-parameter callee
        // rejects the call, and a single-variadic callee collects the empty list.
        Assert.True(Fails("F(a) = a\nF([]...)"));
        AssertEvalCounted("Inspect(...items) = items\nInspect([]...)", 1, ListValue());
    }

    [Fact]
    public void Call_EmptyList_IsOneArgument()
        => AssertEvalCounted("F(x) = x\nF([])", 1, ListValue());

    [Fact]
    public void Call_VariadicParameter_KeepsListAsOneSuppliedItem()
        // The unspread list is one supplied argument, so the variadic parameter collects the
        // nested one-element list [[1, 2]].
        => AssertEvalCounted("F(...items) = items\nA = [1, 2]\nF(A)", 1, ListValue(ListValue(Atom(1), Atom(2))));

    [Fact]
    public void Call_VariadicParameter_SpreadSuppliesElements()
        => AssertEvalCounted("F(...items) = items\nA = [1, 2]\nF(A...)", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void Call_MixedFixedVariadic_LoneListStaysWhole()
        => AssertEvalCounted(
            "F(first, ...rest) = (first, rest)\nA = [1, 2, 3]\nF(A)",
            1,
            SequenceValue(ListValue(Atom(1), Atom(2), Atom(3)), ListValue()));

    [Fact]
    public void DotCall_ListReceiver_IsOneLeadingArgument()
        => AssertAtoms("F(x, y) = y\nA = [1, 2]\nA.F(9)", 9);

    [Fact]
    public void DotCall_ListReceiver_IsNotImplicitlySpread()
        => Assert.True(Fails("F(a, b, c) = a + b + c\nA = [1, 2]\nA.F(3)"));

    // ── Capture ──────────────────────────────────────────────────────────────

    [Fact]
    public void SingleNameCapture_PreservesList()
        => AssertEvalCounted("A = [1, 2, 3]\nx = A\nx", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void SingleNameCapture_OfSpread_CapturesSequence()
        => AssertEvalCounted("A = [1, 2, 3]\ny = A...\ny", 1, SequenceValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void SingleNameCapture_EmptyList()
        => AssertEvalCounted("x = []\nx", 1, ListValue());

    [Fact]
    public void SingleNameCapture_EmptyListSpread_IsEmptySequence()
        // The capture is `()`; the root row keeps it one visible slot.
        => AssertEvalCounted("x = []...\nx", 1, SequenceValue());

    // ── Lone-list deconstruction ─────────────────────────────────────────────

    [Fact]
    public void Deconstruction_OpensLoneListLiteral()
        => AssertAtoms("x, y, z = [1, 2, 3]\nx\ny\nz", 1, 2, 3);

    [Fact]
    public void Deconstruction_ExplicitSpread_BindsIdentically()
        => AssertAtoms("x, y, z = [1, 2, 3]...\nx\ny\nz", 1, 2, 3);

    [Fact]
    public void Deconstruction_OpensLoneListThroughVariable()
        => AssertAtoms("A = [1, 2, 3]\nx, y, z = A\nx\ny\nz", 1, 2, 3);

    [Fact]
    public void Deconstruction_DoesNotOpenRecursively()
        => AssertEvalCounted(
            "x, y = [[1, 2], 3]\n(x, y)",
            1,
            SequenceValue(ListValue(Atom(1), Atom(2)), Atom(3)));

    [Fact]
    public void Deconstruction_ListInMultiItemSupply_StaysOneValue()
        => AssertEvalCounted(
            "x, y = [1, 2], 3\n(x, y)",
            1,
            SequenceValue(ListValue(Atom(1), Atom(2)), Atom(3)));

    [Fact]
    public void Deconstruction_WrongElementCount_Fails()
        => Assert.True(Fails("x, y = [1, 2, 3]\nx"));

    // ── Collecting binding collects an exact immutable list ────────────────────────

    [Fact]
    public void CollectingBinding_CollectsExactList()
        => AssertEvalCounted("x, ...rest = [1, 2, 3]\n(x, rest)", 1,
            SequenceValue(Atom(1), ListValue(Atom(2), Atom(3))));

    [Fact]
    public void CollectingBinding_EmptySegment_IsEmptyList()
        => AssertEvalCounted("x, ...rest = [1]\n(x, rest)", 1,
            SequenceValue(Atom(1), ListValue()));

    [Fact]
    public void CollectingBinding_SingletonSegment_StaysSingletonList()
        // `[2]` is never collapsed to `2` — list structure is exact.
        => AssertEvalCounted("x, ...rest = [1, 2]\n(x, rest)", 1,
            SequenceValue(Atom(1), ListValue(Atom(2))));

    [Fact]
    public void CollectingBinding_NestedLoneList_OpensOuterOnly()
        => AssertEvalCounted("x, ...rest = [[1, 2, 3]]\n(x, rest)", 1,
            SequenceValue(ListValue(Atom(1), Atom(2), Atom(3)), ListValue()));

    [Fact]
    public void CollectingBinding_SpreadProvenance_DoesNotAffectResultKind()
        => AssertEvalCounted("x, ...rest = [1, 2]..., [3, 4]...\n(x, rest)", 1,
            SequenceValue(Atom(1), ListValue(Atom(2), Atom(3), Atom(4))));

    [Fact]
    public void CollectingBinding_NonSpreadListItem_StaysOneListValue()
        => AssertEvalCounted("x, ...rest = 1, [2, 3], 4\n(x, rest)", 1,
            SequenceValue(Atom(1), ListValue(ListValue(Atom(2), Atom(3)), Atom(4))));

    // ── Canonical lone-collecting assignment ────────────────────────────────────────

    [Fact]
    public void LoneCollectingBinding_OfList_CollectsExactList()
        => AssertDisplay("...items = [1, 2, 3]\nitems", "[1, 2, 3]");

    [Fact]
    public void LoneCollectingBinding_EmptySupply_CollectsEmptyExactList()
        => AssertDisplay("...items = ()...\nitems", "[]");

    [Fact]
    public void SingleVariadicParameter_StillWorks()
        => AssertEvalCounted("Inspect(...items) = items\nInspect(1, 2)", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void ExplicitOpeningForm_IsProducerSideSpread()
        => AssertEvalCounted("value = [1, 2, 3]\nitems = value...\nitems", 1,
            SequenceValue(Atom(1), Atom(2), Atom(3)));

    // ── Builtins: lone-list collection view (one boundary opens) ─────────────

    [Fact]
    public void Builtin_LoneListCollection_OpensOneBoundary()
        => AssertAtoms("count([1, 2, 3])", 3);

    [Fact]
    public void Builtin_DotReceiverList_OpensOneBoundary()
        => AssertAtoms("A = [1, 2, 3]\nA.count", 3);

    [Fact]
    public void Builtin_ListItemInsideCollection_IsOneOpaqueItem()
        // The collection view opens only the outer lone boundary; a nested
        // list stays one opaque countable item.
        => AssertAtoms("count((1, [2], 3))", 3);

    [Fact]
    public void Builtin_NumericConstraint_ReportsPerItemListError()
    {
        // A list ITEM inside a numeric collection reports the ordinary
        // per-item numeric error (same wording family as sequence items) —
        // the old "does not support list values yet" guard is gone.
        var result = KatLangEngine.Run("sum((1, [2], 3))");
        Assert.True(result.IsFailure);
        Assert.Contains("item 1 was list value", result.ToDisplayString(), StringComparison.Ordinal);
        Assert.DoesNotContain("does not support list values yet", result.ToDisplayString(), StringComparison.Ordinal);
    }

    [Fact]
    public void Builtin_SpreadList_FollowsOrdinaryFixedArity()
    {
        // Spread supplies the list's items as ordinary argument slots, so a
        // multi-item spread overflows the one-collection signature. The
        // grouped (non-spread) list argument is the supported form.
        AssertArityFailure("count([1, 2, 3]...)", "count(collection)");
        AssertArityFailure("sum([1, 2, 3]...)", "sum(collection)");
        AssertArityFailure("A = [5, 1, 3]\norder(A...)", "order(collection)");
        AssertAtoms("count([1, 2, 3])", 3);
        AssertAtoms("sum([1, 2, 3])", 6);
        AssertAtoms("A = [5, 1, 3]\norder(A)", 1, 3, 5);
    }

    [Fact]
    public void Builtin_FilterCountPipeline_ListReceiverAgreesInBothOptimizerModes()
    {
        var source = "A = [1, 2, 3]\nA.filter({x > 1}).count";
        var parseResult = Parser.Parse(source);
        Assert.False(parseResult.HasErrors);

        var generic = RunWithSequenceOptimization(parseResult.Root, enabled: false);
        var optimized = RunWithSequenceOptimization(parseResult.Root, enabled: true);
        Assert.False(generic.IsError, $"generic path failed: {(generic.IsError ? generic.Error : null)}");
        Assert.False(optimized.IsError, $"optimized path failed: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal([2m], generic.Value.ToAtoms());
        Assert.Equal([2m], optimized.Value.ToAtoms());
    }

    [Fact]
    public void Builtin_FilterCountPipeline_NestedListInLoneKeptItem_AgreesInBothOptimizerModes()
    {
        // A list one level INSIDE the single kept sequence item stays one
        // opaque item on the fused path exactly like the split composition
        // (`K = Src.filter(p)` then `K.count`): filter keeps one item, so the
        // count is 1 in both optimizer modes.
        var source = "Src = (1, [2]), 3\nSrc.filter({a == (1, [2])}).count";
        var parseResult = Parser.Parse(source);
        Assert.False(parseResult.HasErrors);

        var generic = RunWithSequenceOptimization(parseResult.Root, enabled: false);
        var optimized = RunWithSequenceOptimization(parseResult.Root, enabled: true);
        Assert.False(generic.IsError, $"generic path failed: {(generic.IsError ? generic.Error : null)}");
        Assert.False(optimized.IsError, $"optimized path failed: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal([1m], generic.Value.ToAtoms());
        Assert.Equal([1m], optimized.Value.ToAtoms());
    }

    [Fact]
    public void Builtin_FilterCountPipeline_BarePlainFormWorksInBothOptimizerModes()
    {
        var source = "A = [1, 2, 3]\ncount(filter(A, {x > 1}))";
        var parseResult = Parser.Parse(source);
        Assert.False(parseResult.HasErrors);

        var generic = RunWithSequenceOptimization(parseResult.Root, enabled: false);
        var optimized = RunWithSequenceOptimization(parseResult.Root, enabled: true);
        Assert.False(generic.IsError, $"generic path failed: {(generic.IsError ? generic.Error : null)}");
        Assert.False(optimized.IsError, $"optimized path failed: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal([2m], generic.Value.ToAtoms());
        Assert.Equal([2m], optimized.Value.ToAtoms());
    }

    [Fact]
    public void Builtin_FilterCountPipeline_SpreadListSourceIsArityErrorInBothOptimizerModes()
    {
        // `filter(A..., predicate)` spreads three ordinary argument slots into
        // the two-argument signature, so the pipeline is an arity error on the
        // generic and the fused path alike.
        var source = "A = [1, 2, 3]\ncount(filter(A..., {x > 1})...)";
        var parseResult = Parser.Parse(source);
        Assert.False(parseResult.HasErrors);

        var generic = RunWithSequenceOptimization(parseResult.Root, enabled: false);
        var optimized = RunWithSequenceOptimization(parseResult.Root, enabled: true);
        Assert.True(generic.IsError, "generic path unexpectedly succeeded");
        Assert.True(optimized.IsError, "optimized path unexpectedly succeeded");
        Assert.Contains(
            "Callable `filter(collection, predicate)` expects",
            KatLangError.FromEvalError(generic.Error).Message,
            StringComparison.Ordinal);
        Assert.Contains(
            "Callable `filter(collection, predicate)` expects",
            KatLangError.FromEvalError(optimized.Error).Message,
            StringComparison.Ordinal);
    }

    private static EvalResult<Result> RunWithSequenceOptimization(Algorithm root, bool enabled)
        => Evaluator.Run(
            new Expr.Block(root),
            new Evaluation.Caching.RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: enabled,
            sequenceDiagnostics: null);

    // ── Arity model: variadic and collecting bindings collect exact lists ──────────

    [Theory]
    [InlineData("Inspect()", "[]")]
    [InlineData("Inspect(7)", "[7]")]
    [InlineData("Inspect(1, 2)", "[1, 2]")]
    [InlineData("Inspect([1, 2])", "[[1, 2]]")]
    [InlineData("Inspect([1, 2]...)", "[1, 2]")]
    public void VariadicCapture_CollectsExactListOfSuppliedArguments(string call, string expected)
        // Calls never open lists implicitly: a plain list is one supplied
        // argument (collected as one nested element), and only explicit `...`
        // opens it into the stream. The collecting binding always collects the
        // supplied slots as one exact list — zero slots form [], one slot
        // forms [item], never collapsed.
        => AssertDisplay($"Inspect(...items) = items\n{call}", expected);

    [Theory]
    [InlineData("head, ...rest = [1, 2, 3]\nrest", "[2, 3]")]
    [InlineData("head, ...rest = [1]\nrest", "[]")]
    [InlineData("head, ...rest = [1, 2]\nrest", "[2]")]
    [InlineData("first, ...rest = 1, [2, 3]..., (4, 5)...\nfirst", "1")]
    [InlineData("first, ...rest = 1, [2, 3]..., (4, 5)...\nrest", "[2, 3, 4, 5]")]
    public void CollectingBinding_CollectsExactList_AcrossListSources(string source, string expected)
        => AssertDisplay(source, expected);

    [Fact]
    public void CollectingBinding_And_SkipBuiltin_AgreeOnListResult()
    {
        // The collecting binding and the collection builtin now both produce an exact
        // list of the same items, so they compare equal.
        AssertDisplay("head, ...rest = [1, 2, 3]\nrest", "[2, 3]");
        AssertDisplay("skip([1, 2, 3], 1)", "[2, 3]");
        AssertAtoms("head, ...rest = [1, 2, 3]\nrest == skip([1, 2, 3], 1)", 1);
    }

    // ── Collection-producing builtins return one exact list value ────────────

    [Theory]
    [InlineData("take((1, 2, 3), 1)")]
    [InlineData("take([1, 2, 3], 1)")]
    public void BuiltinBindingForms_AgreeOnTheSameListResult(string source)
        => AssertDisplay(source, "[1]");

    [Theory]
    [InlineData("take(1, 2, 3, 1)")]
    [InlineData("take([1, 2, 3]..., 1)")]
    public void BuiltinBindingForms_InlineItemsAndSpreadAreArityErrors(string source)
        // Inline items and spread both supply ordinary argument slots, which
        // overflow the fixed `take(collection, count)` signature.
        => AssertArityFailure(source, "take(collection, count)");

    [Fact]
    public void BuiltinEmptyResult_IsTheEmptyList()
    {
        AssertDisplay("take((1, 2), 0)", "[]");
        AssertDisplay("skip([1, 2], 2)", "[]");
    }

    [Fact]
    public void BuiltinSingletonResult_IsASingletonList()
    {
        AssertDisplay("distinct((1, 1))", "[1]");
        // Two inline items are two arguments, not one collection.
        AssertArityFailure("distinct(1, 1)", "distinct(collection)");
    }

    [Fact]
    public void BuiltinResult_KeepsNestedElementsExact()
    {
        AssertDisplay("take(((1, 2), (3, 4)), 1)", "[(1, 2)]");
        AssertDisplay("take([[1, 2], [3, 4]], 1)", "[[1, 2]]");
    }

    [Fact]
    public void Count_ValueBoundaries_ScalarEmptyAndSiblingForms()
    {
        AssertAtoms("count(3)", 1);
        AssertAtoms("count(())", 0);
        AssertAtoms("count([])", 0);
        // Sibling arguments are extra argument slots, never extra collection
        // items — the fix is grouping them into one collection, where they
        // stay two visible items.
        AssertArityFailure("count(3, 3)", "count(collection)");
        AssertArityFailure("count((), ())", "count(collection)");
        AssertArityFailure("count([], [])", "count(collection)");
        AssertAtoms("count(((), ()))", 2);
        AssertAtoms("count(([], []))", 2);
    }

    [Fact]
    public void NumericBuiltin_LoneListOpens_SpreadFormMustBeRegrouped()
    {
        AssertAtoms("A = [1, 2, 3]\nsum(A)", 6);
        // Spread supplies three ordinary argument slots — an arity error;
        // regrouping the spread restores one collection argument.
        AssertArityFailure("A = [1, 2, 3]\nsum(A...)", "sum(collection)");
        AssertAtoms("A = [1, 2, 3]\nsum((A...))", 6);
    }

    [Fact]
    public void BuiltinListResult_ReEntersArityThroughOrdinaryRules()
    {
        // A stored builtin list result spreads like any other list value.
        AssertDisplay("A = take([1, 2, 3], 1)\nA...", "1");
        AssertDisplay("A = take([1, 2, 3], 2)\nB = A...\nB", "(1, 2)");
    }

    [Fact]
    public void Range_ReturnsExactList_AndKeepsArgumentValidation()
    {
        AssertDisplay("range(1, 3)", "[1, 2, 3]");
        AssertDisplay("range(3, 3)", "[3]");
        AssertDisplay("range(3, 1)", "[3, 2, 1]");
        AssertDisplay("A = range(1, 3)\nB = A...\nB", "(1, 2, 3)");
        Assert.True(Fails("range(1.5, 3)"));
    }

    [Fact]
    public void LoneCollection_DoesNotExposeControlSlots()
    {
        // `count` is an ordinary fixed control parameter of
        // take(collection, count): a lone collection argument never fills it
        // from its own items, so the one-argument call is an arity error for
        // list and sequence collections alike.
        AssertArityFailure("take([1, 2, 3])", "take(collection, count)");
        AssertArityFailure("take((1, 2, 3))", "take(collection, count)");
    }

    // ── Dotted and direct builtin forms agree on both collection kinds ───────

    public static TheoryData<string> DottedEquivalenceComparisons => new()
    {
        "S.take(1) == take(S, 1)",
        "S.skip(1) == skip(S, 1)",
        "S.order == order(S)",
        "S.orderDesc == orderDesc(S)",
        "S.distinct == distinct(S)",
        "S.filter(P) == filter(S, P)",
        "S.map(D) == map(S, D)",
        "S.count == count(S)",
        "S.sum == sum(S)",
        "S.min == min(S)",
        "S.max == max(S)",
        "S.avg == avg(S)",
        "S.first == first(S)",
        "S.last == last(S)",
        "S.contains(2) == contains(S, 2)",
        "S.reduce(Add, 0) == reduce(S, Add, 0)",
    };

    [Theory]
    [MemberData(nameof(DottedEquivalenceComparisons))]
    public void DottedBuiltin_SequenceReceiver_AgreesWithDirectForm(string comparison)
        => AssertAtoms($"P = x > 1\nD = x * 2\nAdd = x + total\nS = 3, 1, 2\n{comparison}", 1);

    [Theory]
    [MemberData(nameof(DottedEquivalenceComparisons))]
    public void DottedBuiltin_ListReceiver_AgreesWithDirectForm(string comparison)
        => AssertAtoms($"P = x > 1\nD = x * 2\nAdd = x + total\nS = [3, 1, 2]\n{comparison}", 1);

    // ── Indexing `:` selects one immediate list element ──────────────────────

    [Fact]
    public void Indexing_SelectsListItem_PreservingTheList()
        => AssertEvalCounted("A = (0, [1, 2])\nA:1", 1, ListValue(Atom(1), Atom(2)));

    [Theory]
    [InlineData("[1, 2, 3]:0", 1)]
    [InlineData("[1, 2, 3]:1", 2)]
    [InlineData("[1, 2, 3]:2", 3)]
    [InlineData("[7]:0", 7)]
    public void Indexing_ListTarget_SelectsElement(string source, decimal expected)
        => AssertEvalCounted(source, 1, Atom(expected));

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public void Indexing_ListTarget_AgreesWithSequenceTarget(int index)
        => AssertAtoms($"((1, 2, 3):{index}) == ([1, 2, 3]:{index})", 1);

    [Fact]
    public void Indexing_BoundListProperty_SelectsElement()
        => AssertEvalCounted("A = [1, 2, 3]\nA:1", 1, Atom(2));

    [Fact]
    public void Indexing_NestedListElement_StaysExactList()
        => AssertEvalCounted("[[1, 2], [3, 4]]:1", 1, ListValue(Atom(3), Atom(4)));

    [Fact]
    public void Indexing_ChainedListProjection_SelectsOneLevelAtATime()
        => AssertEvalCounted("[[1, 2], [3, 4]]:1:0", 1, Atom(3));

    [Fact]
    public void Indexing_DeepChainedListProjection_PeelsOneBoundaryPerColon()
    {
        AssertEvalCounted("A = [[[7]]]\nA:0", 1, ListValue(ListValue(Atom(7))));
        AssertEvalCounted("A = [[[7]]]\nA:0:0", 1, ListValue(Atom(7)));
        AssertEvalCounted("A = [[[7]]]\nA:0:0:0", 1, Atom(7));
    }

    [Fact]
    public void Indexing_SequenceElementInsideList_ProjectsLikeSequenceTarget()
    {
        // A selected sequence element projects one level, so the counted pair
        // matches the sequence-target twin exactly.
        AssertEvalCounted("((1, 2), (3, 4)):0", 2, SequenceValue(Atom(1), Atom(2)));
        AssertEvalCounted("[(1, 2), (3, 4)]:0", 2, SequenceValue(Atom(1), Atom(2)));
    }

    [Fact]
    public void Indexing_ListElementInsideSequence_StaysExactList()
        => AssertEvalCounted("([1, 2], [3, 4]):0", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void Indexing_EmptyNestedStructures_StayExact()
    {
        AssertEvalCounted("[[]]:0", 1, ListValue());
        AssertEvalCounted("[[(1, 2)]]:0", 1, ListValue(SequenceValue(Atom(1), Atom(2))));
    }

    [Fact]
    public void Indexing_SelectedEmptySequenceElement_ProjectsToEmpty()
    {
        // A selected `()` element projects one level to the empty result;
        // the root output row keeps it as one visible `()` row, matching the
        // sequence-target twin exactly.
        AssertEvalCounted("((), 1):0", 1, SequenceValue());
        AssertEvalCounted("[()]:0", 1, SequenceValue());
    }

    [Theory]
    [InlineData("[[1, 2]]:0 == [1, 2]", 1)]
    [InlineData("[(1, 2)]:0 == (1, 2)", 1)]
    [InlineData("[[1, 2]]:0 == (1, 2)", 0)]
    [InlineData("[(1, 2)]:0 == [1, 2]", 0)]
    [InlineData("[[]]:0 == []", 1)]
    [InlineData("[[]]:0 == ()", 0)]
    public void Indexing_SelectedElement_PreservesExactValueKind(string source, decimal expected)
        => AssertAtoms(source, expected);

    [Theory]
    [InlineData("take([1, 2, 3], 1):0", 1)]
    [InlineData("take([1, 2, 3], 2):1", 2)]
    [InlineData("skip([1, 2, 3], 1):0", 2)]
    [InlineData("range(1, 3):0", 1)]
    [InlineData("range(1, 3):2", 3)]
    [InlineData("distinct((3, 1, 3)):1", 1)]
    public void Indexing_CollectionBuiltinResult_IsDirectlyIndexable(string source, decimal expected)
        => AssertEvalCounted(source, 1, Atom(expected));

    [Fact]
    public void Indexing_DottedBuiltinResult_IsDirectlyIndexable()
    {
        AssertEvalCounted("[3, 1, 2].order:0", 1, Atom(1));
        AssertEvalCounted("[3, 1, 2].orderDesc:0", 1, Atom(3));
    }

    [Fact]
    public void Indexing_CallbackBuiltinResult_IsDirectlyIndexable()
    {
        AssertEvalCounted("IsOdd = x mod 2 == 1\nfilter([1, 2, 3], IsOdd):1", 1, Atom(3));
        AssertEvalCounted("Double = x * 2\nmap([1, 2, 3], Double):2", 1, Atom(6));
    }

    [Fact]
    public void Indexing_NestedBuiltinListResult_SelectsExactElement()
        => AssertEvalCounted("take([[1, 2], [3, 4]], 1):0", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void Indexing_BuiltinResult_AgreesWithAssignedProperty()
        => AssertAtoms("A = range(1, 3)\n(A:0) == (range(1, 3):0)", 1);

    [Fact]
    public void Indexing_SelectsOneElement_WhileSpreadOpensAll()
    {
        AssertEvalCounted("A = [1, 2]\nA:0", 1, Atom(1));
        AssertEvalCounted("A = [1, 2]\nA...", 2, SequenceValue(Atom(1), Atom(2)));
        AssertEvalCounted("A = [1, 2]\nB = A...\nB", 1, SequenceValue(Atom(1), Atom(2)));
        AssertEvalCounted("A = [7]\nA:0", 1, Atom(7));
        AssertEvalCounted("A = [7]\nB = A...\nB", 1, Atom(7));
        AssertEvalCounted("A = []\nB = A...\nB", 1, SequenceValue());
    }

    [Fact]
    public void Indexing_ProjectedValue_IsOrdinaryVariadicArgument()
    {
        // The projected element is one supplied argument, collected as the one
        // element of the collecting binding's exact list.
        AssertEvalCounted("Inspect(...items) = items\nA = [1, 2, 3]\nInspect(A:1)", 1, ListValue(Atom(2)));
        AssertEvalCounted(
            "Inspect(...items) = items\nA = [[1, 2]]\nInspect(A:0)",
            1,
            ListValue(ListValue(Atom(1), Atom(2))));
    }

    // ── Parser diagnostics ───────────────────────────────────────────────────

    [Fact]
    public void UnmatchedOpenBracket_ReportsExpectedRBracket()
    {
        var parseResult = Parser.Parse("[1, 2");
        Assert.True(parseResult.HasErrors);
        Assert.Contains(parseResult.Diagnostics, static d => d.Message.Contains("RBracket"));
    }

    [Fact]
    public void UnmatchedCloseBracket_ReportsDiagnostic()
    {
        var parseResult = Parser.Parse("1, 2]");
        Assert.True(parseResult.HasErrors);
    }

    [Fact]
    public void DefinitionInsideBrackets_IsRejected()
    {
        var parseResult = Parser.Parse("[x = 1]");
        Assert.True(parseResult.HasErrors);
    }

    [Fact]
    public void ListLiteral_ParsesToListLiteralNode()
    {
        var parseResult = Parser.ParseSyntax("[1, 2, 3]");
        Assert.False(parseResult.HasErrors);
        var literal = Assert.IsType<Expr.ListLiteral>(Assert.Single(parseResult.Root.Output));
        Assert.Equal(3, literal.Items.Count);
    }

    [Fact]
    public void EmptyListLiteral_ParsesToEmptyListLiteralNode()
    {
        var parseResult = Parser.ParseSyntax("[]");
        Assert.False(parseResult.HasErrors);
        var literal = Assert.IsType<Expr.ListLiteral>(Assert.Single(parseResult.Root.Output));
        Assert.Empty(literal.Items);
    }

    [Fact]
    public void ListLiteral_IsNotAnOpenTarget()
        => Assert.True(Fails("open [1]"));

    [Fact]
    public void ListLiteral_FollowedByParens_IsAdjacency_NotACall()
        // Like `2 (3)`, a '(' after a non-callable list literal separates:
        // two output slots, never a call.
        => AssertEvalCounted("[1, 2](3)", 2, SequenceValue(ListValue(Atom(1), Atom(2)), Atom(3)));

    // ── While/repeat state can hold lists (generic loop path) ────────────────

    [Fact]
    public void LoopState_CanCarryListValues()
        => AssertEvalCounted(
            "Step(state, i) = state, i + 1, i < 3\nStep.while([], 1)",
            2,
            SequenceValue(ListValue(), Atom(3)));
}
