namespace KatLang.Tests;

/// <summary>
/// Exact immutable list values (<c>[]</c> syntax): construction, display,
/// equality, spread, calls, capture, deconstruction, rest binding, and the
/// deferred-builtin guard. Lean parity: the list cases in CoreTests.lean and
/// the list bridge laws in KatLangArityLaws.lean.
/// </summary>
public class ListValueTests
{
    private static decimal[] Atoms(string source) => KatLangEngine.EvaluateToAtoms(source).ToArray();

    private static void AssertAtoms(string source, params decimal[] expected) => Assert.Equal(expected, Atoms(source));

    private static bool Fails(string source) => KatLangEngine.Run(source).IsFailure;

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

    private static EvalError EvalError(string source)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(parseResult.HasErrors, "Expected parse success");
        var result = Evaluator.RunCounted(new Expr.Block(parseResult.Root));
        Assert.True(result.IsError, "Expected an evaluation error");
        return result.Error;
    }

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext(_, var inner) ? Innermost(inner) : error;

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
        // rejects the call, and a rest-only callee binds the empty stream.
        Assert.True(Fails("F(a) = a\nF([]...)"));
        AssertEvalCounted("Inspect(items...) = items\nInspect([]...)", 1, SequenceValue());
    }

    [Fact]
    public void Call_EmptyList_IsOneArgument()
        => AssertEvalCounted("F(x) = x\nF([])", 1, ListValue());

    [Fact]
    public void Call_RestParameter_KeepsListAsOneSuppliedItem()
        => AssertEvalCounted("F(items...) = items\nA = [1, 2]\nF(A)", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void Call_RestParameter_SpreadSuppliesElements()
        => AssertEvalCounted("F(items...) = items\nA = [1, 2]\nF(A...)", 1, SequenceValue(Atom(1), Atom(2)));

    [Fact]
    public void Call_MixedFixedRest_LoneListStaysWhole()
        => AssertEvalCounted(
            "F(first, rest...) = (first, rest)\nA = [1, 2, 3]\nF(A)",
            1,
            SequenceValue(ListValue(Atom(1), Atom(2), Atom(3)), SequenceValue()));

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

    // ── Rest binding always captures a canonical sequence ────────────────────

    [Fact]
    public void RestBinding_CapturesSequence_NeverList()
        => AssertEvalCounted("x, rest... = [1, 2, 3]\n(x, rest)", 1,
            SequenceValue(Atom(1), SequenceValue(Atom(2), Atom(3))));

    [Fact]
    public void RestBinding_EmptyRemainder_IsEmptySequence()
        => AssertEvalCounted("x, rest... = [1]\n(x, rest)", 1,
            SequenceValue(Atom(1), SequenceValue()));

    [Fact]
    public void RestBinding_SingletonRemainder_Normalizes()
        => AssertEvalCounted("x, rest... = [1, 2]\n(x, rest)", 1,
            SequenceValue(Atom(1), Atom(2)));

    [Fact]
    public void RestBinding_NestedLoneList_OpensOuterOnly()
        => AssertEvalCounted("x, rest... = [[1, 2, 3]]\n(x, rest)", 1,
            SequenceValue(ListValue(Atom(1), Atom(2), Atom(3)), SequenceValue()));

    [Fact]
    public void RestBinding_SpreadProvenance_DoesNotAffectResultKind()
        => AssertEvalCounted("x, rest... = [1, 2]..., [3, 4]...\n(x, rest)", 1,
            SequenceValue(Atom(1), SequenceValue(Atom(2), Atom(3), Atom(4))));

    [Fact]
    public void RestBinding_NonSpreadListItem_StaysOneListValue()
        => AssertEvalCounted("x, rest... = 1, [2, 3], 4\n(x, rest)", 1,
            SequenceValue(Atom(1), SequenceValue(ListValue(Atom(2), Atom(3)), Atom(4))));

    // ── Lone-rest assignment stays forbidden ─────────────────────────────────

    [Fact]
    public void LoneRestAssignment_OfList_IsRejected()
    {
        var result = KatLangEngine.Run("items... = [1, 2, 3]");
        Assert.True(result.IsFailure);
    }

    [Fact]
    public void RestOnlyFunctionParameters_StillWork()
        => AssertEvalCounted("Inspect(items...) = items\nInspect(1, 2)", 1, SequenceValue(Atom(1), Atom(2)));

    [Fact]
    public void ExplicitOpeningForm_IsProducerSideSpread()
        => AssertEvalCounted("value = [1, 2, 3]\nitems = value...\nitems", 1,
            SequenceValue(Atom(1), Atom(2), Atom(3)));

    // ── Builtins: deferred list support (targeted error, spread works) ───────

    [Fact]
    public void Builtin_LoneListCollection_ReportsTargetedTypeMismatch()
    {
        var error = Innermost(EvalError("count([1, 2, 3])"));
        var mismatch = Assert.IsType<EvalError.TypeMismatch>(error);
        Assert.Contains("does not support list values yet", mismatch.Message);
    }

    [Fact]
    public void Builtin_DotReceiverList_ReportsTargetedTypeMismatch()
    {
        var error = Innermost(EvalError("A = [1, 2, 3]\nA.count"));
        var mismatch = Assert.IsType<EvalError.TypeMismatch>(error);
        Assert.Contains("does not support list values yet", mismatch.Message);
    }

    [Fact]
    public void Builtin_ListItemInsideCollection_ReportsTargetedTypeMismatch()
    {
        var error = Innermost(EvalError("count((1, [2], 3))"));
        Assert.IsType<EvalError.TypeMismatch>(error);
    }

    [Fact]
    public void Builtin_SpreadListCollection_IsFullySupported()
    {
        AssertAtoms("count([1, 2, 3]...)", 3);
        AssertAtoms("sum([1, 2, 3]...)", 6);
        AssertAtoms("A = [5, 1, 3]\norder(A...)", 1, 3, 5);
    }

    [Fact]
    public void Builtin_FilterCountPipeline_ListReceiverFailsInBothOptimizerModes()
    {
        var source = "A = [1, 2, 3]\ncount(A.filter({x > 1})...)";
        var parseResult = Parser.Parse(source);
        Assert.False(parseResult.HasErrors);

        var generic = RunWithSequenceOptimization(parseResult.Root, enabled: false);
        var optimized = RunWithSequenceOptimization(parseResult.Root, enabled: true);
        Assert.True(generic.IsError, "generic path should reject a list receiver");
        Assert.True(optimized.IsError, "optimized path should reject a list receiver");
        Assert.IsType<EvalError.TypeMismatch>(Innermost(generic.Error));
        Assert.IsType<EvalError.TypeMismatch>(Innermost(optimized.Error));
    }

    [Fact]
    public void Builtin_FilterCountPipeline_NestedListInLoneKeptItem_FailsInBothOptimizerModes()
    {
        // A list one level INSIDE the single kept sequence item must hit the
        // deferred-list guard on the fused path exactly like the split
        // composition (`K = Src.filter(p)` then `K.count`) does.
        var source = "Src = (1, [2]), 3\nSrc.filter({a == (1, [2])}).count";
        var parseResult = Parser.Parse(source);
        Assert.False(parseResult.HasErrors);

        var generic = RunWithSequenceOptimization(parseResult.Root, enabled: false);
        var optimized = RunWithSequenceOptimization(parseResult.Root, enabled: true);
        Assert.True(generic.IsError, "generic path should reject the nested list");
        Assert.True(optimized.IsError, "fused path should reject the nested list");
        Assert.IsType<EvalError.TypeMismatch>(Innermost(generic.Error));
        Assert.IsType<EvalError.TypeMismatch>(Innermost(optimized.Error));
    }

    [Fact]
    public void Builtin_FilterCountPipeline_SpreadListSourceWorksInBothOptimizerModes()
    {
        var source = "A = [1, 2, 3]\ncount(filter(A..., {x > 1})...)";
        var parseResult = Parser.Parse(source);
        Assert.False(parseResult.HasErrors);

        var generic = RunWithSequenceOptimization(parseResult.Root, enabled: false);
        var optimized = RunWithSequenceOptimization(parseResult.Root, enabled: true);
        Assert.False(generic.IsError, $"generic path failed: {(generic.IsError ? generic.Error : null)}");
        Assert.False(optimized.IsError, $"optimized path failed: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal([2m], generic.Value.ToAtoms());
        Assert.Equal([2m], optimized.Value.ToAtoms());
    }

    private static EvalResult<Result> RunWithSequenceOptimization(Algorithm root, bool enabled)
        => Evaluator.Run(
            new Expr.Block(root),
            new Evaluation.Caching.RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: enabled,
            sequenceDiagnostics: null);

    // ── Indexing keeps lists opaque (list indexing is deferred) ──────────────

    [Fact]
    public void Indexing_SelectsListItem_PreservingTheList()
        => AssertEvalCounted("A = (0, [1, 2])\nA:1", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void Indexing_ListTarget_BehavesLikeScalarTarget()
        // `7:0` is `7`; a list is one opaque item, so `[1, 2]:0` is the list.
        => AssertEvalCounted("A = [1, 2]\nA:0", 1, ListValue(Atom(1), Atom(2)));

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
