namespace KatLang.Tests;

/// <summary>
/// The `atoms` builtin (issue #136): recursively collects numeric atoms
/// depth-first, left-to-right, through BOTH sequence and exact list
/// boundaries, and always materializes them as ONE exact immutable list.
/// Strings and other non-numeric leaves contribute no atoms. The result kind
/// never depends on the input kind or the number of atoms found, and `atoms`
/// does not define truthiness (lists still have no truth value).
/// Lean parity: `Result.languageAtoms`, the `atoms` laws in
/// KatLangArityLaws.lean, and the atoms guards in CoreTests.lean.
/// </summary>
public class AtomsBuiltinTests
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

    private static void AssertArityFailure(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result.IsFailure, $"Expected arity failure but got: {result.ToDisplayString()}");
        Assert.Contains("Callable `atoms(value)` expects", result.ToDisplayString(), StringComparison.Ordinal);
    }

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result SequenceValue(params Result[] items) => new Result.SequenceValue(items);

    private static Result ListValue(params Result[] items) => new Result.ListValue(items);

    private static (Result Value, int EmittedCount) EvalCounted(string source)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));
        var result = Evaluator.RunCounted(new Expr.Block(parseResult.Root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        return (result.Value.Value, result.Value.EmittedCount);
    }

    private static void AssertEvalCounted(string source, int expectedEmittedCount, Result expectedValue)
    {
        var (value, emittedCount) = EvalCounted(source);

        Assert.Equal(expectedEmittedCount, emittedCount);
        Assert.True(
            Result.ValueComparer.Equals(expectedValue, value),
            $"Expected {expectedValue} but got {value}");
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    // ── Stable exact-list result (kind never depends on atom count) ──────────

    [Fact]
    public void Atoms_String_IsEmptyList()
        => AssertEvalCounted("atoms('text')", 1, ListValue());

    [Fact]
    public void Atoms_Number_IsSingletonList()
        => AssertEvalCounted("atoms(7)", 1, ListValue(Atom(7)));

    [Fact]
    public void Atoms_Sequence_IsExactList()
        => AssertEvalCounted("atoms((1, 2))", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void Atoms_List_IsExactList()
        => AssertEvalCounted("atoms([1, 2])", 1, ListValue(Atom(1), Atom(2)));

    [Theory]
    [InlineData("atoms('text')", "[]")]
    [InlineData("atoms(7)", "[7]")]
    [InlineData("atoms((1, 2))", "[1, 2]")]
    [InlineData("atoms([1, 2])", "[1, 2]")]
    public void Atoms_Displays_AsExactList(string source, string expected)
        => AssertDisplay(source, expected);

    // ── Empty structures ─────────────────────────────────────────────────────

    [Theory]
    [InlineData("atoms(())")]
    [InlineData("atoms([])")]
    [InlineData("atoms([[], (), ['text']])")]
    [InlineData("atoms(((), ((), ())))")]
    public void Atoms_AtomFreeStructures_AreEmptyList(string source)
        => AssertEvalCounted(source, 1, ListValue());

    // ── Recursive traversal ──────────────────────────────────────────────────

    [Fact]
    public void Atoms_NestedSequences_FlattenRecursively()
        => AssertEvalCounted("atoms(((1, 2), (3, 4)))", 1, ListValue(Atom(1), Atom(2), Atom(3), Atom(4)));

    [Fact]
    public void Atoms_NestedLists_FlattenRecursively()
        => AssertEvalCounted("atoms([[1, 2], [3, 4]])", 1, ListValue(Atom(1), Atom(2), Atom(3), Atom(4)));

    [Theory]
    [InlineData("atoms([(1, 2), [3, [4]], 5])", new[] { 1.0, 2.0, 3.0, 4.0, 5.0 })]
    [InlineData("atoms((1, [2, (3, [4])]))", new[] { 1.0, 2.0, 3.0, 4.0 })]
    [InlineData("atoms([[], (), [1]])", new[] { 1.0 })]
    [InlineData("atoms([[(1, [2])], ((3, [4]), 5)])", new[] { 1.0, 2.0, 3.0, 4.0, 5.0 })]
    public void Atoms_MixedStructures_FlattenRecursively(string source, double[] expected)
        => AssertEvalCounted(source, 1, new Result.ListValue(expected.Select(static n => (Result)new Result.Atom((decimal)n))));

    [Fact]
    public void Atoms_StringsInsideStructures_ContributeNoAtoms()
        => AssertEvalCounted("atoms((1, ['a', 2], 'b'))", 1, ListValue(Atom(1), Atom(2)));

    // ── Traversal order is structural left-to-right ──────────────────────────

    [Fact]
    public void Atoms_PreservesLeftToRightOrder()
        => AssertEvalCounted("atoms([3, (1, [4, 2])])", 1, ListValue(Atom(3), Atom(1), Atom(4), Atom(2)));

    [Fact]
    public void Atoms_DeepMixedNesting_Flattens()
        => AssertEvalCounted("atoms([([([1])])])", 1, ListValue(Atom(1)));

    [Fact]
    public void Atoms_GeneratedDeepNesting_Flattens()
    {
        // Alternate sequence/list wrapper pairs; the collector must stay within
        // ordinary stack limits. 45 pairs (90 container boundaries) is the deepest
        // alternation the parser's cumulative recursion budget admits with slack
        // (each `([` pair charges 7 weighted units of the 384-unit budget);
        // deeper VALUES than source can express are covered by the iterative
        // whole-value walks and the host-AST structural gates.
        const int depth = 45;
        var source = "atoms(" + string.Concat(Enumerable.Repeat("([", depth)) + "7"
            + string.Concat(Enumerable.Repeat("])", depth)) + ")";
        AssertEvalCounted(source, 1, ListValue(Atom(7)));
    }

    // ── Exact result kind (equality probes) ──────────────────────────────────

    [Theory]
    [InlineData("atoms(7) == [7]", 1)]
    [InlineData("atoms(7) == 7", 0)]
    [InlineData("atoms((1, 2)) == [1, 2]", 1)]
    [InlineData("atoms((1, 2)) == (1, 2)", 0)]
    [InlineData("atoms(()) == []", 1)]
    [InlineData("atoms(()) == ()", 0)]
    [InlineData("atoms('text') == []", 1)]
    [InlineData("atoms([1, 2]) == [1, 2]", 1)]
    public void Atoms_ResultKind_IsExactList(string source, decimal expected)
        => AssertAtoms(source, expected);

    // ── Dotted and ordinary calls agree ──────────────────────────────────────

    [Theory]
    [InlineData("[1, [2, 3]].atoms == atoms([1, [2, 3]])", 1)]
    [InlineData("(1, [2, 3]).atoms == atoms((1, [2, 3]))", 1)]
    [InlineData("7 .atoms == atoms(7)", 1)]
    public void Atoms_DottedAndOrdinaryCallsAgree(string source, decimal expected)
        => AssertAtoms(source, expected);

    [Fact]
    public void Atoms_DottedListReceiver_Flattens()
        => AssertEvalCounted("[1, [2, 3]].atoms", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void Atoms_DottedSequenceReceiver_Flattens()
        => AssertEvalCounted("A = 1, [2, 3]\nA.atoms", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    // ── Fixed arity (call boundary unchanged) ────────────────────────────────

    [Fact]
    public void Atoms_TwoArguments_IsArityError()
        => AssertArityFailure("atoms(1, 2)");

    [Fact]
    public void Atoms_SpreadMultiElementList_IsArityError()
        => AssertArityFailure("atoms([1, 2]*)");

    [Fact]
    public void Atoms_SpreadRegrouped_IsOneArgument()
        => AssertEvalCounted("atoms(([1, 2]*))", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void Atoms_UnspreadList_IsOneArgument()
        => AssertEvalCounted("A = [1, 2]\natoms(A)", 1, ListValue(Atom(1), Atom(2)));

    // ── Composition with collection builtins ─────────────────────────────────

    [Theory]
    [InlineData("atoms((3, 1, 2)).order", "[1, 2, 3]")]
    [InlineData("atoms((1, 2, 3)).take(2)", "[1, 2]")]
    [InlineData("atoms((1, 2, 3)).skip(1)", "[2, 3]")]
    [InlineData("[1, 2, 3].skip(1).atoms", "[2, 3]")]
    [InlineData("[[1, 2], [3, 4]].take(1).atoms", "[1, 2]")]
    [InlineData("range(1, 3).atoms", "[1, 2, 3]")]
    [InlineData("[[1, 2], [3, 4]].map({a.sum}).atoms", "[3, 7]")]
    public void Atoms_ComposesWithCollectionBuiltins(string source, string expectedDisplay)
        => AssertDisplay(source, expectedDisplay);

    [Theory]
    [InlineData("atoms((1, 2, 3)).count", 3)]
    [InlineData("atoms((1, 2, 3)).sum", 6)]
    [InlineData("atoms([[1, 2], 3]).count", 3)]
    [InlineData("atoms('text').count", 0)]
    public void Atoms_ResultOpensLikeAnyBoundCollection(string source, decimal expected)
        => AssertAtoms(source, expected);

    [Theory]
    [InlineData("contains((1, [2]), atoms(2))", 1)]
    [InlineData("contains((1, 2), atoms(2))", 0)]
    [InlineData("contains(([1], [2]), atoms(1))", 1)]
    public void Atoms_ResultIsAListInValueEqualityConsumers(string source, decimal expected)
        // The singleton result stays a list, so membership compares it as a
        // list value: atoms(2) equals the element [2], never the atom 2.
        // (Under the old canonical-sequence result atoms(2) collapsed to the
        // bare atom 2 — an intended result-kind-driven flip.)
        => AssertAtoms(source, expected);

    // ── Composition with list indexing ───────────────────────────────────────

    [Theory]
    [InlineData("atoms((10, 20)):0", 10)]
    [InlineData("atoms([10, [20, 30]]):2", 30)]
    public void Atoms_ResultSupportsListIndexing(string source, decimal expected)
        => AssertAtoms(source, expected);

    [Fact]
    public void Atoms_EmptyResultIndexing_IsBadIndex()
    {
        var parseResult = Parser.Parse("atoms('text'):0");
        Assert.False(parseResult.HasErrors);
        var result = Evaluator.Run(new Expr.Block(parseResult.Root));
        Assert.True(result.IsError, "Expected BadIndex but evaluation succeeded.");
        Assert.IsType<EvalError.BadIndex>(Innermost(result.Error));
    }

    // ── Composition with explicit spread ─────────────────────────────────────

    [Fact]
    public void Atoms_Spread_OpensOneListBoundary()
        => AssertEvalCounted("A = atoms((10, 20))\nB = A*\nB", 1, SequenceValue(Atom(10), Atom(20)));

    [Fact]
    public void Atoms_SingletonSpread_CapturesItem()
        => AssertEvalCounted("A = atoms(7)\nB = A*\nB", 1, Atom(7));

    [Fact]
    public void Atoms_EmptySpread_ContributesNoItems()
        => AssertEvalCounted("A = atoms('text')\nB = A*\nB", 1, SequenceValue());

    [Fact]
    public void Atoms_DirectSpread_OpensIntoItems()
        => AssertEvalCounted("atoms([1, [2, 3]])*", 3, SequenceValue(Atom(1), Atom(2), Atom(3)));

    // ── Output count: one persistent collection value ────────────────────────

    [Theory]
    [InlineData("atoms((1, 2, 3))")]
    [InlineData("atoms(7)")]
    [InlineData("atoms(())")]
    [InlineData("atoms('text')")]
    [InlineData("atoms([1, [2], 3])")]
    public void Atoms_EmitsExactlyOneValue(string source)
    {
        var (value, emittedCount) = EvalCounted(source);
        Assert.Equal(1, emittedCount);
        Assert.IsType<Result.ListValue>(value);
    }

    // ── Plain and counted evaluation agree ───────────────────────────────────

    [Theory]
    [InlineData("atoms([1, 2])")]
    [InlineData("atoms([[1, 2], [3, 4]])")]
    [InlineData("atoms((1, [2, (3, [4])]))")]
    [InlineData("atoms('text')")]
    [InlineData("[1, 2, 3].skip(1).atoms")]
    public void Atoms_PlainAndCountedEvaluationAgree(string source)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(parseResult.HasErrors);

        var plain = Evaluator.Run(new Expr.Block(parseResult.Root));
        var counted = Evaluator.RunCounted(new Expr.Block(parseResult.Root));
        Assert.False(plain.IsError, $"plain path failed: {(plain.IsError ? plain.Error : null)}");
        Assert.False(counted.IsError, $"counted path failed: {(counted.IsError ? counted.Error : null)}");

        Assert.True(
            Result.ValueComparer.Equals(plain.Value, counted.Value.Value),
            $"plain {plain.Value} != counted {counted.Value.Value}");
    }

    // ── `atoms` does not define truthiness ───────────────────────────────────

    [Fact]
    public void AtomsResult_HasNoTruthValue()
    {
        // The exact-list result is a list like any other: it stays invalid as
        // an `if` condition, so `atoms` introduces no list truthiness.
        Assert.True(Fails("if(atoms((1, 2)), 10, 20)"));
        Assert.True(Fails("if(atoms(7), 10, 20)"));
    }

    [Fact]
    public void Atoms_AsFilterPredicate_IsRejectedByStrictContract()
        // The predicate now returns one exact list per item, and lists have
        // no truth value under the strict predicate contract.
        => Assert.True(Fails("filter((1, 2), atoms)"));

    [Fact]
    public void Atoms_AsMapCallback_ProducesListElements()
        // Each callback result is one exact list, preserved whole as an
        // element of map's own list result.
        => AssertDisplay("map((1, 2), atoms)", "[[1], [2]]");
}
