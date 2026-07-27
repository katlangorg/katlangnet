namespace KatLang.Tests;

/// <summary>
/// Observable immutability of exact list values (<see cref="Result.ListValue"/>):
/// public construction snapshots untrusted input, and no public item view
/// (<c>Items</c>, <c>SpreadItems</c>, <c>StructureItems</c>, enumeration)
/// exposes storage through which a published value can be mutated.
/// These tests assert semantic guarantees — display, count, value equality,
/// and semantic hash stability — not a specific storage implementation.
/// </summary>
public class ListValueImmutabilityTests
{
    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result.ListValue List(params Result[] items) => new(items);

    private static Result.ListValue EvaluateList(string source)
    {
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        return Assert.IsType<Result.ListValue>(run.Value);
    }

    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString();
    }

    private static void AssertSemanticallyEqual(Result expected, Result actual)
        => Assert.True(
            Result.ValueComparer.Equals(expected, actual),
            $"Expected {expected} but got {actual}");

    /// <summary>
    /// Attempt every plausible host-side mutation path through a public item
    /// view. A mutable cast may legitimately be unavailable; when a cast
    /// succeeds, every mutation member must throw without changing the value.
    /// Callers re-assert the owning value's content afterwards — that content
    /// check, not the exception type, is the actual guarantee.
    /// </summary>
    private static void ProbeViewForMutation(IReadOnlyList<Result> view)
    {
        Assert.False(view is Result[], "item view must not be the raw backing array");
        Assert.False(view is List<Result>, "item view must not be a mutable list");

        if (view is IList<Result> asList)
        {
            Assert.ThrowsAny<Exception>(() => asList.Add(Atom(99)));
            Assert.ThrowsAny<Exception>(() => asList.Insert(0, Atom(99)));
            Assert.ThrowsAny<Exception>(() => asList.Clear());
            if (asList.Count > 0)
            {
                Assert.ThrowsAny<Exception>(() => asList[0] = Atom(99));
                Assert.ThrowsAny<Exception>(() => asList.RemoveAt(0));
                Assert.ThrowsAny<Exception>(() => asList.Remove(asList[0]));
            }
        }

        if (view is ICollection<Result> asCollection && asCollection is not IList<Result>)
        {
            Assert.ThrowsAny<Exception>(() => asCollection.Add(Atom(99)));
            Assert.ThrowsAny<Exception>(() => asCollection.Clear());
        }
    }

    // ── 1. Constructor input is snapshotted ─────────────────────────────────

    [Fact]
    public void Constructor_MutableListInput_IsSnapshotted()
    {
        var source = new List<Result> { Atom(1) };

        var value = new Result.ListValue(source);
        var hashBefore = Result.ValueComparer.GetHashCode(value);

        source.Add(Atom(2));
        source[0] = Atom(42);

        Assert.Single(value.Items);
        AssertSemanticallyEqual(List(Atom(1)), value);
        Assert.Equal(hashBefore, Result.ValueComparer.GetHashCode(value));
        Assert.True(Result.ValueComparer.Equals(
            value,
            new Result.ListValue(new[] { Atom(1) })));
    }

    [Fact]
    public void Constructor_ArrayInput_IsSnapshotted()
    {
        var source = new[] { Atom(1) };

        var value = new Result.ListValue(source);

        source[0] = Atom(2);

        Assert.Single(value.Items);
        AssertSemanticallyEqual(List(Atom(1)), value);
    }

    // ── 2. Evaluator-produced list cannot be mutated from the host ──────────

    [Fact]
    public void EvaluatorProducedList_ResistsHostMutation()
    {
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run("[1]"));
        var value = Assert.IsType<Result.ListValue>(run.Value);
        var hashBefore = Result.ValueComparer.GetHashCode(value);

        Assert.Equal("[1]", run.ToDisplayString());

        ProbeViewForMutation(value.Items);

        Assert.Equal("[1]", run.ToDisplayString());
        Assert.Single(value.Items);
        AssertSemanticallyEqual(List(Atom(1)), value);
        Assert.Equal(hashBefore, Result.ValueComparer.GetHashCode(value));
    }

    [Fact]
    public void EvaluatorProducedEmptyList_ResistsHostMutation()
    {
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run("[]"));
        var value = Assert.IsType<Result.ListValue>(run.Value);

        ProbeViewForMutation(value.Items);

        Assert.Equal("[]", run.ToDisplayString());
        Assert.Empty(value.Items);
        AssertSemanticallyEqual(List(), value);
    }

    // ── 2b. Builtin-produced lists cannot be mutated from the host ──────────

    [Theory]
    [InlineData("take((1, 2, 3), 2)", "[1, 2]")]
    [InlineData("range(1, 3)", "[1, 2, 3]")]
    [InlineData("Double = x * 2\nmap((1, 2, 3), Double)", "[2, 4, 6]")]
    [InlineData("atoms((1, [2, 3]))", "[1, 2, 3]")]
    [InlineData("atoms(7)", "[7]")]
    [InlineData("atoms('text')", "[]")]
    public void BuiltinProducedList_ResistsHostMutation(string source, string expectedDisplay)
    {
        // Collection-producing builtins return one exact immutable list value;
        // the Items view (including mutable-interface downcasts probed by
        // ProbeViewForMutation) must not expose writable storage.
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        var value = Assert.IsType<Result.ListValue>(run.Value);
        var hashBefore = Result.ValueComparer.GetHashCode(value);
        var itemCountBefore = value.Items.Count;

        Assert.Equal(expectedDisplay, run.ToDisplayString());

        ProbeViewForMutation(value.Items);
        ProbeViewForMutation(value.SpreadItems());

        Assert.Equal(expectedDisplay, run.ToDisplayString());
        Assert.Equal(itemCountBefore, value.Items.Count);
        Assert.Equal(hashBefore, Result.ValueComparer.GetHashCode(value));
    }

    // ── 3. Spread view cannot mutate the original list ──────────────────────

    [Fact]
    public void SpreadView_CannotMutateOriginalList()
    {
        var value = EvaluateList("[1, 2, 3]");

        ProbeViewForMutation(value.SpreadItems());

        Assert.Equal(3, value.Items.Count);
        AssertSemanticallyEqual(List(Atom(1), Atom(2), Atom(3)), value);
        Assert.Equal(3, value.SpreadItems().Count);
    }

    [Fact]
    public void SpreadProgram_BehaviorRetained()
    {
        Assert.Equal(
            string.Join(Environment.NewLine, "1", "2", "3"),
            Display("A = [1, 2, 3]\nA..."));
    }

    // ── 4. Structure/deconstruction view cannot mutate the original list ────

    [Fact]
    public void StructureView_CannotMutateOriginalList()
    {
        var value = EvaluateList("[1, 2, 3]");
        var structure = value.StructureItems();

        Assert.NotNull(structure);
        ProbeViewForMutation(structure);

        Assert.Equal(3, value.Items.Count);
        AssertSemanticallyEqual(List(Atom(1), Atom(2), Atom(3)), value);
    }

    // ── 4b. Projection-selected lists cannot be mutated from the host ───────

    [Theory]
    [InlineData("[[1, 2], [3, 4]]:0", "[1, 2]")]
    [InlineData("(0, [1, 2]):1", "[1, 2]")]
    [InlineData("take([[1, 2], [3, 4]], 1):0", "[1, 2]")]
    public void ProjectionSelectedList_ResistsHostMutation(string source, string expectedDisplay)
    {
        // A list selected by `:` is an ordinary immutable list value: no item
        // view of the selection exposes writable storage.
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        var value = Assert.IsType<Result.ListValue>(run.Value);
        var hashBefore = Result.ValueComparer.GetHashCode(value);

        Assert.Equal(expectedDisplay, run.ToDisplayString());

        ProbeViewForMutation(value.Items);
        ProbeViewForMutation(value.SpreadItems());

        Assert.Equal(expectedDisplay, run.ToDisplayString());
        AssertSemanticallyEqual(List(Atom(1), Atom(2)), value);
        Assert.Equal(hashBefore, Result.ValueComparer.GetHashCode(value));
    }

    [Fact]
    public void ProjectionSelectedList_SourceListStaysStable()
    {
        var rows = EvaluateList("[[1, 2], [3, 4]]");
        var selected = Assert.IsType<Result.ListValue>(rows.Index(0));

        ProbeViewForMutation(selected.Items);
        ProbeViewForMutation(selected.SpreadItems());

        AssertSemanticallyEqual(List(Atom(1), Atom(2)), selected);
        Assert.Equal(2, rows.Items.Count);
        AssertSemanticallyEqual(
            List(List(Atom(1), Atom(2)), List(Atom(3), Atom(4))),
            rows);
        AssertSemanticallyEqual(selected, rows.Items[0]);
    }

    [Fact]
    public void DeconstructionProgram_BehaviorRetained()
    {
        Assert.Equal(
            string.Join(Environment.NewLine, "1", "2", "3"),
            Display("A = [1, 2, 3]\nx, y, z = A\nx, y, z"));
    }

    // ── 5. Hash-based collection stability ───────────────────────────────────

    [Fact]
    public void HashSetMembership_SurvivesAllMutationAttempts()
    {
        var constructorInput = new List<Result> { Atom(1) };
        var value = new Result.ListValue(constructorInput);
        var hashBefore = Result.ValueComparer.GetHashCode(value);

        var set = new HashSet<Result>(Result.ValueComparer) { value };

        constructorInput.Add(Atom(2));
        ProbeViewForMutation(value.Items);
        ProbeViewForMutation(value.SpreadItems());
        var structure = value.StructureItems();
        Assert.NotNull(structure);
        ProbeViewForMutation(structure);

        Assert.Contains(value, set);
        Assert.Contains(List(Atom(1)), set);
        Assert.DoesNotContain(List(Atom(1), Atom(2)), set);
        Assert.Equal(hashBefore, Result.ValueComparer.GetHashCode(value));
        AssertSemanticallyEqual(List(Atom(1)), value);
        Assert.Single(value.Items);
    }

    // ── 6. Nested aliasing ────────────────────────────────────────────────────

    [Fact]
    public void NestedLists_MutatingEitherConstructorInput_DoesNotAlterPublishedValue()
    {
        var innerInput = new List<Result> { Atom(1) };
        var inner = new Result.ListValue(innerInput);

        var outerInput = new List<Result> { inner };
        var outer = new Result.ListValue(outerInput);

        innerInput.Add(Atom(2));
        outerInput.Add(Atom(3));
        outerInput[0] = Atom(42);

        AssertSemanticallyEqual(List(List(Atom(1))), outer);
        AssertSemanticallyEqual(List(Atom(1)), inner);
        Assert.Single(outer.Items);
        var publishedInner = Assert.IsType<Result.ListValue>(outer.Items[0]);
        Assert.Single(publishedInner.Items);
    }

    // ── Enumeration exposes values, not storage ──────────────────────────────

    [Fact]
    public void Enumeration_YieldsValuesWithoutExposingStorage()
    {
        var value = EvaluateList("[1, 2]");

        var seen = new List<Result>();
        foreach (var item in value.Items)
            seen.Add(item);

        // Mutating the collection built from enumeration must not touch the value.
        seen.Add(Atom(99));
        seen[0] = Atom(42);

        Assert.Equal(2, value.Items.Count);
        AssertSemanticallyEqual(List(Atom(1), Atom(2)), value);
    }

    // ── 7. Existing semantics remain unchanged ──────────────────────────────

    [Theory]
    [InlineData("[]", "[]")]
    [InlineData("[1]", "[1]")]
    [InlineData("[[1]]", "[[1]]")]
    [InlineData("[[]]", "[[]]")]
    [InlineData("[1, 2] == [1, 2]", "1")]
    [InlineData("[1, 2] != (1, 2)", "1")]
    [InlineData("A = [1, 2, 3]\n[A...]", "[1, 2, 3]")]
    [InlineData("A = [1, 2, 3]\nx = A\nx", "[1, 2, 3]")]
    [InlineData("A = [1, 2, 3]\nx = A...\nx", "(1, 2, 3)")]
    [InlineData("F(x) = x\nA = [1, 2, 3]\nF(A)", "[1, 2, 3]")]
    [InlineData("F(a, b, c) = a + b + c\nA = [1, 2, 3]\nF(A...)", "6")]
    public void RepresentativeListSemantics_Unchanged(string source, string expected)
        => Assert.Equal(expected, Display(source));

    [Fact]
    public void CollectingBinding_CollectsExactList()
        // The collecting binding collects the remaining opened elements as one exact
        // immutable list value.
        => Assert.Equal(
            string.Join(Environment.NewLine, "1", "[2, 3]"),
            Display("A = [1, 2, 3]\nx, ...rest = A\nx, rest"));
}
