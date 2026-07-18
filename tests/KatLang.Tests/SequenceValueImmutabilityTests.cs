namespace KatLang.Tests;

/// <summary>
/// Observable immutability of sequence values (<see cref="Result.SequenceValue"/>),
/// following the same model as <see cref="ListValueImmutabilityTests"/>:
/// public construction snapshots untrusted input, and no public item view
/// (<c>Items</c>, <c>ToItems</c>, <c>SpreadItems</c>, <c>StructureItems</c>,
/// enumeration) exposes storage through which a published value can be
/// mutated. These tests assert semantic guarantees — display, count, value
/// equality, and semantic hash stability — not a specific storage
/// implementation.
/// </summary>
public class SequenceValueImmutabilityTests
{
    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result.SequenceValue Seq(params Result[] items) => new(items);

    private static Result.ListValue Lst(params Result[] items) => new(items);

    private static RunResult.Success Run(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));

    private static Result.SequenceValue EvaluateSequence(string source)
        => Assert.IsType<Result.SequenceValue>(Run(source).Value);

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
    }

    /// <summary>Probe every public item view of one sequence value.</summary>
    private static void ProbeAllViews(Result.SequenceValue value)
    {
        ProbeViewForMutation(value.Items);
        ProbeViewForMutation(value.ToItems());
        ProbeViewForMutation(value.SpreadItems());
        var structure = value.StructureItems();
        Assert.NotNull(structure);
        ProbeViewForMutation(structure);
    }

    /// <summary>Probe every public item view of one exact list value.</summary>
    private static void ProbeAllViews(Result.ListValue value)
    {
        ProbeViewForMutation(value.Items);
        ProbeViewForMutation(value.SpreadItems());
        var structure = value.StructureItems();
        Assert.NotNull(structure);
        ProbeViewForMutation(structure);
    }

    // ── 1. Constructor input is snapshotted ─────────────────────────────────

    [Fact]
    public void Constructor_MutableListInput_IsSnapshotted()
    {
        var source = new List<Result> { Atom(1), Atom(2) };

        var value = new Result.SequenceValue(source);
        var hashBefore = Result.ValueComparer.GetHashCode(value);

        source.Add(Atom(3));
        source[0] = Atom(42);

        Assert.Equal(2, value.Items.Count);
        AssertSemanticallyEqual(Seq(Atom(1), Atom(2)), value);
        Assert.Equal(hashBefore, Result.ValueComparer.GetHashCode(value));
        Assert.True(Result.ValueComparer.Equals(
            value,
            new Result.SequenceValue(new[] { Atom(1), Atom(2) })));
    }

    [Fact]
    public void Constructor_ArrayInput_IsSnapshotted()
    {
        var source = new[] { Atom(1), Atom(2) };

        var value = new Result.SequenceValue(source);

        source[0] = Atom(42);

        Assert.Equal(2, value.Items.Count);
        AssertSemanticallyEqual(Seq(Atom(1), Atom(2)), value);
    }

    // ── 2. Evaluator-produced sequence cannot be mutated from the host ──────

    [Fact]
    public void EvaluatorProducedSequence_ResistsHostMutation()
    {
        var run = Run("(1, 2)");
        var value = Assert.IsType<Result.SequenceValue>(run.Value);
        var hashBefore = Result.ValueComparer.GetHashCode(value);
        var displayBefore = run.ToDisplayString();

        Assert.Equal("(1, 2)", displayBefore);

        ProbeAllViews(value);

        Assert.Equal(displayBefore, run.ToDisplayString());
        Assert.Equal(2, value.Items.Count);
        AssertSemanticallyEqual(Seq(Atom(1), Atom(2)), value);
        Assert.Equal(hashBefore, Result.ValueComparer.GetHashCode(value));
    }

    [Fact]
    public void PropertyCapturedSequence_ResistsHostMutation()
    {
        var run = Run("A = 1, 2\nA");
        var value = Assert.IsType<Result.SequenceValue>(run.Value);

        ProbeAllViews(value);

        Assert.Equal("(1, 2)", run.ToDisplayString());
        AssertSemanticallyEqual(Seq(Atom(1), Atom(2)), value);
    }

    // ── 3. Empty sequence ────────────────────────────────────────────────────

    [Fact]
    public void EmptySequence_ResistsHostMutation_AndKeepsSpecialArity()
    {
        var run = Run("()");
        var value = Assert.IsType<Result.SequenceValue>(run.Value);
        var displayBefore = run.ToDisplayString();

        ProbeAllViews(value);

        Assert.Equal(displayBefore, run.ToDisplayString());
        Assert.Empty(value.Items);
        Assert.Equal(0, value.ValueCount());
        AssertSemanticallyEqual(Seq(), value);
    }

    // ── 4. Nested constructor aliasing ───────────────────────────────────────

    [Fact]
    public void NestedSequences_MutatingEitherConstructorInput_DoesNotAlterPublishedValue()
    {
        var innerInput = new List<Result> { Atom(1), Atom(2) };
        var inner = new Result.SequenceValue(innerInput);

        var outerInput = new List<Result> { inner, Atom(3) };
        var outer = new Result.SequenceValue(outerInput);

        innerInput.Add(Atom(9));
        outerInput.Add(Atom(9));
        outerInput[0] = Atom(42);

        AssertSemanticallyEqual(Seq(Seq(Atom(1), Atom(2)), Atom(3)), outer);
        AssertSemanticallyEqual(Seq(Atom(1), Atom(2)), inner);
        Assert.Equal(2, outer.Items.Count);
        var publishedInner = Assert.IsType<Result.SequenceValue>(outer.Items[0]);
        Assert.Equal(2, publishedInner.Items.Count);
    }

    // ── 5. Hash-based collection stability ───────────────────────────────────

    [Fact]
    public void HashSetMembership_SurvivesAllMutationAttempts()
    {
        var constructorInput = new List<Result> { Atom(1), Atom(2) };
        var value = new Result.SequenceValue(constructorInput);
        var hashBefore = Result.ValueComparer.GetHashCode(value);

        var set = new HashSet<Result>(Result.ValueComparer) { value };

        constructorInput.Add(Atom(3));
        ProbeAllViews(value);

        Assert.Contains(value, set);
        Assert.Contains(Seq(Atom(1), Atom(2)), set);
        Assert.DoesNotContain(Seq(Atom(1), Atom(2), Atom(3)), set);
        Assert.Equal(hashBefore, Result.ValueComparer.GetHashCode(value));
        AssertSemanticallyEqual(Seq(Atom(1), Atom(2)), value);
    }

    // ── 6. Normalize results own their storage ───────────────────────────────

    [Fact]
    public void NormalizedSequence_ResistsHostMutation()
    {
        var run = Run("((1, 2), 3)");
        var value = Assert.IsType<Result.SequenceValue>(run.Value);

        ProbeAllViews(value);
        var nested = Assert.IsType<Result.SequenceValue>(value.Items[0]);
        ProbeAllViews(nested);

        Assert.Equal("((1, 2), 3)", run.ToDisplayString());
        AssertSemanticallyEqual(Seq(Seq(Atom(1), Atom(2)), Atom(3)), value);
    }

    [Fact]
    public void Normalize_RebuiltChildren_OwnTheirStorage()
    {
        var input = new List<Result> { Seq(Atom(1), Atom(2)), Atom(3) };
        var normalized = Assert.IsType<Result.SequenceValue>(
            new Result.SequenceValue(input).Normalize());

        input.Add(Atom(9));
        ProbeAllViews(normalized);

        AssertSemanticallyEqual(Seq(Seq(Atom(1), Atom(2)), Atom(3)), normalized);
    }

    // ── 7. FromItems ──────────────────────────────────────────────────────────

    [Fact]
    public void FromItems_ShapesPreserved_AndResultOwnsStorage()
    {
        AssertSemanticallyEqual(Seq(), Result.FromItems([]));
        AssertSemanticallyEqual(Atom(7), Result.FromItems([Atom(7)]));

        var input = new List<Result> { Atom(1), Atom(2) };
        var value = Assert.IsType<Result.SequenceValue>(Result.FromItems(input));

        input.Add(Atom(3));
        ProbeAllViews(value);

        AssertSemanticallyEqual(Seq(Atom(1), Atom(2)), value);
    }

    // ── 8. Rest and variadic capture (exact immutable list values) ───────────

    [Fact]
    public void RestCapturedList_IsExactList_AndImmutable()
    {
        // Rest bindings collect their assigned slots as one exact immutable
        // list value, probed like ListValueImmutabilityTests probes lists.
        var run = Run("head, rest... = 1, 2, 3\nrest");
        var value = Assert.IsType<Result.ListValue>(run.Value);

        ProbeAllViews(value);

        Assert.Equal("[2, 3]", run.ToDisplayString());
        AssertSemanticallyEqual(Lst(Atom(2), Atom(3)), value);
    }

    [Fact]
    public void VariadicCapturedList_IsExactList_AndImmutable()
    {
        var run = Run("Inspect(items...) = items\nInspect(1, 2, 3)");
        var value = Assert.IsType<Result.ListValue>(run.Value);

        ProbeAllViews(value);

        Assert.Equal("[1, 2, 3]", run.ToDisplayString());
        AssertSemanticallyEqual(Lst(Atom(1), Atom(2), Atom(3)), value);
    }

    // ── 9. Builtin-produced collections ───────────────────────────────────────

    [Theory]
    [InlineData("order((3, 1, 2))", "[1, 2, 3]")]
    [InlineData("map((1, 2, 3), {a * 2})", "[2, 4, 6]")]
    [InlineData("filter((1, 2, 3, 4), {a > 2})", "[3, 4]")]
    [InlineData("range(1, 3)", "[1, 2, 3]")]
    [InlineData("take((1, 2, 3, 4), 2)", "[1, 2]")]
    [InlineData("skip((1, 2, 3, 4), 2)", "[3, 4]")]
    [InlineData("distinct((1, 2, 2, 3))", "[1, 2, 3]")]
    [InlineData("atoms((1, 2, 3))", "[1, 2, 3]")]
    [InlineData("atoms([1, [2, (3, [4])]])", "[1, 2, 3, 4]")]
    [InlineData("atoms('text')", "[]")]
    public void BuiltinProducedList_ResistsHostMutation(string source, string expectedDisplay)
    {
        // Collection-producing builtins return one exact immutable list value.
        var run = Run(source);
        var value = Assert.IsType<Result.ListValue>(run.Value);

        Assert.Equal(expectedDisplay, run.ToDisplayString());

        ProbeAllViews(value);

        Assert.Equal(expectedDisplay, run.ToDisplayString());
    }

    [Fact]
    public void BuiltinProducedSequence_ResistsHostMutation()
    {
        // `first` returns the stored item unchanged, so a sequence-valued
        // item surfaces as a builtin-produced sequence value. (`atoms` now
        // materializes one exact immutable list like the other
        // collection-producing builtins; see ListValueImmutabilityTests.)
        var run = Run("first(((1, 2, 3), 4))");
        var value = Assert.IsType<Result.SequenceValue>(run.Value);

        Assert.Equal("(1, 2, 3)", run.ToDisplayString());

        ProbeAllViews(value);

        Assert.Equal("(1, 2, 3)", run.ToDisplayString());
    }

    // ── 10. Optimizer parity ──────────────────────────────────────────────────

    [Theory]
    [InlineData("Data = 4, 1, 3, 2\nData.filter({a > 1})")]
    [InlineData("Data = 4, 1, 3, 2\nData.order")]
    [InlineData("Step(a, b) = b, a + b, b < 20\nStep.while(1, 1)")]
    public void OptimizerModes_AgreeAndBothProduceImmutableCollections(string source)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(parseResult.HasErrors);

        var generic = RunWithSequenceOptimization(parseResult.Root, enabled: false);
        var optimized = RunWithSequenceOptimization(parseResult.Root, enabled: true);
        Assert.False(generic.IsError, $"generic path failed: {(generic.IsError ? generic.Error : null)}");
        Assert.False(optimized.IsError, $"optimized path failed: {(optimized.IsError ? optimized.Error : null)}");

        Assert.True(
            Result.ValueComparer.Equals(generic.Value, optimized.Value),
            $"optimizer divergence: {generic.Value} vs {optimized.Value}");

        // Every case yields a collection value: filter/order produce exact
        // list values, while loop state stays a sequence value. Probe both
        // kinds so neither silently skips.
        foreach (var value in new[] { generic.Value, optimized.Value })
        {
            var expected = optimized.Value;
            switch (value)
            {
                case Result.SequenceValue sequence:
                    ProbeAllViews(sequence);
                    break;
                case Result.ListValue list:
                    ProbeAllViews(list);
                    break;
                default:
                    Assert.Fail($"expected a collection-valued result but got {value}");
                    break;
            }

            Assert.True(Result.ValueComparer.Equals(expected, value));
        }
    }

    private static EvalResult<Result> RunWithSequenceOptimization(Algorithm root, bool enabled)
        => Evaluator.Run(
            new Expr.Block(root),
            new Evaluation.Caching.RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: enabled,
            sequenceDiagnostics: null);

    // ── 11. Trusted ownership path ────────────────────────────────────────────
    // The never-mutate-after-transfer invariant itself is enforced by the
    // restricted (internal) visibility and code review; deliberately mutating
    // a transferred array is a contract violation, so no test does that.

    [Fact]
    public void TakeOwnership_ExposesOnlyAReadOnlyViewWithStableContents()
    {
        var value = Result.SequenceValue.TakeOwnership([Atom(1), Atom(2)]);

        ProbeAllViews(value);

        Assert.Equal(2, value.Items.Count);
        AssertSemanticallyEqual(Seq(Atom(1), Atom(2)), value);
    }

    // ── Enumeration exposes values, not storage ───────────────────────────────

    [Fact]
    public void Enumeration_YieldsValuesWithoutExposingStorage()
    {
        var value = EvaluateSequence("(1, 2)");

        var seen = new List<Result>();
        foreach (var item in value.Items)
            seen.Add(item);

        seen.Add(Atom(99));
        seen[0] = Atom(42);

        Assert.Equal(2, value.Items.Count);
        AssertSemanticallyEqual(Seq(Atom(1), Atom(2)), value);
    }

    // ── Existing semantics remain unchanged ──────────────────────────────────

    [Theory]
    [InlineData("()", "()")]
    [InlineData("(1)", "1")]
    [InlineData("(1, 2)", "(1, 2)")]
    [InlineData("((1, 2))", "(1, 2)")]
    [InlineData("((1, 2), 3)", "((1, 2), 3)")]
    [InlineData("(1, 2) == (1, 2)", "1")]
    [InlineData("A = 1, 2, 3\nx = A\nx", "(1, 2, 3)")]
    [InlineData("F(x) = x\nA = 1, 2, 3\nF(A)", "(1, 2, 3)")]
    [InlineData("F(a, b, c) = a + b + c\nA = 1, 2, 3\nF(A...)", "6")]
    [InlineData("Sum(items...) = items.sum\nA = 1, 2, 3\nSum(A...)", "6")]
    public void RepresentativeSequenceSemantics_Unchanged(string source, string expected)
        // (The grouped rest call `Sum(A)` is intentionally absent: the rest
        // binding collects [A] whose element is non-numeric, so it errors.)
        => Assert.Equal(expected, Run(source).ToDisplayString());

    [Fact]
    public void RootRowsAndDeconstruction_BehaviorRetained()
    {
        Assert.Equal(
            string.Join(Environment.NewLine, "1", "2", "3"),
            Run("A = 1, 2, 3\nA...").ToDisplayString());
        Assert.Equal(
            string.Join(Environment.NewLine, "1", "2", "3"),
            Run("A = 1, 2, 3\nx, y, z = A\nx, y, z").ToDisplayString());
    }
}
