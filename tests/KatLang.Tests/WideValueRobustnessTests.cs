using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// Companion to <see cref="DeepValueRobustnessTests"/> for the BREADTH axis:
/// a legal collection holds up to 100,000 items
/// (<see cref="EvaluationLimits.MaxSupportedCollectionItems"/>), so whole-value
/// walks must keep their auxiliary traversal storage proportional to nesting
/// depth — indexed continuation frames, never one stack entry per pending
/// sibling, which for wide, shallow values allocated large-object-heap-sized
/// backing arrays. Output storage (atom collections, diagnostic strings,
/// reified ASTs) legitimately scales with the produced result.
/// </summary>
public class WideValueRobustnessTests
{
    private const int Wide = 100_000;

    // ── Language-level coverage at the maximum ordinary breadth ─────────────

    private static EvalResult<IReadOnlyList<decimal>> Eval(string source)
    {
        var ast = SourceProvenance.ParseValid(source).Root;
        return Evaluator.RunFlat(new Expr.AlgorithmExpr(ast));
    }

    private static void AssertEval(string source, params decimal[] expected)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value);
    }

    [Fact]
    public void WideListEquality()
        => AssertEval($"range(1, {Wide}) == range(1, {Wide}), range(1, {Wide}) == range(0, {Wide - 1})", 1, 0);

    [Fact]
    public void WideDistinct()
        => AssertEval($"distinct((range(1, {Wide}), range(1, {Wide}))).count", 1);

    [Fact]
    public void WideContains()
        => AssertEval($"contains((range(1, {Wide}), 5), range(1, {Wide}))", 1);

    [Fact]
    public void WideAtomsBuiltin()
        => AssertEval($"atoms(range(1, {Wide})).count", Wide);

    [Fact]
    public void WideDotCallReceiverReification()
        => AssertEval($"range(1, {Wide}).count", Wide);

    // ── Direct coverage of the Result walks ─────────────────────────────────

    private static Result.Atom[] WideAtoms(int count, int lastDelta = 0)
    {
        var items = new Result.Atom[count];
        for (var i = 0; i < count; i++)
            items[i] = new Result.Atom(i);
        items[count - 1] = new Result.Atom(count - 1 + lastDelta);
        return items;
    }

    private static Result WideList(int count, int lastDelta = 0)
        => Result.ListValue.TakeOwnership(WideAtoms(count, lastDelta));

    private static Result WideSequence(int count, int lastDelta = 0)
        => Result.SequenceValue.TakeOwnership(WideAtoms(count, lastDelta));

    /// <summary>
    /// A value that is deep AND wide at once: <paramref name="depth"/> nested
    /// list levels, each carrying <paramref name="breadth"/> filler atoms after
    /// the nested child, so traversal must suspend and resume sibling runs at
    /// every level.
    /// </summary>
    private static Result Comb(int depth, int breadth, decimal leaf)
    {
        Result value = new Result.Atom(leaf);
        for (var level = 0; level < depth; level++)
        {
            var items = new Result[breadth + 1];
            items[0] = value;
            for (var i = 1; i <= breadth; i++)
                items[i] = new Result.Atom(i);
            value = Result.ListValue.TakeOwnership(items);
        }

        return value;
    }

    [Fact]
    public void ValueComparerHandlesWideValues()
    {
        Assert.True(Result.ValueComparer.Equals(WideList(Wide), WideList(Wide)));
        Assert.True(Result.ValueComparer.Equals(WideSequence(Wide), WideSequence(Wide)));

        // The lone difference sits at the final item, so the walk visits the
        // full breadth before deciding.
        Assert.False(Result.ValueComparer.Equals(WideList(Wide), WideList(Wide, lastDelta: 1)));
        Assert.False(Result.ValueComparer.Equals(WideSequence(Wide), WideSequence(Wide, lastDelta: 1)));

        // Kind stays decisive regardless of identical elements.
        Assert.False(Result.ValueComparer.Equals(WideList(Wide), WideSequence(Wide)));
    }

    [Fact]
    public void ValueComparerHandlesCombValues()
    {
        Assert.True(Result.ValueComparer.Equals(Comb(2_000, 49, 0), Comb(2_000, 49, 0)));
        Assert.False(Result.ValueComparer.Equals(Comb(2_000, 49, 0), Comb(2_000, 49, 1)));
        Assert.Equal(
            Result.ValueComparer.GetHashCode(Comb(2_000, 49, 0)),
            Result.ValueComparer.GetHashCode(Comb(2_000, 49, 0)));
    }

    [Fact]
    public void ValueComparerHashesWideValuesConsistently()
    {
        Assert.Equal(
            Result.ValueComparer.GetHashCode(WideList(Wide)),
            Result.ValueComparer.GetHashCode(WideList(Wide)));

        var seen = new HashSet<Result>(Result.ValueComparer)
        {
            WideList(Wide),
            WideList(Wide),
            WideList(Wide, lastDelta: 1),
        };
        Assert.Equal(2, seen.Count);
    }

    [Fact]
    public void AtomViewsHandleWideValues()
    {
        var expected = new decimal[Wide];
        for (var i = 0; i < Wide; i++)
            expected[i] = i;

        Assert.Equal(expected, WideSequence(Wide).ToAtoms());
        Assert.Equal(expected, WideList(Wide).LanguageAtoms());
        Assert.Equal(expected, WideList(Wide).ToHostAtoms());
    }

    [Fact]
    public void BoundedAtomCollectionStopsEarlyOnWideValues()
    {
        // The bound must stop the walk at the atom that would exceed it and
        // return exactly the atoms collected up to that point.
        Assert.False(WideList(Wide).TryLanguageAtoms(10, out var languageAtoms));
        Assert.Equal([0m, 1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m], languageAtoms);

        Assert.False(WideList(Wide).TryToHostAtoms(10, out var hostAtoms));
        Assert.Equal([0m, 1m, 2m, 3m, 4m, 5m, 6m, 7m, 8m, 9m], hostAtoms);
    }

    [Fact]
    public void NormalizeHandlesWideValues()
    {
        // Scattered redundant singleton sequences canonicalize away while the
        // wide flat remainder is preserved element for element.
        var items = new Result[Wide];
        for (var i = 0; i < Wide; i++)
            items[i] = new Result.Atom(i);
        items[0] = Result.SequenceValue.TakeOwnership([new Result.Atom(0)]);
        items[Wide / 2] = Result.SequenceValue.TakeOwnership([new Result.Atom(Wide / 2)]);
        items[Wide - 1] = Result.SequenceValue.TakeOwnership([new Result.Atom(Wide - 1)]);

        var normalized = Result.SequenceValue.TakeOwnership(items).Normalize();
        Assert.True(Result.ValueComparer.Equals(WideSequence(Wide), normalized));

        var normalizedList = WideList(Wide).Normalize();
        Assert.True(Result.ValueComparer.Equals(WideList(Wide), normalizedList));
    }

    [Fact]
    public void DiagnosticFormattingHandlesWideValues()
    {
        // The full expansion is ~588,000 characters. The diagnostic fragment is bounded
        // during construction, so the renderer emits the budgeted prefix of exactly that
        // text and stops — the naive expansion is the oracle, never the output.
        var full = $"[{string.Join(", ", Enumerable.Range(0, Wide))}]";

        Assert.Equal(
            full[..DiagnosticValueRenderer.MaxRenderedValueLength] + DiagnosticValueRenderer.TruncationMarker,
            Evaluator.FormatResultForDiagnostic(WideList(Wide)));
    }

    [Fact]
    public void WideFlatTraversalsAllocateOnlyContinuationFrames()
    {
        var left = WideList(Wide);
        var right = WideList(Wide);

        // Warm up so first-call JIT and lazy statics do not count against the
        // measured pass.
        for (var i = 0; i < 3; i++)
        {
            _ = Result.ValueComparer.Equals(left, right);
            _ = Result.ValueComparer.GetHashCode(left);
        }

        var before = GC.GetAllocatedBytesForCurrentThread();
        var equal = Result.ValueComparer.Equals(left, right);
        var equalityAllocated = GC.GetAllocatedBytesForCurrentThread() - before;

        before = GC.GetAllocatedBytesForCurrentThread();
        _ = Result.ValueComparer.GetHashCode(left);
        var hashAllocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.True(equal);

        // Sibling-granular stacks allocated ~4.2 MB per wide equality and
        // ~2.1 MB per wide hash (measured before the indexed-frame rewrite).
        // A flat wide value needs only an empty continuation stack, so 64 KB
        // is a deliberately generous deterministic ceiling that still fails
        // decisively on any O(breadth) traversal storage.
        Assert.True(
            equalityAllocated < 64_000,
            $"wide flat equality allocated {equalityAllocated} bytes of traversal storage");
        Assert.True(
            hashAllocated < 64_000,
            $"wide flat hashing allocated {hashAllocated} bytes of traversal storage");
    }

    [Fact]
    public void BoundedDisplayStopsWideTraversalWithoutBreadthSizedStack()
    {
        var value = WideList(Wide);
        var displayOptions = new DisplayOptions(null, 16);

        // Warm up the renderer and its numeric formatting before measuring.
        for (var i = 0; i < 3; i++)
        {
            var warmupWriter = new BoundedDisplayWriter(displayOptions.MaxDisplayLength);
            _ = RunResult.AppendValue(value, displayOptions, warmupWriter);
        }

        var writer = new BoundedDisplayWriter(displayOptions.MaxDisplayLength);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var completed = RunResult.AppendValue(value, displayOptions, writer);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.False(completed);
        Assert.True(writer.LimitExceeded);

        // The old pending-sibling stack allocated ~4.2 MB before rendering
        // the opening delimiter, even though this writer stops after 16 UTF-16
        // units. Output plus depth-only traversal state stays far below this
        // ceiling and any O(breadth) regression fails decisively.
        Assert.True(
            allocated < 64_000,
            $"bounded display of a wide flat value allocated {allocated} bytes");
    }
}
