namespace KatLang.Tests;

/// <summary>
/// Focused regression matrix for the dot-call receiver binding law. A lexical
/// dot-call receiver (<c>recv.F(extra...)</c> falling back to lexical
/// <c>F</c>) is injected as ONE leading argument segment. Segments are
/// allocated to parameters first — arity check plus fixed prefix/suffix
/// binding from front and back — and the receiver's item count never
/// satisfies arity. A fixed parameter binds the segment's VALUE; if and only
/// if the segment is allocated to a flat TOP-LEVEL collecting parameter does
/// the collector consume the segment's evaluated top-level SUPPLY items (one
/// level, never recursive). The receiver's supply is its raw counted
/// evaluation: an inline group <c>(1, 2, 3)</c> or zero-parameter brace block
/// emits its row supply, a named property receiver emits its value-boundary
/// count (one item, zero for an empty-sequence property), and exact lists
/// stay opaque (one item). Direct calls are unchanged: a written argument
/// slot always reifies one value.
/// </summary>
public class DotCallCollectingReceiverTests
{
    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result Seq(params Result[] items) => new Result.SequenceValue(items);

    private static Result List(params Result[] items) => new Result.ListValue(items);

    /// <summary>
    /// STRICT-SOURCE: requires a clean front end, then evaluates through both
    /// the plain and the counted evaluator entry points and asserts they agree
    /// on the same value before returning it.
    /// </summary>
    private static Result Evaluate(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        var expr = new Expr.AlgorithmExpr(provenance.Root);

        var plain = Evaluator.Run(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");

        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");

        Assert.True(
            Result.ValueComparer.Equals(plain.Value, counted.Value.Value),
            $"Plain/counted divergence: {plain.Value} vs {counted.Value.Value}");
        return plain.Value;
    }

    private static void AssertResult(string source, Result expected)
    {
        var actual = Evaluate(source);
        Assert.True(
            Result.ValueComparer.Equals(expected, actual),
            $"Expected {expected} but got {actual}{Environment.NewLine}Source:{Environment.NewLine}{source}");
    }

    // ── A. Collecting mean: direct call and dot-call receiver agree ─────────

    [Fact]
    public void Mean_DirectCallCollectsSuppliedSlots()
        => AssertResult(
            """
            Mean(*Vector) = Vector.sum / Vector.count
            Mean(1, 2, 2.718)
            """,
            Atom(1.906m));

    [Fact]
    public void Mean_InlineGroupReceiverSuppliesRowItems()
        => AssertResult(
            """
            Mean(*Vector) = Vector.sum / Vector.count
            (1, 2, 2.718).Mean
            """,
            Atom(1.906m));

    // ── B. Receiver supply boundaries and cardinality (Collect(*items)) ─────

    private const string CollectDef = "Collect(*items) = items\n";

    private const string CollectWithValuesDef = CollectDef + "Values = 1, 2, 3\n";

    [Fact]
    public void InlineGroupReceiver_SuppliesItsRowItems()
        => AssertResult(CollectDef + "(1, 2).Collect", List(Atom(1), Atom(2)));

    [Fact]
    public void NestedGroupReceiver_SuppliesOneInnerSequenceItem()
        // The nested capture emits ONE row — the inner sequence value — so the
        // collector consumes a one-item supply. Never recursive.
        => AssertResult(CollectDef + "((1, 2)).Collect", List(Seq(Atom(1), Atom(2))));

    [Fact]
    public void EmptyGroupReceiver_SuppliesZeroItems()
        => AssertResult(CollectDef + "().Collect", List());

    [Fact]
    public void ExactListReceiver_StaysOneOpaqueItem()
        => AssertResult(CollectDef + "[1, 2].Collect", List(List(Atom(1), Atom(2))));

    [Fact]
    public void FluentSpreadListReceiver_LowersToDirectSpreadCall()
        // `[1, 2]*.Collect` is the fluent chain: it lowers to Collect([1, 2]*)
        // where the spread opens the one list boundary into two slots.
        => AssertResult(CollectDef + "[1, 2]*.Collect", List(Atom(1), Atom(2)));

    [Fact]
    public void MixedGroupReceiver_KeepsNestedSequenceItemOpaque()
        // The supply is consumed one level deep: the group's two rows are the
        // atom 1 and the nested sequence value (2, 3), collected exactly.
        => AssertResult(
            CollectDef + "(1, (2, 3)).Collect",
            List(Atom(1), Seq(Atom(2), Atom(3))));

    [Fact]
    public void SpreadJoinGroupReceiver_SuppliesSpreadItemsAndSlot()
        // The group's row supply is Values's three spread items plus 7.
        => AssertResult(
            CollectWithValuesDef + "(Values*, 7).Collect",
            List(Atom(1), Atom(2), Atom(3), Atom(7)));

    [Fact]
    public void NestedSpreadJoinGroupReceiver_SuppliesOneCapturedItem()
        // The extra parentheses capture the spread-join into ONE sequence
        // value, so the outer group's row supply is that single item.
        => AssertResult(
            CollectWithValuesDef + "((Values*, 7)).Collect",
            List(Seq(Atom(1), Atom(2), Atom(3), Atom(7))));

    [Fact]
    public void CaptureOfSpreadReceiver_SuppliesSpreadItems()
        // `(Values*)` works through the same general rule — a capture whose
        // row supply is the spread items. No callee-shape special case.
        => AssertResult(
            CollectWithValuesDef + "(Values*).Collect",
            List(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void NamedPropertyReceiver_SuppliesOneValueBoundaryItem()
        // A property result boundary is a value boundary: the receiver's
        // supply is ONE item, the sequence value (1, 2, 3). UNCHANGED.
        => AssertResult(
            CollectWithValuesDef + "Values.Collect",
            List(Seq(Atom(1), Atom(2), Atom(3))));

    [Fact]
    public void FluentSpreadNamedReceiver_SuppliesSpreadItems()
        // Fluent chain again: `Values*.Collect` is Collect(Values*).
        => AssertResult(
            CollectWithValuesDef + "Values*.Collect",
            List(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void DirectCall_GroupedArgumentStaysOneCollectedItem()
        // The receiver law changes nothing about direct calls: a written
        // argument slot reifies ONE value, so the grouped argument is one
        // collected item.
        => AssertResult(CollectDef + "Collect((1, 2))", List(Seq(Atom(1), Atom(2))));

    // ── C. Fixed parameters and builtins are unchanged ──────────────────────

    [Fact]
    public void FixedParameterReceiver_BindsTheSegmentValue()
        // The segment is allocated to the fixed parameter, which binds the
        // segment's VALUE — the whole sequence — never its supply items.
        => AssertResult(
            """
            F(x) = [x]
            (1, 2).F
            """,
            List(Seq(Atom(1), Atom(2))));

    [Fact]
    public void BuiltinDotCallReceivers_AreUnchanged()
    {
        AssertResult("(1, 2, 3).count", Atom(3));
        AssertResult("(1, 2, 3).take(2)", List(Atom(1), Atom(2)));
    }

    // ── D. Segment allocation happens before collector consumption ──────────

    [Fact]
    public void CollectingWithSuffix_SuffixAllocatesBeforeReceiverSupplyIsConsumed()
        // Two segments: the receiver and 10. The suffix binds 10 from the
        // back; the collector consumes the receiver's three-item row supply.
        => AssertResult(
            """
            Scale(*values, factor) = values, factor
            (1, 2, 3).Scale(10)
            """,
            Seq(List(Atom(1), Atom(2), Atom(3)), Atom(10)));

    [Fact]
    public void PrefixCollectingSuffix_ReceiverSegmentBindsThePrefixValue()
        // Segments [receiver, 9]: `first` binds the receiver's VALUE (1, 2),
        // `last` binds 9, and the collector gets an empty middle.
        => AssertResult(
            """
            F(first, *middle, last) = [first], middle, [last]
            (1, 2).F(9)
            """,
            Seq(List(Seq(Atom(1), Atom(2))), List(), List(Atom(9))));

    [Fact]
    public void PrefixCollectingSuffix_ReceiverItemCountNeverSatisfiesArity()
    {
        // One segment cannot bind two fixed parameters, even though the
        // receiver's supply holds two items: arity counts segments.
        var arity = SourceProvenance.ParseValid(
            """
            F(first, *middle, last) = [first], middle, [last]
            (1, 2).F
            """).ExpectEvaluationError<EvalError.VariadicArityMismatch>();

        Assert.Equal(2, arity.ExpectedMinimum);
        Assert.Equal(1, arity.Actual);
    }

    [Fact]
    public void CollectingSuffix_LoneReceiverSegmentBindsTheSuffixValue()
        // The only segment is allocated to the fixed suffix, which binds its
        // VALUE; the collector gets nothing.
        => AssertResult(
            """
            F(*middle, last) = middle, [last]
            (1, 2).F
            """,
            Seq(List(), List(Seq(Atom(1), Atom(2)))));

    [Fact]
    public void PrefixCollectingSuffix_ExtraArgumentsAllocateAroundTheCollector()
        // Segments [receiver, 3, 4, 5]: `a` binds the receiver value, `z`
        // binds 5, and the middle segments 3 and 4 are ordinary collected
        // slots (only the RECEIVER segment contributes supply items).
        => AssertResult(
            """
            F(a, *mid, z) = [a], mid, [z]
            (1, 2).F(3, 4, 5)
            """,
            Seq(List(Seq(Atom(1), Atom(2))), List(Atom(3), Atom(4)), List(Atom(5))));

    // ── E. Structured safeguards stay intact ────────────────────────────────

    [Fact]
    public void SequenceValueCollectingPattern_KeepsOneBoundaryDestructuring()
    {
        // The nested pattern `((*values))` is not a flat top-level collector:
        // the receiver segment binds as ONE value and the pattern opens
        // exactly one boundary — direct and dot forms agree.
        AssertResult(
            """
            CountSequenceValue((*values)) = values.count
            CountSequenceValue((1, 2, 3))
            """,
            Atom(3));
        AssertResult(
            """
            CountSequenceValue((*values)) = values.count
            (1, 2, 3).CountSequenceValue
            """,
            Atom(3));
    }

    [Fact]
    public void SequenceValuePattern_DestructuresTheReceiverValue()
        // Patterned callee: the receiver segment binds whole and the pattern
        // destructures it — x = 1, y = [2, 3], z = 4.
        => AssertResult(
            """
            F((x, *y, z)) = [x], y, [z]
            (1, 2, 3, 4).F
            """,
            Seq(List(Atom(1)), List(Atom(2), Atom(3)), List(Atom(4))));

    [Fact]
    public void SingleCollectingMapCallback_KeepsEachElementAsOneCollectedSlot()
    {
        AssertResult(CollectDef + "[7].map(Collect)", List(List(Atom(7))));
        AssertResult(
            CollectDef + "[(1, 2)].map(Collect)",
            List(List(Seq(Atom(1), Atom(2)))));
    }

    [Fact]
    public void DeconstructionCollectingBinding_IsUnchanged()
        => AssertResult(
            """
            x, *y, z = (1, 2, 3, 4)
            x, y, z
            """,
            Seq(Atom(1), List(Atom(2), Atom(3)), Atom(4)));

    [Fact]
    public void CollectingForwarding_RoundTripsThroughExplicitSpread()
        => AssertResult(
            """
            Target(*items) = items
            Forward(*items) = Target(items*)
            Forward(1, 2, 3)
            """,
            List(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void FunctionShapedReceiver_ReportsTheCollectingTypeMismatch()
    {
        var mismatch = SourceProvenance.ParseValid(
            """
            Collect(*items) = items
            F(x) = x
            F.Collect
            """).ExpectEvaluationError<EvalError.TypeMismatch>();

        Assert.Contains("Collecting parameter `*items` collects values", mismatch.Message, StringComparison.Ordinal);
        Assert.Contains("a supplied argument is a function", mismatch.Message, StringComparison.Ordinal);
    }

    // ── F. Scalar, string, and brace-block receivers ────────────────────────

    [Fact]
    public void ScalarReceiver_SuppliesItselfAsOneItem()
        => AssertResult(CollectDef + "7.Collect", List(Atom(7)));

    [Fact]
    public void StringReceiver_SuppliesItselfAsOneItem()
        => AssertResult(CollectDef + "'ab'.Collect", List(Str("ab")));

    [Fact]
    public void BraceBlockReceiver_SuppliesItsRowItems()
        // A zero-parameter brace-block receiver emits its row supply exactly
        // like an inline group.
        => AssertResult(CollectDef + "{1, 2, 3}.Collect", List(Atom(1), Atom(2), Atom(3)));

    // ── G. Counted projection receivers ─────────────────────────────────────

    [Fact]
    public void ProjectionGroupReceiver_SuppliesTheProjectedCountedItems()
    {
        // `S:0` re-emits the projected count, so the receiver's raw counted
        // supply is the two projected items; the direct call's written slot
        // reifies them back into ONE sequence value.
        const string defs = "S = ((1, 2), (3, 4))\nCollect(*items) = items\n";
        AssertResult(defs + "(S:0).Collect", List(Atom(1), Atom(2)));
        AssertResult(defs + "Collect(S:0)", List(Seq(Atom(1), Atom(2))));
    }

    // ── H. Plain expression-spine path parity ───────────────────────────────

    [Fact]
    public void BinaryOperandDotCall_UsesTheSameReceiverSupplyRule()
        // The dot call sits inside a binary operand (the plain iterative
        // expression spine), not on a root output row: the receiver still
        // supplies its three row items, so 1 + 2 = 3.
        => AssertResult(
            """
            Mean(*V) = V.sum / V.count
            1 + (1, 2, 3).Mean
            """,
            Atom(3));

    // ── I. Empty named receiver ─────────────────────────────────────────────

    [Fact]
    public void EmptySequenceNamedReceiver_SuppliesZeroItems()
        // `V = ()` is a value boundary with emitted count 0: the receiver
        // segment's supply is empty, matching `().Collect`.
        => AssertResult(
            """
            Collect(*items) = items
            V = ()
            V.Collect
            """,
            List());
}
