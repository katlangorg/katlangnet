namespace KatLang.Tests;

/// <summary>
/// Focused regression matrix for the extension dot-call receiver rule:
/// DOT-CALL PASSES A VALUE. A dot-call receiver that falls back to a lexical
/// callable (<c>recv.F(extra...)</c> → <c>F(recv, extra...)</c>) is the ordinary
/// FIRST written argument of that call — one reified value, never a supply of
/// its own — so fixed parameters bind it whole and arity counts it as one
/// argument, while a collecting parameter binds it through the collector
/// supply-boundary law exactly as it binds the written argument
/// (<see cref="CollectorSupplyBoundaryTests"/>): a lone sequence-valued receiver
/// opens one level (<c>(1, 2).Coll</c> is <c>[1, 2]</c>, <c>().Coll</c> is
/// <c>[]</c>), a list stays exact (<c>[].Coll</c> is <c>[[]]</c>), and a receiver
/// beside another written argument is collected exactly (<c>(1, 2).Coll(3)</c> is
/// <c>[(1, 2), 3]</c>). The spread marker opens a receiver into final items: the
/// fluent <c>recv*.F(extra...)</c> is exactly <c>F(recv*, extra...)</c>. The receiver's
/// origin — literal, group, brace block, property, call result, conditional,
/// selection — never changes the argument it supplies. Collection builtins in
/// dot form bind the receiver as their ordinary <c>collection</c> argument and
/// then open it through their own post-binding collection view (builtin
/// semantics, not dot-call opening). The metamorphic invariant family lives in
/// <see cref="DotCallValueBoundaryTests"/>; Lean: <c>callLexicalWithReceiverCounted</c>,
/// <c>CoreTests/DotReceiverSegments.lean</c>, the laws
/// <c>dot_receiver_is_ordinary_leading_argument</c> /
/// <c>spread_dot_receiver_is_ordinary_spread_argument</c>.
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

    private const string CollectDef = "Collect(*items) = items\n";

    private const string CollectWithValuesDef = CollectDef + "Values = 1, 2, 3\n";

    // ── A. The expected table: receiver.Coll / receiver*.Coll ───────────────

    [Fact]
    public void EmptySequenceReceiver_OpensToNothingAlone_AndIsOneItemBesideAnother()
    {
        // `()` has value-boundary count 0, but a written argument is one SLOT
        // whose value is `()` — and the dotted spelling is that written argument.
        // As the lone collector's whole segment the empty sequence opens to zero
        // items (like the spread); beside another argument it is one visible item.
        AssertResult(CollectDef + "Collect(())", List());
        AssertResult(CollectDef + "().Collect", List());
        AssertResult(CollectDef + "Collect((), 3)", List(Seq(), Atom(3)));
        AssertResult(CollectDef + "().Collect(3)", List(Seq(), Atom(3)));
        AssertResult(CollectDef + "Collect(()*)", List());
        AssertResult(CollectDef + "()*.Collect", List());
        AssertResult(CollectDef + "Collect(()*, 3)", List(Atom(3)));
    }

    [Fact]
    public void ScalarReceiver_IsOneCollectedItem()
    {
        AssertResult(CollectDef + "Collect(1)", List(Atom(1)));
        AssertResult(CollectDef + "1.Collect", List(Atom(1)));
        AssertResult(CollectDef + "1*.Collect", List(Atom(1)));
        AssertResult(CollectDef + "'ab'.Collect", List(Str("ab")));
    }

    [Fact]
    public void SequenceReceiver_OpensOneLevelAlone_AndIsOneItemBesideAnother()
    {
        AssertResult(CollectDef + "Collect((1, 2))", List(Atom(1), Atom(2)));
        AssertResult(CollectDef + "(1, 2).Collect", List(Atom(1), Atom(2)));
        AssertResult(CollectDef + "Collect((1, 2), 3)", List(Seq(Atom(1), Atom(2)), Atom(3)));
        AssertResult(CollectDef + "(1, 2).Collect(3)", List(Seq(Atom(1), Atom(2)), Atom(3)));
        AssertResult(CollectDef + "Collect((1, 2)*)", List(Atom(1), Atom(2)));
        AssertResult(CollectDef + "(1, 2)*.Collect", List(Atom(1), Atom(2)));
        // A spread-produced sequence value is a FINAL item, even when it is the lone item.
        AssertResult(CollectDef + "Collect([(1, 2)]*)", List(Seq(Atom(1), Atom(2))));
        AssertResult(CollectDef + "[(1, 2)]*.Collect", List(Seq(Atom(1), Atom(2))));
    }

    [Fact]
    public void EmptyListReceiver_IsOneExactListItem_AndSpreadSuppliesNothing()
    {
        AssertResult(CollectDef + "Collect([])", List(List()));
        AssertResult(CollectDef + "[].Collect", List(List()));
        AssertResult(CollectDef + "Collect([]*)", List());
        AssertResult(CollectDef + "[]*.Collect", List());
    }

    [Fact]
    public void ListReceiver_IsOneExactListItem_AndSpreadOpensIt()
    {
        AssertResult(CollectDef + "Collect([1, 2])", List(List(Atom(1), Atom(2))));
        AssertResult(CollectDef + "[1, 2].Collect", List(List(Atom(1), Atom(2))));
        AssertResult(CollectDef + "Collect([1, 2]*)", List(Atom(1), Atom(2)));
        AssertResult(CollectDef + "[1, 2]*.Collect", List(Atom(1), Atom(2)));
    }

    // ── B. Receiver origin never changes the argument ───────────────────────

    [Fact]
    public void GroupReceivers_AreOneValue_NeverTheirRows()
    {
        // A written group is a capture: ONE value, exactly as the direct call's
        // written argument `Collect((1, 2))`, and the lone collector opens that
        // written sequence value exactly one level. Nesting adds nothing:
        // `((1, 2))` is the same one value; `(1, (2, 3))` keeps its nested pair.
        AssertResult(CollectDef + "((1, 2)).Collect", List(Atom(1), Atom(2)));
        AssertResult(CollectDef + "(1, (2, 3)).Collect", List(Atom(1), Seq(Atom(2), Atom(3))));
        AssertResult(CollectWithValuesDef + "(Values*, 7).Collect", List(Atom(1), Atom(2), Atom(3), Atom(7)));
        AssertResult(CollectWithValuesDef + "((Values*, 7)).Collect", List(Atom(1), Atom(2), Atom(3), Atom(7)));
        // The rows themselves are never the receiver: beside a written argument the
        // group is ONE collected value.
        AssertResult(CollectDef + "(1, (2, 3)).Collect(9)", List(Seq(Atom(1), Seq(Atom(2), Atom(3))), Atom(9)));

        // `(Values*)` captures the spread supply as one written value, which the
        // lone collector opens again; the fluent `Values*.Collect` — the call
        // `Collect(Values*)` — supplies the same items as final slots.
        AssertResult(CollectWithValuesDef + "(Values*).Collect", List(Atom(1), Atom(2), Atom(3)));
        AssertResult(CollectWithValuesDef + "Values*.Collect", List(Atom(1), Atom(2), Atom(3)));
        AssertResult(CollectWithValuesDef + "(Values*).Collect(9)", List(Seq(Atom(1), Atom(2), Atom(3)), Atom(9)));
    }

    [Fact]
    public void BraceBlockReceiver_IsOneValue()
    {
        // A zero-parameter brace block is one value — exactly the written
        // argument `Collect({1, 2, 3})` — whose lone sequence opens one level.
        AssertResult(CollectDef + "{1, 2, 3}.Collect", List(Atom(1), Atom(2), Atom(3)));
        AssertResult(CollectDef + "Collect({1, 2, 3})", List(Atom(1), Atom(2), Atom(3)));
        AssertResult(CollectDef + "{1, 2, 3}.Collect(9)", List(Seq(Atom(1), Atom(2), Atom(3)), Atom(9)));
    }

    [Fact]
    public void NamedPropertyReceiver_IsOneValue()
    {
        AssertResult(CollectWithValuesDef + "Values.Collect", List(Atom(1), Atom(2), Atom(3)));
        AssertResult(CollectWithValuesDef + "Collect(Values)", List(Atom(1), Atom(2), Atom(3)));
        AssertResult(CollectWithValuesDef + "Values.Collect(9)", List(Seq(Atom(1), Atom(2), Atom(3)), Atom(9)));

        // `V = ()` has value-boundary count 0, yet it is one written argument
        // whose value is `()` — `V.Collect` is `Collect(V)`, never zero arguments
        // (`One(a) = 1` binds it); the lone `()` opens to nothing at the collector.
        AssertResult(CollectDef + "V = ()\nV.Collect", List());
        AssertResult(CollectDef + "V = ()\nCollect(V)", List());
        AssertResult(CollectDef + "V = ()\nOne(a) = 1\nV.One", Atom(1));
        AssertResult(CollectDef + "V = ()\nV.Collect(9)", List(Seq(), Atom(9)));
        AssertResult(CollectDef + "V = ()\nV*.Collect", List());
    }

    [Fact]
    public void CallConditionalAndSelectionReceivers_AreOneValue()
    {
        const string defs = CollectDef + "Fz(x) = ()\nA = ((1, 2), 3)\nB = ((), 1)\nC = ([1, 2], 3)\n";
        AssertResult(defs + "Fz(1).Collect", List());
        AssertResult(defs + "Collect(Fz(1))", List());
        AssertResult(defs + "Fz(1).Collect(9)", List(Seq(), Atom(9)));
        AssertResult(defs + "if(true, (), 1).Collect", List());
        AssertResult(defs + "Collect(if(true, (), 1))", List());
        AssertResult(defs + "if(true, (), 1).Collect(9)", List(Seq(), Atom(9)));
        AssertResult(defs + "Fz(1)*.Collect", List());

        AssertResult(defs + "A:0.Collect", List(Atom(1), Atom(2)));
        AssertResult(defs + "first(A).Collect", List(Atom(1), Atom(2)));
        AssertResult(defs + "A:0.Collect(9)", List(Seq(Atom(1), Atom(2)), Atom(9)));
        AssertResult(defs + "(A:0)*.Collect", List(Atom(1), Atom(2)));
        AssertResult(defs + "(first(A))*.Collect", List(Atom(1), Atom(2)));
        AssertResult(defs + "B:0.Collect", List());
        AssertResult(defs + "first(B).Collect", List());
        AssertResult(defs + "B:0.Collect(9)", List(Seq(), Atom(9)));
        AssertResult(defs + "(B:0)*.Collect", List());
        AssertResult(defs + "C:0.Collect", List(List(Atom(1), Atom(2))));
        AssertResult(defs + "first(C).Collect", List(List(Atom(1), Atom(2))));
        AssertResult(defs + "(C:0)*.Collect", List(Atom(1), Atom(2)));
    }

    // ── C. Fixed parameters, allocation, and callee shapes ──────────────────

    [Fact]
    public void FixedParameterReceiver_BindsTheWholeValue()
        => AssertResult(
            """
            F(x) = [x]
            (1, 2).F
            """,
            List(Seq(Atom(1), Atom(2))));

    [Fact]
    public void CollectingWithSuffix_ReceiverOpensAfterSuffixAllocation()
    {
        // Two arguments: the receiver and 10. The suffix binds 10 from the
        // back FIRST; the segment left to the collector is the receiver's one
        // written sequence value, which opens one level — exactly as
        // `Scale((1, 2, 3), 10)` does. A list receiver stays one item, and
        // a second written argument makes the receiver one collected item.
        AssertResult(
            """
            Scale(*values, factor) = values, factor
            (1, 2, 3).Scale(10)
            """,
            Seq(List(Atom(1), Atom(2), Atom(3)), Atom(10)));
        AssertResult(
            """
            Scale(*values, factor) = values, factor
            [1, 2, 3].Scale(10)
            """,
            Seq(List(List(Atom(1), Atom(2), Atom(3))), Atom(10)));
        AssertResult(
            """
            Scale(*values, factor) = values, factor
            (1, 2, 3).Scale(4, 10)
            """,
            Seq(List(Seq(Atom(1), Atom(2), Atom(3)), Atom(4)), Atom(10)));
    }

    [Fact]
    public void PrefixCollectingSuffix_ReceiverBindsThePrefixValue()
        => AssertResult(
            """
            F(first, *middle, last) = [first], middle, [last]
            (1, 2).F(9)
            """,
            Seq(List(Seq(Atom(1), Atom(2))), List(), List(Atom(9))));

    [Fact]
    public void PrefixCollectingSuffix_ReceiverIsOneArgumentForArity()
    {
        // One argument cannot bind two fixed parameters, even though the
        // receiver holds two items: arity counts arguments, and the receiver
        // is one — exactly as in `F((1, 2))`.
        var arity = SourceProvenance.ParseValid(
            """
            F(first, *middle, last) = [first], middle, [last]
            (1, 2).F
            """).ExpectEvaluationError<EvalError.VariadicArityMismatch>();

        Assert.Equal(2, arity.ExpectedMinimum);
        Assert.Equal(1, arity.Actual);
    }

    [Fact]
    public void CollectingSuffix_LoneReceiverBindsTheSuffixValue()
        => AssertResult(
            """
            F(*middle, last) = middle, [last]
            (1, 2).F
            """,
            Seq(List(), List(Seq(Atom(1), Atom(2)))));

    [Fact]
    public void PrefixCollectingSuffix_ExtraArgumentsAllocateAroundTheCollector()
        => AssertResult(
            """
            F(a, *mid, z) = [a], mid, [z]
            (1, 2).F(3, 4, 5)
            """,
            Seq(List(Seq(Atom(1), Atom(2))), List(Atom(3), Atom(4)), List(Atom(5))));

    [Fact]
    public void SequenceValueCollectingPattern_DestructuresTheReceiverValue()
    {
        AssertResult(
            """
            CountSequenceValue((*values)) = values.count
            (1, 2, 3).CountSequenceValue
            """,
            Atom(3));
        AssertResult(
            """
            F((x, *y, z)) = [x], y, [z]
            (1, 2, 3, 4).F
            """,
            Seq(List(Atom(1)), List(Atom(2), Atom(3)), List(Atom(4))));
    }

    [Fact]
    public void PatternedBraceBlockReceiver_IsOneValue()
    {
        // Repeating the fixed suffix name selects patterned binding; the
        // receiver is still one written argument, so the top-level collector
        // applies the same collector law: the lone block sequence opens one
        // level, a list stays one item, and a second middle slot keeps the
        // block as one collected item.
        AssertResult(
            """
            CollectChecked(*items, marker, marker) = items
            {1, 2, 3}.CollectChecked(9, 9)
            """,
            List(Atom(1), Atom(2), Atom(3)));
        AssertResult(
            """
            CollectChecked(*items, marker, marker) = items
            [1, 2, 3].CollectChecked(9, 9)
            """,
            List(List(Atom(1), Atom(2), Atom(3))));
        AssertResult(
            """
            CollectChecked(*items, marker, marker) = items
            {1, 2, 3}.CollectChecked(4, 9, 9)
            """,
            List(Seq(Atom(1), Atom(2), Atom(3)), Atom(4)));
    }

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
        Assert.Contains("a supplied argument is a callable", mismatch.Message, StringComparison.Ordinal);
    }

    // ── D. Builtins, callbacks, and unrelated binders stay as they are ──────

    [Fact]
    public void BuiltinDotCallReceivers_BindAsTheCollectionArgument()
    {
        // The receiver is the builtin's ordinary `collection` argument; the
        // builtin's own post-binding view opens it (builtin semantics, not
        // dot-call opening).
        AssertResult("(1, 2, 3).count", Atom(3));
        AssertResult("(1, 2, 3).take(2)", List(Atom(1), Atom(2)));
        AssertResult("V = ()\nV.count", Atom(0));
        AssertResult("().count", Atom(0));
        AssertResult("[].count", Atom(0));
    }

    [Fact]
    public void SingleCollectingMapCallback_BindsEachElementByTheCollectorLaw()
    {
        // A whole callback item is ONE written slot of the callback call: a scalar or
        // a list element is one collected item, a sequence element opens one level.
        AssertResult(CollectDef + "[7].map(Collect)", List(List(Atom(7))));
        AssertResult(
            CollectDef + "[(1, 2)].map(Collect)",
            List(List(Atom(1), Atom(2))));
        AssertResult(
            CollectDef + "[[1, 2]].map(Collect)",
            List(List(List(Atom(1), Atom(2)))));
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

    // ── E. Plain expression-spine path parity ───────────────────────────────

    [Fact]
    public void BinaryOperandDotCall_UsesTheSameReceiverRule()
        // The dot call sits inside a binary operand (the plain iterative
        // expression spine), not on a root output row: the receiver is still
        // one value, so the mean of the ONE collected item (the sequence value,
        // opened by `sum`/`count` of the collected list) needs the spread form.
        => AssertResult(
            """
            Mean(*V) = V.sum / V.count
            1 + (1, 2, 3)*.Mean
            """,
            Atom(3));
}
