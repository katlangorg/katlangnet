using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Focused coverage for the collecting-binding model: every collecting binding —
/// deconstruction collecting bindings, single variadic parameters, and mixed
/// prefix/collecting/suffix parameter lists — COLLECTS the item slots assigned to it
/// into ONE exact immutable list (<c>CollectSegment</c>; Lean <c>collectSegment</c>).
/// The three item-supply operations stay distinct: <c>capture</c> (ordinary
/// canonicalizing value capture), <c>collect</c> (collecting binding), and
/// <c>open</c> (the named spread intrinsic), with the round trip
/// <c>spread(collect(xs)) = xs</c> making variadic forwarding ordinary spread.
/// Lean twins: the "Collecting bindings collect exact immutable lists" section of
/// <c>lean/CoreTests.lean</c> and the collect laws in
/// <c>lean/KatLangArityLaws.lean</c>.
/// </summary>
public class CollectingBindingTests
{
    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result.ListValue List(params Result[] items) => new(items);

    private static Result.SequenceValue Seq(params Result[] items) => new(items);

    private static void AssertSemanticallyEqual(Result expected, Result actual)
        => Assert.True(
            Result.ValueComparer.Equals(expected, actual),
            $"Expected {expected} but got {actual}");

    /// <summary>
    /// Run one source through the public engine and both evaluator entry
    /// points with the optimizers on and off; assert every mode agrees on the
    /// same single result value, then return it. This is the parity matrix the
    /// collecting-binding change must hold across: ordinary evaluation, counted
    /// evaluation, optimizer enabled, and optimizer disabled.
    /// </summary>
    private static Result EvaluateAllModes(string source)
    {
        var ast = Parser.Parse(source).Root;
        var expr = new Expr.Block(ast);

        var plainOptimized = Evaluator.Run(
            expr, new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true, loopDiagnostics: null,
            enableSequencePipelineOptimization: true, sequenceDiagnostics: null);
        var plainGeneric = Evaluator.Run(
            expr, new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: false, loopDiagnostics: null,
            enableSequencePipelineOptimization: false, sequenceDiagnostics: null);
        var counted = Evaluator.RunCounted(expr);
        var engineRun = KatLangEngine.Run(source);

        Assert.True(plainOptimized.IsOk, $"optimizer-on evaluation failed: {(plainOptimized.IsError ? plainOptimized.Error.ToString() : "")}");
        Assert.True(plainGeneric.IsOk, $"optimizer-off evaluation failed: {(plainGeneric.IsError ? plainGeneric.Error.ToString() : "")}");
        Assert.True(counted.IsOk, $"counted evaluation failed: {(counted.IsError ? counted.Error.ToString() : "")}");
        var success = Assert.IsType<RunResult.Success>(engineRun);

        AssertSemanticallyEqual(plainOptimized.Value, plainGeneric.Value);
        AssertSemanticallyEqual(plainOptimized.Value, counted.Value.Value);
        AssertSemanticallyEqual(plainOptimized.Value, success.Value);
        return plainOptimized.Value;
    }

    private static void AssertCollects(string source, Result expected)
        => AssertSemanticallyEqual(expected, EvaluateAllModes(source));

    // ── Deconstruction collecting binding: empty, singleton, multiple ─────────────────────

    [Theory]
    [InlineData("head, rest... = [1]\nrest", "[]")]
    [InlineData("head, rest... = [1, 2]\nrest", "[2]")]
    [InlineData("head, rest... = [1, 2, 3]\nrest", "[2, 3]")]
    [InlineData("rest..., last = [1, 2, 3]\nrest", "[1, 2]")]
    [InlineData("first, middle..., last = [1, 2, 3, 4]\nmiddle", "[2, 3]")]
    [InlineData("first, middle..., last = [1, 2]\nmiddle", "[]")]
    [InlineData("first, middle..., last = [1, 2, 3, 4, 5]\nmiddle", "[2, 3, 4]")]
    [InlineData("first, rest... = 1\nrest", "[]")]
    public void DeconstructionCollectingBinding_CollectsExactList(string source, string expectedDisplay)
    {
        var value = EvaluateAllModes(source);
        Assert.IsType<Result.ListValue>(value);
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(expectedDisplay, run.ToDisplayString());
    }

    // ── Structured singleton items are preserved exactly ────────────────────

    [Fact]
    public void DeconstructionCollectingBinding_PreservesStructuredSingletonRow()
    {
        AssertCollects(
            "Rows = [[1, 2], [3, 4]]\nfirst, rest... = Rows\nrest",
            List(List(Atom(3), Atom(4))));
        AssertCollects(
            "Rows = [[1, 2], [3, 4]]\nfirst, rest... = Rows\nrest.count",
            Atom(1));
    }

    [Fact]
    public void DeconstructionCollectingBinding_SingletonStructurePreservesExactKind()
    {
        AssertCollects("first, rest... = 1, [2, 3]\nrest", List(List(Atom(2), Atom(3))));
        AssertCollects("first, rest... = 1, (2, 3)\nrest", List(Seq(Atom(2), Atom(3))));
        AssertCollects("first, rest... = 1, []\nrest", List(List()));
        AssertCollects("first, rest... = 1, ()\nrest", List(Seq()));
    }

    [Fact]
    public void DeconstructionCollectingBinding_EmptySegmentStaysDistinctFromEmptyStructureElement()
    {
        AssertCollects("first, rest... = 1, []\nrest == []", Atom(0));
        AssertCollects("first, rest... = 1, ()\nrest == []", Atom(0));
        AssertCollects("first, rest... = 1\nrest == []", Atom(1));
    }

    // ── Deconstruction implicit opening matches explicit spread ─────────────

    [Fact]
    public void DeconstructionCollectingBinding_ImplicitOpeningMatchesSpread()
    {
        AssertCollects("first, rest... = [1, 2, 3]\nrest", List(Atom(2), Atom(3)));
        AssertCollects("first, rest... = [1, 2, 3].spread\nrest", List(Atom(2), Atom(3)));
    }

    [Fact]
    public void DeconstructionSpread_CaptureBoundaryCanOpenSingletonStructuredElementFurther()
    {
        // A written RHS spread is captured into the parser-elaborated shared
        // value before the deconstruction receiver opens it. Bare [(1, 2)]
        // therefore supplies one row and cannot bind two fixed targets, while
        // spreading it lets singleton capture return the row; deconstruction
        // then opens that row into the two target slots.
        Assert.IsType<RunResult.EvalFailure>(
            KatLangEngine.Run("x, y = [(1, 2)]\nx, y"));
        AssertCollects(
            "x, y = [(1, 2)].spread\nx, y",
            Seq(Atom(1), Atom(2)));
    }

    // ── Provenance independence ─────────────────────────────────────────────

    [Fact]
    public void DeconstructionCollectingBinding_CollectsAssembledSupplyRegardlessOfSpreadSources()
    {
        AssertCollects(
            "first, rest... = 1, [2, 3].spread, (4, 5).spread\nfirst",
            Atom(1));
        AssertCollects(
            "first, rest... = 1, [2, 3].spread, (4, 5).spread\nrest",
            List(Atom(2), Atom(3), Atom(4), Atom(5)));
    }

    // ── Variadic capture matrix ─────────────────────────────────────────────

    [Fact]
    public void VariadicCapture_CollectsExactList()
    {
        const string inspect = "Inspect(items...) = items\n";
        AssertCollects(inspect + "Inspect()", List());
        AssertCollects(inspect + "Inspect(7)", List(Atom(7)));
        AssertCollects(inspect + "Inspect(1, 2, 3)", List(Atom(1), Atom(2), Atom(3)));
        AssertCollects(inspect + "Inspect([1, 2])", List(List(Atom(1), Atom(2))));
        AssertCollects(inspect + "Inspect([1, 2].spread)", List(Atom(1), Atom(2)));
        AssertCollects(inspect + "Inspect((1, 2))", List(Seq(Atom(1), Atom(2))));
        AssertCollects(inspect + "Inspect((1, 2).spread)", List(Atom(1), Atom(2)));
    }

    [Theory]
    [InlineData("CountArgs()", 0)]
    [InlineData("CountArgs(7)", 1)]
    [InlineData("CountArgs(1, 2)", 2)]
    [InlineData("CountArgs([10, 20])", 1)]
    [InlineData("CountArgs([10, 20].spread)", 2)]
    [InlineData("CountArgs((10, 20))", 1)]
    [InlineData("CountArgs((10, 20).spread)", 2)]
    public void VariadicCounting_ObservesSuppliedSlots(string call, decimal expected)
        => AssertCollects("CountArgs(items...) = items.count\n" + call, Atom(expected));

    // ── Empty-structure arguments: unspread stays a visible slot, spread vanishes ─

    [Fact]
    public void VariadicCapture_EmptyStructureArgumentsAreVisibleSlotsUntilSpread()
    {
        const string inspect = "Inspect(items...) = items\n";
        AssertCollects(inspect + "Inspect(())", List(Seq()));
        AssertCollects(inspect + "Inspect(().spread)", List());
        AssertCollects(inspect + "Inspect([])", List(List()));
        AssertCollects(inspect + "Inspect([].spread)", List());
    }

    // ── Mixed parameter patterns ────────────────────────────────────────────

    [Fact]
    public void MixedPatterns_CollectingBindingCollectsMiddleSupply()
    {
        AssertCollects("F(first, middle..., last) = middle\nF(1, 2, 3, 4)", List(Atom(2), Atom(3)));
        AssertCollects("F(first, middle..., last) = middle\nF(1, 2)", List());
        AssertCollects("F(prefix..., last) = prefix\nF(1, 2, 3)", List(Atom(1), Atom(2)));
        AssertCollects("F(first, suffix...) = suffix\nF(1, [2, 3])", List(List(Atom(2), Atom(3))));
    }

    [Fact]
    public void MixedPatterns_GroupedMiddleStaysOneCollectedSlotUntilSpread()
    {
        // Direct user call: the grouped middle argument is ONE collected slot
        // preserving its boundary; explicit spread supplies the operand's items.
        AssertCollects(
            "Middle(first, middle..., last) = middle\nMiddle(10, (20, 30), 40)",
            List(Seq(Atom(20), Atom(30))));
        AssertCollects(
            "Middle(first, middle..., last) = middle\nMiddle(10, (20, 30).spread, 40)",
            List(Atom(20), Atom(30)));
        AssertCollects(
            "Middle(first, middle..., last) = middle\nMiddle(10, [20, 30], 40)",
            List(List(Atom(20), Atom(30))));
        AssertCollects(
            "Middle(first, middle..., last) = middle\nMiddle(10, [20, 30].spread, 40)",
            List(Atom(20), Atom(30)));
    }

    // ── Forwarding ──────────────────────────────────────────────────────────

    [Fact]
    public void VariadicForwarding_SpreadRoundTripsCollectedItems()
    {
        const string defs = "Target(items...) = items\nForward(items...) = Target(items.spread)\n";
        AssertCollects(defs + "Forward()", List());
        AssertCollects(defs + "Forward(7)", List(Atom(7)));
        AssertCollects(defs + "Forward(1, 2)", List(Atom(1), Atom(2)));
        AssertCollects(defs + "Forward([1, 2])", List(List(Atom(1), Atom(2))));
        AssertCollects(defs + "Forward([1, 2].spread)", List(Atom(1), Atom(2)));
        AssertCollects(defs + "Forward((1, 2))", List(Seq(Atom(1), Atom(2))));
        AssertCollects(defs + "Forward((1, 2).spread)", List(Atom(1), Atom(2)));
    }

    [Fact]
    public void VariadicForwarding_UnspreadCollectedListIsOneArgument()
    {
        AssertCollects(
            "TargetOne(item) = item\nForwardAsOne(items...) = TargetOne(items)\nForwardAsOne(1, 2)",
            List(Atom(1), Atom(2)));
    }

    // ── Implicit forwarding: spread decided by the SOURCE binding kind ──────
    // The implicit-argument resolver re-spreads a forwarded value only when the
    // caller-side binding is itself a collecting binding's exact list. An ordinary source
    // parameter always forwards as ONE argument, even into a variadic
    // destination.

    [Fact]
    public void ImplicitForwarding_OrdinarySourceParameterIsOneArgument()
    {
        const string defs = "Target(items...) = items\nUse(items) = Target\n";
        AssertCollects(defs + "Use([1, 2])", List(List(Atom(1), Atom(2))));
        AssertCollects(defs + "Use((1, 2))", List(Seq(Atom(1), Atom(2))));
        AssertCollects(defs + "Use(7)", List(Atom(7)));
    }

    [Fact]
    public void ImplicitForwarding_OrdinarySourceAgreesWithExplicitForm()
    {
        const string implicitForm = "Target(items...) = items\nUse(items) = Target\n";
        const string explicitForm = "Target(items...) = items\nUse(items) = Target(items)\n";
        foreach (var call in new[] { "Use([1, 2])", "Use((1, 2))", "Use(7)" })
        {
            AssertSemanticallyEqual(
                EvaluateAllModes(explicitForm + call),
                EvaluateAllModes(implicitForm + call));
        }
    }

    [Fact]
    public void ImplicitForwarding_VariadicSourceSpreadsAndAgreesWithExplicitForm()
    {
        const string implicitForm = "Target(items...) = items\nUse(items...) = Target\n";
        const string explicitForm = "Target(items...) = items\nUse(items...) = Target(items.spread)\n";

        AssertCollects(implicitForm + "Use()", List());
        AssertCollects(implicitForm + "Use(7)", List(Atom(7)));
        AssertCollects(implicitForm + "Use(1, 2)", List(Atom(1), Atom(2)));
        AssertCollects(implicitForm + "Use([1, 2])", List(List(Atom(1), Atom(2))));

        foreach (var call in new[] { "Use()", "Use(7)", "Use(1, 2)", "Use([1, 2])" })
        {
            AssertSemanticallyEqual(
                EvaluateAllModes(explicitForm + call),
                EvaluateAllModes(implicitForm + call));
        }
    }

    [Fact]
    public void ImplicitForwarding_LiftedVariadicForwardsAsSpread()
    {
        // With no explicit caller parameters, the callee's variadic parameter is lifted as a
        // caller variadic parameter, so the lifted source legitimately forwards as spread.
        const string defs = "Target(items...) = items\nUse = Target\n";
        AssertCollects(defs + "Use(1, 2, 3)", List(Atom(1), Atom(2), Atom(3)));
        AssertCollects(defs + "Use([1, 2])", List(List(Atom(1), Atom(2))));
    }

    [Fact]
    public void ImplicitForwarding_MixedSignatureSpreadsOnlyTheVariadicSource()
    {
        AssertCollects(
            "Target(first, middle..., last) = middle\n"
            + "Use(first, middle..., last) = Target\n"
            + "Use(1, 2, 3, 4)",
            List(Atom(2), Atom(3)));
    }

    [Fact]
    public void ImplicitForwarding_NestedFixedNameMatchingVariadicDestinationStaysOneValue()
    {
        // Caller `a` is a nested FIXED pattern name; destination `a...` is a
        // rest. The list-valued source must remain one argument.
        AssertCollects(
            "Target(a...) = a\nUse((a, b)) = Target\nUse(([1, 2], 5))",
            List(List(Atom(1), Atom(2))));
    }

    [Fact]
    public void ImplicitForwarding_NestedVariadicSourceForwardsItsCollectedItems()
    {
        AssertCollects(
            "Target(r...) = r\nUse((first, r...)) = Target\nUse((1, 2, 3))",
            List(Atom(2), Atom(3)));
    }

    [Fact]
    public void ImplicitForwarding_CrossedNamesFollowEachSourceKind()
    {
        // Caller: a is fixed, b is variadic. Callee: b is fixed, a is variadic.
        // The fixed destination b receives the caller's collected list as one
        // value; the variadic destination a receives the ordinary source a as one
        // collected slot (never spread).
        AssertCollects(
            "T2(b, a...) = (b, a)\nUse(a, b...) = T2\nUse([5, 6], 2, 3)",
            Seq(List(Atom(2), Atom(3)), List(List(Atom(5), Atom(6)))));
    }

    [Fact]
    public void ImplicitForwarding_VariadicSourceIntoFixedDestinationIsOneListArgument()
    {
        AssertCollects(
            "TargetOne(items) = items\nUse(items...) = TargetOne\nUse(1, 2)",
            List(Atom(1), Atom(2)));
    }

    [Fact]
    public void ImplicitForwarding_SharedLiftedNameUsesOneSourceKindAcrossDependencies()
    {
        // The first dependency establishes the single lifted `items` binding.
        // Every later dependency forwards from that source kind; destination
        // kinds never overwrite it or make dictionary order observable.
        AssertCollects(
            "Fixed(items) = items\nVariadic(items...) = items\nUse = Fixed, Variadic\nUse([1, 2])",
            Seq(List(Atom(1), Atom(2)), List(List(Atom(1), Atom(2)))));
        AssertCollects(
            "Variadic(items...) = items\nFixed(items) = items\nUse = Variadic, Fixed\nUse([1, 2])",
            Seq(
                List(List(Atom(1), Atom(2))),
                List(List(Atom(1), Atom(2)))));
    }

    // ── Callback collecting binding: flat callees route through the shared binder ─
    // map/filter/reduce callbacks with a top-level variadic parameter collect
    // exactly like ordinary calls: a single-variadic callee keeps the iterated
    // element as ONE collected slot, and a multi-parameter flat callee opens
    // the lone element into row slots first (the established flat-callback
    // row convention) before prefix/collecting/suffix allocation.

    [Fact]
    public void SingleVariadicMapCallback_CollectsOneElementSlot()
    {
        const string defs = "Collect(items...) = items\n";
        AssertCollects(defs + "[7].map(Collect)", List(List(Atom(7))));
        AssertCollects(defs + "[7, 8].map(Collect)", List(List(Atom(7)), List(Atom(8))));
        AssertCollects(defs + "map((7, 8), Collect)", List(List(Atom(7)), List(Atom(8))));
    }

    [Fact]
    public void SingleVariadicMapCallback_PreservesElementKindExactly()
    {
        const string defs = "Collect(items...) = items\n";
        AssertCollects(defs + "[[1, 2]].map(Collect)", List(List(List(Atom(1), Atom(2)))));
        AssertCollects(defs + "[(1, 2)].map(Collect)", List(List(Seq(Atom(1), Atom(2)))));
        AssertCollects(defs + "[[]].map(Collect)", List(List(List())));
        AssertCollects(defs + "[()].map(Collect)", List(List(Seq())));
    }

    [Fact]
    public void MixedVariadicMapCallback_OpensRowSlotsThenCollects()
    {
        AssertCollects(
            "F(first, middle..., last) = middle\nRows = [(1, 2, 3, 4)]\nRows.map(F)",
            List(List(Atom(2), Atom(3))));
        AssertCollects(
            "F((first, middle..., last)) = middle\nRows = [(1, 2, 3, 4)]\nRows.map(F)",
            List(List(Atom(2), Atom(3))));
        AssertCollects(
            "F(first, rest...) = rest\n[(1, 2, 3)].map(F)",
            List(List(Atom(2), Atom(3))));
        AssertCollects(
            "F(first, rest...) = rest\n[7].map(F)",
            List(List()));
        AssertCollects(
            "F(init..., last) = init\n[(1, 2, 3)].map(F)",
            List(List(Atom(1), Atom(2))));
    }

    [Fact]
    public void SingleVariadicFilterCallback_ObservesCollectedListKind()
    {
        // `items == [7]` distinguishes the collected list [7] from scalar 7;
        // a `.count == 1` style predicate could not.
        AssertCollects(
            "IsSingleSeven(items...) = items == [7]\n[7, 8].filter(IsSingleSeven)",
            List(Atom(7)));
        AssertCollects(
            "P(items...) = items == [[7]]\n[[7], [8]].filter(P)",
            List(List(Atom(7))));
    }

    [Fact]
    public void ReducerElementSideVariadic_CollectsProjectedElement()
    {
        // The variadic parameter sits BEFORE the accumulator boundary: each step observes
        // items = [element], never the bare scalar element.
        AssertCollects(
            "R(items..., acc) = items == [10]\nreduce([10], R, 99)",
            Atom(1));
        AssertCollects(
            "R(items..., acc) = (acc.spread, items)\nreduce((10, 20), R, ())",
            Seq(Atom(10), List(Atom(20))));
    }

    [Fact]
    public void SingleVariadicReducer_CollectsElementAndAccumulatorSlotsExactly()
    {
        const string reducer = "R(items...) = items\n";
        AssertCollects(reducer + "reduce([10], R, 99)", List(Atom(10), Atom(99)));
        AssertCollects(
            reducer + "reduce([[1, 2]], R, [])",
            List(List(Atom(1), Atom(2)), List()));
        AssertCollects(
            reducer + "reduce([(1, 2)], R, ())",
            List(Seq(Atom(1), Atom(2)), Seq()));
        AssertCollects(reducer + "reduce([()], R, [])", List(Seq(), List()));
        AssertCollects(reducer + "reduce([[]], R, ())", List(List(), Seq()));
    }

    [Fact]
    public void ReducerAccumulatorSideVariadic_KeepsSharedPatternBinding()
    {
        AssertCollects(
            "Append(item, history...) = (history.spread, item)\nreduce((2, 3, 4), Append, 1)",
            Seq(Atom(1), Atom(2), Atom(3), Atom(4)));
        AssertCollects(
            "R(el, acc, extra...) = (acc, el, extra)\nreduce((5), R, 0)",
            Seq(Atom(0), Atom(5), List()));
    }

    [Fact]
    public void FixedFlatCallbacks_KeepExistingRowBehavior()
    {
        AssertCollects(
            "Add(x, y) = x + y\n((1, 2), (3, 4)).map(Add)",
            List(Atom(3), Atom(7)));
        AssertCollects(
            "Add(x, y) = x + y\n[(1, 2), (3, 4)].map(Add)",
            List(Atom(3), Atom(7)));
    }

    // ── Receiver distinction ────────────────────────────────────────────────

    [Fact]
    public void CallReceiver_PreservesArgumentBoundaries()
    {
        const string defs = "Inspect(items...) = items\nA = [1, 2, 3]\nB = (1, 2, 3)\n";
        AssertCollects(defs + "Inspect(A)", List(List(Atom(1), Atom(2), Atom(3))));
        AssertCollects(defs + "Inspect(A.spread)", List(Atom(1), Atom(2), Atom(3)));
        AssertCollects(defs + "Inspect(B)", List(Seq(Atom(1), Atom(2), Atom(3))));
        AssertCollects(defs + "Inspect(B.spread)", List(Atom(1), Atom(2), Atom(3)));
    }

    [Fact]
    public void DottedReceiver_IsOneCollectedSlot()
    {
        AssertCollects(
            "Inspect(items...) = items\nA = [1, 2]\nA.Inspect",
            List(List(Atom(1), Atom(2))));
    }

    [Fact]
    public void LoopStep_GroupedMiddleRemainsOneCollectedSequenceSlot()
    {
        const string source =
            "Step(first, middle..., last) = middle\nStep.repeat(1, 10, (20, 30), 40)";
        AssertCollects(source, List(Seq(Atom(20), Atom(30))));
        AssertCollects(
            "Step(first, middle..., last) = middle.count\nStep.repeat(1, 10, (20, 30), 40)",
            Atom(1));
    }

    [Fact]
    public void WhileLoopStep_VariadicCollectsExactList_EmptySingletonAndMulti()
    {
        // While twin of LoopStep_GroupedMiddleRemainsOneCollectedSequenceSlot:
        // the while state-binding path collects its middle segment through the same
        // exact-list collector as repeat, deconstruction, and calls. The
        // `middle == [...]` comparison pins the collected KIND (an exact
        // immutable list), not just the flattened atoms.
        AssertCollects(
            "Step(n, middle..., last) = n + 10, (middle == [(20, 30)]), last, n < 2\nStep.while(1, (20, 30), 40)",
            Seq(Atom(11), Atom(1), Atom(40)));

        // Empty collected segment: `[]`, never `()` and never an arity error.
        AssertCollects(
            "Step(n, middle..., last) = n + 10, (middle == []), last, n < 2\nStep.while(1, 40)",
            Seq(Atom(11), Atom(1), Atom(40)));

        // Multi-item collected segment.
        AssertCollects(
            "Step(n, middle..., last) = n + 10, (middle == [7, 8]), last, n < 2\nStep.while(1, 7, 8, 40)",
            Seq(Atom(11), Atom(1), Atom(40)));
    }

    // ── Equality ────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("Inspect() == []", 1)]
    [InlineData("Inspect(7) == [7]", 1)]
    [InlineData("Inspect(1, 2) == [1, 2]", 1)]
    [InlineData("Inspect([1, 2]) == [[1, 2]]", 1)]
    [InlineData("Inspect([1, 2]) == [1, 2]", 0)]
    [InlineData("Inspect(1, 2) == (1, 2)", 0)]
    public void CollectedSegment_EqualityIsKindExact(string comparison, decimal expected)
        => AssertCollects("Inspect(items...) = items\n" + comparison, Atom(expected));

    // ── Collection composition ──────────────────────────────────────────────

    [Fact]
    public void CollectedSegment_ComposesWithCollectionBuiltins()
    {
        const string tail = "Tail(source) = {\n    first, rest... = source\n    rest\n}\n";
        AssertCollects(tail + "Tail([[1, 2], [3, 4]])", List(List(Atom(3), Atom(4))));
        AssertCollects(tail + "Tail([[1, 2], [3, 4]]).count", Atom(1));
        AssertCollects("skip([[1, 2], [3, 4]], 1)", List(List(Atom(3), Atom(4))));
        AssertCollects(
            "first, rest... = [1, 2, 3]\nrest == skip([1, 2, 3], 1)",
            Atom(1));
    }

    // ── Ordinary capture stays canonical (capture vs collect) ───────────────

    [Fact]
    public void OrdinaryCapture_StaysCanonicalSequence()
    {
        AssertCollects("x = 1, 2, 3\nx", Seq(Atom(1), Atom(2), Atom(3)));
        AssertCollects("x = [1, 2, 3]\nx", List(Atom(1), Atom(2), Atom(3)));
        AssertCollects("x = [1, 2, 3].spread\nx", Seq(Atom(1), Atom(2), Atom(3)));
    }

    // ── Immutability of collected lists ─────────────────────────────────

    /// <summary>
    /// Attempt every plausible host-side mutation path through a public item
    /// view; a mutable cast may legitimately be unavailable, but when a cast
    /// succeeds every mutation member must throw without changing the value.
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

    public static TheoryData<string, string> ImmutableCollectedResults => new()
    {
        // source producing a collected list                             expected display
        { "Inspect(items...) = items\nInspect()", "[]" },
        { "Inspect(items...) = items\nInspect(7)", "[7]" },
        { "Inspect(items...) = items\nInspect([1, 2])", "[[1, 2]]" },
        { "Inspect(items...) = items\nInspect((1, 2))", "[(1, 2)]" },
        { "first, rest... = [1, 2, 3]\nrest", "[2, 3]" },
        // forwarding path: the re-collected list must be just as protected
        { "Target(items...) = items\nForward(items...) = Target(items.spread)\nForward([1, 2])", "[[1, 2]]" },
    };

    [Theory]
    [MemberData(nameof(ImmutableCollectedResults))]
    public void CollectedList_IsObservablyImmutable(string source, string expectedDisplay)
    {
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        var value = Assert.IsType<Result.ListValue>(run.Value);
        var hashBefore = Result.ValueComparer.GetHashCode(value);
        var snapshot = new Result.ListValue(value.Items);

        Assert.Equal(expectedDisplay, run.ToDisplayString());

        // Public view, interface downcasts, and nested aliases reject mutation.
        ProbeViewForMutation(value.Items);
        ProbeViewForMutation(value.SpreadItems());
        var structureItems = value.StructureItems();
        Assert.NotNull(structureItems);
        ProbeViewForMutation(structureItems!);
        foreach (var element in value.Items)
        {
            if (element is Result.ListValue nested)
                ProbeViewForMutation(nested.Items);
            if (element is Result.SequenceValue nestedSeq)
                ProbeViewForMutation(nestedSeq.Items);
        }

        // Display, count, element identity, indexing, equality, and semantic
        // hash are stable after every probe.
        Assert.Equal(expectedDisplay, run.ToDisplayString());
        Assert.Equal(snapshot.Items.Count, value.Items.Count);
        for (var i = 0; i < snapshot.Items.Count; i++)
        {
            AssertSemanticallyEqual(snapshot.Items[i], value.Items[i]);
            Assert.NotNull(value.Index(i));
        }

        AssertSemanticallyEqual(snapshot, value);
        Assert.Equal(hashBefore, Result.ValueComparer.GetHashCode(value));
    }

    [Fact]
    public void CollectedList_IsStableAsDictionaryAndHashSetKey()
    {
        var run = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("Inspect(items...) = items\nInspect(1, [2, 3])"));
        var value = Assert.IsType<Result.ListValue>(run.Value);

        var dictionary = new Dictionary<Result, string>(Result.ValueComparer) { [value] = "rest" };
        var set = new HashSet<Result>(Result.ValueComparer) { value };

        ProbeViewForMutation(value.Items);

        var equivalent = List(Atom(1), List(Atom(2), Atom(3)));
        Assert.True(dictionary.ContainsKey(value));
        Assert.True(dictionary.ContainsKey(equivalent));
        Assert.Equal("rest", dictionary[equivalent]);
        Assert.Contains(value, set);
        Assert.Contains(equivalent, set);
    }
}
