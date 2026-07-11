namespace KatLang.Tests;

/// <summary>
/// Deconstruction binding patterns: a comma binding pattern with one movable rest
/// binding. Assignment deconstruction (<c>x, y..., z = RHS</c>) is an unpacking
/// receiver (Python-style): a single sequence-valued right-hand side <c>A</c> is
/// unpacked element-by-element, so <c>x, y, z = A</c> splits <c>A</c> and explicit
/// <c>x, y, z = A...</c> supplies the same items. This unpacking is
/// deconstruction-specific: a function call <c>F(A)</c> still passes <c>A</c> as one
/// argument and needs <c>F(A...)</c> to open it. The rest binding captures its items
/// as one grouped sequence value and may appear at the start, middle, or end.
/// </summary>
public class DeconstructionBindingTests
{
    private static decimal[] Atoms(string source)
        => KatLangEngine.EvaluateToAtoms(source).ToArray();

    private static void AssertAtoms(string source, params decimal[] expected)
        => Assert.Equal(expected, Atoms(source));

    private static bool Fails(string source)
        => KatLangEngine.Run(source).IsFailure;

    // ───────────────────────── Assignment deconstruction ─────────────────────

    [Fact]
    public void Assignment_MovableRest_UnpacksAroundCapturedMiddle()
    {
        // The deconstruction pattern unpacks a stored sequence value (no spread
        // needed). The rest binding captures the middle items as one grouped value.
        const string define = "A = 1, 2, 3, 4, 5\nx, y..., z = A\n";
        AssertAtoms(define + "x", 1);
        AssertAtoms(define + "y", 2, 3, 4);
        AssertAtoms(define + "y.count", 3);
        AssertAtoms(define + "z", 5);
        AssertAtoms(define + "x + y.sum + z", 15);
    }

    [Fact]
    public void Assignment_MovableRest_ExplicitSpread_SuppliesSameItems()
        // Explicit `...` supplies the same items as the bare unpack above.
        => AssertAtoms("A = 1, 2, 3, 4, 5\nx, y..., z = A...\nx, y.count, z", 1, 3, 5);

    [Fact]
    public void Assignment_StoredSequenceValue_AgainstFixedTargets_IsUnpacked()
    {
        // Python-style: `x, y, z = A` unpacks the stored sequence value A.
        const string define = "A = 1, 2, 3\nx, y, z = A\n";
        AssertAtoms(define + "x", 1);
        AssertAtoms(define + "y", 2);
        AssertAtoms(define + "z", 3);
    }

    [Fact]
    public void Assignment_StoredSequenceValue_ExplicitSpread_BindsFixedTargets()
    {
        // Explicit `...` supplies the same items as the bare unpack above.
        const string define = "A = 1, 2, 3\nx, y, z = A...\n";
        AssertAtoms(define + "x", 1);
        AssertAtoms(define + "y", 2);
        AssertAtoms(define + "z", 3);
    }

    [Fact]
    public void Assignment_DirectItemSupply_Deconstructs()
    {
        const string define = "x, y..., z = 1, 2, 3, 4, 5\n";
        AssertAtoms(define + "x", 1);
        AssertAtoms(define + "y", 2, 3, 4);
        AssertAtoms(define + "z", 5);
    }

    [Fact]
    public void Assignment_RestForStoredSequenceValue_Unpacks()
    {
        // `first, rest... = A` unpacks A: first = 1, rest = (2, 3).
        const string define = "A = 1, 2, 3\nfirst, rest... = A\n";
        AssertAtoms(define + "first", 1);
        AssertAtoms(define + "rest", 2, 3);
        AssertAtoms(define + "rest.count", 2);
    }

    [Fact]
    public void Assignment_RestForStoredSequenceValue_ExplicitSpread_SuppliesSameItems()
    {
        // `first, rest... = A...` supplies the same items as the bare unpack above.
        const string define = "A = 1, 2, 3\nfirst, rest... = A...\n";
        AssertAtoms(define + "first", 1);
        AssertAtoms(define + "rest", 2, 3);
    }

    [Fact]
    public void Assignment_RestCapturesZeroItems_AsEmptyGroupedValue()
    {
        const string define = "x, y..., z = 1, 2\n";
        AssertAtoms(define + "x", 1);
        AssertAtoms(define + "y.count", 0);
        AssertAtoms(define + "z", 2);
        // The empty rest is a grouped sequence value, so summing it is 0.
        AssertAtoms(define + "x + y.sum + z", 3);
    }

    [Fact]
    public void Assignment_NoRest_RequiresExactCount()
    {
        AssertAtoms("x, y = 1, 2\nx", 1);
        AssertAtoms("x, y = 1, 2\ny", 2);
    }

    [Theory]
    [InlineData("A = 1, 2, 3\nx, y, z = A")]
    [InlineData("A = 1, 2, 3\nw, x, y, z = A")]   // more targets still share one source
    [InlineData("A = 1, 2, 3\nfirst, rest... = A")]
    public void Assignment_RightHandSide_IsHoistedIntoSingleSharedSource(string source)
    {
        // Deterministic structural guard for once-evaluation: the elaborator hoists the
        // right-hand side into exactly one synthetic `$deconstruct$N` source property,
        // and every target binds from that shared source — regardless of how many
        // targets there are. A re-evaluation regression (inlining the RHS into each
        // target, or hoisting one source per target) would produce zero shared sources
        // or several, which this catches without relying on runtime non-determinism.
        var root = (Algorithm.User)Parser.Parse(source).Root;

        var shared = Assert.Single(
            root.Properties, p => p.Name.StartsWith("$deconstruct$", StringComparison.Ordinal));

        // The single shared source carries the right-hand side itself (the `A` reference).
        var sharedBody = Assert.IsType<Algorithm.User>(shared.Value);
        var rhs = Assert.Single(sharedBody.Output);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(rhs).Name);
    }

    [Fact]
    public void Assignment_RightHandSide_IsEvaluatedOnce()
    {
        // Runtime complement to Assignment_RightHandSide_IsHoistedIntoSingleSharedSource:
        // that test proves the elaboration shares one source; this one proves the shared
        // source is actually evaluated only once at run time (via the zero-arg property
        // cache). KatLang has no deterministic side-effect/counter primitive to observe
        // evaluation count directly, so we use the one observable non-determinism —
        // Math.RandomInt — as a probe: the right-hand side is evaluated once, not
        // re-evaluated per target, so an ordered pair stays ordered. (Re-evaluating per
        // target would draw independent pairs, making x <= y hold only by chance.)
        // Repeated to make a per-target re-evaluation regression statistically certain
        // to fail (false-pass probability under a regression is ~2^-25).
        const string source =
            "x, y = order((Math.RandomInt(1, 1000000), Math.RandomInt(1, 1000000)))\nx, y";
        for (var i = 0; i < 25; i++)
        {
            var atoms = Atoms(source);
            Assert.Equal(2, atoms.Length);
            Assert.True(atoms[0] <= atoms[1], "deconstruction right-hand side must be evaluated once");
        }
    }

    [Fact]
    public void Assignment_RestAtStart_CapturesLeadingItems()
    {
        const string define = "head..., last = 1, 2, 3\n";
        AssertAtoms(define + "head", 1, 2);
        AssertAtoms(define + "head.count", 2);
        AssertAtoms(define + "last", 3);
    }

    [Fact]
    public void Assignment_RestAtStart_ForStoredSequenceValue_Unpacks()
    {
        // Head-position rest also unpacks a stored sequence value (Option A applies
        // at head, middle, and tail rest positions). `head..., last = A` opens A.
        const string define = "A = 1, 2, 3\nhead..., last = A\n";
        AssertAtoms(define + "head", 1, 2);
        AssertAtoms(define + "head.count", 2);
        AssertAtoms(define + "last", 3);
    }

    [Fact]
    public void Assignment_RestAtStart_ForStoredSequenceValue_ExplicitSpread_SuppliesSameItems()
    {
        // `head..., last = A...` supplies the same items as the bare unpack above.
        const string define = "A = 1, 2, 3\nhead..., last = A...\n";
        AssertAtoms(define + "head", 1, 2);
        AssertAtoms(define + "head.count", 2);
        AssertAtoms(define + "last", 3);
    }

    [Fact]
    public void Assignment_RestAtEnd_CapturesTrailingItems()
    {
        const string define = "first, tail... = 1, 2, 3\n";
        AssertAtoms(define + "first", 1);
        AssertAtoms(define + "tail", 2, 3);
        AssertAtoms(define + "tail.count", 2);
    }

    [Fact]
    public void Assignment_MatchingAlgorithm_BindsPrefixSuffixAndMiddle()
    {
        // p1, p2, rest..., q1, q2 against i1..i7 binds the middle three to rest.
        const string define = "p1, p2, rest..., q1, q2 = 1, 2, 3, 4, 5, 6, 7\n";
        AssertAtoms(define + "p1, p2, rest.count, q1, q2", 1, 2, 3, 6, 7);
        AssertAtoms(define + "rest", 3, 4, 5);
    }

    [Fact]
    public void Assignment_DeconstructionAfterOutputLine_DoesNotAbsorbIntoOutput()
    {
        // An implicit output line ends at a following deconstruction assignment:
        // the output stays the single `F(A...)` row (15), and `x, y..., z = A` defines
        // its own (unused) properties instead of being swallowed as more output.
        AssertAtoms(
            """
            A = 1, 2, 3, 4, 5
            F(x, y..., z) = x + y.sum + z

            F(A...)

            x, y..., z = A
            """,
            15);

        // The deconstructed properties remain usable when referenced after the
        // output line. `= A` unpacks the stored sequence value.
        AssertAtoms(
            """
            A = 1, 2, 3, 4, 5
            x, y..., z = A
            x + y.sum + z
            """,
            15);
    }

    [Fact]
    public void Assignment_ScalarRhs_RestAtEndCapturesZeroItems()
    {
        // A scalar right-hand side is a one-item supply, so the fixed `first` binds
        // it and the rest captures zero items.
        const string define = "first, tail... = 1\n";
        AssertAtoms(define + "first", 1);
        AssertAtoms(define + "tail.count", 0);
        AssertAtoms(define + "tail"); // the empty rest is the empty sequence value (), which has no atoms
    }

    [Fact]
    public void Assignment_ScalarRhs_RestAtStartCapturesZeroItems()
    {
        const string define = "head..., last = 1\n";
        AssertAtoms(define + "head.count", 0);
        AssertAtoms(define + "head"); // the empty rest is the empty sequence value (), which has no atoms
        AssertAtoms(define + "last", 1);
    }

    [Fact]
    public void Assignment_SingleRestOnly_IsNotAValidAssignmentForm()
    {
        // `all... = RHS` is not a comma deconstruction (no comma) and not an
        // ordinary single-name assignment, so it is rejected. Rest-only collecting
        // belongs to function parameters (Sum(values...)), not to assignment.
        Assert.True(Fails("all... = 1, 2, 3\nall"));
        Assert.True(Fails("all... = 1\nall"));
    }

    [Theory]
    [InlineData("x, y = 1, 2, 3\nx")]           // too many items
    [InlineData("x, y..., z = 1\nx")]           // fewer than the two fixed bindings
    public void Assignment_ArityMismatch_Fails(string source)
        => Assert.True(Fails(source));

    [Fact]
    public void Assignment_TooFewItems_ReportsArityMismatch()
    {
        // A scalar right-hand side is a one-item supply; matching it against two
        // fixed targets is an arity mismatch (expected 2, actual 1), not a generic
        // shape/BadArity failure.
        var result = Evaluator.Run(new Expr.Block(Parser.Parse("x, y = 1\nx").Root));

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(2, arity.Expected);
        Assert.Equal(1, arity.Actual);
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    [Fact]
    public void Assignment_MultipleRestBindings_IsRejected()
    {
        var result = KatLangEngine.Run("a..., b... = 1, 2, 3\na");
        Assert.True(result.IsFailure);
        Assert.Contains("at most one rest binding", result.ToDisplayString(), StringComparison.Ordinal);
    }

    // ───────────────────── Function-parameter deconstruction ──────────────────

    [Fact]
    public void Parameter_SingleGroupedArgument_IsNotImplicitlyDeconstructed()
        => Assert.True(Fails("A = 1, 2, 3, 4, 5\nF(x, y..., z) = x + y.sum + z\nF(A)"));

    [Fact]
    public void Parameter_SpreadArgument_IsDeconstructed()
        => AssertAtoms("A = 1, 2, 3, 4, 5\nF(x, y..., z) = x + y.sum + z\nF(A...)", 15);

    [Fact]
    public void Parameter_DirectItemSupply_IsDeconstructed()
        => AssertAtoms("F(x, y..., z) = x + y.sum + z\nF(1, 2, 3, 4, 5)", 15);

    [Fact]
    public void Parameter_RestCapturesZeroItems()
        // x = 1, y = (), z = 2; sum of the empty rest is 0.
        => AssertAtoms("F(x, y..., z) = x + y.sum + z\nF(1, 2)", 3);

    [Fact]
    public void Parameter_MatchingAlgorithm_BindsPrefixSuffixAndMiddle()
        => AssertAtoms(
            "F(p1, p2, rest..., q1, q2) = p1, p2, rest.count, q1, q2\nF(1, 2, 3, 4, 5, 6, 7)",
            1, 2, 3, 6, 7);

    [Fact]
    public void Parameter_ScalarArgument_RestCapturesZeroItems()
        // A single scalar argument is a one-item supply: first = 1, tail = ().
        => AssertAtoms("F(first, tail...) = first, tail.count\nF(1)", 1, 0);

    [Fact]
    public void Parameter_MixedRestShape_DistinguishesPlainArgumentFromSpread()
    {
        // G(first, rest...): a plain stored sequence value A is one supplied argument,
        // so first captures the whole value (count 2) and rest is empty (count 0).
        // Explicit spread opens A into two supplied arguments, so first = 1 (count 1)
        // and rest = (2) (count 1). Flattened atoms alone cannot see this difference,
        // so the body exposes the structural counts.
        const string g = "A = 1, 2\nG(first, rest...) = first.count, rest.count\n";
        AssertAtoms(g + "G(A)", 2, 0);      // first = (1, 2), rest = ()
        AssertAtoms(g + "G(A...)", 1, 1);   // first = 1, rest = (2)
    }

    // ─────────────── Existing behavior preserved (regression guards) ──────────

    [Fact]
    public void SingleNameCapture_StillPacksRightHandSide()
        => AssertAtoms("c = 1, 2, 3\nc.count", 3);

    [Fact]
    public void RestOnlyVariadicCall_ConsumesItemSupply()
    {
        // Rest-only `Sum(values...)` captures the supplied argument stream. A single
        // grouped argument and separate slots display the same sum here, but mixed
        // fixed/rest shapes below make the boundary difference observable.
        AssertAtoms("c = 1, 2, 3\nSum(values...) = values.sum\nSum(c)", 6);
        AssertAtoms("Sum(values...) = values.sum\nSum(1, 2, 3)", 6);
    }

    [Fact]
    public void ExpressionSpread_StillOpensInExpressionPosition()
    {
        AssertAtoms("A = 1, 2, 3\n(A...).count", 3);
        AssertAtoms("A = 1, 2, 3\nB = 4, 5\n(A..., B...).count", 5);
    }

    // ─────────────────── Aspect 2: unified item-supply binding ─────────────────

    [Fact]
    public void RestOnly_AllCallFormsCanDisplaySameCollectionResult()
    {
        // G(x...) = x.sum can hide call-boundary differences: plain A and
        // grouped `(1, 2, 3, 4, 5)` each supply one sequence-valued argument,
        // while A... and inline items supply five arguments. The rest capture
        // plus collection-style .sum makes all four display 15.
        const string g = "A = 1, 2, 3, 4, 5\nG(x...) = x.sum\n";
        AssertAtoms(g + "G(A)", 15);
        AssertAtoms(g + "G(A...)", 15);
        AssertAtoms("G(x...) = x.sum\nG(1, 2, 3, 4, 5)", 15);
        AssertAtoms("G(x...) = x.sum\nG((1, 2, 3, 4, 5))", 15);
    }

    [Fact]
    public void RestOnly_EmptyCallBindsEmptyItemSupply()
        // An empty call binds an empty item supply (min arity 0): sum is 0.
        => AssertAtoms("G(x...) = x.sum\nG()", 0);

    [Fact]
    public void RestWithSuffix_PlainSequenceArgumentPreservesBoundary()
    {
        // Plain A supplies one sequence-valued argument, so y receives that value
        // and the numeric body fails. Explicit spread and direct item supplies work.
        const string f = "A = 1, 2, 3, 4, 5\nF(x..., y) = x.sum + y\n";
        Assert.True(Fails(f + "F(A)"));
        AssertAtoms(f + "F(A...)", 15);
        AssertAtoms("F(x..., y) = x.sum + y\nF(1, 2, 3, 4, 5)", 15);
        Assert.True(Fails("F(x..., y) = x.sum + y\nF((1, 2, 3, 4, 5))"));
    }

    [Fact]
    public void RestWithPrefixAndSuffix_PlainSequenceArgumentPreservesBoundary()
    {
        const string h = "A = 1, 2, 3, 4, 5\nH(x, y..., z) = x + y.sum + z\n";
        Assert.True(Fails(h + "H(A)"));
        AssertAtoms(h + "H(A...)", 15);
        AssertAtoms("H(x, y..., z) = x + y.sum + z\nH(1, 2, 3, 4, 5)", 15);
        Assert.True(Fails("H(x, y..., z) = x + y.sum + z\nH((1, 2, 3, 4, 5))"));
    }

    [Fact]
    public void SiblingGroupedValues_ArePreservedUnlessExplicitlyOpened()
    {
        // Multiple sibling grouped values are preserved (count 2), not flattened.
        AssertAtoms("A = 1, 2\nB = 3, 4\nG(x...) = x.count\nG(A, B)", 2);
        // Only explicit `...` opens them into one item supply (count 4).
        AssertAtoms("A = 1, 2\nB = 3, 4\nG(x...) = x.count\nG(A..., B...)", 4);
    }

    [Fact]
    public void RepeatedSingletonBoundary_DoesNotImplicitlyOpenCallArgument()
    {
        // Redundant unary grouping canonicalizes the value, but function calls still
        // receive one argument unless explicit spread is written.
        AssertAtoms("G(x...) = x.sum\nG(((1, 2, 3, 4, 5)))", 15);
        Assert.True(Fails("F(x..., y) = x.sum + y\nF(((1, 2, 3, 4, 5)))"));
        AssertAtoms("F(x..., y) = x.sum + y\nF(((1, 2, 3, 4, 5))...)", 15);
        Assert.True(Fails("H(x, y..., z) = x + y.sum + z\nH(((1, 2, 3, 4, 5)))"));
        AssertAtoms("H(x, y..., z) = x + y.sum + z\nH(((1, 2, 3, 4, 5))...)", 15);
    }

    [Fact]
    public void ParenthesizedScalarPropertyItem_PatternCallMatchesAssignmentDeconstruction()
    {
        // `(A)` inside a written sequence value is one grouping level around a
        // single already-evaluated item, so both binding forms receive the
        // scalar 5 — never a literal-unwritable orphan `(5)`.
        AssertAtoms("A = 5\nx, y = ((A), 6)\nx == 5", 1);
        AssertAtoms("A = 5\nF((x, y)) = x == 5\nF(((A), 6))", 1);
    }

    [Fact]
    public void ParenthesizedSequencePropertyItem_PatternCallMatchesAssignmentDeconstruction()
    {
        // With A = (1, 2) both binding forms receive the canonical (1, 2) as
        // one item, so x:0 selects 1 in both.
        AssertAtoms("A = 1, 2\nx, y = ((A), 6)\nx:0, y", 1, 6);
        AssertAtoms("A = 1, 2\nF((x, y)) = x:0, y\nF(((A), 6))", 1, 6);
    }

    [Fact]
    public void LiteralWrappedPair_DeconstructionOpensWhilePatternCallReadsWrittenSlots()
    {
        // Assignment deconstruction is an unpacking receiver: ((1, 2))
        // evaluates once to the canonical (1, 2) and its items match the
        // targets element-by-element.
        AssertAtoms("x, y = ((1, 2))\nx, y", 1, 2);

        // A sequence-value parameter pattern reads the inline-written
        // argument's slots instead: ((1, 2)) writes one item, so binding
        // (x, y) arity-errors rather than opening the single written item.
        Assert.True(Fails("F((x, y)) = x\nF(((1, 2)))"));

        // The same value stored in a property opens canonically at the call.
        AssertAtoms("A = ((1, 2))\nF((x, y)) = x\nF(A)", 1);
    }

    [Fact]
    public void CallbackSequenceValueDeconstruction_OnScalarElement_StaysStrict()
        // Callback deconstruction is deferred: the counted callback path keeps the
        // strict singleton-only scalar fallback (matching Lean), so a sequence-value
        // deconstruction callback applied to scalar map elements fails instead of
        // silently deconstructing each scalar into first/tail.
        => Assert.True(Fails("F((first, tail...)) = first, tail.count\nmap((1, 2, 3), F)"));

    [Fact]
    public void CallbackDeconstruction_OnSequenceValueRows_BindsPerRow()
    {
        // A deconstruction-shaped callback applied per sequence-value row binds
        // x/y.../z within each row: (1, 2, 3) -> 1 + 2 + 3 = 6 and
        // (4, 5, 6) -> 4 + 5 + 6 = 15. The flat and sequence-value parameter
        // forms agree here. This pins the deferred callback boundary: row
        // callbacks work while scalar-element deconstruction stays strict above.
        AssertAtoms("Rows = (1, 2, 3), (4, 5, 6)\nF(x, y..., z) = x + y.sum + z\nRows.map(F)", 6, 15);
        AssertAtoms("Rows = (1, 2, 3), (4, 5, 6)\nF((x, y..., z)) = x + y.sum + z\nRows.map(F)", 6, 15);
    }
}
