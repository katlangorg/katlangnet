using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorCollectingParameterTests
{
    // â”€â”€ Grace operator end-to-end tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_CollectingParameter_DotCallReceiverOpensOneLevelAtTheLoneCollector()
    {
        // Dot-call passes a value: the receiver is the one leading argument of
        // `Collect(Arg)` — a written sequence value that is the lone collector's
        // whole segment, so the collector supply-boundary law opens it one
        // level: [1, 2, 3] (count 3). A list receiver stays one exact item, and
        // beside a written argument the sequence is one collected item.
        AssertEval(
            """
            Arg = 1, 2, 3
            Collect(*list) = list
            Arg.Collect.count
            """,
            3);
        AssertEval(
            """
            Arg = [1, 2, 3]
            Collect(*list) = list
            Arg.Collect.count
            """,
            1);
        AssertEval(
            """
            Arg = 1, 2, 3
            Collect(*list) = list
            Arg.Collect(0).count
            """,
            2);
    }

    [Fact]
    public void Eval_CollectingParameter_ExplicitReceiverSpreadAlsoSuppliesReceiverTopLevelItems()
    {
        AssertEval(
            """
            Arg = 1, 2, 3
            Collect(*list) = list
            Arg*.Collect.count
            """,
            3);

        // The parenthesized spread is a capture — one written sequence value —
        // which the lone collector opens one level again, exactly like the bare
        // named receiver.
        AssertEval(
            """
            Arg = 1, 2, 3
            Collect(*list) = list
            (Arg*).Collect.count
            """,
            3);
    }

    [Fact]
    public void Eval_NormalParameter_DotCallStillPreservesReceiverBoundary()
    {
        AssertEval(
            """
            Arg = 1, 2, 3
            Collect(list) = list
            Arg.Collect.count
            """,
            3);
    }

    [Fact]
    public void Eval_CollectingParameter_PreservesNestedSequenceValues()
    {
        // The spread receiver supplies the two pair items as ordinary slots, and
        // each stays one opaque sequence value inside the collected list:
        // [(1, 2), (3, 4)].
        AssertEval(
            """
            Arg = (1, 2), (3, 4)
            Collect(*list) = list
            Arg*.Collect.count
            """,
            2);
    }

    [Fact]
    public void Eval_CollectingParameter_DoesNotReplaceAtomsRecursiveFlattening()
    {
        AssertEval(
            """
            Arg = (1, 2), (3, 4)
            Collect(*list) = list
            atoms(Arg.Collect).count
            """,
            4);
    }

    [Fact]
    public void Eval_CollectingParameter_WithPrefix_BindsFrontItem()
    {
        AssertEval(
            """
            Arg = 1, 2, 3
            Head(first, *rest) = first
            Head(1, (2, 3))
            """,
            1);
    }

    [Fact]
    public void Eval_CollectingParameter_WithPrefix_CapturesRemainingItems()
    {
        // The spread supplies 2 and 3 as separate slots, so the collecting parameter
        // collects the list [2, 3]. (An unspread `(2, 3)` would be one collected item.)
        AssertEval(
            """
            Arg = 1, 2, 3
            Tail(first, *rest) = rest
            Tail(1, (2, 3)*).count
            """,
            2);
    }

    [Fact]
    public void Eval_CollectingParameter_WithSuffix_CapturesLeadingItems()
    {
        AssertEval(
            """
            Arg = 1, 2, 3
            Init(*init, last) = init
            Init((1, 2)*, 3).count
            """,
            2);
    }

    [Fact]
    public void Eval_CollectingParameter_WithSuffix_BindsBackItem()
    {
        AssertEval(
            """
            Arg = 1, 2, 3
            Last(*init, last) = last
            Last(Arg, 3)
            """,
            3);
    }

    [Fact]
    public void Eval_CollectingParameter_BeforeSuffix_SupportsSequenceStyleScale()
    {
        // The spread receiver supplies the items as ordinary slots; the suffix
        // binds the factor.
        AssertEval(
            """
            Arg = 1, 2, 3
            Scale(*values, factor) = values.map{n * factor}
            Arg*.Scale(10)
            """,
            10, 20, 30);
    }

    [Fact]
    public void Eval_CollectingParameter_InlineSequenceSpreadDotCallWithSuffixSuppliesReceiverItems()
    {
        AssertEvalSequenceModes(
            """
            TotalWithFee(*values, fee) = values.sum + fee
            (10, 20, 30)*.TotalWithFee(5)
            """,
            65);
    }

    [Fact]
    public void Eval_CollectingParameter_NamedMultiOutputSpreadDotCallWithSuffixSuppliesReceiverItems()
    {
        AssertEvalSequenceModes(
            """
            TotalWithFee(*values, fee) = values.sum + fee
            Data = 10, 20, 30
            Data*.TotalWithFee(5)
            """,
            65);
    }

    [Fact]
    public void Eval_CollectingParameter_InlineTupleSpreadDotCallMatchesNamedReceiver()
    {
        AssertEvalSequenceModes(
            """
            TotalWithFee(*values, fee) = values.sum + fee
            Data = 10, 20, 30
            Data*.TotalWithFee(5), (10, 20, 30)*.TotalWithFee(5)
            """,
            65, 65);
    }

    [Fact]
    public void Eval_CollectingParameter_NestedInlineTupleDotCall_ReceiverOpensOneLevel()
    {
        // The nested capture `((10, 20, 30))` is one sequence value, and so is
        // the single group `(10, 20, 30)`: dot-call passes a value, the suffix
        // binds 5 first, and the lone written sequence left to the collector
        // opens one level — 65, exactly like the fluent spread forms above. A
        // genuinely nested receiver `((10, 20), 30)` opens exactly ONE level,
        // so the inner pair stays one element and the numeric `values.sum` fails.
        AssertEval(
            """
            TotalWithFee(*values, fee) = values.sum + fee
            ((10, 20, 30)).TotalWithFee(5)
            """,
            65);

        var result = EvalFull(
            """
            TotalWithFee(*values, fee) = values.sum + fee
            ((10, 20), 30).TotalWithFee(5)
            """);
        Assert.True(result.IsError, $"Expected failure but got: {(result.IsOk ? result.Value : null)}");
        Assert.IsType<EvalError.BadArity>(Innermost(result.Error));
        Assert.Contains(
            "sum expects each collection element to be a single numeric value",
            KatLangError.FromEvalError(result.Error).Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_NormalParameter_InlineTupleDotCallStillPreservesReceiverBoundary()
    {
        AssertEvalSequenceModes(
            """
            Collect(list) = list.count
            (10, 20, 30).Collect
            """,
            3);
    }

    [Fact]
    public void Eval_CollectingParameter_SpreadReceiverExpandsReceiverItems()
    {
        // The spread marker opens a receiver into final items:
        // `(10, 20, 30)*.Collect` is `Collect(10, 20, 30)`, so the collecting
        // parameter collects [10, 20, 30]; the plain inline group
        // `(10, 20, 30).Collect` passes ONE written sequence value, which the
        // lone collector opens one level to the same three items, while a list
        // receiver stays one exact item.
        AssertEvalSequenceModes(
            """
            Collect(*list) = list.count
            (10, 20, 30)*.Collect
            """,
            3);
        AssertEvalSequenceModes(
            """
            Collect(*list) = list.count
            (10, 20, 30).Collect
            """,
            3);
        AssertEvalSequenceModes(
            """
            Collect(*list) = list.count
            [10, 20, 30].Collect
            """,
            1);
    }

    [Fact]
    public void Eval_SequenceBuiltin_InlineTupleDotCallBehaviorIsUnchanged()
    {
        AssertEvalSequenceModes("(10, 20, 30).sum", 60);

        AssertEvalSequenceModes("((10, 20, 30)).sum", 60);
    }

    [Fact]
    public void Eval_CollectingParameter_BeforeTwoSuffixes_SupportsSequenceStyleFilter()
    {
        AssertEval(
            """
            Arg = 1, 2, 3, 4, 5
            Between(*values, min, max) = values.filter{n >= min and n <= max}
            Arg*.Between(2, 4)
            """,
            2, 3, 4);
    }

    [Fact]
    public void Eval_CollectingParameter_PlainCallBindsListSourceAsOneElement()
    {
        // Arg is the exact list [1, 2, 3]; the plain call passes it as one
        // argument, so the collecting parameter collects [[1, 2, 3]] and the numeric body hits
        // the per-element constraint. Lean twin: Qmean(Vector) numeric error.
        var result = EvalFull(
            """
            Arg = range(1, 3)
            Qmean(*values) = values.sum / values.count
            Qmean(Arg)
            """);

        Assert.True(result.IsError);
        Assert.Contains(
            "sum expects each collection element to be a single numeric value",
            KatLangError.FromEvalError(result.Error).Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_CollectingParameter_ExplicitSpreadCapturesSourceItems()
    {
        AssertEval(
            """
            Arg = range(1, 3)
            Qmean(*values) = values.sum / values.count
            Qmean(Arg*)
            """,
            2);
    }

    [Fact]
    public void Eval_CollectingParameter_SpreadReceiverDotCallCapturesRangeItems()
    {
        // The fluent spread receiver opens the range list's one boundary,
        // supplying its items to the collecting parameter as ordinary slots.
        AssertEval(
            """
            Arg = range(1, 3)
            Qmean(*values) = values.sum / values.count
            Arg*.Qmean
            """,
            2);
    }

    [Fact]
    public void Eval_NormalParameter_WithSingleSequenceValueRange_RemainsOrdinary()
    {
        var result = EvalFull(
            """
            Arg = range(1, 3)
            Qmean_err(list) = list.sum / list.count
            Qmean_err(Arg)
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([2m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_CollectingParameter_ReportsBindingErrorWhenNormalParametersCannotBind()
    {
        // F(first, *rest, last) is a comma deconstruction parameter list. F(1)
        // supplies one scalar item (not implicitly opened), but the two fixed
        // bindings first and last need at least two items.
        var result = EvalFull(
            """
            F(first, *rest, last) = first, rest, last
            F(1)
            """);

        Assert.True(result.IsError);
        var error = Innermost(result.Error);
        var arity = Assert.IsType<EvalError.VariadicArityMismatch>(error);
        Assert.Equal(2, arity.ExpectedMinimum);
        Assert.Equal(1, arity.Actual);
    }

    [Fact]
    public void Eval_SequenceValueCollectingParameter_CapturesImmediateSequenceValueItems()
    {
        AssertEval(
            """
            F((*xs)) = xs.count
            F((1, 2, 3))
            """,
            3);
    }

    [Fact]
    public void Eval_SequenceValueCollectingParameter_RemovesOnlyOneSequenceValueBoundary()
    {
        AssertEval(
            """
            F((*xs)) = xs.count
            F(((1, 2), 3))
            """,
            2);
    }

    [Fact]
    public void Eval_SequenceValueCollectingParameter_PreservesNestedSequenceValueItem()
    {
        var result = EvalFull(
            """
            F((*xs)) = xs:0
            F(((1, 2), 3))
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(ResultFromAtoms(1, 2), result.Value),
            $"Expected (1, 2) but got {result.Value}");
    }

    [Fact]
    public void Eval_SequenceValueCollectingParameter_IgnoresRedundantCallSiteGrouping()
    {
        // PARENTHESES GROUP SYNTAX: a group of one non-spread slot is that slot, so
        // `((1, 2, 3))` IS the sequence value `(1, 2, 3)` at every depth. The lone
        // top-level collector (1) opens the one written sequence slot one level
        // (count 3), and the pattern callee (2) opens the argument's VALUE one level
        // — the same three items whatever grouping the call site wrote. A pattern
        // never sees a "written level": non-unary structure is what it opens, so
        // `((1, 2), 3)` and `(1, (2, 3))` count 2.
        AssertEval(
            """
            CountSequenceValue1(*values) = values.count
            CountSequenceValue2((*values)) = values.count

            CountSequenceValue1((1, 2, 3))
            CountSequenceValue1(((1, 2, 3)))
            CountSequenceValue2((1, 2, 3))
            CountSequenceValue2(((1, 2, 3)))
            CountSequenceValue2((((1, 2, 3))))
            CountSequenceValue2(((1, 2), 3))
            CountSequenceValue2((1, (2, 3)))
            """,
            3, 3, 3, 3, 3, 2, 2);
    }

    [Fact]
    public void Eval_NestedSequenceValueCollectingParameter_OpensOneRealBoundaryPerLevel()
    {
        // A nested pattern `((*values))` opens two boundaries: the argument must open
        // to exactly ONE item that itself opens. Unary sequence structure never
        // survives normalization (`(((1, 2, 3)))` IS `(1, 2, 3)`), so only a
        // one-element LIST can supply a real outer structural level. Scalars also
        // bind via the ordinary one-item fallback (no sequence wrapper is created).
        AssertEval(
            """
            CountSequenceValue3(((*values))) = values.count
            CountSequenceValue3([(1, 2, 3)])
            CountSequenceValue3([[1, 2, 3]])
            """,
            3, 3);

        foreach (var argument in new[] { "(1, 2, 3)", "((1, 2, 3))", "(((1, 2, 3)))" })
        {
            var result = EvalFull(
                "CountSequenceValue3(((*values))) = values.count\n"
                + $"CountSequenceValue3({argument})");

            Assert.True(result.IsError);
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
            Assert.Equal(1, arity.Expected);
            Assert.Equal(3, arity.Actual);
        }
    }

    [Fact]
    public void Eval_SequenceValueCollectingParameter_GroupedPropertyReferenceIsTheReference()
    {
        // The bare reference supplies Inner's canonical value, which the pattern
        // opens into its three items — and redundant grouping around the
        // reference is the reference: `(Inner)` and `((Inner))` supply exactly the
        // same value, never a "written level" for the pattern to consume.
        AssertEval(
            """
            Inner = (1, 2, 3)
            CountSequenceValue2((*values)) = values.count

            CountSequenceValue2(Inner)
            CountSequenceValue2((Inner))
            CountSequenceValue2(((Inner)))
            """,
            3, 3, 3);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_ParenthesizedScalarPropertyItemIsNotAnOrphanSequenceValue()
    {
        // `(A)` is erased to `A`, whose value occupies one item beside 6,
        // so the bound item is the scalar 5 itself — never a
        // literal-unwritable orphan sequence value displaying as `(5)`.
        var result = EvalFull(
            """
            A = 5
            F((x, y)) = x
            F(((A), 6))
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(new Result.Atom(5), result.Value),
            $"Expected 5 but got {result.Value}");
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_ParenthesizedScalarPropertyItemComparesEqualToScalar()
    {
        AssertEvalBool(
            """
            A = 5
            F((x, y)) = x == 5
            F(((A), 6))
            """,
            true);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_ParenthesizedSequencePropertyItemStaysOneCanonicalItem()
    {
        // With A = (1, 2), redundant `(A)` is `A` and supplies the canonical
        // value (1, 2) as one item beside 6 — not an orphan ((1, 2)) — matching
        // assignment deconstruction of the same right-hand side.
        var result = EvalFull(
            """
            A = 1, 2
            F((x, y)) = x
            F(((A), 6))
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(ResultFromAtoms(1, 2), result.Value),
            $"Expected (1, 2) but got {result.Value}");
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_EmptySequenceSiblingItemIsPreserved()
    {
        // A non-spread `()` item is one visible item, exactly as in ordinary
        // sequence-value construction: the pattern sees ((), 6), so x binds ()
        // and y binds 6.
        var result = EvalFull(
            """
            F((x, y)) = x
            F(((), 6))
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(new Result.SequenceValue([]), result.Value),
            $"Expected () but got {result.Value}");

        AssertEval(
            """
            F((x, y)) = y
            F(((), 6))
            """,
            6);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_GroupedEmptySequenceItemCanonicalizesLikeEmptySequence()
    {
        // `(())` normalizes to `()`, so as a written item it behaves exactly
        // like a bare `()` item.
        AssertEval(
            """
            F((x, y)) = y
            F(((()), 6))
            """,
            6);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_SpreadOfEmptyStillContributesNoItems()
    {
        // Only an explicit spread contributes zero items: E* with E = ()
        // vanishes, so the pattern sees the single item 6.
        AssertEval(
            """
            E = ()
            F((*xs)) = xs.count
            F((E*, 6))
            """,
            1);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_LiteralWrappedPairArgumentOpensLikeThePair()
    {
        // `((1, 2))` IS the canonical pair (1, 2) — parentheses group syntax — so the
        // sequence-value pattern (x, y) opens it and binds x = 1, at every redundant
        // depth and beside a trailing fixed argument; no written slot survives for
        // the pattern to reject, and no orphan ((1, 2)) is ever minted.
        AssertEval(
            """
            Wrap((x, y)) = x
            KeepFirst((x, y), z) = x + z
            Wrap((1, 2))
            Wrap(((1, 2)))
            Wrap((((1, 2))))
            KeepFirst(((1, 2)), 3)
            """,
            1, 1, 1, 4);

        // The pattern still demands exactly two items: a grouped three-item value is
        // the same arity error whatever the grouping depth.
        foreach (var argument in new[] { "(1, 2, 3)", "((1, 2, 3))" })
        {
            AssertEvalFailsWithArityMismatch(
                "Wrap((x, y)) = x\n" + $"Wrap({argument})",
                expected: 2,
                actual: 3);
        }
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_PropertyStoredWrappedPairOpensCanonically()
    {
        // A = ((1, 2)) normalizes at construction to (1, 2); Wrap(A) opens
        // the stored canonical value, binds x = 1, and every observation —
        // display, count, .count, equality against both writable spellings,
        // and navigation — agrees on the scalar 1.
        AssertEvalResults(
            """
            Wrap((x, y)) = x
            A = ((1, 2))
            R = Wrap(A)
            R, count(R), R.count, R == (1, 2), R == ((1, 2)), R:0
            """,
            new Result.Atom(1), new Result.Atom(1), new Result.Atom(1), new Result.Bool(false), new Result.Bool(false), new Result.Atom(1));
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_SingletonPatternOpensTheArgumentValue()
    {
        // A singleton sequence-value pattern `(x)` opens the argument's VALUE to
        // exactly one item: a pair opens to two (arity error, in every redundant
        // grouping), while a one-element list opens to its element — the canonical
        // (1, 2), never a literal-unwritable orphan ((1, 2)).
        foreach (var argument in new[] { "(1, 2)", "((1, 2))", "(((1, 2)))" })
        {
            AssertEvalFailsWithArityMismatch(
                "IdSeq((x)) = x\n" + $"IdSeq({argument})",
                expected: 1,
                actual: 2);
        }

        var result = EvalFull(
            """
            IdSeq((x)) = x
            IdSeq([(1, 2)])
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(ResultFromAtoms(1, 2), result.Value),
            $"Expected (1, 2) but got {result.Value}");

        // count, .count, equality against both writable literal spellings, and
        // navigation all agree with the canonical (1, 2).
        AssertEvalResults(
            """
            IdSeq((x)) = x
            R = IdSeq([((1, 2))])
            R, count(R), R.count, R == (1, 2), R == ((1, 2)), R:0
            """,
            ResultFromAtoms(1, 2), new Result.Atom(2), new Result.Atom(2), new Result.Bool(true), new Result.Bool(true), new Result.Atom(1));
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_TwoEmptySequenceSiblingItemsBindPositionally()
    {
        // The shallow combiner never drops empty-sequence siblings: ((), ())
        // writes two items, so (x, y) binds both empties positionally and x is
        // the real empty sequence value.
        AssertEvalBools(
            """
            F((x, y)) = x == (), y == ()
            F(((), ()))
            """,
            true, true);

        var result = EvalFull(
            """
            F((x, y)) = x
            F(((), ()))
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(new Result.SequenceValue([]), result.Value),
            $"Expected () but got {result.Value}");
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_WrappedPairReprosAgreeAcrossOptimizerModes()
    {
        // Post-#133 audit follow-up: with the orphan shape unconstructable, the
        // generic, loop-optimized, and sequence-pipeline paths observe
        // identical results through the sequence-value pattern binding repros.
        const string singleCaptureRepro =
            """
            IdSeq((x)) = x
            IdSeq([((1, 2))])
            """;
        AssertEvalResultLoopModes(singleCaptureRepro, ResultFromAtoms(1, 2));
        AssertEvalResultSequenceModes(singleCaptureRepro, ResultFromAtoms(1, 2));

        const string propertyStoredRepro =
            """
            Wrap((x, y)) = x
            A = ((1, 2))
            Wrap(A)
            """;
        AssertEvalResultLoopModes(propertyStoredRepro, Atom(1));
        AssertEvalResultSequenceModes(propertyStoredRepro, Atom(1));
    }

    [Fact]
    public void Eval_SequenceValueCollectingParameter_RequiresSequenceValueArgumentSlot()
    {
        var result = EvalFull(
            """
            F((*xs)) = xs.count
            F(1, 2, 3)
            """);

        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_NestedSequenceValueParameter_WrongShapeFailsWithInnerArityMismatch()
    {
        var result = EvalFull(
            """
            F(((x, y))) = x + y
            F((1, 2))
            """);

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(1, arity.Expected);
        Assert.Equal(2, arity.Actual);
    }

    [Fact]
    public void Eval_SequenceValueParameter_ArityMismatchUsesSequenceValueSignatureDisplay()
    {
        var result = EvalFull(
            """
            PairSum((x, y)) = x + y
            PairSum(1, 2)
            """);

        Assert.True(result.IsError);
        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("PairSum((x, y))", formatted, StringComparison.Ordinal);
        Assert.DoesNotContain("PairSum(x, y)", formatted, StringComparison.Ordinal);
        Assert.Equal("Callable `PairSum((x, y))` expects 1 argument, but was called with 2 arguments.", formatted);
    }

    [Fact]
    public void Eval_SequenceValueCollectingParameter_ArityMismatchUsesSequenceValueCollectingSignatureDisplay()
    {
        var result = EvalFull(
            """
            CountSequenceValue((*values)) = values.count
            CountSequenceValue(1, 2, 3)
            """);

        Assert.True(result.IsError);
        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("CountSequenceValue((*values))", formatted, StringComparison.Ordinal);
        Assert.DoesNotContain("CountSequenceValue(*values)", formatted, StringComparison.Ordinal);
        Assert.Equal("Callable `CountSequenceValue((*values))` expects 1 argument, but was called with 3 arguments.", formatted);
    }

    [Fact]
    public void Eval_PatternedUserCall_TopLevelCaptureCanBindAlgorithmChannel()
    {
        AssertEval(
            """
            Apply(f, (x)) = f(x)
            Double(n) = n * 2
            Apply(Double, (4))
            """,
            8);
    }

    [Fact]
    public void Eval_Count_PatternedUserCall_TopLevelCapturePreservesAlgorithmChannel()
    {
        AssertEval(
            """
            Apply(f, (x)) = f(x)
            Pair(n) = n, n + 1
            Apply(Pair, (4)).count
            """,
            2);
    }

    [Fact]
    public void Eval_PatternedUserCall_SequenceValueNestedCaptureDoesNotBindAlgorithmChannel()
    {
        var result = EvalFull(
            """
            ApplySequenceValue((f)) = f()
            Thunk = 42
            ApplySequenceValue((Thunk))
            """);

        Assert.True(result.IsError);
        var notAlgorithm = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(result.Error));
        Assert.Equal("param(f)", notAlgorithm.Description);
    }

    [Fact]
    public void Eval_PatternedUserCall_SingletonSequenceValuePatternAcceptsScalarFallback()
    {
        AssertEval(
            """
            F((x)) = x
            F(5)
            """,
            5);
    }

    [Fact]
    public void Eval_PatternedUserCall_ExplicitZeroParamBlockExposesSlotsToSequenceValueBinding()
    {
        AssertEval(
            """
            PairSum((x, y)) = x + y
            PairSum({1, 2})
            """,
            3);
    }

    [Fact]
    public void Eval_PatternedCallback_SequenceValueCollectingCaptureKeepsStoredItems()
    {
        AssertEvalSequenceModes(
            """
            Signature((*values)) = values.count * 10 + values.sum
            map(((1, 2, 3), (4, 5)), Signature)
            """,
            36, 29);
    }

    [Fact]
    public void Eval_PatternedCallback_SequenceValueVariadicCountReceivesEachSequenceValueItem()
    {
        AssertEvalSequenceModes(
            """
            CountSequenceValue((*values)) = values.count
            map(((1, 2), (3, 4)), CountSequenceValue)
            """,
            2, 2);
    }

    [Fact]
    public void Eval_SequenceValueCollectingParameter_WithMixedTopLevelParameters()
    {
        AssertEval(
            """
            F((*xs), a, b) = xs.count, a, b
            F((1, 2, 3), 4, 5)
            """,
            3, 4, 5);
    }

    [Fact]
    public void Eval_SequenceValueParameter_AllowsSeparateVariadicsAtDifferentLevels()
    {
        AssertEval(
            """
            F((*inner), *outer) = inner.count, outer.count
            F((1, 2), 3, 4)
            """,
            2, 2);
    }
}
